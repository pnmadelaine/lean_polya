import .comp

namespace polya
open native

meta def sum_form := rb_map expr ℚ

meta def expr_coeff_list_to_expr : list (expr × ℚ) → tactic expr
| [] := return `(0 : ℚ)
| [(e, q)] := tactic.to_expr ``(%%(↑q.reflect : expr)*%%e)
| ((e, q)::t) := do e' ← expr_coeff_list_to_expr t, h ← tactic.to_expr ``(%%(q.reflect : expr)*%%e), tactic.to_expr ``(%%h + %%e')

meta def sum_form.to_expr (sf : sum_form) : tactic expr := 
expr_coeff_list_to_expr sf.to_list

namespace sum_form

private meta def lt_core (sf1 sf2 : sum_form) : bool := sf1.to_list < sf2.to_list
meta def lt : sum_form → sum_form → Prop := λ sf1 sf2, ↑(lt_core sf1 sf2)
meta instance has_lt : has_lt sum_form := ⟨lt⟩
meta instance lt_decidable : decidable_rel lt := by delta lt; apply_instance
meta def cmp : sum_form → sum_form → ordering := cmp_using sum_form.lt

meta instance : has_to_format sum_form := by delta sum_form; apply_instance


meta def zero : sum_form := rb_map.mk _ _
meta instance : has_zero sum_form := ⟨sum_form.zero⟩

meta def of_expr (e : expr) : sum_form := 
mk_rb_map.insert e 1

meta def get_coeff (sf : sum_form) (e : expr) : ℚ :=
match sf.find e with
| some q := q
| none := 0
end

meta def get_nonzero_factors (sf : sum_form) : list (expr × ℚ) :=
sf.to_list

meta def add_coeff (sf : sum_form) (e : expr) (c : ℚ) : sum_form :=
if (sf.get_coeff e) + c = 0 then sf.erase e
else sf.insert e ((sf.get_coeff e) + c)

meta def add (lhs rhs : sum_form) : sum_form :=
rhs.fold lhs (λ e q sf, sf.add_coeff e q)

meta def scale (sf : sum_form) (c : ℚ) : sum_form :=
sf.map (λ q, if q=1/c then 1 else c*q) -- replace this with a real implementation of ℚ

meta def sub (lhs rhs : sum_form) : sum_form :=
lhs.add (rhs.scale (-1))

meta def negate (lhs : sum_form) : sum_form :=
lhs.scale (-1)

meta instance : has_add sum_form := ⟨sum_form.add⟩
meta instance : has_sub sum_form := ⟨sum_form.sub⟩

meta def add_factor (lhs rhs : sum_form) (c : ℚ) : sum_form :=
lhs + (rhs.scale c)

meta def normalize (sf : sum_form) : sum_form :=
match rb_map.to_list sf with
| [] := sf
| (_, m)::t := if abs m = 1 then sf else sf.scale (abs (1/m))
end

meta def is_normalized (sd : sum_form) : bool :=
match rb_map.to_list sd with
| [] := tt
| (_, m)::t := abs m = 1
end

meta def to_tactic_format (sf : sum_form) : tactic format :=
do exs ← sf.to_list.mmap (λ pr, do e ← to_string <$> tactic.pp pr.1, return $ e ++ " ← " ++ repr pr.2 ++ ", "),
   return $ "{ " ++ string.join exs ++ " }"
end sum_form

meta structure sum_form_comp :=
(sf : sum_form) (c : spec_comp) 

meta def sum_form_comp.to_expr (sfc : sum_form_comp) : tactic expr :=
do e ← sfc.sf.to_expr,
   sfc.c.to_comp.to_function e `(0 : ℚ)

namespace sum_form_comp

meta def order : sum_form_comp → sum_form_comp → ordering
| ⟨_, spec_comp.lt⟩ ⟨_, spec_comp.le⟩ := ordering.lt
| ⟨_, spec_comp.lt⟩ ⟨_, spec_comp.eq⟩ := ordering.lt
| ⟨_, spec_comp.le⟩ ⟨_, spec_comp.eq⟩ := ordering.lt
| ⟨sf1, _⟩ ⟨sf2, _⟩ := sum_form.cmp sf1.normalize sf2.normalize

meta instance sum_form_comp.has_to_format : has_to_format sum_form_comp :=
⟨λ sfc, "{" ++ to_fmt (sfc.sf) ++ to_fmt sfc.c ++ "0}"⟩

/--
 This is only valid for positive m
-/
meta def scale (m : ℚ) : sum_form_comp → sum_form_comp
| ⟨sf, c⟩ := ⟨sf.scale m, c⟩


meta def normalize : sum_form_comp → sum_form_comp
| ⟨sf, c⟩ := ⟨sf.normalize, c⟩

meta def is_normalized : sum_form_comp → bool
| ⟨sf, _⟩ := sf.is_normalized

meta def is_contr : sum_form_comp → bool
| ⟨sf, c⟩ := (c = spec_comp.lt) && (sf.keys.length = 0)


meta def of_ineq (lhs rhs : expr) (id : ineq) : sum_form_comp :=
match id.to_slope, spec_comp_and_flipped_of_comp id.to_comp with
| slope.horiz, (cmp, flp) := ⟨if flp then (sum_form.of_expr rhs).negate else sum_form.of_expr rhs, cmp⟩
| slope.some m, (cmp, flp) := 
   let nsfc := (sum_form.of_expr lhs).add_factor (sum_form.of_expr rhs) (-m) in
   ⟨if flp then nsfc.negate else nsfc, cmp⟩
end

meta def of_eq (lhs rhs : expr) (c : ℚ) : sum_form_comp :=
⟨(sum_form.of_expr lhs).add_factor (sum_form.of_expr rhs) (-c), spec_comp.eq⟩

meta def of_sign (e : expr) : gen_comp → sum_form_comp
| gen_comp.ne := ⟨mk_rb_map, spec_comp.eq⟩
| gen_comp.eq := ⟨sum_form.of_expr e, spec_comp.eq⟩
| gen_comp.le := ⟨sum_form.of_expr e, spec_comp.le⟩
| gen_comp.lt := ⟨sum_form.of_expr e, spec_comp.lt⟩
| gen_comp.ge := ⟨(sum_form.of_expr e).scale (-1), spec_comp.le⟩
| gen_comp.gt := ⟨(sum_form.of_expr e).scale (-1), spec_comp.lt⟩


--(sum_form_comp.of_eq lhs rhs c

end sum_form_comp

meta structure prod_form := 
(coeff : ℚ)
(exps : rb_map expr ℤ)

namespace prod_form
protected meta def one : prod_form := ⟨1, mk_rb_map⟩

meta instance : has_one prod_form := ⟨prod_form.one⟩

meta def get_exp (pf : prod_form) (e : expr) := 
match pf.exps.find e with
| some z := z
| none := 0
end

-- this assumes e ≠ 0
meta def mul_exp (pf : prod_form) (e : expr) (c : ℤ) : prod_form :=
if pf.get_exp e + c = 0 then {pf with exps := pf.exps.erase e}
else {pf with exps := pf.exps.insert e ((pf.get_exp e) + c)}

protected meta def mul (lhs rhs : prod_form) : prod_form :=
{rhs.exps.fold lhs (λ e q pf, pf.mul_exp e q) with coeff := lhs.coeff * rhs.coeff}

meta def scale (pf : prod_form) (q : ℚ) : prod_form :=
{pf with coeff := pf.coeff * q}

meta def pow (pf : prod_form) (z : ℤ) : prod_form :=
{coeff := if pf.coeff = 1 then pf.coeff else if z = 1 then pf.coeff else pf.coeff^z, exps := pf.exps.map (λ q, q*z)}


meta instance : has_mul prod_form := ⟨prod_form.mul⟩ 

meta def of_expr (e : expr) : prod_form :=
{coeff := 1, exps := mk_rb_map.insert e 1}

meta def get_nonone_factors (pf : prod_form) : list (expr × ℤ) :=
pf.exps.to_list

meta instance : has_to_format prod_form :=
⟨λ pf, to_fmt pf.coeff ++ "*" ++ to_fmt pf.exps⟩

private meta def lt_core (pf1 pf2 : prod_form) : bool :=
pf1.coeff < pf2.coeff ∨ (pf1.coeff = pf2.coeff ∧ pf1.exps.to_list < pf2.exps.to_list)
meta def lt : prod_form → prod_form → Prop := λ pf1 pf2, ↑(lt_core pf1 pf2)
meta instance has_lt : has_lt prod_form := ⟨lt⟩
meta instance lt_decidable : decidable_rel lt := by delta lt; apply_instance
meta def cmp : prod_form → prod_form → ordering := cmp_using lt

end prod_form

meta structure prod_form_comp :=
(pf : prod_form) (c : spec_comp)

namespace prod_form_comp

meta def default : prod_form_comp := ⟨prod_form.one, spec_comp.eq⟩

meta instance has_to_format : has_to_format prod_form_comp :=
⟨λ sfc, "{1" ++ to_fmt sfc.c ++ to_fmt sfc.pf.coeff ++ "*" ++ to_fmt (sfc.pf.exps) ++  "}"⟩

meta def is_contr : prod_form_comp → bool
| ⟨sf, c⟩ := (sf.exps.keys.length = 0) &&
    (((c = spec_comp.lt) && (sf.coeff ≥ 0)) || ((c = spec_comp.le) && (sf.coeff > 0)))




/-
-- assumes that lhs is positive
meta def of_ineq_pos_lhs (lhs rhs : expr) (id : ineq) : prod_form_comp :=
match id.to_slope, spec_comp_and_flipped_of_comp id.to_comp with
| slope.horiz, (cmp, flp) := default
| slope.some m, (cmp, flp) := 
   if m = 0 then default else
   let nsfc := ((prod_form.of_expr lhs).pow (-1)) * (prod_form.of_expr rhs) in
   ⟨if flp then (nsfc.scale m).pow (-1) else nsfc.scale m, cmp⟩
end

-- assumes that lhs is negative
meta def of_ineq_neg_lhs (lhs rhs : expr) (id : ineq) : prod_form_comp :=
match id.to_slope, spec_comp_and_flipped_of_comp id.to_comp with
| slope.horiz, (cmp, flp) := default
| slope.some m, (cmp, flp) := 
   if m = 0 then default else
   let nsfc := ((prod_form.of_expr lhs).pow (-1)) * (prod_form.of_expr rhs) in
   ⟨if flp then nsfc.scale m else (nsfc.scale m).pow (-1), cmp⟩--⟨nsfc.scale (if flp then m else -m), cmp⟩
end
-/

-- is_redundant_data cmp is_pos_coeff s_lhs s_rhs assumes lhs has sign s_lhs, rhs has sign s_rhs, c has sign is_pos_coeff,
-- and returns true if lhs cmp 0 cmp c*rhs
private meta def is_redundant_data (cmp : comp) (is_pos_coeff : bool) (s_lhs s_rhs : gen_comp) : bool :=
if s_lhs.is_less = s_rhs.is_less then 
   if is_pos_coeff then ff else cmp.is_less
else if s_lhs.is_less then 
   if is_pos_coeff then cmp.is_less else ff
else 
   if is_pos_coeff then bnot cmp.is_less else ff 


-- lhs cl 0 and rhs cr 0, and iq lhs rhs. cl and cr should be strict ineqs
meta def of_ineq (lhs rhs : expr) (cl cr : gen_comp) (iq : ineq) : prod_form_comp :=
match (/-trace_val-/ ("iq slope, lhs, rhs:", iq.to_slope, lhs, rhs)).2.1, (/-trace_val-/ ("iq comp:", iq.to_comp)).2 with
| slope.horiz, _ := default
| slope.some m, cmp := 
   if (m = 0) || (is_redundant_data cmp (m > 0) cl cr) then (/-trace_val-/ ("redundant", default)).2 else
   let nsfc := /-trace_val $-/ (((prod_form.of_expr lhs).pow (-1)) * (prod_form.of_expr rhs)).scale m,
       (sc, flp) := spec_comp_and_flipped_of_comp cmp in
   ⟨if ((bnot cl.is_less) = flp) then nsfc.pow (-1) else nsfc, sc⟩
end

meta def of_eq (lhs rhs : expr) (c : ℚ) : prod_form_comp :=
⟨(((prod_form.of_expr lhs).pow (-1)) * (prod_form.of_expr rhs)).scale c, spec_comp.eq⟩

meta def pow (pfc : prod_form_comp) (z : ℤ) : prod_form_comp :=
⟨pfc.pf.pow z, pfc.c⟩

end prod_form_comp
end polya
