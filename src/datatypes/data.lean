import .proof

namespace polya
open native comp

section data_objs

meta structure ineq_data (lhs rhs : expr) :=
(inq : ineq)
(prf : ineq_proof lhs rhs inq)

meta def ineq_data.reverse {lhs rhs : expr} (id : ineq_data lhs rhs) : ineq_data rhs lhs :=
if id.inq.is_horiz then
 let sp := sign_proof.ineq_rhs id.inq.to_comp/-.reverse-/ id.prf in
  ⟨_, ineq_proof.zero_comp_of_sign_proof lhs id.inq.reverse sp⟩
else if id.inq.is_zero_slope then
 let sp := sign_proof.ineq_lhs id.inq.to_comp id.prf in
  ⟨_, ineq_proof.horiz_of_sign_proof rhs id.inq.reverse sp⟩
else
 ⟨id.inq.reverse, id.prf.sym⟩

meta def ineq_data.to_format {lhs rhs} : ineq_data lhs rhs → format
| ⟨inq, prf⟩ := "⟨" ++ to_fmt inq ++ " : " ++ to_fmt prf ++ "⟩"

meta instance ineq_data.has_to_format (lhs rhs) : has_to_format (ineq_data lhs rhs) :=
⟨ineq_data.to_format⟩

/-meta instance ineq_data.has_decidable_eq (lhs rhs) : decidable_eq (ineq_data lhs rhs) :=
by tactic.mk_dec_eq_instance-/

-- TODO: move this to comp.lean?
-- TODO
section
open tactic

-- TODO : add proof argument and move
meta def ineq.to_type (id : ineq) (lhs rhs : expr) : tactic expr :=
match id.to_slope with
| slope.horiz := id.to_comp.to_function rhs `(0 : ℚ) --, to_expr `(fake_ineq_to_expr_proof %%tp)
| slope.some m := 
 -- let rhs' : expr := (if m=0 then `(0 : ℚ) else `(m*%%rhs : ℚ)) in
do rhs' ← to_expr (if m=0 then ``(0 : ℚ) else ``(%%(↑(reflect m) : expr)*%%rhs : ℚ)),
     id.to_comp.to_function lhs rhs'
     --to_expr `(fake_ineq_to_expr_proof %%tp)
end 

end 

/- meta def ineq_data.to_expr {lhs rhs} (id : ineq_data lhs rhs) : tactic expr :=
id.inq.to_expr lhs rhs -/

meta structure eq_data (lhs rhs : expr) :=
(c   : ℚ)
(prf : eq_proof lhs rhs c)

meta def eq_data.refl (e : expr) : eq_data e e :=
⟨1, eq_proof.adhoc e e 1 (do s ← to_string <$> tactic.pp e, return ⟨s ++ " = " ++ s, "reflexivity", []⟩) $ do (_, pr) ← tactic.solve_aux `(%%e = (1 : ℚ) * %%e) `[simp only [one_mul]], return pr⟩

meta def eq_data.reverse {lhs rhs : expr} (ei : eq_data lhs rhs) : eq_data rhs lhs :=
⟨(1/ei.c), ei.prf.sym⟩

meta def eq_data.implies_ineq {lhs rhs} (ed : eq_data lhs rhs) (id : ineq) : bool :=
match id.to_slope with
| slope.some c := (c = ed.c) && bnot (id.strict)
| horiz        := ff
end

meta def eq_data.to_format {lhs rhs} : eq_data lhs rhs → format
| ⟨c, prf⟩ := "⟨(lhs)=" ++ to_fmt c ++ "*(rhs)⟩" 

meta instance eq_data.has_to_format (lhs rhs) : has_to_format (eq_data lhs rhs) :=
⟨eq_data.to_format⟩


meta structure diseq_data (lhs rhs : expr) :=
(c : ℚ)
(prf : diseq_proof lhs rhs c)

meta def diseq_data.reverse {lhs rhs : expr} (di : diseq_data lhs rhs) : diseq_data rhs lhs :=
⟨(1/di.c), di.prf.sym⟩

meta structure sign_data (e : expr) :=
(c : gen_comp)
(prf : sign_proof e c)

meta def sign_data.to_format {e} : sign_data e → format
| ⟨c, _⟩ := to_fmt "{" ++ to_fmt e ++ to_fmt c ++ to_fmt "0}"

meta instance sign_data.has_to_format {e} : has_to_format (sign_data e) :=
⟨sign_data.to_format⟩ 

end data_objs

namespace sum_form_comp

-- is this needed?
meta def of_ineq_proof {lhs rhs id} (ip : ineq_proof lhs rhs id) : sum_form_comp :=
sum_form_comp.of_ineq lhs rhs id

end sum_form_comp  

meta structure sum_form_comp_data :=
(sfc : sum_form_comp) (prf : sum_form_proof sfc) (elim_list : rb_set expr)

namespace sum_form_comp_data

-- TODO: do we need to take elim_vars into account for this order?
meta def sum_form_comp_data.order : sum_form_comp_data → sum_form_comp_data → ordering
| ⟨sfc1, _, _⟩ ⟨sfc2, _, _⟩ := sfc1.order sfc2

meta instance : has_lt sum_form_comp_data := ⟨λ x y, sum_form_comp_data.order x y = ordering.lt⟩
meta instance : decidable_rel (@has_lt.lt sum_form_comp_data _) := λ _ _, by apply_instance

meta def of_ineq_data {lhs rhs} (id : ineq_data lhs rhs) : sum_form_comp_data :=
⟨_, sum_form_proof.of_ineq_proof id.prf, mk_rb_set⟩

meta def of_eq_data {lhs rhs} (ed : eq_data lhs rhs) : sum_form_comp_data :=
⟨_, sum_form_proof.of_eq_proof ed.prf, mk_rb_set⟩

meta def of_sign_data {e} (sd : sign_data e) : sum_form_comp_data :=
⟨_, sum_form_proof.of_sign_proof sd.prf, mk_rb_set⟩

meta def vars (sfcd : sum_form_comp_data) : list expr :=
sfcd.sfc.sf.keys

meta instance has_to_format : has_to_format sum_form_comp_data :=
⟨λ sfcd, to_fmt sfcd.sfc⟩

meta def get_coeff (sfcd : sum_form_comp_data) (e : expr) : ℚ :=
sfcd.sfc.sf.get_coeff e


meta def normalize (sd : sum_form_comp_data) : sum_form_comp_data :=
match rb_map.to_list sd.sfc.sf with
| [] := sd
| (_, m)::t := if abs m = 1 then sd else ⟨_, sum_form_proof.of_scale (abs (1/m)) sd.prf, sd.elim_list⟩
end

meta def is_normalized : sum_form_comp_data → bool
| ⟨sfc, _, _⟩ := sfc.is_normalized


meta def is_contr : sum_form_comp_data → bool
| ⟨sfc, _, _⟩ := sfc.is_contr

end sum_form_comp_data


meta structure prod_form_comp_data :=
(pfc : prod_form_comp) (prf : prod_form_proof pfc) (elim_list : rb_set expr)
namespace prod_form_comp_data

meta def vars (pfcd : prod_form_comp_data) : list expr :=
pfcd.pfc.pf.exps.keys

meta def of_ineq_data {lhs rhs cl cr} (id : ineq_data lhs rhs) (spl : sign_proof lhs cl) (spr : sign_proof rhs cr) : prod_form_comp_data :=
⟨_, prod_form_proof.of_ineq_proof id.prf spl spr, mk_rb_set⟩

meta def of_eq_data {lhs rhs} (ed : eq_data lhs rhs) (sp : sign_proof lhs gen_comp.ne) : prod_form_comp_data :=
⟨_, prod_form_proof.of_eq_proof ed.prf sp, mk_rb_set⟩

meta instance has_to_format : has_to_format prod_form_comp_data :=
⟨λ sfcd, to_fmt sfcd.pfc⟩

end prod_form_comp_data
end polya