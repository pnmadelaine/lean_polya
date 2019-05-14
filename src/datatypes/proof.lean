import .expr_form

namespace polya


section proof_sketch

meta inductive proof_sketch
| mk (fact : string) (reason : string) (justifications : list proof_sketch) : proof_sketch

meta def proof_sketch.justifications : proof_sketch → list proof_sketch
| ⟨_, _, j⟩ := j

meta def proof_sketch.reason : proof_sketch → string
| ⟨_, r, _⟩ := r

end proof_sketch

section proof_objs

meta inductive diseq_proof : expr → expr → ℚ → Type
| hyp : Π lhs rhs c, expr → diseq_proof lhs rhs c
| sym : Π {lhs rhs c}, Π (dp : diseq_proof lhs rhs c), diseq_proof rhs lhs (1/c)

meta mutual inductive eq_proof, ineq_proof, sign_proof, sum_form_proof
with eq_proof : expr → expr → ℚ → Type
| hyp : Π lhs rhs c, expr → eq_proof lhs rhs c
| sym : Π {lhs rhs c}, Π (ep : eq_proof lhs rhs c), eq_proof rhs lhs (1/c)
| of_opp_ineqs : Π {lhs rhs i}, Π c,
  ineq_proof lhs rhs i → ineq_proof lhs rhs (i.reverse) → eq_proof lhs rhs c
| of_sum_form_proof : Π lhs rhs c {sf}, sum_form_proof ⟨sf, spec_comp.eq⟩ → eq_proof lhs rhs c
| adhoc : Π lhs rhs c, tactic proof_sketch →  tactic expr → eq_proof lhs rhs c

with ineq_proof : expr → expr → ineq → Type
| hyp : Π lhs rhs i, expr → ineq_proof lhs rhs i
| sym : Π {lhs rhs i}, ineq_proof lhs rhs i → ineq_proof rhs lhs (i.reverse)
| of_ineq_proof_and_diseq : Π {lhs rhs i c}, 
    ineq_proof lhs rhs i → diseq_proof lhs rhs c → ineq_proof lhs rhs (i.strengthen)
| of_ineq_proof_and_sign_lhs : Π {lhs rhs i c},
    ineq_proof lhs rhs i → sign_proof lhs c → ineq_proof lhs rhs (i.strengthen)
| of_ineq_proof_and_sign_rhs : Π {lhs rhs i c},
    ineq_proof lhs rhs i → sign_proof rhs c → ineq_proof lhs rhs (i.strengthen)
| zero_comp_of_sign_proof : Π {lhs c} rhs i, sign_proof lhs c → ineq_proof lhs rhs i
| horiz_of_sign_proof : Π {rhs c} lhs i, sign_proof rhs c → ineq_proof lhs rhs i
| of_sum_form_proof : Π lhs rhs i {sfc}, sum_form_proof sfc → ineq_proof lhs rhs i
| adhoc : Π lhs rhs i, tactic proof_sketch → tactic expr → ineq_proof lhs rhs i

with sign_proof : expr → gen_comp → Type
| hyp  : Π e c, expr → sign_proof e c
| scaled_hyp : Π e c, expr → ℚ → sign_proof e c
| ineq_lhs : Π c, Π {lhs rhs iqp}, ineq_proof lhs rhs iqp → sign_proof lhs c
| ineq_rhs : Π c, Π {lhs rhs iqp}, ineq_proof lhs rhs iqp → sign_proof rhs c
| eq_of_two_eqs_lhs : Π {lhs rhs eqp1 eqp2}, 
    eq_proof lhs rhs eqp1 → eq_proof lhs rhs eqp2 → sign_proof lhs gen_comp.eq
| eq_of_two_eqs_rhs : Π {lhs rhs eqp1 eqp2}, 
    eq_proof lhs rhs eqp1 → eq_proof lhs rhs eqp2 → sign_proof rhs gen_comp.eq
| diseq_of_diseq_zero : Π {lhs rhs}, diseq_proof lhs rhs 0 → sign_proof lhs gen_comp.ne
| eq_of_eq_zero : Π {lhs rhs}, eq_proof lhs rhs 0 → sign_proof lhs gen_comp.eq
| eq_of_le_of_ge : Π {e}, sign_proof e gen_comp.le → sign_proof e gen_comp.ge → sign_proof e gen_comp.eq
| ineq_of_eq_and_ineq_lhs : Π {lhs rhs i c}, Π c', 
    eq_proof lhs rhs c → ineq_proof lhs rhs i →  sign_proof lhs c'
| ineq_of_eq_and_ineq_rhs : Π {lhs rhs i c}, Π c', 
    eq_proof lhs rhs c → ineq_proof lhs rhs i →  sign_proof rhs c'
| ineq_of_ineq_and_eq_zero_rhs : Π {lhs rhs i}, Π c, 
    ineq_proof lhs rhs i → sign_proof lhs gen_comp.eq → sign_proof rhs c
| diseq_of_strict_ineq : Π {e c}, sign_proof e c → sign_proof e gen_comp.ne 
| of_sum_form_proof : Π e c {sfc}, sum_form_proof sfc → sign_proof e c
| adhoc : Π e c, tactic proof_sketch → tactic expr → sign_proof e c

with sum_form_proof : sum_form_comp → Type
| of_ineq_proof : Π {lhs rhs iq}, Π id : ineq_proof lhs rhs iq,
    sum_form_proof (sum_form_comp.of_ineq lhs rhs iq)
| of_eq_proof : Π {lhs rhs c}, Π id : eq_proof lhs rhs c,
    sum_form_proof (sum_form_comp.of_eq lhs rhs c)
| of_sign_proof : Π {e c}, Π id : sign_proof e c, sum_form_proof (sum_form_comp.of_sign e c)
| of_add_factor_same_comp : Π {lhs rhs c1 c2}, Π m : ℚ, -- assumes m is positive
  sum_form_proof ⟨lhs, c1⟩ → sum_form_proof ⟨rhs, c2⟩ → sum_form_proof ⟨lhs.add_factor rhs m, spec_comp.strongest c1 c2⟩ 
| of_add_eq_factor_op_comp : Π {lhs rhs c1}, Π m : ℚ, -- assumes m is negative
  sum_form_proof ⟨lhs, c1⟩ → sum_form_proof ⟨rhs, spec_comp.eq⟩ → sum_form_proof ⟨lhs.add_factor rhs m, c1⟩ 
| of_scale : Π {sfc}, Π m, sum_form_proof sfc → sum_form_proof (sfc.scale m)
| of_expr_def : Π (e : expr) (sf : sum_form),  sum_form_proof ⟨sf, spec_comp.eq⟩ 
| fake : Π sd, sum_form_proof sd

meta inductive prod_form_proof : prod_form_comp → Type
| of_ineq_proof : Π {lhs rhs iq cl cr},
    Π (id : ineq_proof lhs rhs iq) (spl : sign_proof lhs cl) (spr : sign_proof rhs cr), prod_form_proof (prod_form_comp.of_ineq lhs rhs cl cr iq)
| of_eq_proof : Π {lhs rhs c}, Π (id : eq_proof lhs rhs c) (lhsne : sign_proof lhs gen_comp.ne),
    prod_form_proof (prod_form_comp.of_eq lhs rhs c)
| of_expr_def : Π (e : expr) (pf : prod_form), prod_form_proof ⟨pf, spec_comp.eq⟩
| of_pow : Π {pfc}, Π z, prod_form_proof pfc → prod_form_proof (pfc.pow z)
| of_mul : Π {lhs rhs c1 c2}, prod_form_proof ⟨lhs, c1⟩ → prod_form_proof ⟨rhs, c2⟩ → (list Σ e : expr, sign_proof e gen_comp.ne) → prod_form_proof ⟨lhs*rhs, spec_comp.strongest c1 c2⟩ 
| adhoc : Π pfc, tactic proof_sketch → tactic expr → prod_form_proof pfc
| fake : Π pd, prod_form_proof pd

open ineq_proof
meta def ineq_proof.to_format  {lhs rhs c} : ineq_proof lhs rhs c → format
| p := "proof"

meta def ineq_proof.to_format2 :
     Π {lhs rhs : expr} {iq : ineq}, ineq_proof lhs rhs iq → format
| .(_) .(_) .(_) (hyp (lhs) (rhs) (iq) e) := "hyp"
| .(_) .(_) .(_) (@sym lhs rhs c ip) := "sym"
| .(_) .(_) .(_) (@of_ineq_proof_and_diseq lhs rhs iq c ip dp) := "of_ineq_proof_and_diseq"
| .(_) .(_) .(_) (@of_ineq_proof_and_sign_lhs lhs rhs iq c ip sp) := "of_ineq_proof_and_sign_lhs"
| .(_) .(_) .(_) (@of_ineq_proof_and_sign_rhs lhs rhs iq c ip sp) :=  "of_ineq_proof_and_sign_rhs"
| .(_) .(_) .(_) (@zero_comp_of_sign_proof lhs c rhs iq sp) := "zero_comp_of_sign"
| .(_) .(_) .(_) (@horiz_of_sign_proof rhs c lhs iq sp) := "horiz_of_sign"
| .(_) .(_) .(_) (@of_sum_form_proof lhs rhs i _ sp) := "of_sum_form"
| .(_) .(_) .(_) (adhoc _ _ _ _ t) := "adhoc"

meta instance ineq_proof.has_to_format (lhs rhs c) : has_to_format (ineq_proof lhs rhs c) :=
⟨ineq_proof.to_format2⟩

section
open sign_proof
meta def sign_proof.to_format : Π {e c}, sign_proof e c → format
| (_) (_) (hyp _ _ _) := "hyp"
| (_) (_) (scaled_hyp _ _ _ _) := "scaled_hyp"
| (_) (_) (ineq_lhs _ _) := "ineq_lhs"
| (_) (_) (ineq_rhs _ _) := "ineq_rhs"
| (_) (_) (eq_of_two_eqs_rhs _ _) := "eq_of_two_eqs_rhs"
| (_) (_) (eq_of_two_eqs_lhs _ _) := "eq_of_two_eqs_lhs"
| (_) (_) (diseq_of_diseq_zero _) := "diseq_of_diseq_zero"
| (_) (_) (eq_of_eq_zero _) := "eq_of_eq_zero"
| (_) (_) (eq_of_le_of_ge _ _) := "eq_of_le_of_ge"
| (_) (_) (ineq_of_eq_and_ineq_lhs _ _ _) := "ineq_of_eq_and_ineq_lhs"
| (_) (_) (ineq_of_eq_and_ineq_rhs _ _ _) := "ineq_of_eq_and_ineq_rhs"
| (_) (_) (ineq_of_ineq_and_eq_zero_rhs _ _ _) := "ineq_of_ineq_and_eq_zero_rhs"
| (_) (_) (diseq_of_strict_ineq _) := "diseq_of_strict_ineq"
| (_) (_) (of_sum_form_proof _ _ _) := "of_sum_form_proof"
| (_) (_) (adhoc _ _ _ _) := "adhoc"

meta instance sign_proof.has_to_format {e c} : has_to_format (sign_proof e c) := ⟨sign_proof.to_format⟩
end

meta def prod_form_proof.to_format {pfc} (pfp : prod_form_proof pfc) : format :=
begin
cases pfp,
exact "of_ineq_proof",
exact "of_eq_proof",
exact "of_expr_def",
exact "of_pow",
exact "of_mul",
exact "adhoc",
exact "fake"
end

meta instance prod_form_proof.has_to_format {pfc} : has_to_format (prod_form_proof pfc) :=
⟨prod_form_proof.to_format⟩

end proof_objs
end polya
