import .info

namespace polya

-- id.x ≥ 0, id.strict
private meta def mk_cmp_aux : bool → bool → gen_comp
| tt tt := gen_comp.gt
| tt ff := gen_comp.ge
| ff tt := gen_comp.lt
| ff ff := gen_comp.le

-- assumes id.to_slope = slope.horiz
meta def eq_data.get_implied_sign_info_from_horiz_ineq {lhs rhs} (ed : eq_data lhs rhs) :
     ineq_data lhs rhs → sign_info lhs × sign_info rhs | ⟨id, prf⟩ := 
if ed.c > 0 then
  let cmp := mk_cmp_aux (id.x ≥ 0) id.strict,
      pr1 := sign_proof.ineq_of_eq_and_ineq_lhs cmp ed.prf prf,
      pr2 := sign_proof.ineq_rhs cmp prf in
  (some ⟨_, pr1⟩, some ⟨_, pr2⟩)
else if h : ed.c = 0 then
  let pr1 := sign_proof.eq_of_eq_zero (by rw ←h; apply ed.prf),
      pr2 := sign_proof.ineq_rhs (mk_cmp_aux (id.x ≥ 0) id.strict) prf in
  (some ⟨_, pr1⟩, some ⟨_, pr2⟩)
else 
  let cmp := mk_cmp_aux (id.x ≤ 0) id.strict,
      pr1 := sign_proof.ineq_of_eq_and_ineq_lhs cmp ed.prf prf,
      pr2 := sign_proof.ineq_rhs cmp.reverse prf in
  (some ⟨_, pr1⟩, some ⟨_, pr2⟩)

-- assumes id.to_slope = slope.some m, with m ≠ ed.c
meta def eq_data.get_implied_sign_info_from_slope_ineq {lhs rhs} (ed : eq_data lhs rhs) (m : ℚ) :
     ineq_data lhs rhs → sign_info lhs × sign_info rhs | ⟨id, prf⟩ := 
let cmp  := if m - ed.c < 0 then id.to_comp else id.to_comp.reverse in 
if ed.c > 0 then 
  let pr1 := sign_proof.ineq_of_eq_and_ineq_lhs cmp ed.prf prf,
      pr2 := sign_proof.ineq_of_eq_and_ineq_rhs cmp ed.prf prf in
      (some ⟨_, pr1⟩, some ⟨_, pr2⟩)
else if h : ed.c = 0 then
  let pr1 := sign_proof.eq_of_eq_zero (by rw ←h; apply ed.prf),
      pr2 := sign_proof.ineq_of_ineq_and_eq_zero_rhs cmp prf pr1 in
      (some ⟨_, pr1⟩, some ⟨_, pr2⟩)
else
  let pr1 := sign_proof.ineq_of_eq_and_ineq_lhs cmp.reverse ed.prf prf,
      pr2 := sign_proof.ineq_of_eq_and_ineq_rhs cmp ed.prf prf in
      (some ⟨_, pr1⟩, some ⟨_, pr2⟩)


meta def eq_data.get_implied_sign_info_from_ineq {lhs rhs} (ed : eq_data lhs rhs) 
     (id : ineq_data lhs rhs) : sign_info lhs × sign_info rhs  := 
match id.inq.to_slope with
| slope.horiz := ed.get_implied_sign_info_from_horiz_ineq id
| slope.some m := 
  if m = ed.c then (none, none)
  else ed.get_implied_sign_info_from_slope_ineq m id
end

-- TODO: make comp_option_of_sign_info private?
meta def eq_data.implies_ineq_with_sign_info {lhs rhs} (ed : eq_data lhs rhs) (iq : ineq) 
     (sil : sign_info lhs) (sir : sign_info rhs) : bool :=
match point_of_coeff_and_comps ed.c (comp_option_of_sign_info sil) (comp_option_of_sign_info sir) with
| some (x, y) := (iq.clockwise_of ⟨tt, x, y⟩ && ((bnot iq.strict) || sil.is_strict || sir.is_strict)) 
                  || ed.implies_ineq iq
| none := ff
end

meta def ineq_data.strengthen_from_diseq {lhs rhs} (id : ineq_data lhs rhs) (dd : diseq_data lhs rhs) :
         ineq_data lhs rhs :=
if id.inq.strict then id else
match id.inq.to_slope with
| slope.horiz  := id
| slope.some m := 
    if m = dd.c then 
    ⟨id.inq.strengthen, ineq_proof.of_ineq_proof_and_diseq id.prf dd.prf⟩ 
    else id
end

meta def ineq_data.strengthen_from_sign_lhs {lhs rhs} (id : ineq_data lhs rhs) (dd : sign_data lhs) :
         ineq_data lhs rhs :=
if id.inq.strict || bnot (dd.c = gen_comp.ne) then id else
match id.inq.to_slope with
| slope.horiz := id
| slope.some m :=
    if (m = 0) then 
    ⟨id.inq.strengthen, ineq_proof.of_ineq_proof_and_sign_lhs id.prf dd.prf⟩ 
    else id
end

meta def ineq_data.strengthen_from_sign_rhs {lhs rhs} (id : ineq_data lhs rhs) (dd : sign_data rhs) :
         ineq_data lhs rhs :=
if id.inq.strict || bnot (dd.c = gen_comp.ne) then id else
match id.inq.to_slope with
| slope.horiz := ⟨id.inq.strengthen, ineq_proof.of_ineq_proof_and_sign_rhs id.prf dd.prf⟩
| slope.some m := id
end

end polya