import .data

namespace polya
open native

section info_objs

/--
 In the two_comps case, we maintain the invariant that the defining ray of the first is 
 counterclockwise to that of the second.
-/
meta inductive ineq_info (lhs rhs : expr)
| no_comps {}  : ineq_info
| one_comp     : ineq_data lhs rhs → ineq_info
| two_comps    : ineq_data lhs rhs → ineq_data lhs rhs → ineq_info
| equal        : eq_data lhs rhs → ineq_info
open ineq_info

meta def ineq_info.data {lhs rhs} : ineq_info lhs rhs → list (ineq_data lhs rhs)
| no_comps := []
| (one_comp id) := [id]
| (two_comps id1 id2) := [id1, id2]
| (equal _) := []


meta def ineq_info.mk_two_comps {lhs rhs} (id1 id2 : ineq_data lhs rhs) : ineq_info lhs rhs :=
if id2.inq.clockwise_of id1.inq then two_comps id1 id2 else two_comps id2 id1

meta instance ineq_info.inhabited (lhs rhs) : inhabited (ineq_info lhs rhs) :=
⟨no_comps⟩

meta def ineq_info.reverse {lhs rhs : expr} : ineq_info lhs rhs → ineq_info rhs lhs
| no_comps            := no_comps
| (one_comp id1)      := one_comp id1.reverse
| (two_comps id1 id2) := ineq_info.mk_two_comps id1.reverse id2.reverse
| (equal ed)          := equal ed.reverse

meta def ineq_info.to_format {lhs rhs} : ineq_info lhs rhs → format
| no_comps := "ineq_info.empty"
| (one_comp id1) := "{" ++ to_fmt id1 ++ "}"
| (two_comps id1 id2) := "{" ++ to_fmt id1 ++ " | " ++ to_fmt id2 ++ "}"
| (equal ed) := "{" ++ to_fmt ed ++ "}"

meta instance ineq_info.has_to_format (lhs rhs) : has_to_format (ineq_info lhs rhs) :=
⟨ineq_info.to_format⟩

meta def ineq_info.implies_ineq {lhs rhs : expr} : ineq_info lhs rhs → ineq → bool
| (one_comp ⟨inq1, _⟩) ninq := inq1.implies ninq
| (two_comps ⟨inq1, _⟩ ⟨inq2, _⟩) ninq := ineq.two_imply inq1 inq2 ninq
| (equal ed) ninq := ed.implies_ineq ninq
| _ _ := ff

meta def ineq_info.implies_eq {lhs rhs : expr} : ineq_info lhs rhs → ℚ → bool
| (equal ed) m := ed.c = m
| _ _ := ff

meta def diseq_info (lhs rhs : expr) := rb_map ℚ (diseq_data lhs rhs)

meta instance diseq_info.inhabited (lhs rhs) : inhabited (diseq_info lhs rhs) :=
⟨mk_rb_map⟩

meta def diseq_info.reverse {lhs rhs : expr} : diseq_info lhs rhs → diseq_info rhs lhs :=
rb_map.map diseq_data.reverse

@[reducible]
meta def sign_info (e : expr) := option (sign_data e)

meta def sign_info.is_strict {e : expr} : sign_info e → bool
| (some sd) := sd.c.is_strict
| none := ff

meta instance sign_info.inhabited (lhs) : inhabited (sign_info lhs) :=
⟨none⟩

--TODO: rename?
meta def comp_option_of_sign_info {e} : sign_info e → option gen_comp
| (some c) := c.c
| none := none

end info_objs


--TODO: where to put this?
section two_var_ineqs
meta def ineq_info.implies {lhs rhs : expr} (ii : ineq_info lhs rhs) (id : ineq_data lhs rhs) : bool :=
ii.implies_ineq id.inq
end two_var_ineqs

end polya
