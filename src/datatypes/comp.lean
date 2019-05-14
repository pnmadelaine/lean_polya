import .basic

namespace polya

@[derive decidable_eq]
inductive comp
| le | lt | ge | gt

@[derive decidable_eq]
inductive gen_comp
| le | lt | ge | gt | eq | ne

@[derive decidable_eq]
inductive spec_comp
| lt | le | eq

namespace comp
--instance : decidable_eq comp := by tactic.mk_dec_eq_instance

def dir : comp → ℤ
| le := -1
| lt := -1
| ge := 1
| gt := 1

def reverse : comp → comp
| le := ge
| lt := gt
| ge := le
| gt := lt

def negate : comp → comp
| le := gt
| lt := ge
| ge := lt
| gt := le

def strengthen : comp → comp
| le := lt
| ge := gt
| a  := a

def is_strict : comp → bool
| lt := tt
| gt := tt
| _  := ff

def is_less : comp → bool
| lt := tt
| le := tt
| _  := ff

def is_greater : comp → bool := bnot ∘ is_less

def implies (c1 c2 : comp) : bool :=
(is_less c1 = is_less c2) && (is_strict c1 || bnot (is_strict c2))

meta def to_format : comp → format
| le := "≤"
| lt := "<"
| ge := "≥"
| gt := ">"

def to_gen_comp : comp → gen_comp
| le := gen_comp.le
| lt := gen_comp.lt
| ge := gen_comp.ge
| gt := gen_comp.gt

meta def to_pexpr : comp → pexpr
| le := ``(has_le.le)
| lt := ``(has_lt.lt)
| ge := ``(ge)
| gt := ``(gt)

section
open tactic
meta def to_function (lhs rhs : expr) : comp → tactic expr
| lt := to_expr ``(%%lhs < %%rhs)
| le := to_expr ``(%%lhs ≤ %%rhs)
| gt := to_expr ``(%%lhs > %%rhs)
| ge := to_expr ``(%%lhs ≥ %%rhs)
end

def prod : comp → comp → comp
| gt a := a
| a gt := a
| ge ge := ge
| ge lt := le
| ge le := le
| lt ge := le
| le ge := le
| le le := ge
| le lt := ge
| lt le := ge
| lt lt := gt

meta instance : has_coe comp gen_comp :=
⟨to_gen_comp⟩ 

meta instance : has_to_format comp :=
⟨to_format⟩

end comp

namespace gen_comp
--instance : decidable_eq gen_comp := by tactic.mk_dec_eq_instance
instance : inhabited gen_comp := ⟨eq⟩

def dir : gen_comp → ℤ
| le := -1
| lt := -1
| ge := 1
| gt := 1
| eq := 0
| ne := 0

def reverse : gen_comp → gen_comp
| le := ge
| lt := gt
| ge := le
| gt := lt
| eq := eq
| ne := ne

def negate : gen_comp → gen_comp
| le := gt
| lt := ge
| ge := lt
| gt := le
| eq := ne
| ne := eq

def is_strict : gen_comp → bool
| lt := tt
| gt := tt
| _  := ff

def is_less : gen_comp → bool
| lt := tt
| le := tt
| _  := ff

def is_greater : gen_comp → bool
| gt := tt
| ge := tt
| _ := ff

def is_less_or_eq : gen_comp → bool
| lt := tt
| le := tt
| eq := tt
| _ := ff

def is_greater_or_eq : gen_comp → bool
| gt := tt
| ge := tt
| eq := tt
| _ := ff

def is_ineq : gen_comp → bool
| eq := ff
| ne := ff
| _  := tt

def strongest : gen_comp → gen_comp → gen_comp
| gt ge := gt
| lt le := lt
| ge gt := gt
| le lt := lt
| eq b  := b
| a eq  := a
| a b   := if a = b then a else b

def implies_aux : gen_comp → gen_comp → bool
| lt le := tt
| gt ge := tt
| eq le := tt
| eq ge := tt
| lt ne := tt
| gt ne := tt
| _ _   := ff

def implies (c1 c2 : gen_comp) : bool :=
(c1 = c2) || implies_aux c1 c2 

def contr : gen_comp → gen_comp → bool
| lt gt := tt
| lt ge := tt
| lt eq := tt
| le gt := tt
| eq ne := tt
| eq lt := tt
| eq gt := tt
| ge lt := tt
| gt lt := tt
| gt le := tt
| gt eq := tt
| _ _ := ff

def prod : gen_comp → gen_comp → option gen_comp
| ne ne := ne
| ne eq := eq
| eq ne := eq
| ne gt := ne
| ne lt := ne
| gt ne := ne
| lt ne := ne
| ne a := none
| a ne := none
| gt a := a
| a gt := a
| eq a := eq
| a eq := eq
| ge ge := ge
| ge le := le
| le ge := le
| ge lt := le
| lt ge := le
| le le := ge
| le lt := ge
| lt le := ge
| lt lt := gt

-- may not be right for = or ≠
def pow (c1 : gen_comp) (z : ℤ) : gen_comp :=
if (bnot c1.is_less) || (z ≥ 0) || (z % 2 = 0) then c1 
else c1.reverse

meta def to_format : gen_comp → format
| le := "≤"
| lt := "<"
| ge := "≥"
| gt := ">"
| eq := "="
| ne := "≠"

/--
 Be careful. In the ne or eq case, this returns ge.
-/
meta def to_comp : gen_comp → comp
| le := comp.le
| lt := comp.lt
| ge := comp.ge
| gt := comp.gt
| _  := comp.ge

/--
 Be careful. This only matches strength
-/
meta def to_spec_comp : gen_comp → spec_comp
| le := spec_comp.le
| ge := spec_comp.le
| lt := spec_comp.lt
| gt := spec_comp.lt
| _ := spec_comp.eq

meta def to_function (lhs rhs : expr) : gen_comp → tactic expr
| le := tactic.to_expr ``(%%lhs ≤ %%rhs)
| lt := tactic.to_expr ``(%%lhs < %%rhs)
| ge := tactic.to_expr ``(%%lhs ≥ %%rhs)
| gt := tactic.to_expr ``(%%lhs > %%rhs)
| eq := tactic.to_expr ``(%%lhs = %%rhs)
| ne := tactic.to_expr ``(%%lhs ≠ %%rhs)

meta instance : has_to_format gen_comp :=
⟨to_format⟩


end gen_comp


def spec_comp_and_flipped_of_comp : comp → spec_comp × bool
| comp.lt := (spec_comp.lt, ff)
| comp.le := (spec_comp.le, ff)
| comp.gt := (spec_comp.lt, tt)
| comp.ge := (spec_comp.le, tt)

namespace spec_comp

--instance : decidable_eq spec_comp := by tactic.mk_dec_eq_instance

def strongest : spec_comp → spec_comp → spec_comp
| spec_comp.lt _ := spec_comp.lt
| _ spec_comp.lt := spec_comp.lt
| spec_comp.le _ := spec_comp.le
| _ spec_comp.le := spec_comp.le
| spec_comp.eq spec_comp.eq := spec_comp.eq

/--
 This is nonsense on eq
-/
def to_comp : spec_comp → comp
| spec_comp.lt := comp.lt
| spec_comp.le := comp.le
| spec_comp.eq := comp.gt

def to_gen_comp : spec_comp → gen_comp
| spec_comp.lt := gen_comp.lt
| spec_comp.le := gen_comp.le
| spec_comp.eq := gen_comp.eq

meta def to_format : spec_comp → format
| spec_comp.lt := "<"
| spec_comp.le := "≤"
| spec_comp.eq := "="

meta instance has_to_format : has_to_format spec_comp :=
⟨spec_comp.to_format⟩

end spec_comp

/--
 This does not represent the traditional slope, but (x/y) if (x, y) is a point on the line
-/
@[derive decidable_eq]
inductive slope
| horiz : slope
| some : rat → slope

--instance slope.decidable_eq : decidable_eq slope := by tactic.mk_dec_eq_instance

meta def slope.to_format : slope → format
| slope.horiz := "horiz"
| (slope.some m) := to_fmt m

meta instance : has_to_format slope :=
⟨slope.to_format⟩ 

meta def slope.invert : slope → slope
| slope.horiz := slope.some 0
| (slope.some m) := if m = 0 then slope.horiz else slope.some (1/m)

/--
 An inequality (str, a, b) represents the halfplane counterclockwise from the vector (a, b).
 If str is true, it is strict (ie, it doesn't include the line bx-ay=0).
-/
@[derive decidable_eq]
structure ineq :=
(strict : bool)
(x y : ℚ)

namespace ineq
instance : inhabited ineq :=
⟨⟨ff, 1, 0⟩⟩

/-meta instance rat.has_to_format : has_to_format ℚ :=
⟨λ q, ↑"0"⟩-/

def is_axis (i : ineq) : bool :=
(i.x = 0) || (i.y = 0)

open polya.comp slope

def to_comp (i : ineq) : comp := -- DOUBLE CHECK THIS
/-if i.x ≥ 0 then
  if i.y > 0 then
    if i.strict then lt else le
  else 
    if i.strict then gt else ge
else
  if i.y > 0 then
    if i.strict then lt else le
  else
    if i.strict then gt else ge-/
if i.y > 0 then
  if i.strict then lt else le
else if i.y < 0 then
  if i.strict then gt else ge
else if i.x < 0 then
  if i.strict then lt else le
else if i.strict then gt else ge

def to_slope (i : ineq) : slope :=
if i.y = 0 then slope.horiz else slope.some (i.x / i.y) 

meta def to_format (inq : ineq) : format :=
let cf := to_fmt inq.to_comp in
match inq.to_slope with
| slope.horiz := "(rhs)" ++ cf ++ "0"
| slope.some c := if c = 0 then "(lhs)" ++ cf ++ "0" else
"(lhs) " ++ cf ++ to_fmt c ++ "(rhs)"
end

meta instance ineq.has_to_format : has_to_format ineq :=
⟨to_format⟩

meta def is_zero_slope (i : ineq) : bool :=
(i.x = 0) && bnot (i.y = 0)

meta def is_horiz (i : ineq) : bool :=
i.y = 0

def equiv (i1 i2 : ineq) : bool :=
to_slope i1 = to_slope i2

def of_comp_and_slope (c : comp) : slope → ineq
| horiz    := if is_less c then ⟨is_strict c, -1, 0⟩ else ⟨is_strict c, 1, 0⟩
| (some v) :=
  if v > 0 then 
    if is_less c then ⟨is_strict c, v, 1⟩ else ⟨is_strict c, -v, -1⟩
  else
    if is_less c then ⟨is_strict c, v, 1⟩ else ⟨is_strict c, -v, -1⟩


/--
 Turns a < 3b into a > 3b
-/
def flip (i : ineq) : ineq :=
⟨i.strict, -i.x, -i.y⟩

/--
 Turns a < 3b into a ≥ 3b
-/
def negate (i : ineq) : ineq :=
⟨bnot i.strict, -i.x, -i.y⟩

/--
 Turns a < 3b into b > 1/3 a.
 This is equivalent to reflecting over the identity line and flipping
-/
def reverse (i : ineq) : ineq :=
⟨i.strict, -i.y, -i.x⟩

/--
 Turns a ≤ 3b into a < 3b.
-/
def strengthen (i : ineq) : ineq :=
{i with strict := tt}

def same_quadrant (i1 i2 : ineq) : bool :=
(i1.x > 0 ↔ i2.x > 0) && (i1.y > 0 ↔ i2.y > 0)

def implies (i1 i2 : ineq) : bool :=
(i1.to_slope = i2.to_slope) && (same_quadrant i1 i2) && (i1.strict || bnot (i2.strict))


def clockwise_of (i1 i2 : ineq) : bool :=
i1.x*i2.y - i1.y*i2.x > 0

/--
 True if the conjunction of i1 and i2 implies ninq
-/
def two_imply (i1 i2 : ineq) (ninq : ineq) : bool :=
(ninq.clockwise_of i1 && i2.clockwise_of ninq) || (i1.implies ninq) || (i2.implies ninq)

end ineq

-- TODO: where to put this?
meta def point_of_coeff_and_comps (c : ℚ) : option gen_comp → option gen_comp → option (ℚ × ℚ)
| (some gen_comp.eq) r := point_of_coeff_and_comps none r
| (some gen_comp.ne) r := point_of_coeff_and_comps none r
| l (some gen_comp.eq) := point_of_coeff_and_comps l none
| l (some gen_comp.ne) := point_of_coeff_and_comps l none
| (some l) none := if l.is_less then some (-1, -1/c) else some (1, 1/c)
| none (some r) := if r.is_less then some (-c, -1) else some (c, 1)
| none none := none
| (some l) (some r) := 
if (c ≥ 0) && (l.is_less = r.is_less) then point_of_coeff_and_comps (some l) none
else if (c < 0) && bnot (l.is_less = r.is_less) then point_of_coeff_and_comps (some l) none
else none

end polya