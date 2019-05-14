import data.hash_map data.complex.basic rat_additions

def {u} list.bfilter {α : Type u} (p : α → bool) : list α → list α
| [] := []
| (h::t) := if p h then h::list.bfilter t else list.bfilter t

def {u v} list.mfoldl' {m : Type u → Type v} [monad m] {s : Type u} : (s → s → m s) → s → list s → m s
| f s [] := return s
| f s [a] := return a
| f s (h :: r) := do
  s' ← f s h,
  list.mfoldl f s' r

meta def reduce_option_list {α} : list (option α) → list α
| [] := []
| (none::l) := reduce_option_list l
| (some a::l) := a::reduce_option_list l

namespace hash_map
def {u v} find' {α : Type u} {β : α → Type v} [decidable_eq α] (m : hash_map α β) (a : α) [inhabited (β a)] : β a :=
match m.find a with
| none := default _
| some b := b
end
end hash_map

meta def string.to_name (s : string) : name :=
name.mk_string s name.anonymous
