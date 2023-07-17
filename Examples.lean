import Mathlib.Data.Finset.Sort
import Hfzfa

open HFSet

/-- Get all of the atoms recursively from a given `HFSet`:
    - `flatten (atom x) = {x}`
    - `flatten A = ⋃ x ∈ A, flatten x` -/
def flatten [DecidableEq atoms] (s : HFSet atoms) : Finset atoms :=
  if h : s.isAtom then
    {s.getAtom h}
  else
    s.toFinset.attach.sup (fun x => flatten x)
termination_by flatten s => s
decreasing_by exact mem_toFinset_iff.mp x.prop

lemma flatten_atom [DecidableEq atoms] (x : atoms) :
    flatten (atom x) = {x} := by
  rw [flatten, dif_pos] <;> simp

lemma flatten_ofFinset [DecidableEq atoms] (s : Finset (HFSet atoms)) :
    flatten (ofFinset s) = s.biUnion (fun x => flatten x) := by
  rw [flatten, dif_neg] <;> simp [Finset.sup_eq_biUnion]


def v₁ : HFSet ℕ :=
  {atom 1, {atom 2, atom 3}, {atom 4, {atom 5}}, atom 1}

def v₂ : HFSet ℕ :=
  {{atom 3, atom 2}, {atom 4, {atom 5}}, atom 1}

example : v₁ = v₂ := by decide

#eval v₁ -- {1, {2, 3}, {4, {5}}}
#eval v₁ = v₂ -- true
#eval flatten v₁ -- {1, 2, 3, 4, 5}
#eval v₁.rank -- 3

/-- The union of two `HFSet`'s. If either is an atom, it is treated as the empty set. -/
def union [DecidableEq atoms] (x y : HFSet atoms) : HFSet atoms :=
  ofFinset (x.toFinset ∪ y.toFinset)

instance [DecidableEq atoms] : Union (HFSet atoms) := ⟨union⟩

example [DecidableEq atoms] (x y z : HFSet atoms) :
    z ∈ x ∪ y ↔ z ∈ x ∨ z ∈ y :=
  by simp [Union.union, union]

def v₃ : HFSet ℕ := {{atom 2}}
#eval v₁ ∪ v₃ -- {{2, 3}, {4, {5}}, 1, {2}}
#eval v₁ ∪ v₃ = v₂ -- false because {atom 2} ∈ v₁ ∪ v₃ but {atom 2} ∉ v₂
#eval {atom 2} ∈ v₁ ∪ v₃ -- true
#eval {atom 2} ∈ v₂ -- false

