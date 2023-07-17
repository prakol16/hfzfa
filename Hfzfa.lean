import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Set.Finite

/-!
  A theory of hereditarily finite lists and sets with atoms.

  In this file, we define a type `HFSet` of hereditarily finite sets with atoms.
  That is, an `HFSet` is either:
    - An atom, `HFSet.atom a : HFSet atoms` where `a : atoms`
    - A set of `HFSet`'s, `HFSet.ofFinset s` where `s : Finset HFSet`
  
  The core ideas are the same as in mathlib's definition
  of ZFC sets, but we allow for atoms, and we restrict to the finite case).
  https://leanprover-community.github.io/mathlib4_docs/Mathlib/SetTheory/ZFC/Basic.html#PSet

  The core definitions are:
    - `PreHFSet atoms` - The type of hereditarily finite lists with atoms in `atoms`
    - `HFSet atoms` - The type of hereditarily finite sets with atoms in `atoms`
    - `∈ : HFSet atoms → HFSet atoms → Prop` - Membership relation for `HFSet`
    - `isAtom : HFSet atoms → Bool` - Whether a given `HFSet` is an atom
    - `toFinset : HFSet atoms → Finset (HFSet atoms)` - Convert an `HFSet` to the `Finset` of `HFSet`'s it contains

  Constructors:
    - `atom : atoms → HFSet atoms` - Create an atom
    - `ofFinset : Finset (HFSet atoms) → HFSet atoms` - Create an `HFSet` from a `Finset`
  
  Induction Principles:
    - `wf_mem`: The membership relation is well-founded (this allows for well-founded recursive definitions with the equation compiler) 
    - `HFSet.induction`: To prove a property `P` of all `HFSet`s, we can assume that `P` holds for all elements of `y` for all `y ∈ x` before proving `P x`
    - `HFSet.induction'`: To prove a property `P` of all `HFSet`s, it suffices to prove that `P` holds for all atoms and that `P` is preserved by `HFSet.ofFinset`.

  Main results:
    - `ext_of_not_atom`: Two `HFSet`s are equal if neither is an atom and they have the same elements
    - `toFinset_ofFinset`, `ofFinset_toFinset`: `toFinset` and `ofFinset` are inverses of each other

-/

/-- A hereditarily finite set with atoms where order matters -/
inductive PreHFSet (atoms : Type _)
| atom : atoms → PreHFSet atoms
| lst : {n : ℕ} → (Fin n → PreHFSet atoms) → PreHFSet atoms

namespace PreHFSet
variable {atoms : Type _}

def Equiv : PreHFSet atoms → PreHFSet atoms → Prop
| (atom a), (atom b) => a = b
| (lst a), (lst b) => (∀ i, ∃ j, Equiv (a i) (b j)) ∧ (∀ j, ∃ i, Equiv (a i) (b j))
| _, _ => False

-- Note: this is a very slow equality check; if there is an order
-- we can do this faster by sorting the lists and then comparing
def EquivDecidable [DecidableEq atoms] : (x : PreHFSet atoms) → (y : PreHFSet atoms) → Decidable (Equiv x y)
| (atom a), (atom b) => inferInstanceAs (Decidable (a = b))
| (lst a), (lst b) =>
    haveI : ∀ i j, Decidable (Equiv (a i) (b j)) := fun i j => EquivDecidable _ _
    inferInstanceAs (Decidable $ (∀ i, ∃ j, Equiv (a i) (b j)) ∧ ∀ j, ∃ i, Equiv (a i) (b j))
| (atom _), (lst _) => inferInstanceAs (Decidable False)
| (lst _), (atom _) => inferInstanceAs (Decidable False)

protected theorem Equiv.rfl : ∀ {x : PreHFSet atoms}, Equiv x x
| (atom a) => rfl
| (lst a) => ⟨fun i => ⟨i, Equiv.rfl⟩, fun i => ⟨i, Equiv.rfl⟩⟩

theorem Equiv.euc : ∀ {x y z : PreHFSet atoms}, Equiv x y → Equiv z y → Equiv x z
| (atom a), (atom b), (atom c), h₁, h₂ => h₁.trans h₂.symm
| (lst a), (lst b), (lst c), ⟨h₁, h₂⟩, ⟨h₃, h₄⟩ =>
  ⟨fun x => let ⟨y, h⟩ := h₁ x
            let ⟨z, h'⟩ := h₄ y
            ⟨z, Equiv.euc h h'⟩,
   fun x => let ⟨y, h⟩ := h₃ x
            let ⟨z, h'⟩ := h₂ y
            ⟨z, Equiv.euc h' h⟩⟩

theorem Equiv.symm {x y : PreHFSet atoms} (h : Equiv x y) : Equiv y x :=
  Equiv.rfl.euc h

theorem Equiv.trans {x y z : PreHFSet atoms} (h₁ : Equiv x y) (h₂ : Equiv y z) : Equiv x z :=
  h₁.euc h₂.symm

instance : Setoid (PreHFSet atoms) := ⟨Equiv, @Equiv.rfl atoms, Equiv.symm, Equiv.trans⟩

instance [DecidableEq atoms] : DecidableRel ((· ≈ ·) : PreHFSet atoms → PreHFSet atoms → Prop) :=
  EquivDecidable

def Mem : PreHFSet atoms → PreHFSet atoms → Prop
| x, (lst b) => ∃ i, x ≈ (b i)
| _, (atom _) => False

instance : Membership (PreHFSet atoms) (PreHFSet atoms) := ⟨Mem⟩

theorem mem_of_mem_of_equiv : ∀ {x y z : PreHFSet atoms}, x ≈ y → x ∈ z → y ∈ z
| x, y, (lst a), h₁, ⟨i, hi⟩ => ⟨i, h₁.symm.trans hi⟩

theorem mem_of_mem_of_equiv_right : ∀ {x y z : PreHFSet atoms}, x ≈ y → z ∈ x → z ∈ y
| (lst a), (lst b), z, ⟨h₁, h₂⟩, ⟨i, hi⟩ => 
  let ⟨j, hj⟩ := h₁ i
  ⟨j, hi.trans hj⟩

lemma mem_iff_of_equiv {x y z : PreHFSet atoms} (h : x ≈ y) : z ∈ x ↔ z ∈ y :=
  ⟨mem_of_mem_of_equiv_right h, mem_of_mem_of_equiv_right h.symm⟩

instance : EmptyCollection (PreHFSet atoms) := ⟨lst Fin.elim0⟩

instance : Inhabited (PreHFSet atoms) := ⟨∅⟩

theorem not_mem_empty {x : PreHFSet atoms} : x ∉ (∅ : PreHFSet atoms)
| ⟨i, _⟩ => Fin.elim0 i

theorem not_mem_atom (x : PreHFSet atoms) (y : atoms) : x ∉ (atom y)
| _ => nomatch x

/-- Insert the first item into the second item (which should be a set). 
  If the second item is an atom, just return the second item unchanged. -/
def insert : PreHFSet atoms → PreHFSet atoms → PreHFSet atoms
| _, (atom a) => atom a
| x, (lst b) => lst (Fin.cons x b)

def isAtom : (x : PreHFSet atoms) → Bool
| (atom _) => true
| (lst _) => false

def getAtom : (x : PreHFSet atoms) → x.isAtom → atoms
| (atom x), _ => x

@[simp] lemma getAtom_atom (x : atoms) (h : (atom x).isAtom) : getAtom (atom x) h = x := rfl

@[simp]
theorem isAtom_insert (x y : PreHFSet atoms) : (insert x y).isAtom = y.isAtom :=
  match y with
  | (atom _) => rfl
  | (lst _) => rfl

theorem equiv_ext_of_not_atom {x y : PreHFSet atoms} (hx : x.isAtom = false) (hy : y.isAtom = false)
  (h : ∀ z, (z ∈ x ↔ z ∈ y)) : x ≈ y :=
  match x, y, hx, hy with
  | (lst x), (lst y), _, _ => ⟨fun i => (h (x i)).mp ⟨i, Equiv.rfl⟩, fun j => 
    let ⟨i, hi⟩ := (h (y j)).mpr ⟨j, Equiv.rfl⟩
    ⟨i, hi.symm⟩⟩

theorem insert_equiv_of_equiv {x y z z' : PreHFSet atoms} (h : x ≈ y) (h' : z ≈ z') : insert x z ≈ insert y z' :=
  match z, z', h' with
  | (atom a), (atom b), h' => h'
  | (lst a), (lst b), ⟨h₂, h₃⟩ => by
    constructor
    · intro i
      induction' i using Fin.cases with i
      · exact ⟨0, h⟩
      · let ⟨j, hj⟩ := h₂ i
        exact ⟨j.succ, hj⟩
    · intro i
      induction' i using Fin.cases with i
      · exact ⟨0, h⟩
      · let ⟨j, hj⟩ := h₃ i
        exact ⟨j.succ, hj⟩

@[simp]
theorem insert_atom (x : atoms) (y : PreHFSet atoms) : insert y (atom x) = (atom x) := rfl

theorem mem_insert_self (x y : PreHFSet atoms) (hy : y.isAtom = false) : x ∈ insert x y :=
  match y, hy with
  | (lst b), hy => ⟨0, Equiv.rfl⟩

theorem mem_insert_of_mem {x y z : PreHFSet atoms} (h : x ∈ z) : x ∈ insert y z :=
  match z, h with
  | (lst b), ⟨i, hi⟩ => ⟨i.succ, hi⟩

theorem eq_or_mem_of_mem_insert {x y z : PreHFSet atoms} : x ∈ insert y z → z.isAtom = false ∧ (x ≈ y ∨ x ∈ z) :=
  match z with
  | (atom a) => by simp [insert, isAtom, Membership.mem, Mem]
  | (lst b) => by
      rintro ⟨i, hi⟩
      induction' i using Fin.cases with i
      · refine ⟨rfl, Or.inl ?_⟩
        simpa using hi
      · refine ⟨rfl, Or.inr ⟨i, ?_⟩⟩
        simpa using hi

def rank : PreHFSet atoms → ℕ
| (atom _) => 0
| (@lst _ n b) => ((Finset.univ : Finset (Fin n)).sup (fun i => rank (b i))) + 1

theorem rank_eq_of_equiv : ∀ {x y : PreHFSet atoms}, x ≈ y → rank x = rank y 
| (atom _), (atom _), _ => rfl
| (lst a), (lst b), ⟨h₁, h₂⟩ => by
  apply le_antisymm
  · simp only [rank, Nat.succ_le_succ_iff, Finset.sup_le_iff]
    intro i _
    obtain ⟨j, hj⟩ := h₁ i
    rw [rank_eq_of_equiv hj]
    exact Finset.le_sup (f := fun i => rank (b i)) (Finset.mem_univ j)
  · simp only [rank, Nat.succ_le_succ_iff, Finset.sup_le_iff]
    intro i _
    obtain ⟨j, hj⟩ := h₂ i
    rw [← rank_eq_of_equiv hj]
    exact Finset.le_sup (f := fun i => rank (a i)) (Finset.mem_univ j)

theorem rank_eq_zero_iff : ∀ {x : PreHFSet atoms}, rank x = 0 ↔ x.isAtom
| (atom _) => by simp [rank, isAtom]
| (lst _) => by simp [rank, isAtom]
  

theorem rank_lt_of_mem {x y : PreHFSet atoms} (h : x ∈ y) : rank x < rank y :=
  match y, h with 
  | (lst b), h => by
    simp only [rank, Nat.lt_succ_iff]
    rcases h with ⟨i, hi⟩
    rw [rank_eq_of_equiv hi]
    exact Finset.le_sup (f := fun i => rank (b i)) (Finset.mem_univ i)

theorem exists_mem_rank_eq_rank_succ {y : PreHFSet atoms} (hy : ∃ z, z ∈ y) : ∃ z ∈ y, rank y = rank z + 1 :=
  let ⟨z, hz⟩ := hy
  match z, y, hz with
  | _, (@lst _ (n + 1) y), _ => by
    obtain ⟨i, _, hi⟩ := Finset.exists_mem_eq_sup' (Finset.univ_nonempty (α := Fin (n + 1))) (fun i => rank (y i))
    refine ⟨y i, ⟨i, Equiv.rfl⟩, ?_⟩
    rw [← hi, rank, Finset.sup'_eq_sup]

def toList : PreHFSet atoms → List (PreHFSet atoms)
| (atom _) => []
| (lst b) => .ofFn b

theorem mem_toList_iff {x y : PreHFSet atoms} : x ∈ y ↔ ∃ x', x' ∈ toList y ∧ x' ≈ x :=
  match y with
  | (atom _) => by simp [toList, not_mem_atom]
  | (lst b) =>
    ⟨fun ⟨i, hi⟩ => ⟨b i, (List.mem_ofFn _ _).mpr ⟨i, rfl⟩, hi.symm⟩, 
     fun ⟨x', h₁, h₂⟩ => by
      obtain ⟨i, rfl⟩ := (List.mem_ofFn _ _).mp h₁
      exact ⟨i, h₂.symm⟩⟩

protected def repr [Repr atoms] (openParen : Std.Format) (closeParen : Std.Format) (comma : Std.Format) : PreHFSet atoms → Std.Format
| (atom a) => repr a
| (lst a) => openParen ++ Std.Format.joinSep (List.ofFn (fun i => PreHFSet.repr openParen closeParen comma (a i))) comma ++ closeParen

instance [Repr atoms] : Repr (PreHFSet atoms) := ⟨fun s _ => s.repr "[" "]" ", "⟩

end PreHFSet

def HFSet (atoms : Type _) := Quotient (@PreHFSet.instSetoidPreHFSet atoms)

namespace HFSet
variable {atoms : Type _}

def atom (a : atoms) : HFSet atoms := ⟦PreHFSet.atom a⟧

instance [DecidableEq atoms] : DecidableEq (HFSet atoms) := Quotient.decidableEq

instance : EmptyCollection (HFSet atoms) := ⟨⟦∅⟧⟩
instance : Inhabited (HFSet atoms) := ⟨∅⟩

def Mem : HFSet atoms → HFSet atoms → Prop := Quotient.lift₂ PreHFSet.Mem fun x y z w h₁ h₂ =>
  propext ⟨
    fun h => 
      have h' := PreHFSet.mem_of_mem_of_equiv h₁ h
      PreHFSet.mem_of_mem_of_equiv_right h₂ h', 
    fun h => 
      have h' := PreHFSet.mem_of_mem_of_equiv h₁.symm h
      PreHFSet.mem_of_mem_of_equiv_right h₂.symm h'⟩

instance : Membership (HFSet atoms) (HFSet atoms) := ⟨Mem⟩

@[simp]
theorem not_mem_empty (x : HFSet atoms) : x ∉ (∅ : HFSet atoms) :=
  Quotient.inductionOn x (fun _ => PreHFSet.not_mem_empty)

@[simp]
theorem not_mem_atom (x : HFSet atoms) (y : atoms) : x ∉ atom y :=
  Quotient.inductionOn x (fun x => PreHFSet.not_mem_atom x y)

protected def insert : HFSet atoms → HFSet atoms → HFSet atoms := Quotient.lift₂ (fun x y => ⟦.insert x y⟧) fun x y z w h₁ h₂ => Quotient.sound (PreHFSet.insert_equiv_of_equiv h₁ h₂)

instance : Insert (HFSet atoms) (HFSet atoms) := ⟨HFSet.insert⟩

def isAtom : (x : HFSet atoms) → Bool := Quotient.lift (fun x => PreHFSet.isAtom x) fun x y h =>
  match x, y, h with
  | (PreHFSet.atom _), (PreHFSet.atom _), _ => rfl
  | (PreHFSet.lst _), (PreHFSet.lst _), _ => rfl

def getAtom (x : HFSet atoms) : x.isAtom → atoms :=
  Quotient.rec (fun x h => PreHFSet.getAtom x h) (fun x y h => 
  match x, y, h with
  | (PreHFSet.atom a), (PreHFSet.atom b), h => by
    ext h'
    cases h
    rfl
  | (PreHFSet.lst _), (PreHFSet.lst _), _ => by
    ext h'
    exact False.elim (Bool.noConfusion h')
  ) x

@[simp] lemma getAtom_atom (a : atoms) (h : (atom a).isAtom) : getAtom (atom a) h = a := rfl

theorem isAtom_eq_true_iff {x : HFSet atoms} : x.isAtom ↔ ∃ a, x = atom a :=
  Quotient.inductionOn x fun a => match a with
  | PreHFSet.atom a => ⟨fun h => ⟨a, rfl⟩, fun ⟨a', h⟩ => h.symm ▸ rfl⟩
  | PreHFSet.lst _ => ⟨fun h => Bool.noConfusion h, fun ⟨a, h⟩ => h.symm ▸ rfl⟩

theorem isAtom_eq_false_iff' {x : HFSet atoms} : x.isAtom = false ↔ ∃ (n : ℕ) (l : Fin n → PreHFSet atoms), 
    x = ⟦PreHFSet.lst l⟧ :=
  Quotient.inductionOn x fun a => match a with
  | PreHFSet.atom a => ⟨fun h => Bool.noConfusion h, fun ⟨n, l, h⟩ => h.symm ▸ rfl⟩
  | PreHFSet.lst l => ⟨fun h => ⟨_, _, rfl⟩, fun ⟨n, l, h⟩ => h.symm ▸ rfl⟩

@[simp] theorem isAtom_empty : isAtom (∅ : HFSet atoms) = false := rfl

@[simp] theorem isAtom_atom (a : atoms) : isAtom (atom a) := rfl

@[simp]
theorem isAtom_insert (x y : HFSet atoms) : (insert x y).isAtom = y.isAtom :=
  Quotient.inductionOn₂ x y fun _ _ => PreHFSet.isAtom_insert _ _

@[simp]
theorem insert_atom (x : atoms) (y : HFSet atoms) : insert y (atom x) = atom x :=
  Quotient.inductionOn y fun _ => rfl

@[ext]
theorem ext_of_not_atom {x y : HFSet atoms} :
    x.isAtom = false → y.isAtom = false → (∀ z, z ∈ x ↔ z ∈ y) → x = y :=
  Quotient.inductionOn₂ x y fun x y hx hy h => 
    Quotient.sound (PreHFSet.equiv_ext_of_not_atom hx hy (fun z => h ⟦z⟧))

@[simp]
theorem mem_insert_self (x y : HFSet atoms) : y.isAtom = false → x ∈ insert x y :=
  Quotient.inductionOn₂ x y fun x y hy => PreHFSet.mem_insert_self x y hy

theorem mem_insert_of_mem {x y z : HFSet atoms} : x ∈ z → x ∈ insert y z :=
  Quotient.inductionOn₃ x y z fun x y z h => PreHFSet.mem_insert_of_mem h

theorem eq_or_mem_of_mem_insert {x y z : HFSet atoms} : x ∈ insert y z → z.isAtom = false ∧ (x = y ∨ x ∈ z) :=
  Quotient.inductionOn₃ x y z fun x y z h => by
    rw [Quotient.eq]
    exact PreHFSet.eq_or_mem_of_mem_insert h

@[simp]
theorem mem_insert_iff {x y z : HFSet atoms} : x ∈ insert y z ↔ z.isAtom = false ∧ (x = y ∨ x ∈ z) := by
  constructor
  · intro h
    exact eq_or_mem_of_mem_insert h
  · rintro ⟨h₁, rfl|h₂⟩
    · exact mem_insert_self _ _ h₁
    · exact mem_insert_of_mem h₂

instance : Singleton (HFSet atoms) (HFSet atoms) := ⟨fun x => insert x ∅⟩

theorem mem_singleton_self (x : HFSet atoms) : x ∈ ({x} : HFSet atoms) :=
  mem_insert_self _ _ rfl

def ofMultiset (s : Multiset (HFSet atoms)) : HFSet atoms := s.foldr (fun x y => insert x y) 
  (by
    intros x y z
    cases H : z.isAtom
    · ext w <;> simp only [isAtom_insert] <;> try assumption
      simp [H]; tauto
    · rcases isAtom_eq_true_iff.mp H with ⟨a, rfl⟩
      simp) 
  ∅

@[simp]
theorem ofMultiset_cons (s : Multiset (HFSet atoms)) (x : HFSet atoms) : ofMultiset (x ::ₘ s) = insert x (ofMultiset s) :=
  by simp [ofMultiset]

@[simp]
theorem ofMultiset_isAtom (s : Multiset (HFSet atoms)) : (ofMultiset s).isAtom = false :=
  s.induction_on (by simp [ofMultiset]) (fun y s ih => by simpa)

@[simp]
theorem mem_ofMultiset_iff {s : Multiset (HFSet atoms)} {x : HFSet atoms} : x ∈ ofMultiset s ↔ x ∈ s :=
  s.induction_on (by simp [ofMultiset]) (fun y s ih => by simp [ih])

def ofFinset (s : Finset (HFSet atoms)) : HFSet atoms := ofMultiset s.1

@[simp]
theorem ofFinset_isAtom (s : Finset (HFSet atoms)) : (ofFinset s).isAtom = false :=
  ofMultiset_isAtom _


@[simp]
theorem mem_ofFinset_iff {s : Finset (HFSet atoms)} {x : HFSet atoms} : x ∈ ofFinset s ↔ x ∈ s :=
  by simp [ofFinset]

def toFinset [DecidableEq atoms] (s : HFSet atoms) : Finset (HFSet atoms) :=
  Quotient.lift (fun s => (s.toList.map $ fun z => ⟦z⟧).toFinset) (fun a b h => by
    ext z
    induction' z using Quotient.inductionOn with z
    simp only [List.mem_toFinset, List.mem_map, Quotient.eq, ← PreHFSet.mem_toList_iff]
    exact PreHFSet.mem_iff_of_equiv h
  ) s

@[simp]
theorem mem_toFinset_iff [DecidableEq atoms] {x s : HFSet atoms} : x ∈ s.toFinset ↔ x ∈ s :=
  Quotient.inductionOn₂ s x fun s x => by 
    rw [toFinset, Quotient.lift_mk, List.mem_toFinset (a := ⟦x⟧)]
    simp only [List.mem_map, Quotient.eq, ← PreHFSet.mem_toList_iff]
    rfl

instance [DecidableEq atoms] : DecidableRel (· ∈ · : HFSet atoms → HFSet atoms → Prop) :=
  fun x y => decidable_of_iff (x ∈ y.toFinset) (by simp) 

@[simp]
theorem toFinset_ofFinset [DecidableEq atoms] (s : HFSet atoms) (hs : s.isAtom = false) : ofFinset s.toFinset = s := by
  ext x <;> simp [hs]

@[simp]
theorem ofFinset_toFinset [DecidableEq atoms] (s : Finset (HFSet atoms)) : (ofFinset s).toFinset = s := by
  ext x; simp

lemma ofFinset_insert [DecidableEq atoms] (x : HFSet atoms) (s : Finset (HFSet atoms)) :
    ofFinset (insert x s) = insert x (ofFinset s) := by
  ext z <;> simp

lemma toFinset_eq_empty_iff [DecidableEq atoms] (x : HFSet atoms) :
    x.toFinset = ∅ ↔ x.isAtom ∨ x = ∅ :=
  ⟨fun h => if h' : x.isAtom then Or.inl h' else Or.inr 
    (by ext z; simpa using h'; simp; simpa using congr_arg (z ∈ ·) h),
  (by
    rintro (h'|rfl)
    · obtain ⟨a, rfl⟩ := isAtom_eq_true_iff.mp h'; rfl 
    · rfl )⟩

def rank (s : HFSet atoms) : ℕ :=
  Quotient.lift (fun x => PreHFSet.rank x) (fun x y h => PreHFSet.rank_eq_of_equiv h) s

theorem rank_lt_of_mem {x y : HFSet atoms} : x ∈ y → rank x < rank y :=
  Quotient.inductionOn₂ x y fun x y h => PreHFSet.rank_lt_of_mem h

@[simp] lemma rank_atom (a : atoms) : rank (HFSet.atom a) = 0 := rfl

@[simp] lemma rank_empty : rank (∅ : HFSet atoms) = 1 := rfl

@[simp] lemma rank_eq_zero_iff {x : HFSet atoms} : rank x = 0 ↔ x.isAtom :=
  Quotient.inductionOn x (fun _ => PreHFSet.rank_eq_zero_iff)

theorem rank_def [DecidableEq atoms] (x : HFSet atoms) (h : x.isAtom = false) : rank x = x.toFinset.sup rank + 1 := by
  apply le_antisymm; swap
  · rw [Nat.succ_le_iff, Finset.sup_lt_iff]
    · intro; simpa using rank_lt_of_mem
    · contrapose! h; simpa using h
  · by_cases H : (toFinset x).Nonempty; swap
    · simp only [Finset.not_nonempty_iff_eq_empty, toFinset_eq_empty_iff, h, false_or] at H 
      simp [H]
    · rcases H with ⟨z, hz⟩
      rw [mem_toFinset_iff] at hz
      revert h hz; refine Quotient.inductionOn₂ x z fun x z h hz => ?_
      obtain ⟨y, hy, hr⟩ := PreHFSet.exists_mem_rank_eq_rank_succ ⟨z, hz⟩
      conv_lhs => dsimp only [rank]
      simp only [Quotient.lift_mk, hr, add_le_add_iff_right, bot_eq_zero']
      refine Finset.le_sup (f := rank) (b := ⟦y⟧) ?_
      simpa using hy

@[simp]
theorem rank_ofFinset (s : Finset (HFSet atoms)) : rank (ofFinset s) = s.sup rank + 1 := by
  classical
  rw [rank_def] <;> simp

lemma wf_rank : WellFounded fun (x y : HFSet atoms) => rank x < rank y := (measure rank).wf

lemma wf_mem : WellFounded (· ∈ · : HFSet atoms → HFSet atoms → Prop) := Subrelation.wf rank_lt_of_mem wf_rank

instance : WellFoundedRelation (HFSet atoms) := ⟨_, wf_mem⟩ 

def induction {motive : HFSet atoms → Sort _} (h : ∀ (y : HFSet atoms), (∀ z, z ∈ y → motive z) → motive y) : ∀ x, motive x :=
  WellFounded.fix wf_mem h

lemma induction' {motive : HFSet atoms → Prop} (x : HFSet atoms) (h₁ : ∀ a, motive (HFSet.atom a))
    (h₂ : ∀ (s : Finset (HFSet atoms)), (∀ y ∈ s, motive y) → motive (ofFinset s)) : motive x :=
  induction (fun y ih => by
    cases H : y.isAtom; swap
    · rcases isAtom_eq_true_iff.mp H with ⟨a, rfl⟩
      exact h₁ a
    · classical
      simpa [H] using h₂ y.toFinset (by simpa)
  ) x

section repr

-- not in mathlib??
lemma _root_.Finset.map_id (x : Finset α) : x.map ⟨fun z => z, fun a b => id⟩ = x := by
  ext y; simp

/-- This is the identity function, but in the VM it removes duplicates from the underlying `PreHFSet` representation -/
partial def normalize [DecidableEq atoms] (s : HFSet atoms) : { x : HFSet atoms // x = s }  :=
  have : ∀ x, ↑(normalize x) = x := fun x => (normalize x).prop 
  if h : s.isAtom then ⟨s, rfl⟩
  else ⟨ofFinset (s.toFinset.map ⟨fun x => (normalize x).1, fun a b => by simp [this]⟩),
    by simp [this, Finset.map_id s.toFinset, h]⟩

lemma normalize_eq [DecidableEq atoms] : (@normalize atoms _) = fun s => ⟨s, rfl⟩ := by
  ext s : 2; exact (normalize s).prop

unsafe instance [DecidableEq atoms] [Repr atoms] : Repr (HFSet atoms) :=
  ⟨fun s _ => (Quot.unquot s.normalize.1).repr "{" "}" ", "⟩

end repr

end HFSet