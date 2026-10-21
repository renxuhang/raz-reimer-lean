import Std

/-!
Abigail Raz's 2017 counterexample to Conjecture 3 of
"Note on the union-closed sets conjecture", EJC 24(3), P3.53.
Source: https://www.combinatorics.org/ojs/index.php/eljc/article/download/v24i3p53/pdf/
The exact sets are Counterexample 9, printed page 4; Condition 1 is
Definition 2, printed page 2. Elements 1,...,n use bit positions 0,...,n-1.

This proves the negative answer to the Reimer-condition strengthening.
It does not disprove Frankl's union-closed sets conjecture, prove Reimer's
average-set-size theorem, or prove minimality of Raz's example.
The mathematical construction is Raz's, not a new discovery.
-/

namespace RazReimer

abbrev SmallSet (n : Nat) := Fin (2 ^ n)

def Mem {n : Nat} (x : Fin n) (s : SmallSet n) : Prop :=
  s.val.testBit x.val = true

instance {n : Nat} (x : Fin n) (s : SmallSet n) : Decidable (Mem x s) :=
  inferInstanceAs (Decidable (s.val.testBit x.val = true))

def Subset {n : Nat} (s t : SmallSet n) : Prop :=
  ∀ x : Fin n, Mem x s → Mem x t

instance {n : Nat} (s t : SmallSet n) : Decidable (Subset s t) :=
  inferInstanceAs (Decidable (∀ x : Fin n, Mem x s → Mem x t))

-- Every subset of Fin n is represented, including predicates supplied
-- independently of this file's finite encoding.
theorem all_subsets_represented {n : Nat} (P : Fin n → Prop) :
    ∃ s : SmallSet n, ∀ x : Fin n, Mem x s ↔ P x := by
  classical
  let f : Fin n → Bool := fun x => decide (P x)
  let b := BitVec.ofBoolListLE (List.ofFn f)
  refine ⟨⟨b.toNat, ?_⟩, ?_⟩
  · simpa [b] using b.isLt
  · intro x
    have hbit : b.toNat.testBit x.val = f x := by
      rw [BitVec.testBit_toNat]
      change (BitVec.ofBoolListLE (List.ofFn f)).getLsbD x.val = f x
      rw [BitVec.getLsbD_ofBoolListLE]
      simp [List.getD_eq_getElem?_getD, x.isLt]
    change b.toNat.testBit x.val = true ↔ P x
    rw [hbit]
    simp [f]

theorem smallSet_ext {n : Nat} {s t : SmallSet n}
    (h : ∀ x : Fin n, Mem x s ↔ Mem x t) : s = t := by
  apply Fin.ext
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hi : i < n
  · have hh := h ⟨i, hi⟩
    unfold Mem at hh
    cases hs : s.val.testBit i <;> cases ht : t.val.testBit i <;> simp_all
  · have hpow : 2 ^ n ≤ 2 ^ i := Nat.pow_le_pow_right (by decide) (by omega)
    rw [Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le s.isLt hpow),
      Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le t.isLt hpow)]

theorem subset_trans {n : Nat} {a b c : SmallSet n}
    (hab : Subset a b) (hbc : Subset b c) : Subset a c := by
  intro x hx
  exact hbc x (hab x hx)

def UpwardClosed {n m : Nat} (F : Fin m → SmallSet n) : Prop :=
  ∀ i : Fin m, ∀ s : SmallSet n, Subset (F i) s → ∃ j : Fin m, F j = s

def PairSeparated {n m : Nat} (A F : Fin m → SmallSet n) : Prop :=
  ∀ i j : Fin m, i ≠ j → ¬ Subset (A i) (F j) ∨ ¬ Subset (A j) (F i)

def IntervalsDisjoint {n m : Nat} (A F : Fin m → SmallSet n) : Prop :=
  ∀ i j : Fin m, i ≠ j → ∀ s : SmallSet n,
    Subset (A i) s → Subset s (F i) →
    Subset (A j) s → Subset s (F j) → False

theorem intervalsDisjoint_of_pairSeparated {n m : Nat}
    {A F : Fin m → SmallSet n} (h : PairSeparated A F) :
    IntervalsDisjoint A F := by
  intro i j hij s hiA hiF hjA hjF
  cases h i j hij with
  | inl hc => exact hc (subset_trans hiA hjF)
  | inr hc => exact hc (subset_trans hjA hiF)

-- The common index is an explicit bijection between the two ranges,
-- since both enumerations are injective. No duplicates can inflate counts.
def ReimerCondition {n m : Nat} (A : Fin m → SmallSet n) : Prop :=
  ∃ F : Fin m → SmallSet n,
    Function.Injective A ∧ Function.Injective F ∧ UpwardClosed F ∧
    (∀ i : Fin m, Subset (A i) (F i)) ∧ IntervalsDisjoint A F

-- Explicitly check that the shared index really gives a bijection of ranges.
def Paired {n m : Nat} (A F : Fin m → SmallSet n) (s t : SmallSet n) : Prop :=
  ∃ i : Fin m, A i = s ∧ F i = t

theorem correspondence_bijective {n m : Nat} {A F : Fin m → SmallSet n}
    (hA : Function.Injective A) (hF : Function.Injective F) :
    (∀ s, (∃ i, A i = s) → ∃ t, (∃ j, F j = t) ∧ Paired A F s t ∧
      ∀ t', Paired A F s t' → t' = t) ∧
    (∀ t, (∃ j, F j = t) → ∃ s, (∃ i, A i = s) ∧ Paired A F s t ∧
      ∀ s', Paired A F s' t → s' = s) := by
  constructor
  · intro s ⟨i, hi⟩
    refine ⟨F i, ⟨i, rfl⟩, ⟨i, hi, rfl⟩, ?_⟩
    intro t' ⟨j, hjA, hjF⟩
    have hji : j = i := hA (hjA.trans hi.symm)
    subst j
    exact hjF.symm
  · intro t ⟨i, hi⟩
    refine ⟨A i, ⟨i, rfl⟩, ⟨i, rfl, hi⟩, ?_⟩
    intro s' ⟨j, hjA, hjF⟩
    have hji : j = i := hF (hjF.trans hi.symm)
    subst j
    exact hjA.symm

def frequency {n m : Nat} (A : Fin m → SmallSet n) (x : Fin n) : Nat :=
  ((List.finRange m).filter fun i => decide (Mem x (A i))).length

def HasAbundantElement {n m : Nat} (A : Fin m → SmallSet n) : Prop :=
  ∃ x : Fin n, m ≤ 2 * frequency A x

-- Data transcribed from Raz's Counterexample 9, with zero-based bit positions.
def A (i : Fin 11) : SmallSet 8 :=
  match i.val with
  | 0 => ⟨255, by decide⟩
  | 1 => ⟨234, by decide⟩
  | 2 => ⟨149, by decide⟩
  | 3 => ⟨201, by decide⟩
  | 4 => ⟨54, by decide⟩
  | 5 => ⟨69, by decide⟩
  | 6 => ⟨22, by decide⟩
  | 7 => ⟨42, by decide⟩
  | 8 => ⟨120, by decide⟩
  | 9 => ⟨128, by decide⟩
  | _ => ⟨1, by decide⟩

def F (i : Fin 11) : SmallSet 8 :=
  match i.val with
  | 0 => ⟨255, by decide⟩
  | 1 => ⟨254, by decide⟩
  | 2 => ⟨253, by decide⟩
  | 3 => ⟨251, by decide⟩
  | 4 => ⟨247, by decide⟩
  | 5 => ⟨239, by decide⟩
  | 6 => ⟨223, by decide⟩
  | 7 => ⟨191, by decide⟩
  | 8 => ⟨127, by decide⟩
  | 9 => ⟨252, by decide⟩
  | _ => ⟨243, by decide⟩

theorem A_injective : Function.Injective A := by
  unfold Function.Injective
  decide
theorem F_injective : Function.Injective F := by
  unfold Function.Injective
  decide
set_option maxRecDepth 4096 in
theorem F_upwardClosed : UpwardClosed F := by
  unfold UpwardClosed
  decide
theorem A_subset_F : ∀ i : Fin 11, Subset (A i) (F i) := by decide
theorem separated : PairSeparated A F := by
  unfold PairSeparated
  decide

theorem condition : ReimerCondition A :=
  ⟨F, A_injective, F_injective, F_upwardClosed, A_subset_F,
    intervalsDisjoint_of_pairSeparated separated⟩

theorem frequencies : ∀ x : Fin 8, frequency A x = 5 := by decide
theorem no_abundant_element : ¬ HasAbundantElement A := by
  unfold HasAbundantElement
  decide

def ReimerStrengthening : Prop :=
  ∀ n m : Nat, 0 < m → ∀ B : Fin m → SmallSet n,
    ReimerCondition B → HasAbundantElement B

theorem not_reimerStrengthening : ¬ ReimerStrengthening := by
  intro h
  exact no_abundant_element (h 8 11 (by decide) A condition)

-- This additional check makes the distinction from Frankl's conjecture explicit.
def UnionClosed {n m : Nat} (B : Fin m → SmallSet n) : Prop :=
  ∀ i j : Fin m, ∃ k : Fin m, ∀ x : Fin n,
    Mem x (B k) ↔ Mem x (B i) ∨ Mem x (B j)

theorem A_not_unionClosed : ¬ UnionClosed A := by
  unfold UnionClosed
  decide

theorem counterexample :
    ∃ n m : Nat, ∃ B : Fin m → SmallSet n,
      0 < m ∧ Function.Injective B ∧ ReimerCondition B ∧
      (∀ x : Fin n, 2 * frequency B x < m) ∧ ¬ UnionClosed B := by
  refine ⟨8, 11, A, by decide, A_injective, condition, ?_, A_not_unionClosed⟩
  intro x
  rw [frequencies]
  decide

#print axioms all_subsets_represented
#print axioms smallSet_ext
#print axioms correspondence_bijective
#print axioms condition
#print axioms frequencies
#print axioms not_reimerStrengthening
#print axioms A_not_unionClosed
#print axioms counterexample

end RazReimer
