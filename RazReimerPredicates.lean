import RazReimer

/-!
A statement-facing presentation of Raz's counterexample. Subsets are arbitrary
predicates on a finite ground set; inclusion and interval membership have their
ordinary pointwise meaning. The existing bit encoding is only an implementation.
Mathematical credit: Abigail Raz (2017). This does not resolve Frankl's conjecture.
-/

namespace RazReimerPredicates

abbrev SubsetOf (α : Type) := α → Prop

def Included {α : Type} (S T : SubsetOf α) : Prop := ∀ x, S x → T x

def UpwardClosed {α : Type} {m : Nat}
    (F : Fin m → SubsetOf α) : Prop :=
  ∀ i, ∀ T : SubsetOf α, Included (F i) T → ∃ j, F j = T

def IntervalsDisjoint {α : Type} {m : Nat}
    (S F : Fin m → SubsetOf α) : Prop :=
  ∀ i j, i ≠ j → ∀ T : SubsetOf α,
    Included (S i) T → Included T (F i) →
    Included (S j) T → Included T (F j) → False

def ReimerCondition {α : Type} {m : Nat}
    (S : Fin m → SubsetOf α) : Prop :=
  ∃ F : Fin m → SubsetOf α,
    Function.Injective S ∧ Function.Injective F ∧ UpwardClosed F ∧
    (∀ i, Included (S i) (F i)) ∧ IntervalsDisjoint S F

def Nontrivial {α : Type} {m : Nat} (S : Fin m → SubsetOf α) : Prop :=
  ∃ i x, S i x

def UnionClosed {α : Type} {m : Nat} (S : Fin m → SubsetOf α) : Prop :=
  ∀ i j, ∃ k, ∀ x, S k x ↔ S i x ∨ S j x

-- This relation is a bijection of the actual ranges, not just of index names.
def Paired {α : Type} {m : Nat}
    (S F : Fin m → SubsetOf α) (P Q : SubsetOf α) : Prop :=
  ∃ i, S i = P ∧ F i = Q

theorem shared_index_bijective {α : Type} {m : Nat}
    {S F : Fin m → SubsetOf α}
    (hS : Function.Injective S) (hF : Function.Injective F) :
    (∀ P, (∃ i, S i = P) → ∃ Q, (∃ j, F j = Q) ∧ Paired S F P Q ∧
      ∀ Q', Paired S F P Q' → Q' = Q) ∧
    (∀ Q, (∃ j, F j = Q) → ∃ P, (∃ i, S i = P) ∧ Paired S F P Q ∧
      ∀ P', Paired S F P' Q → P' = P) := by
  constructor
  · intro P ⟨i, hi⟩
    refine ⟨F i, ⟨i, rfl⟩, ⟨i, hi, rfl⟩, ?_⟩
    intro Q' ⟨j, hjS, hjF⟩
    have hji : j = i := hS (hjS.trans hi.symm)
    subst j
    exact hjF.symm
  · intro Q ⟨i, hi⟩
    refine ⟨S i, ⟨i, rfl⟩, ⟨i, rfl, hi⟩, ?_⟩
    intro P' ⟨j, hjS, hjF⟩
    have hji : j = i := hF (hjF.trans hi.symm)
    subst j
    exact hjS.symm

noncomputable def frequency {α : Type} {m : Nat}
    (S : Fin m → SubsetOf α) (x : α) : Nat := by
  classical
  exact ((List.finRange m).filter fun i => decide (S i x)).length

def HasAbundantElement {α : Type} {m : Nat}
    (S : Fin m → SubsetOf α) : Prop :=
  ∃ x, m ≤ 2 * frequency S x

def decode {n : Nat} (s : RazReimer.SmallSet n) : SubsetOf (Fin n) :=
  fun x => RazReimer.Mem x s

theorem decode_injective {n : Nat} : Function.Injective (@decode n) := by
  intro s t h
  apply RazReimer.smallSet_ext
  intro x
  exact iff_of_eq (congrFun h x)

theorem every_predicate_represented {n : Nat} (P : SubsetOf (Fin n)) :
    ∃ s : RazReimer.SmallSet n, decode s = P := by
  obtain ⟨s, hs⟩ := RazReimer.all_subsets_represented P
  exact ⟨s, funext (fun x => propext (hs x))⟩

theorem condition_transfer {n m : Nat} {S : Fin m → RazReimer.SmallSet n}
    (h : RazReimer.ReimerCondition S) :
    ReimerCondition (fun i => decode (S i)) := by
  obtain ⟨F, hS, hF, hup, hsub, hdis⟩ := h
  refine ⟨(fun i => decode (F i)), ?_, ?_, ?_, ?_, ?_⟩
  · intro i j hij
    exact hS (decode_injective hij)
  · intro i j hij
    exact hF (decode_injective hij)
  · intro i P hi
    obtain ⟨p, hp⟩ := every_predicate_represented P
    have hinc : RazReimer.Subset (F i) p := by
      intro x hx
      have hxP := hi x hx
      change decode p x
      rw [hp]
      exact hxP
    obtain ⟨j, hj⟩ := hup i p hinc
    exact ⟨j, (congrArg decode hj).trans hp⟩
  · exact hsub
  · intro i j hij P hiS hiF hjS hjF
    obtain ⟨p, hp⟩ := every_predicate_represented P
    apply hdis i j hij p
    · intro x hx
      change decode p x
      rw [hp]
      exact hiS x hx
    · intro x hx
      apply hiF x
      change decode p x at hx
      rwa [hp] at hx
    · intro x hx
      change decode p x
      rw [hp]
      exact hjS x hx
    · intro x hx
      apply hjF x
      change decode p x at hx
      rwa [hp] at hx

theorem condition_reflection {n m : Nat} {S : Fin m → RazReimer.SmallSet n}
    (h : ReimerCondition (fun i => decode (S i))) :
    RazReimer.ReimerCondition S := by
  classical
  obtain ⟨F, hS, hF, hup, hsub, hdis⟩ := h
  let G : Fin m → RazReimer.SmallSet n :=
    fun i => Classical.choose (every_predicate_represented (F i))
  have hG (i : Fin m) : decode (G i) = F i :=
    Classical.choose_spec (every_predicate_represented (F i))
  refine ⟨G, ?_, ?_, ?_, ?_, ?_⟩
  · intro i j hij
    exact hS (congrArg decode hij)
  · intro i j hij
    exact hF ((hG i).symm.trans ((congrArg decode hij).trans (hG j)))
  · intro i p hi
    have hinc : Included (F i) (decode p) := by
      rw [← hG i]
      exact hi
    obtain ⟨j, hj⟩ := hup i (decode p) hinc
    exact ⟨j, decode_injective ((hG j).trans hj)⟩
  · intro i x hx
    change decode (G i) x
    rw [hG i]
    exact hsub i x hx
  · intro i j hij p hiS hiF hjS hjF
    apply hdis i j hij (decode p) hiS
    · rw [← hG i]
      exact hiF
    · exact hjS
    · rw [← hG j]
      exact hjF

theorem condition_iff {n m : Nat} {S : Fin m → RazReimer.SmallSet n} :
    ReimerCondition (fun i => decode (S i)) ↔ RazReimer.ReimerCondition S :=
  ⟨condition_reflection, condition_transfer⟩

theorem frequency_transfer {n m : Nat}
    (S : Fin m → RazReimer.SmallSet n) (x : Fin n) :
    frequency (fun i => decode (S i)) x = RazReimer.frequency S x := by
  unfold frequency RazReimer.frequency
  apply congrArg List.length
  apply List.filter_congr
  intro i hi
  by_cases h : RazReimer.Mem x (S i)
  · simp [decode, h]
  · simp [decode, h]

def A : Fin 11 → SubsetOf (Fin 8) := fun i => decode (RazReimer.A i)

theorem A_nontrivial : Nontrivial A := by
  refine ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ?_⟩
  change (255 : Nat).testBit 0 = true
  decide

theorem A_injective : Function.Injective A := by
  intro i j h
  exact RazReimer.A_injective (decode_injective h)

theorem A_condition : ReimerCondition A :=
  condition_transfer RazReimer.condition

theorem A_frequencies : ∀ x : Fin 8, frequency A x = 5 := by
  intro x
  exact (frequency_transfer RazReimer.A x).trans (RazReimer.frequencies x)

theorem A_not_unionClosed : ¬ UnionClosed A := by
  exact RazReimer.A_not_unionClosed

def Strengthening : Prop :=
  ∀ n m : Nat, 0 < m → ∀ S : Fin m → SubsetOf (Fin n),
    Nontrivial S → ReimerCondition S → HasAbundantElement S

theorem counterexample :
    ∃ S : Fin 11 → SubsetOf (Fin 8),
      Nontrivial S ∧ Function.Injective S ∧ ReimerCondition S ∧
      (∀ x : Fin 8, frequency S x = 5) ∧
      ¬ HasAbundantElement S ∧ ¬ UnionClosed S := by
  refine ⟨A, A_nontrivial, A_injective, A_condition, A_frequencies, ?_,
    A_not_unionClosed⟩
  · intro ⟨x, hx⟩
    rw [A_frequencies x] at hx
    omega

theorem not_strengthening : ¬ Strengthening := by
  intro h
  obtain ⟨S, hn, _, hS, _, habs, _⟩ := counterexample
  exact habs (h 8 11 (by decide) S hn hS)

end RazReimerPredicates
