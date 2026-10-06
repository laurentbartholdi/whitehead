module

public import RequestProject.OrderConstructionPartialOrder
public import RequestProject.OrderNerveContiguousHomotopy
public import Mathlib.Topology.Homotopy.Equiv

@[expose] public section

/-! An actual homotopy equivalence from the realization of a poset mapping
cylinder to its base when the outer poset has height at most one. Collapsing
outer edge vertices first and outer zero vertices second gives two genuine
contiguous homotopies; pointwise order comparison is not mistaken for
cross-comparability. -/

noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains.Comb
open CategoryTheory
open scoped unitInterval Topology Classical

theorem orderNerveRealizationMap_congr {P Q : Type} [PartialOrder P] [PartialOrder Q]
    {f g : P → Q} (hf : Monotone f) (hg : Monotone g) (he : f = g)
    (x : orderNerveRealization P) :
    orderNerveRealizationMap f hf x = orderNerveRealizationMap g hg x := by
  subst g
  rfl

variable {X S : Type} [PartialOrder X] [PartialOrder S]
  (a : S →o X) (d : S → ℕ) (hd : StrictMono d) (hd₁ : ∀ s, d s ≤ 1)

include hd hd₁ in
theorem rankOne_maximal {s t : S} (hs : d s = 1) (h : s ≤ t) : s = t := by
  by_contra hne
  have hh := hd (lt_of_le_of_ne h hne)
  have ht := hd₁ t
  omega

include hd in
theorem rankOne_minimal {s t : S} (ht : d t = 0) (h : s ≤ t) : s = t := by
  by_contra hne
  have hh := hd (lt_of_le_of_ne h hne)
  omega

def cylinderHalfCollapse : CylP a → CylP a
  | .inl x => .inl x
  | .inr s => if d s = 1 then .inl (a s) else .inr s

include hd hd₁ in
theorem cylinderHalfCollapse_monotone : Monotone (cylinderHalfCollapse a d) := by
  intro p q hpq
  rcases p with x | s <;> rcases q with y | t
  · exact hpq
  · exact hpq.elim
  · change a s ≤ y at hpq
    change CylP.le a (cylinderHalfCollapse a d (Sum.inr s)) (cylinderHalfCollapse a d (Sum.inl y))
    by_cases hs : d s = 1 <;> simpa only [cylinderHalfCollapse, hs, ↓reduceIte, CylP.le] using hpq
  · change s ≤ t at hpq
    by_cases hs : d s = 1
    · have he := rankOne_maximal d hd hd₁ hs hpq
      subst t
      exact le_rfl
    · by_cases ht : d t = 1
      · change ((if d s = 1 then Sum.inl (a s) else Sum.inr s) : CylP a) ≤
          (if d t = 1 then Sum.inl (a t) else Sum.inr t)
        rw [if_neg hs, if_pos ht]
        exact a.monotone hpq
      · change CylP.le a (cylinderHalfCollapse a d (Sum.inr s)) (cylinderHalfCollapse a d (Sum.inr t))
        simpa only [cylinderHalfCollapse, if_neg hs, if_neg ht, CylP.le] using hpq

include hd hd₁ in
theorem cylinderHalfCollapse_cross :
    ∀ p q : CylP a, p ≤ q ∨ q ≤ p →
      p ≤ cylinderHalfCollapse a d q ∨ cylinderHalfCollapse a d q ≤ p := by
  intro p q hpq
  rcases p with x | s <;> rcases q with y | t
  · exact hpq
  · by_cases ht : d t = 1
    · rw [cylinderHalfCollapse, if_pos ht]
      rcases hpq with h | h
      · exact h.elim
      · exact Or.inr h
    · simpa only [cylinderHalfCollapse, CylP.le, if_neg ht] using hpq
  · exact hpq
  · by_cases ht : d t = 1
    · rw [cylinderHalfCollapse, if_pos ht]
      rcases hpq with h | h
      · exact Or.inl (a.monotone h)
      · have he := rankOne_maximal d hd hd₁ ht h
        subst s
        exact Or.inl (le_refl (a t))
    · simpa only [cylinderHalfCollapse, CylP.le, if_neg ht] using hpq

include hd hd₁ in
theorem cylinderCollapse_half_cross :
    ∀ p q : CylP a, p ≤ q ∨ q ≤ p →
      cylinderHalfCollapse a d p ≤ cylCollapse a q ∨
        cylCollapse a q ≤ cylinderHalfCollapse a d p := by
  intro p q hpq
  rcases p with x | s <;> rcases q with y | t
  · exact hpq
  · rcases hpq with h | h
    · exact h.elim
    · exact Or.inr h
  · rcases hpq with h | h
    · by_cases hs : d s = 1
      · change CylP.le a (cylinderHalfCollapse a d (Sum.inr s)) (cylCollapse a (Sum.inl y)) ∨
          CylP.le a (cylCollapse a (Sum.inl y)) (cylinderHalfCollapse a d (Sum.inr s))
        simpa only [cylinderHalfCollapse, if_pos hs, cylCollapse, cylRetr, cylIn, Sum.elim_inl, id_eq, CylP.le] using
          (Or.inl h : a s ≤ y ∨ y ≤ a s)
      · apply Or.inl
        simpa only [cylinderHalfCollapse, CylP.le, if_neg hs, cylCollapse, cylRetr, cylIn, Sum.elim_inl, id_eq] using h
    · exact h.elim
  · by_cases hs : d s = 1
    · simp only [cylinderHalfCollapse, CylP.le, if_pos hs, cylCollapse, cylRetr, cylIn, Sum.elim_inl, id_eq]
      exact hpq.elim (fun h => Or.inl (a.monotone h)) (fun h => Or.inr (a.monotone h))
    · have hs₀ : d s = 0 := by have := hd₁ s; omega
      apply Or.inl
      change ((if d s = 1 then Sum.inl (a s) else Sum.inr s) : CylP a) ≤ Sum.inl (a t)
      rw [if_neg hs]
      rcases hpq with h | h
      · exact a.monotone h
      · have he := rankOne_minimal d hd hs₀ h
        subst t
        exact le_rfl

def cylinderRealizationInclusion :
    C(orderNerveRealization X, orderNerveRealization (CylP a)) :=
  ⟨orderNerveRealizationMap (cylIn a) (cylIn_monotone a),
    (orderNerveRealizationMap (cylIn a) (cylIn_monotone a)).hom.continuous⟩

def cylinderRealizationRetraction :
    C(orderNerveRealization (CylP a), orderNerveRealization X) :=
  ⟨orderNerveRealizationMap (cylRetr a) (cylRetr_monotone a),
    (orderNerveRealizationMap (cylRetr a) (cylRetr_monotone a)).hom.continuous⟩

theorem cylinderRealization_section :
    (cylinderRealizationRetraction a).comp (cylinderRealizationInclusion a) =
      ContinuousMap.id (orderNerveRealization X) := by
  apply ContinuousMap.ext
  intro x
  change orderNerveRealizationMap (cylRetr a) (cylRetr_monotone a)
    (orderNerveRealizationMap (cylIn a) (cylIn_monotone a) x) = x
  rw [orderNerveRealizationMap_comp]
  have he : cylRetr a ∘ cylIn a = id := rfl
  exact (orderNerveRealizationMap_congr _ monotone_id he x).trans
    (orderNerveRealizationMap_id _ _)

def rankOneCylinderRealizationDeformation : ContinuousMap.Homotopy
    (ContinuousMap.id (orderNerveRealization (CylP a)))
    ((cylinderRealizationInclusion a).comp (cylinderRealizationRetraction a)) := by
  let H₀ := orderNerveRealizationContiguousHomotopy id monotone_id
    (cylinderHalfCollapse a d) (cylinderHalfCollapse_monotone a d hd hd₁)
    (cylinderHalfCollapse_cross a d hd hd₁)
  let H₁ := orderNerveRealizationContiguousHomotopy
    (cylinderHalfCollapse a d) (cylinderHalfCollapse_monotone a d hd hd₁)
    (cylCollapse a) (cylCollapse_monotone a) (cylinderCollapse_half_cross a d hd hd₁)
  have hzero :
      (⟨orderNerveRealizationMap id monotone_id,
        (orderNerveRealizationMap id monotone_id).hom.continuous⟩ :
          C(orderNerveRealization (CylP a), orderNerveRealization (CylP a))) =
        ContinuousMap.id _ := by
    apply ContinuousMap.ext
    exact orderNerveRealizationMap_id (CylP a)
  have hone :
      (⟨orderNerveRealizationMap (cylCollapse a) (cylCollapse_monotone a),
        (orderNerveRealizationMap (cylCollapse a) (cylCollapse_monotone a)).hom.continuous⟩ :
          C(orderNerveRealization (CylP a), orderNerveRealization (CylP a))) =
      (cylinderRealizationInclusion a).comp (cylinderRealizationRetraction a) := by
    apply ContinuousMap.ext
    intro x
    exact (orderNerveRealizationMap_comp (cylRetr a) (cylRetr_monotone a)
      (cylIn a) (cylIn_monotone a) x).symm
  exact (hzero ▸ hone ▸ H₀.trans H₁)

def rankOneCylinderRealizationHomotopyEquiv :
    ContinuousMap.HomotopyEquiv (orderNerveRealization (CylP a)) (orderNerveRealization X) where
  toFun := cylinderRealizationRetraction a
  invFun := cylinderRealizationInclusion a
  left_inv := ⟨(rankOneCylinderRealizationDeformation a d hd hd₁).symm⟩
  right_inv := by rw [cylinderRealization_section]

end FiniteChains.Comb
