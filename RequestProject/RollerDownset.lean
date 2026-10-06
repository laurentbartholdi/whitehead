import RequestProject.RollerGraphMetric

/-!
# Down-sets of a poset of width at most three form a median graph

This file provides the standard supply of (in general infinite) cube complexes to which the
results of `RequestProject/RollerGraphMetric.lean` apply, with **medianness as a conclusion**
rather than as a hypothesis, and with no finiteness or local finiteness assumption.

Let `ι` be a partially ordered set of *width at most three*: every antichain has at most three
elements.  Consider the finite down-sets of `ι` (`FiniteChains.IsDownset`), each viewed as the
set of hyperplanes separating a vertex from the base vertex.  Then:

* the finite down-sets contain `∅` and are closed under the majority operation;
* a vertex has at most three descending neighbours, one for each maximal element;
* from any down-set one can step towards any other by adding a minimal missing element or
  deleting a maximal superfluous one.

Hence `FiniteChains.downsetModel` is a `FiniteChains.GatedRollerModel`, so by
`RequestProject/RollerGraphMetric.lean` its graph — where two down-sets are adjacent when they
differ in one element — is connected, its distance is the number of separating elements, it is
a median graph in the graph-theoretic sense, and `ker d₂ = im d₃` holds for its cellular
chains (`FiniteChains.downsetModel_ker_d₂_eq_range_d₃`).

The example `FiniteChains.chainPoset` (three disjoint copies of `ℕ`) shows that the hypotheses
are satisfied by infinite three-dimensional complexes: the down-sets of three disjoint chains
are the vertices of the cubulated positive octant.
-/

namespace FiniteChains

open RollerBridge

universe u

variable {ι : Type u} [DecidableEq ι] [PartialOrder ι]

/-- A finite set is a *down-set* when it contains every element below one of its elements. -/
def IsDownset (A : Finset ι) : Prop := ∀ p ∈ A, ∀ q : ι, q ≤ p → q ∈ A

omit [DecidableEq ι] in
theorem isDownset_empty : IsDownset (∅ : Finset ι) := by
  intro p hp
  simp at hp

theorem isDownset_medFinset {A B C : Finset ι} (hA : IsDownset A) (hB : IsDownset B)
    (hC : IsDownset C) : IsDownset (medFinset A B C) := by
  intro p hp q hq
  simp only [medFinset, Finset.mem_union, Finset.mem_inter] at hp ⊢
  rcases hp with (⟨h1, h2⟩ | ⟨h1, h2⟩) | ⟨h1, h2⟩
  · exact Or.inl (Or.inl ⟨hA p h1 q hq, hB p h2 q hq⟩)
  · exact Or.inl (Or.inr ⟨hB p h1 q hq, hC p h2 q hq⟩)
  · exact Or.inr ⟨hA p h1 q hq, hC p h2 q hq⟩

/-- Deleting a maximal element of a down-set leaves a down-set. -/
theorem isDownset_erase {A : Finset ι} (hA : IsDownset A) {p : ι}
    (hmax : ∀ q ∈ A, ¬ p < q) : IsDownset (A.erase p) := by
  intro x hx q hq
  rw [Finset.mem_erase] at hx ⊢
  refine ⟨?_, hA x hx.2 q hq⟩
  rintro rfl
  exact hmax x hx.2 (lt_of_le_of_ne hq (Ne.symm hx.1))

omit [PartialOrder ι] in
/-- The number of separating elements between a finite set and the set obtained by deleting a
member is one. -/
theorem dsym_erase {A : Finset ι} {p : ι} (hp : p ∈ A) : dsym A (A.erase p) = 1 := by
  have h1 : A \ A.erase p = {p} := by
    ext x
    simp only [Finset.mem_sdiff, Finset.mem_erase, Finset.mem_singleton, not_and]
    by_cases hxp : x = p <;> simp [hxp, hp]
  have h2 : A.erase p \ A = ∅ :=
    Finset.sdiff_eq_empty_iff_subset.2 (Finset.erase_subset _ _)
  simp [dsym, h1, h2]

omit [PartialOrder ι] in
/-- The number of separating elements between a finite set and the set obtained by inserting a
new element is one. -/
theorem dsym_insert {A : Finset ι} {p : ι} (hp : p ∉ A) : dsym A (insert p A) = 1 := by
  have h1 : A \ insert p A = ∅ :=
    Finset.sdiff_eq_empty_iff_subset.2 (Finset.subset_insert _ _)
  have h2 : insert p A \ A = {p} := by
    ext x
    simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton]
    by_cases hxp : x = p <;> simp [hxp, hp]
  simp [dsym, h1, h2]

/-- **The step towards another vertex.**  Given two distinct finite down-sets, one can change a
single element of the first and get one step closer to the second. -/
theorem exists_step_downset {A B : Finset ι} (hA : IsDownset A) (hB : IsDownset B)
    (hne : A ≠ B) : ∃ C : Finset ι, IsDownset C ∧ dsym A C = 1 ∧ dsym C B + 1 = dsym A B := by
  by_cases hAB : (A \ B).Nonempty
  · -- delete a maximal element of `A \ B`
    obtain ⟨p, hpmax⟩ := Finset.exists_maximal hAB
    have hp := Finset.mem_sdiff.1 hpmax.1
    have hmax : ∀ q ∈ A, ¬ p < q := by
      intro q hq hlt
      by_cases hqB : q ∈ B
      · exact hp.2 (hB q hqB p hlt.le)
      · have := hpmax.2 (Finset.mem_sdiff.2 ⟨hq, hqB⟩) hlt.le
        exact absurd (le_antisymm hlt.le this) (ne_of_lt hlt)
    refine ⟨A.erase p, isDownset_erase hA hmax, dsym_erase hp.1, ?_⟩
    have e1 : A.erase p \ B = (A \ B).erase p := by
      ext x
      simp only [Finset.mem_sdiff, Finset.mem_erase]
      tauto
    have e2 : B \ A.erase p = B \ A := by
      ext x
      simp only [Finset.mem_sdiff, Finset.mem_erase, not_and]
      by_cases hxp : x = p
      · subst hxp
        simp [hp.2]
      · simp [hxp]
    have hcard : ((A \ B).erase p).card + 1 = (A \ B).card :=
      Finset.card_erase_add_one (Finset.mem_sdiff.2 ⟨hp.1, hp.2⟩)
    simp only [dsym, e1, e2]
    omega
  · -- add a minimal element of `B \ A`
    have hsub : A ⊆ B := by
      intro x hx
      by_contra hxB
      exact hAB ⟨x, Finset.mem_sdiff.2 ⟨hx, hxB⟩⟩
    have hBA : (B \ A).Nonempty := by
      rcases Finset.eq_empty_or_nonempty (B \ A) with h | h
      · exact absurd (Finset.Subset.antisymm hsub (by
          intro x hx
          by_contra hxA
          have : x ∈ B \ A := Finset.mem_sdiff.2 ⟨hx, hxA⟩
          rw [h] at this
          simp at this)) hne
      · exact h
    obtain ⟨p, hpmin⟩ := Finset.exists_minimal hBA
    have hp := Finset.mem_sdiff.1 hpmin.1
    have hdown : IsDownset (insert p A) := by
      intro x hx q hq
      rw [Finset.mem_insert] at hx ⊢
      rcases hx with rfl | hx
      · rcases eq_or_lt_of_le hq with rfl | hlt
        · exact Or.inl rfl
        · have hqB : q ∈ B := hB x hp.1 q hq
          by_cases hqA : q ∈ A
          · exact Or.inr hqA
          · have := hpmin.2 (Finset.mem_sdiff.2 ⟨hqB, hqA⟩) hlt.le
            exact absurd (le_antisymm this hlt.le) (Ne.symm (ne_of_lt hlt))
      · exact Or.inr (hA x hx q hq)
    refine ⟨insert p A, hdown, dsym_insert hp.2, ?_⟩
    have e1 : insert p A \ B = A \ B := by
      ext x
      simp only [Finset.mem_sdiff, Finset.mem_insert]
      constructor
      · rintro ⟨rfl | hx, hxB⟩
        · exact absurd hp.1 hxB
        · exact ⟨hx, hxB⟩
      · rintro ⟨hx, hxB⟩
        exact ⟨Or.inr hx, hxB⟩
    have e2 : B \ insert p A = (B \ A).erase p := by
      ext x
      simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_erase, not_or]
      tauto
    have hcard : ((B \ A).erase p).card + 1 = (B \ A).card :=
      Finset.card_erase_add_one (Finset.mem_sdiff.2 ⟨hp.1, hp.2⟩)
    simp only [dsym, e1, e2]
    omega

/-- **Down-sets of a poset of width at most three form a gated Roller model.**  The width
hypothesis is the statement that the complex is at most three dimensional. -/
noncomputable def downsetModel
    (hw : ∀ s : Finset ι, (∀ p ∈ s, ∀ q ∈ s, p ≠ q → ¬ p ≤ q) → s.card ≤ 3) :
    GatedRollerModel ι where
  W := {A : Finset ι | IsDownset A}
  base_mem := isDownset_empty
  med_mem := fun hA hB hC => isDownset_medFinset hA hB hC
  dim_le := by
    intro A hA s hs
    classical
    -- each descending neighbour is `A.erase p` for a maximal element `p` of `A`
    have hchoice : ∀ B ∈ s, ∃ p ∈ A, B = A.erase p ∧ ∀ q ∈ A, ¬ p < q := by
      intro B hB
      obtain ⟨hBW, hBA, hcard⟩ := hs B hB
      have hstrict : B ⊂ A := ⟨hBA, fun h => by
        have := Finset.card_le_card h
        omega⟩
      obtain ⟨p, hpA, hpB⟩ := Finset.exists_of_ssubset hstrict
      have hBe : B = A.erase p := by
        refine Finset.eq_of_subset_of_card_le (fun x hx => ?_) ?_
        · exact Finset.mem_erase.2 ⟨fun h => hpB (h ▸ hx), hBA hx⟩
        · rw [Finset.card_erase_of_mem hpA]
          omega
      refine ⟨p, hpA, hBe, ?_⟩
      intro q hq hlt
      have : q ∈ B := by
        have hqe : q ∈ A.erase p := Finset.mem_erase.2 ⟨fun h => absurd (h ▸ hlt) (lt_irrefl q), hq⟩
        rwa [← hBe] at hqe
      have hpB' : p ∈ B := hBW q this p hlt.le
      exact hpB hpB'
    choose f hfA hfe hfmax using hchoice
    have hinj : Function.Injective (fun B : {x // x ∈ s} => f B.1 B.2) := by
      intro B B' h
      simp only at h
      refine Subtype.ext ?_
      rw [hfe B.1 B.2, hfe B'.1 B'.2, h]
    have hanti : ∀ p ∈ s.attach.image (fun B => f B.1 B.2),
        ∀ q ∈ s.attach.image (fun B => f B.1 B.2), p ≠ q → ¬ p ≤ q := by
      intro p hp q hq hpq hle
      simp only [Finset.mem_image, Finset.mem_attach, true_and] at hp hq
      obtain ⟨B, rfl⟩ := hp
      obtain ⟨B', rfl⟩ := hq
      exact hfmax B.1 B.2 _ (hfA B'.1 B'.2) (lt_of_le_of_ne hle hpq)
    have hcard : (s.attach.image (fun B => f B.1 B.2)).card = s.card := by
      rw [Finset.card_image_of_injective _ hinj, Finset.card_attach]
    rw [← hcard]
    exact hw _ hanti
  step := by
    intro A B hA hB hne
    obtain ⟨C, hC, h1, h2⟩ := exists_step_downset hA hB hne
    exact ⟨C, hC, h1, h2⟩

/-- **Every two-cycle bounds** in the cellular chain complex of the cube complex of finite
down-sets of a poset of width at most three. -/
theorem downsetModel_ker_d₂_eq_range_d₃
    (hw : ∀ s : Finset ι, (∀ p ∈ s, ∀ q ∈ s, p ≠ q → ¬ p ≤ q) → s.card ≤ 3) :
    LinearMap.ker (((downsetModel hw).toMedianSimpleGraph).toDescCubeStr).d₂ =
      LinearMap.range (((downsetModel hw).toMedianSimpleGraph).toDescCubeStr).d₃ :=
  (downsetModel hw).ker_d₂_eq_range_d₃

/-! ### An infinite three-dimensional example: three disjoint chains -/

/-- Three disjoint copies of `ℕ`: the poset whose finite down-sets are the vertices of the
cubulated positive octant. -/
structure ChainPoset where
  /-- Which of the three chains the element lies on. -/
  idx : Fin 3
  /-- The position along that chain. -/
  lvl : ℕ
deriving DecidableEq

instance : PartialOrder ChainPoset where
  le x y := x.idx = y.idx ∧ x.lvl ≤ y.lvl
  le_refl _ := ⟨rfl, le_refl _⟩
  le_trans _ _ _ h₁ h₂ := ⟨h₁.1.trans h₂.1, h₁.2.trans h₂.2⟩
  le_antisymm x y h₁ h₂ := by
    cases x
    cases y
    simp only [ChainPoset.mk.injEq]
    exact ⟨h₁.1, le_antisymm h₁.2 h₂.2⟩

/-- Three disjoint chains have width three: an antichain contains at most one element of each
chain. -/
theorem chainPoset_width (s : Finset ChainPoset)
    (h : ∀ p ∈ s, ∀ q ∈ s, p ≠ q → ¬ p ≤ q) : s.card ≤ 3 := by
  classical
  have hinj : Set.InjOn (fun p : ChainPoset => p.idx) s := by
    intro p hp q hq hfst
    by_contra hpq
    rcases le_total p.lvl q.lvl with hle | hle
    · exact h p hp q hq hpq ⟨hfst, hle⟩
    · exact h q hq p hp (Ne.symm hpq) ⟨hfst.symm, hle⟩
  have hcard := Finset.card_image_of_injOn hinj
  have hle : (s.image (fun p : ChainPoset => p.idx)).card ≤ (Finset.univ : Finset (Fin 3)).card :=
    Finset.card_le_card (Finset.subset_univ _)
  simp only [Finset.card_univ, Fintype.card_fin] at hle
  omega

/-- The cubulated positive octant: the finite down-sets of three disjoint chains form an
infinite three-dimensional cube complex whose one-skeleton is a median graph, and every
two-cycle of its cellular chain complex bounds. -/
theorem octantDownset_ker_d₂_eq_range_d₃ :
    LinearMap.ker (((downsetModel chainPoset_width).toMedianSimpleGraph).toDescCubeStr).d₂ =
      LinearMap.range (((downsetModel chainPoset_width).toMedianSimpleGraph).toDescCubeStr).d₃ :=
  downsetModel_ker_d₂_eq_range_d₃ chainPoset_width

end FiniteChains
