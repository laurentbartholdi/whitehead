import RequestProject.CubeRollerModel
import RequestProject.CubeMedianGraph

/-!
# The Roller model is a median graph

`RequestProject/CubeRollerModel.lean` and `RequestProject/CubeMedianGraph.lean` derive the
descending-cube axioms from the two standard combinatorial descriptions of a CAT(0) cube
complex.  This file relates the two descriptions: the vertex set of a Roller model, with the
distance «number of hyperplanes separating two vertices» and the majority operation, *is* a
median graph (`FiniteChains.RollerModel.toMedianGraph`).  In particular the median-graph
axioms are satisfied by a large family of complexes, and the median-graph theorem subsumes
the Roller one.

The combinatorial content is elementary but worth recording:

* `FiniteChains.RollerBridge.dsym_med` — the majority set lies on a geodesic between each pair
  of the three arguments;
* `FiniteChains.RollerBridge.between_of_dsym` — conversely, a vertex on a geodesic from `A` to
  `B` satisfies `A ∩ B ⊆ Z ⊆ A ∪ B`;
* `FiniteChains.RollerBridge.eq_med_of_between` — a vertex between each pair of `A`, `B`, `C`
  is the majority set, so the median is unique.
-/

namespace FiniteChains

universe u

namespace RollerBridge

variable {ι : Type u} [DecidableEq ι]

/-- The number of hyperplanes separating two vertices. -/
def dsym (A B : Finset ι) : ℕ := (A \ B).card + (B \ A).card

@[simp] theorem dsym_self (A : Finset ι) : dsym A A = 0 := by simp [dsym]

theorem dsym_comm (A B : Finset ι) : dsym A B = dsym B A := by
  simp only [dsym]; omega

theorem dsym_empty (A : Finset ι) : dsym ∅ A = A.card := by simp [dsym]

theorem eq_of_dsym_eq_zero {A B : Finset ι} (h : dsym A B = 0) : A = B := by
  simp only [dsym] at h
  have h1 : A \ B = ∅ := Finset.card_eq_zero.1 (by omega)
  have h2 : B \ A = ∅ := Finset.card_eq_zero.1 (by omega)
  apply Finset.Subset.antisymm
  · exact Finset.sdiff_eq_empty_iff_subset.1 h1
  · exact Finset.sdiff_eq_empty_iff_subset.1 h2

theorem dsym_triangle (A B C : Finset ι) : dsym A C ≤ dsym A B + dsym B C := by
  have s1 : A \ C ⊆ (A \ B) ∪ (B \ C) := by
    intro x hx
    simp only [Finset.mem_sdiff, Finset.mem_union] at hx ⊢
    by_cases hb : x ∈ B
    · exact Or.inr ⟨hb, hx.2⟩
    · exact Or.inl ⟨hx.1, hb⟩
  have s2 : C \ A ⊆ (C \ B) ∪ (B \ A) := by
    intro x hx
    simp only [Finset.mem_sdiff, Finset.mem_union] at hx ⊢
    by_cases hb : x ∈ B
    · exact Or.inr ⟨hb, hx.2⟩
    · exact Or.inl ⟨hx.1, hb⟩
  have c1 := (Finset.card_le_card s1).trans (Finset.card_union_le (A \ B) (B \ C))
  have c2 := (Finset.card_le_card s2).trans (Finset.card_union_le (C \ B) (B \ A))
  simp only [dsym]
  omega

/-- The majority set lies on a geodesic between its first two arguments. -/
theorem dsym_med (A B C : Finset ι) :
    dsym A (medFinset A B C) + dsym (medFinset A B C) B = dsym A B := by
  have h1 : (A \ medFinset A B C) ∪ (medFinset A B C \ B) = A \ B := by
    ext x
    simp only [medFinset, Finset.mem_union, Finset.mem_sdiff, Finset.mem_inter]
    tauto
  have h2 : (medFinset A B C \ A) ∪ (B \ medFinset A B C) = B \ A := by
    ext x
    simp only [medFinset, Finset.mem_union, Finset.mem_sdiff, Finset.mem_inter]
    tauto
  have d1 : Disjoint (A \ medFinset A B C) (medFinset A B C \ B) := by
    refine Finset.disjoint_left.2 ?_
    intro x hx hx'
    simp only [Finset.mem_sdiff] at hx hx'
    exact hx.2 hx'.1
  have d2 : Disjoint (medFinset A B C \ A) (B \ medFinset A B C) := by
    refine Finset.disjoint_left.2 ?_
    intro x hx hx'
    simp only [Finset.mem_sdiff] at hx hx'
    exact hx'.2 hx.1
  have c1 : (A \ medFinset A B C).card + (medFinset A B C \ B).card = (A \ B).card := by
    rw [← h1, Finset.card_union_of_disjoint d1]
  have c2 : (medFinset A B C \ A).card + (B \ medFinset A B C).card = (B \ A).card := by
    rw [← h2, Finset.card_union_of_disjoint d2]
  simp only [dsym]
  omega

theorem medFinset_comm₁₂ (A B C : Finset ι) : medFinset A B C = medFinset B A C := by
  ext x
  simp only [medFinset, Finset.mem_union, Finset.mem_inter]
  tauto

theorem medFinset_comm₂₃ (A B C : Finset ι) : medFinset A B C = medFinset A C B := by
  ext x
  simp only [medFinset, Finset.mem_union, Finset.mem_inter]
  tauto

/-- A vertex on a geodesic from `A` to `B` lies between them. -/
theorem between_of_dsym {A B Z : Finset ι} (h : dsym A Z + dsym Z B = dsym A B) :
    A ∩ B ⊆ Z ∧ Z ⊆ A ∪ B := by
  have s1 : A \ B ⊆ (A \ Z) ∪ (Z \ B) := by
    intro x hx
    simp only [Finset.mem_sdiff, Finset.mem_union] at hx ⊢
    by_cases hz : x ∈ Z
    · exact Or.inr ⟨hz, hx.2⟩
    · exact Or.inl ⟨hx.1, hz⟩
  have s2 : B \ A ⊆ (B \ Z) ∪ (Z \ A) := by
    intro x hx
    simp only [Finset.mem_sdiff, Finset.mem_union] at hx ⊢
    by_cases hz : x ∈ Z
    · exact Or.inr ⟨hz, hx.2⟩
    · exact Or.inl ⟨hx.1, hz⟩
  have c1 := Finset.card_union_le (A \ Z) (Z \ B)
  have c2 := Finset.card_union_le (B \ Z) (Z \ A)
  have k1 := Finset.card_le_card s1
  have k2 := Finset.card_le_card s2
  simp only [dsym] at h
  have u1 : A \ B = (A \ Z) ∪ (Z \ B) := Finset.eq_of_subset_of_card_le s1 (by omega)
  have u2 : B \ A = (B \ Z) ∪ (Z \ A) := Finset.eq_of_subset_of_card_le s2 (by omega)
  have hAZ : A \ Z ⊆ A \ B := by rw [u1]; exact Finset.subset_union_left
  have hZA : Z \ A ⊆ B \ A := by rw [u2]; exact Finset.subset_union_right
  constructor
  · intro x hx
    simp only [Finset.mem_inter] at hx
    by_contra hz
    have : x ∈ A \ B := hAZ (Finset.mem_sdiff.2 ⟨hx.1, hz⟩)
    exact (Finset.mem_sdiff.1 this).2 hx.2
  · intro x hx
    simp only [Finset.mem_union]
    by_cases ha : x ∈ A
    · exact Or.inl ha
    · have : x ∈ B \ A := hZA (Finset.mem_sdiff.2 ⟨hx, ha⟩)
      exact Or.inr (Finset.mem_sdiff.1 this).1

/-- A vertex lying between each pair of `A`, `B`, `C` is their majority set. -/
theorem eq_med_of_between {A B C Z : Finset ι}
    (h₁ : A ∩ B ⊆ Z) (h₁' : Z ⊆ A ∪ B) (h₂ : B ∩ C ⊆ Z) (h₂' : Z ⊆ B ∪ C)
    (h₃ : A ∩ C ⊆ Z) (h₃' : Z ⊆ A ∪ C) : Z = medFinset A B C := by
  ext x
  constructor
  · intro hx
    have m1 := Finset.mem_union.1 (h₁' hx)
    have m2 := Finset.mem_union.1 (h₂' hx)
    have m3 := Finset.mem_union.1 (h₃' hx)
    simp only [medFinset, Finset.mem_union, Finset.mem_inter]
    tauto
  · intro hx
    simp only [medFinset, Finset.mem_union, Finset.mem_inter] at hx
    rcases hx with (⟨ha, hb⟩ | ⟨hb, hc⟩) | ⟨ha, hc⟩
    · exact h₁ (Finset.mem_inter.2 ⟨ha, hb⟩)
    · exact h₂ (Finset.mem_inter.2 ⟨hb, hc⟩)
    · exact h₃ (Finset.mem_inter.2 ⟨ha, hc⟩)

end RollerBridge

namespace RollerModel

open RollerBridge

variable {ι : Type u} [DecidableEq ι] (M : RollerModel ι)

/-- **The vertex set of a Roller model is a median graph**, with the distance counting the
hyperplanes separating two vertices and with the majority operation as median. -/
def toMedianGraph : MedianGraph M.Vtx where
  dist u v := dsym u.1 v.1
  base := ⟨∅, M.base_mem⟩
  dist_self := fun x => dsym_self x.1
  eq_of_dist_eq_zero := fun h => Subtype.ext (eq_of_dsym_eq_zero h)
  dist_comm := fun x y => dsym_comm x.1 y.1
  dist_triangle := fun x y z => dsym_triangle x.1 y.1 z.1
  med := fun a b c => ⟨medFinset a.1 b.1 c.1, M.med_mem a.2 b.2 c.2⟩
  med_ab := fun a b c => dsym_med a.1 b.1 c.1
  med_bc := fun a b c => by
    have h := dsym_med b.1 c.1 a.1
    rwa [show medFinset b.1 c.1 a.1 = medFinset a.1 b.1 c.1 by
      rw [medFinset_comm₂₃, medFinset_comm₁₂, medFinset_comm₂₃]] at h
  med_ac := fun a b c => by
    have h := dsym_med a.1 c.1 b.1
    rwa [← medFinset_comm₂₃] at h
  med_unique := by
    intro a b c z h₁ h₂ h₃
    obtain ⟨k₁, k₁'⟩ := between_of_dsym h₁
    obtain ⟨k₂, k₂'⟩ := between_of_dsym h₂
    obtain ⟨k₃, k₃'⟩ := between_of_dsym h₃
    exact Subtype.ext (eq_med_of_between k₁ k₁' k₂ k₂' k₃ k₃')
  dim_le := by
    intro w s hs
    have hinj : Set.InjOn (fun v : M.Vtx => v.1) s := fun x _ y _ h => Subtype.ext h
    have hcard : (s.image (fun v : M.Vtx => v.1)).card = s.card :=
      Finset.card_image_of_injOn hinj
    rw [← hcard]
    refine M.dim_le w.1 w.2 _ ?_
    intro B hB
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.1 hB
    obtain ⟨hd, hh⟩ := hs v hv
    have hd' : (v.1 \ w.1).card + (w.1 \ v.1).card = 1 := hd
    have hh0 : dsym (∅ : Finset ι) v.1 + 1 = dsym (∅ : Finset ι) w.1 := hh
    rw [dsym_empty, dsym_empty] at hh0
    have i1 := Finset.card_sdiff_add_card_inter v.1 w.1
    have i2 := Finset.card_sdiff_add_card_inter w.1 v.1
    have i3 : (v.1 ∩ w.1).card = (w.1 ∩ v.1).card := by rw [Finset.inter_comm]
    have hsub : v.1 ⊆ w.1 := by
      have hzero : (v.1 \ w.1).card = 0 := by omega
      exact Finset.sdiff_eq_empty_iff_subset.1 (Finset.card_eq_zero.1 hzero)
    exact ⟨v.2, hsub, hh0⟩

end RollerModel

end FiniteChains
