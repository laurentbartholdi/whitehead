import RequestProject.TopologicalSingular.SubdivisionSupport

namespace FiniteChains.SingularSubdivision
open TopologicalSingular
universe u v
variable {X : Type u} [TopologicalSpace X] {ι : Type v}

structure SmallRefinementStage (U : ι → Set X) (n : ℕ) where
  smallMap : Chain X n →ₗ[ℤ] Chain X n
  homotopyMap : Chain X n →ₗ[ℤ] Chain X (n + 1)
  small : ∀ c, smallMap c ∈ smallChains U n
  small_support : ∀ σ : Simplex X n,
    smallMap (Finsupp.single σ 1) ∈ subChains (Set.range σ) n
  homotopy_support : ∀ σ : Simplex X n,
    homotopyMap (Finsupp.single σ 1) ∈ subChains (Set.range σ) (n + 1)
  on_boundary : ∀ c : Chain X (n + 1),
    boundary n (homotopyMap (boundary n c)) = boundary n c - smallMap (boundary n c)

theorem all_zero_chains_small (U : ι → Set X) (hcover : ∀ x, ∃ i, x ∈ U i)
    (c : Chain X 0) : c ∈ smallChains U 0 := by
  induction c using Finsupp.induction_linear with
  | zero => exact Submodule.zero_mem _
  | add c d hc hd => exact Submodule.add_mem _ hc hd
  | single σ r =>
    obtain ⟨i, hi⟩ := hcover (σ (stdSimplex.vertex 0))
    apply single_mem_small U 0 σ r
    refine ⟨i, fun z => ?_⟩
    letI : Subsingleton (Domain 0) := inferInstanceAs (Subsingleton (stdSimplex ℝ (Fin 1)))
    rwa [show z = stdSimplex.vertex 0 from Subsingleton.elim _ _]

noncomputable def smallRefinementStageZero (U : ι → Set X) (hcover : ∀ x, ∃ i, x ∈ U i) :
    SmallRefinementStage U 0 where
  smallMap := LinearMap.id
  homotopyMap := 0
  small := all_zero_chains_small U hcover
  small_support σ := single_mem_range_subChains σ 1
  homotopy_support _ := Submodule.zero_mem _
  on_boundary _ := by simp

/-- Correct the boundary first, then subdivide. The correction and homotopy stay
inside the image of the original simplex. -/
theorem smallRefinementStep_exists (U : ι → Set X) (hU : ∀ i, IsOpen (U i))
    (hcover : ∀ x, ∃ i, x ∈ U i) {n : ℕ} (s : SmallRefinementStage U n)
    (σ : Simplex X (n + 1)) :
    ∃ d : Chain X (n + 1), ∃ h : Chain X (n + 2),
      d ∈ smallChains U (n + 1) ∧ d ∈ subChains (Set.range σ) (n + 1) ∧
      h ∈ subChains (Set.range σ) (n + 2) ∧
      boundary (n + 1) h = Finsupp.single σ 1 - d - s.homotopyMap (boundary n (Finsupp.single σ 1)) := by
  let c := Finsupp.single σ 1 - s.homotopyMap (boundary n (Finsupp.single σ 1))
  have hc : c ∈ subChains (Set.range σ) (n + 1) :=
    Submodule.sub_mem _ (single_mem_range_subChains σ 1)
      (carried_linearMap_mem_subChains s.homotopyMap s.homotopy_support _
        (boundary_mem_subChains _ n (single_mem_range_subChains σ 1)))
  have hbc : boundary n c = s.smallMap (boundary n (Finsupp.single σ 1)) := by
    dsimp only [c]
    rw [map_sub, s.on_boundary]
    abel
  have hsmallbc : boundary n c ∈ smallChains U n := by
    rw [hbc]
    exact s.small _
  obtain ⟨k, hk⟩ := exists_subdivision_small U hU hcover (n + 1) c
  refine ⟨((subdivide (n + 1))^[k]) c - iteratedHomotopy n k (boundary n c),
    -iteratedHomotopy (n + 1) k c,
    Submodule.sub_mem _ hk (iteratedHomotopy_mem_small U k n hsmallbc),
    Submodule.sub_mem _ (iterated_subdivide_mem_subChains _ k (n + 1) hc)
      (iteratedHomotopy_mem_subChains _ k n (boundary_mem_subChains _ n hc)),
    Submodule.neg_mem _ (iteratedHomotopy_mem_subChains _ k (n + 1) hc), ?_⟩
  have he := eq_sub_of_add_eq (iteratedHomotopy_identity_succ k n c)
  rw [map_neg, he]
  dsimp only [c]
  abel

end FiniteChains.SingularSubdivision
