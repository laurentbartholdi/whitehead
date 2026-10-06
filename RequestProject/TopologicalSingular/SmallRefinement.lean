module

public import RequestProject.TopologicalSingular.SmallRefinementStep

@[expose] public section

namespace FiniteChains.SingularSubdivision
open TopologicalSingular
universe u v
variable {X : Type u} [TopologicalSpace X] {ι : Type v}

noncomputable def smallRefinementNextMap (U : ι → Set X) (hU : ∀ i, IsOpen (U i))
    (hcover : ∀ x, ∃ i, x ∈ U i) {n : ℕ} (s : SmallRefinementStage U n) :
    Chain X (n + 1) →ₗ[ℤ] Chain X (n + 1) :=
  Finsupp.linearCombination ℤ (fun σ => (smallRefinementStep_exists U hU hcover s σ).choose)

noncomputable def smallRefinementNextHomotopy (U : ι → Set X) (hU : ∀ i, IsOpen (U i))
    (hcover : ∀ x, ∃ i, x ∈ U i) {n : ℕ} (s : SmallRefinementStage U n) :
    Chain X (n + 1) →ₗ[ℤ] Chain X (n + 2) :=
  Finsupp.linearCombination ℤ
    (fun σ => (smallRefinementStep_exists U hU hcover s σ).choose_spec.choose)

theorem smallRefinementNextHomotopy_identity (U : ι → Set X) (hU : ∀ i, IsOpen (U i))
    (hcover : ∀ x, ∃ i, x ∈ U i) {n : ℕ} (s : SmallRefinementStage U n)
    (c : Chain X (n + 1)) :
    boundary (n + 1) (smallRefinementNextHomotopy U hU hcover s c) =
      c - smallRefinementNextMap U hU hcover s c - s.homotopyMap (boundary n c) := by
  have he : (boundary (n + 1)).comp (smallRefinementNextHomotopy U hU hcover s) =
      LinearMap.id - smallRefinementNextMap U hU hcover s -
        s.homotopyMap.comp (boundary n) := by
    apply Finsupp.lhom_ext'
    intro σ
    apply LinearMap.ext_ring
    simp only [LinearMap.comp_apply, LinearMap.sub_apply, LinearMap.id_apply,
      smallRefinementNextHomotopy, smallRefinementNextMap,
      Finsupp.lsingle_apply, Finsupp.linearCombination_single, one_smul]
    exact (smallRefinementStep_exists U hU hcover s σ).choose_spec.choose_spec.2.2.2
  exact DFunLike.congr_fun he c

noncomputable def smallRefinementStageNext (U : ι → Set X) (hU : ∀ i, IsOpen (U i))
    (hcover : ∀ x, ∃ i, x ∈ U i) {n : ℕ} (s : SmallRefinementStage U n) :
    SmallRefinementStage U (n + 1) where
  smallMap := smallRefinementNextMap U hU hcover s
  homotopyMap := smallRefinementNextHomotopy U hU hcover s
  small c := by
    induction c using Finsupp.induction_linear with
    | zero => simp only [map_zero, Submodule.zero_mem]
    | add c d hc hd => simpa only [map_add] using Submodule.add_mem _ hc hd
    | single σ r =>
      dsimp only [smallRefinementNextMap]
      rw [Finsupp.linearCombination_single]
      exact Submodule.smul_mem _ r
        (smallRefinementStep_exists U hU hcover s σ).choose_spec.choose_spec.1
  small_support σ := by
    dsimp only [smallRefinementNextMap]
    rw [Finsupp.linearCombination_single, one_smul]
    exact (smallRefinementStep_exists U hU hcover s σ).choose_spec.choose_spec.2.1
  homotopy_support σ := by
    dsimp only [smallRefinementNextHomotopy]
    rw [Finsupp.linearCombination_single, one_smul]
    exact (smallRefinementStep_exists U hU hcover s σ).choose_spec.choose_spec.2.2.1
  on_boundary c := by
    rw [smallRefinementNextHomotopy_identity, boundary_boundary, map_zero, sub_zero]

noncomputable def smallRefinementStage (U : ι → Set X) (hU : ∀ i, IsOpen (U i))
    (hcover : ∀ x, ∃ i, x ∈ U i) : (n : ℕ) → SmallRefinementStage U n
  | 0 => smallRefinementStageZero U hcover
  | n + 1 => smallRefinementStageNext U hU hcover (smallRefinementStage U hU hcover n)

noncomputable def smallRefinement (U : ι → Set X) (hU : ∀ i, IsOpen (U i))
    (hcover : ∀ x, ∃ i, x ∈ U i) (n : ℕ) : Chain X n →ₗ[ℤ] Chain X n :=
  (smallRefinementStage U hU hcover n).smallMap

noncomputable def smallRefinementHomotopy (U : ι → Set X) (hU : ∀ i, IsOpen (U i))
    (hcover : ∀ x, ∃ i, x ∈ U i) (n : ℕ) : Chain X n →ₗ[ℤ] Chain X (n + 1) :=
  (smallRefinementStage U hU hcover n).homotopyMap

theorem smallRefinementHomotopy_identity (U : ι → Set X) (hU : ∀ i, IsOpen (U i))
    (hcover : ∀ x, ∃ i, x ∈ U i) (n : ℕ) (c : Chain X (n + 1)) :
    boundary (n + 1) (smallRefinementHomotopy U hU hcover (n + 1) c) =
      c - smallRefinement U hU hcover (n + 1) c -
        smallRefinementHomotopy U hU hcover n (boundary n c) :=
  smallRefinementNextHomotopy_identity U hU hcover (smallRefinementStage U hU hcover n) c

theorem smallRefinement_boundary (U : ι → Set X) (hU : ∀ i, IsOpen (U i))
    (hcover : ∀ x, ∃ i, x ∈ U i) (n : ℕ) (c : Chain X (n + 1)) :
    boundary n (smallRefinement U hU hcover (n + 1) c) =
      smallRefinement U hU hcover n (boundary n c) := by
  have he := congrArg (boundary n) (smallRefinementHomotopy_identity U hU hcover n c)
  rw [boundary_boundary, map_sub, map_sub, smallRefinementHomotopy,
    (smallRefinementStage U hU hcover n).on_boundary] at he
  change 0 = boundary n c - boundary n (smallRefinement U hU hcover (n + 1) c) -
    (boundary n c - smallRefinement U hU hcover n (boundary n c)) at he
  linear_combination (norm := abel) he

theorem smallRefinement_mem_small (U : ι → Set X) (hU : ∀ i, IsOpen (U i))
    (hcover : ∀ x, ∃ i, x ∈ U i) (n : ℕ) (c : Chain X n) :
    smallRefinement U hU hcover n c ∈ smallChains U n :=
  (smallRefinementStage U hU hcover n).small c

/-- Refinement preserves every subspace, even though the subdivision count may
depend on the individual simplex. -/
theorem smallRefinement_support (U : ι → Set X) (hU : ∀ i, IsOpen (U i))
    (hcover : ∀ x, ∃ i, x ∈ U i) (n : ℕ) (A : Set X) {c : Chain X n}
    (hc : c ∈ subChains A n) : smallRefinement U hU hcover n c ∈ subChains A n :=
  carried_linearMap_mem_subChains _ (smallRefinementStage U hU hcover n).small_support A hc

theorem smallRefinementHomotopy_support (U : ι → Set X) (hU : ∀ i, IsOpen (U i))
    (hcover : ∀ x, ∃ i, x ∈ U i) (n : ℕ) (A : Set X) {c : Chain X n}
    (hc : c ∈ subChains A n) :
    smallRefinementHomotopy U hU hcover n c ∈ subChains A (n + 1) :=
  carried_linearMap_mem_subChains _ (smallRefinementStage U hU hcover n).homotopy_support A hc

end FiniteChains.SingularSubdivision
