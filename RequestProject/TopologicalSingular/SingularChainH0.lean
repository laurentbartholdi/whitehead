/- Adapted from the local 2026-09-11 Lean audit; see PROVENANCE.json. -/

import RequestProject.TopologicalSingular.SingularChainMaps

/-! # Exactness of the augmented singular complex in degree zero

Paths give actual singular one-simplices. A chosen path from the root to
each point constructs the required bounding chain explicitly.
-/


namespace FiniteChains.TopologicalSingular

open Set Topology

universe u

variable {X : Type u} [TopologicalSpace X]

def pathSimplex {a b : X} (γ : Path a b) : Simplex X 1 :=
  ⟨fun z => γ (stdSimplexHomeomorphUnitInterval z),
    γ.continuous.comp stdSimplexHomeomorphUnitInterval.continuous⟩

@[simp] theorem face_pathSimplex_zero {a b : X} (γ : Path a b) :
    face (0 : Fin 2) (pathSimplex γ) = ContinuousMap.const _ b := by
  letI : Subsingleton (Domain 0) := inferInstanceAs (Subsingleton (stdSimplex ℝ (Fin 1)))
  ext z
  rw [show z = stdSimplex.vertex 0 from Subsingleton.elim _ _]
  rw [face_apply, stdSimplex.map_vertex]
  exact γ.target

@[simp] theorem face_pathSimplex_one {a b : X} (γ : Path a b) :
    face (1 : Fin 2) (pathSimplex γ) = ContinuousMap.const _ a := by
  letI : Subsingleton (Domain 0) := inferInstanceAs (Subsingleton (stdSimplex ℝ (Fin 1)))
  ext z
  rw [show z = stdSimplex.vertex 0 from Subsingleton.elim _ _]
  rw [face_apply, stdSimplex.map_vertex]
  exact γ.source

theorem boundary_pathSimplex {a b : X} (γ : Path a b) (r : ℤ) :
    boundary 0 (Finsupp.single (pathSimplex γ) r) =
      Finsupp.single (ContinuousMap.const _ b) r - Finsupp.single (ContinuousMap.const _ a) r := by
  rw [boundary_single]
  rw [Fin.sum_univ_two]
  change (1 : ℤ) • Finsupp.single (face 0 (pathSimplex γ)) r +
    (-1 : ℤ) • Finsupp.single (face 1 (pathSimplex γ)) r = _
  rw [one_smul, neg_smul, one_smul, face_pathSimplex_zero, face_pathSimplex_one, sub_eq_add_neg]

noncomputable def pathCone [PathConnectedSpace X] (root : X) : Chain X 0 →ₗ[ℤ] Chain X 1 :=
  Finsupp.linearCombination ℤ (fun σ : Simplex X 0 =>
    Finsupp.single (pathSimplex (PathConnectedSpace.somePath root (zeroSimplexEquiv σ))) 1)

theorem pathCone_single [PathConnectedSpace X] (root : X) (σ : Simplex X 0) (a : ℤ) :
    pathCone root (Finsupp.single σ a) =
      Finsupp.single (pathSimplex (PathConnectedSpace.somePath root (zeroSimplexEquiv σ))) a := by
  rw [pathCone, Finsupp.linearCombination_single, Finsupp.smul_single]
  simp only [smul_eq_mul, mul_one]

theorem boundary_pathCone [PathConnectedSpace X] (root : X) (c : Chain X 0) :
    boundary 0 (pathCone root c) = c - augmentation c • Finsupp.single (ContinuousMap.const _ root) 1 := by
  have he : (boundary 0).comp (pathCone root) = LinearMap.id -
      augmentation.smulRight (Finsupp.single (ContinuousMap.const _ root) 1) := by
    apply Finsupp.lhom_ext
    intro σ a
    simp only [LinearMap.comp_apply, pathCone_single, boundary_pathSimplex, LinearMap.sub_apply,
      LinearMap.id_apply, LinearMap.smulRight_apply, augmentation_single, Finsupp.smul_single,
      smul_eq_mul, mul_one]
    rw [show ContinuousMap.const (Domain 0) (zeroSimplexEquiv σ) = σ from zeroSimplexEquiv.symm_apply_apply σ]
  exact DFunLike.congr_fun he c

theorem ker_augmentation_eq_range_boundary [PathConnectedSpace X] :
    LinearMap.ker (augmentation (X := X)) = LinearMap.range (boundary 0) := by
  apply le_antisymm
  · intro c hc
    let root : X := Classical.arbitrary X
    refine ⟨pathCone root c, ?_⟩
    rw [boundary_pathCone, show augmentation c = 0 from hc, zero_smul, sub_zero]
  · rintro c ⟨d, rfl⟩
    exact augmentation_boundary d

end FiniteChains.TopologicalSingular
