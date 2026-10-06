/- Adapted from the local 2026-09-11 Lean audit; see PROVENANCE.json. -/

import RequestProject.TopologicalSingular.SingularSubdivisionModels

/-! # Barycentric subdivision of actual singular chains

The universal affine chains are pushed forward by each continuous
singular simplex. The operator commutes with boundary and is naturally
chain homotopic to the identity. No mesh or excision conclusion is assumed.
-/


set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains.SingularSubdivision

open TopologicalSingular AffineVertexChains

universe u v
variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]

noncomputable def fromModel {k l : ℕ} (m : Chain (Domain k) l) : Chain X k →ₗ[ℤ] Chain X l :=
  Finsupp.linearCombination ℤ (fun σ : Simplex X k => TopologicalSingular.map σ l m)

theorem fromModel_single {k l : ℕ} (m : Chain (Domain k) l) (σ : Simplex X k) (r : ℤ) :
    fromModel m (Finsupp.single σ r) = r • TopologicalSingular.map σ l m :=
  Finsupp.linearCombination_single ℤ r σ

theorem fromModel_naturality {k l : ℕ} (m : Chain (Domain k) l) (f : C(X, Y)) (c : Chain X k) :
    TopologicalSingular.map f l (fromModel m c) = fromModel m (TopologicalSingular.map f k c) := by
  have he : (TopologicalSingular.map f l).comp (fromModel m) =
      (fromModel m).comp (TopologicalSingular.map f k) := by
    apply VertexChains.linearMap_ext_basis
    intro σ
    simp only [LinearMap.comp_apply, fromModel_single, one_smul, map_single]
    exact (DFunLike.congr_fun (map_comp σ f l) m).symm
  exact DFunLike.congr_fun he c

noncomputable def subdivide (n : ℕ) : Chain X n →ₗ[ℤ] Chain X n := fromModel (model n)

noncomputable def homotopy (n : ℕ) : Chain X n →ₗ[ℤ] Chain X (n + 1) := fromModel (homotopyModel n)

theorem subdivide_single (n : ℕ) (σ : Simplex X n) (r : ℤ) :
    subdivide n (Finsupp.single σ r) = r • TopologicalSingular.map σ n (model n) := fromModel_single _ _ _

theorem homotopy_single (n : ℕ) (σ : Simplex X n) (r : ℤ) :
    homotopy n (Finsupp.single σ r) = r • TopologicalSingular.map σ (n + 1) (homotopyModel n) :=
  fromModel_single _ _ _

theorem subdivide_zero (c : Chain X 0) : subdivide 0 c = c := by
  have he : subdivide (X := X) 0 = LinearMap.id := by
    apply VertexChains.linearMap_ext_basis
    intro σ
    rw [subdivide_single, one_smul, model_zero, map_single]
    rfl
  exact DFunLike.congr_fun he c

theorem homotopy_zero (c : Chain X 0) : homotopy 0 c = 0 := by
  have he : homotopy (X := X) 0 = 0 := by
    apply VertexChains.linearMap_ext_basis
    intro σ
    simp only [homotopy_single, homotopyModel_zero, map_zero, smul_zero, LinearMap.zero_apply]
  exact DFunLike.congr_fun he c

theorem push_face {n k : ℕ} (σ : Simplex X (n + 1)) (i : Fin (n + 2)) (c : Chain (Domain n) k) :
    TopologicalSingular.map σ k (TopologicalSingular.map (standardMap i.succAbove) k c) =
      TopologicalSingular.map (face i σ) k c :=
  (DFunLike.congr_fun (map_comp (standardMap i.succAbove) σ k) c).symm

theorem subdivide_boundary (n : ℕ) (c : Chain X (n + 1)) :
    subdivide n (boundary n c) = boundary n (subdivide (n + 1) c) := by
  have he : (subdivide n).comp (boundary n) = (boundary n).comp (subdivide (X := X) (n + 1)) := by
    apply VertexChains.linearMap_ext_basis
    intro σ
    simp only [LinearMap.comp_apply, boundary_single, map_sum, map_zsmul, subdivide_single, one_smul]
    rw [← map_boundary, boundary_model]
    simp only [map_sum, map_zsmul, push_face]
  exact DFunLike.congr_fun he c

theorem homotopy_identity_zero (c : Chain X 0) :
    boundary 0 (homotopy 0 c) = subdivide 0 c - c := by
  rw [homotopy_zero, map_zero, subdivide_zero, sub_self]

theorem homotopy_identity_succ (n : ℕ) (c : Chain X (n + 1)) :
    boundary (n + 1) (homotopy (n + 1) c) + homotopy n (boundary n c) = subdivide (n + 1) c - c := by
  have he : (boundary (n + 1)).comp (homotopy (X := X) (n + 1)) +
      (homotopy n).comp (boundary n) = subdivide (n + 1) - LinearMap.id := by
    apply VertexChains.linearMap_ext_basis
    intro σ
    have hm := congrArg (TopologicalSingular.map σ (n + 1)) (homotopyModel_identity n)
    simp only [map_add, map_sub, map_sum, map_zsmul, map_boundary, push_face, map_single] at hm
    simpa only [LinearMap.add_apply, LinearMap.comp_apply, LinearMap.sub_apply, LinearMap.id_apply,
      simplexMap, ContinuousMap.comp_id, homotopy_single, subdivide_single, boundary_single, map_sum, map_zsmul, one_smul] using hm
  exact DFunLike.congr_fun he c

theorem subdivide_naturality (f : C(X, Y)) (n : ℕ) (c : Chain X n) :
    TopologicalSingular.map f n (subdivide n c) = subdivide n (TopologicalSingular.map f n c) :=
  fromModel_naturality (model n) f c

theorem homotopy_naturality (f : C(X, Y)) (n : ℕ) (c : Chain X n) :
    TopologicalSingular.map f (n + 1) (homotopy n c) = homotopy n (TopologicalSingular.map f n c) :=
  fromModel_naturality (homotopyModel n) f c

theorem cycle_difference_bounds (n : ℕ) (c : Chain X (n + 1)) (hc : boundary n c = 0) :
    subdivide (n + 1) c - c ∈ LinearMap.range (boundary (n + 1)) := by
  refine ⟨homotopy (n + 1) c, ?_⟩
  simpa only [hc, map_zero, add_zero] using homotopy_identity_succ n c

end FiniteChains.SingularSubdivision
