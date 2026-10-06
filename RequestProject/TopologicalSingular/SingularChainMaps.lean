module

/- Adapted from the local 2026-09-11 Lean audit; see PROVENANCE.json. -/

public import RequestProject.TopologicalSingular.SingularChains

@[expose] public section

/-! # Functorial maps on the explicit singular chain groups -/


set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains.TopologicalSingular

open Set Topology

universe u v w

variable {X : Type u} {Y : Type v} {Z : Type w}
variable [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]

def simplexMap (f : C(X, Y)) (n : ℕ) (σ : Simplex X n) : Simplex Y n := f.comp σ

@[simp] theorem simplexMap_apply (f : C(X, Y)) (n : ℕ) (σ : Simplex X n) (z : Domain n) :
    simplexMap f n σ z = f (σ z) := rfl

theorem face_simplexMap (f : C(X, Y)) {n : ℕ} (i : Fin (n + 2)) (σ : Simplex X (n + 1)) :
    face i (simplexMap f (n + 1) σ) = simplexMap f n (face i σ) := rfl

noncomputable def map (f : C(X, Y)) (n : ℕ) : Chain X n →ₗ[ℤ] Chain Y n :=
  Finsupp.lmapDomain ℤ ℤ (simplexMap f n)

@[simp] theorem map_single (f : C(X, Y)) (n : ℕ) (σ : Simplex X n) (a : ℤ) :
    map f n (Finsupp.single σ a) = Finsupp.single (simplexMap f n σ) a :=
  Finsupp.mapDomain_single

theorem map_id (n : ℕ) : map (ContinuousMap.id X) n = LinearMap.id := by
  apply Finsupp.lhom_ext
  intro σ a
  rw [map_single]
  rfl

theorem map_comp (f : C(X, Y)) (g : C(Y, Z)) (n : ℕ) :
    map (g.comp f) n = (map g n).comp (map f n) := by
  apply Finsupp.lhom_ext
  intro σ a
  simp only [LinearMap.comp_apply, map_single]
  rfl

theorem map_boundary (f : C(X, Y)) (n : ℕ) (c : Chain X (n + 1)) :
    map f n (boundary n c) = boundary n (map f (n + 1) c) := by
  have he : (map f n).comp (boundary n) = (boundary n).comp (map f (n + 1)) := by
    apply Finsupp.lhom_ext
    intro σ a
    simp only [LinearMap.comp_apply, boundary_single, map_single, map_sum, map_smul,
      face_simplexMap]
  exact DFunLike.congr_fun he c

theorem augmentation_map (f : C(X, Y)) (c : Chain X 0) : augmentation (map f 0 c) = augmentation c := by
  have he : augmentation.comp (map f 0) = augmentation := by
    apply Finsupp.lhom_ext
    intro σ a
    simp only [LinearMap.comp_apply, map_single, augmentation_single]
  exact DFunLike.congr_fun he c

end FiniteChains.TopologicalSingular
