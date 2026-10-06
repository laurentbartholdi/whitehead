/- Adapted from the local 2026-09-11 Lean audit; see PROVENANCE.json. -/

import RequestProject.TopologicalSingular.VertexChains

/-! # Recursive subdivision of vertex chains

The boundary identity is valid for any chosen center of every simplex.
Barycenters will be used for the geometric specialization. Naturality
requires that the vertex map carry the chosen centers to chosen centers.
-/


namespace FiniteChains.VertexChains

universe u v
variable {V : Type u} {W : Type v}
variable (center : ∀ n, Vertices V n → V)

noncomputable def subdivide : (n : ℕ) → Chain V n →ₗ[ℤ] Chain V n
  | 0 => LinearMap.id
  | n + 1 => Finsupp.linearCombination ℤ (fun v : Vertices V (n + 1) =>
      cone (center (n + 1) v) n (subdivide n (boundary n (Finsupp.single v 1))))

theorem subdivide_zero (c : Chain V 0) : subdivide center 0 c = c := rfl

theorem subdivide_succ_single (n : ℕ) (v : Vertices V (n + 1)) (r : ℤ) :
    subdivide center (n + 1) (Finsupp.single v r) =
      r • cone (center (n + 1) v) n (subdivide center n (boundary n (Finsupp.single v 1))) := by
  simp only [subdivide, Finsupp.linearCombination_single]

theorem boundary_subdivide (n : ℕ) :
    (boundary n).comp (subdivide center (n + 1)) = (subdivide center n).comp (boundary n) := by
  induction n with
  | zero =>
    apply linearMap_ext_basis
    intro v
    simp only [LinearMap.comp_apply, subdivide_succ_single, one_smul, subdivide_zero]
    rw [boundary_cone_zero, augmentation_boundary, zero_smul, sub_zero]
  | succ n ih =>
    apply linearMap_ext_basis
    intro v
    simp only [LinearMap.comp_apply, subdivide_succ_single, one_smul]
    rw [boundary_cone]
    have hz : boundary n (subdivide center (n + 1)
        (boundary (n + 1) (Finsupp.single v 1))) = 0 := by
      rw [← LinearMap.comp_apply, ih, LinearMap.comp_apply, boundary_boundary, map_zero]
    rw [hz, map_zero, sub_zero]

theorem subdivide_boundary (n : ℕ) (c : Chain V (n + 1)) :
    subdivide center n (boundary n c) = boundary n (subdivide center (n + 1) c) :=
  (DFunLike.congr_fun (boundary_subdivide center n) c).symm

theorem subdivide_naturality (other : ∀ n, Vertices W n → W) (f : V → W)
    (hf : ∀ n v, f (center n v) = other n (f ∘ v)) (n : ℕ) :
    (map f n).comp (subdivide center n) = (subdivide other n).comp (map f n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    apply linearMap_ext_basis
    intro v
    simp only [LinearMap.comp_apply, subdivide_succ_single, one_smul, map_single]
    rw [map_cone, hf]
    have he := DFunLike.congr_fun ih (boundary n (Finsupp.single v 1))
    dsimp only [LinearMap.comp_apply] at he
    rw [he, map_boundary, map_single]

end FiniteChains.VertexChains
