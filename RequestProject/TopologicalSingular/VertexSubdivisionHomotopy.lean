module

/- Adapted from the local 2026-09-11 Lean audit; see PROVENANCE.json. -/

public import RequestProject.TopologicalSingular.VertexSubdivision

@[expose] public section

/-! # The explicit chain homotopy for recursive vertex subdivision -/


set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains.VertexChains

universe u v
variable {V : Type u} {W : Type v}
variable (center : ∀ n, Vertices V n → V)

noncomputable def subdivideHomotopy : (n : ℕ) → Chain V n →ₗ[ℤ] Chain V (n + 1)
  | 0 => 0
  | n + 1 => Finsupp.linearCombination ℤ (fun v : Vertices V (n + 1) =>
      cone (v 0) (n + 1) (subdivide center (n + 1) (Finsupp.single v 1) -
        Finsupp.single v 1 - subdivideHomotopy n (boundary n (Finsupp.single v 1))))

theorem subdivideHomotopy_zero (c : Chain V 0) : subdivideHomotopy center 0 c = 0 := rfl

theorem subdivideHomotopy_succ_single (n : ℕ) (v : Vertices V (n + 1)) (r : ℤ) :
    subdivideHomotopy center (n + 1) (Finsupp.single v r) =
      r • cone (v 0) (n + 1) (subdivide center (n + 1) (Finsupp.single v 1) -
        Finsupp.single v 1 - subdivideHomotopy center n (boundary n (Finsupp.single v 1))) := by
  simp only [subdivideHomotopy, Finsupp.linearCombination_single]

theorem subdivideHomotopy_identity_zero (c : Chain V 0) :
    boundary 0 (subdivideHomotopy center 0 c) = subdivide center 0 c - c := by
  rw [subdivideHomotopy_zero, map_zero, subdivide_zero, sub_self]

theorem subdivideHomotopy_step (n : ℕ)
    (h : ∀ c : Chain V (n + 1), boundary n (subdivideHomotopy center n (boundary n c)) =
      subdivide center n (boundary n c) - boundary n c) :
    (boundary (n + 1)).comp (subdivideHomotopy center (n + 1)) +
      (subdivideHomotopy center n).comp (boundary n) = subdivide center (n + 1) - LinearMap.id := by
  apply linearMap_ext_basis
  intro v
  change boundary (n + 1) (subdivideHomotopy center (n + 1) (Finsupp.single v 1)) +
    subdivideHomotopy center n (boundary n (Finsupp.single v 1)) =
    subdivide center (n + 1) (Finsupp.single v 1) - Finsupp.single v 1
  rw [subdivideHomotopy_succ_single, one_smul, boundary_cone]
  have hz : boundary n (subdivide center (n + 1) (Finsupp.single v 1) - Finsupp.single v 1 -
      subdivideHomotopy center n (boundary n (Finsupp.single v 1))) = 0 := by
    rw [map_sub, map_sub, ← subdivide_boundary, h, sub_self]
  rw [hz, map_zero, sub_zero]
  abel

theorem subdivideHomotopy_identity (n : ℕ) :
    (boundary (n + 1)).comp (subdivideHomotopy center (n + 1)) +
      (subdivideHomotopy center n).comp (boundary n) = subdivide center (n + 1) - LinearMap.id := by
  induction n with
  | zero =>
    apply subdivideHomotopy_step
    intro c
    exact subdivideHomotopy_identity_zero center (boundary 0 c)
  | succ n ih =>
    apply subdivideHomotopy_step
    intro c
    have he := DFunLike.congr_fun ih (boundary (n + 1) c)
    simpa only [LinearMap.add_apply, LinearMap.comp_apply, LinearMap.sub_apply,
      LinearMap.id_apply, boundary_boundary, map_zero, add_zero] using he

theorem subdivideHomotopy_identity_succ (n : ℕ) (c : Chain V (n + 1)) :
    boundary (n + 1) (subdivideHomotopy center (n + 1) c) +
      subdivideHomotopy center n (boundary n c) = subdivide center (n + 1) c - c :=
  DFunLike.congr_fun (subdivideHomotopy_identity center n) c

theorem subdivideHomotopy_naturality (other : ∀ n, Vertices W n → W) (f : V → W)
    (hf : ∀ n v, f (center n v) = other n (f ∘ v)) (n : ℕ) :
    (map f (n + 1)).comp (subdivideHomotopy center n) =
      (subdivideHomotopy other n).comp (map f n) := by
  induction n with
  | zero => ext c; simp only [LinearMap.comp_apply, subdivideHomotopy_zero, map_zero]
  | succ n ih =>
    apply linearMap_ext_basis
    intro v
    simp only [LinearMap.comp_apply, subdivideHomotopy_succ_single, one_smul, map_single]
    rw [map_cone]
    simp only [map_sub]
    have hs := DFunLike.congr_fun (subdivide_naturality center other f hf (n + 1)) (Finsupp.single v 1)
    have ht := DFunLike.congr_fun ih (boundary n (Finsupp.single v 1))
    dsimp only [LinearMap.comp_apply] at hs ht
    rw [hs, ht, map_boundary, map_single]
    rfl

end FiniteChains.VertexChains
