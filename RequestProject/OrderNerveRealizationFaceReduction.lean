import RequestProject.TopologicalSingular.SimplexCoordinates
import RequestProject.OrderNerveRealizationInterior
import RequestProject.OrderNerveRealizationNondegenerate

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains.Comb
open CategoryTheory Simplicial

/-- A standard-simplex point with a zero coordinate comes from the corresponding face. -/
theorem topologicalSimplex_zero_coordinate_face {n : ℕ}
    (z : SimplexCategory.toTop.obj ⦋n + 1⦌) (i : Fin (n + 2))
    (hi : z.down.weights i = 0) :
    ∃ w : SimplexCategory.toTop.obj ⦋n⦌, SimplexCategory.toTop.map (SimplexCategory.δ i) w = z := by
  let zold := TopologicalSingular.simplexCoordinates (n + 1) z.down
  have hiold : zold.val i = 0 := hi
  let w : stdSimplex ℝ (Fin (n + 1)) :=
    ⟨fun j => zold.val (i.succAbove j), fun j => zold.property.1 _, by
      have hs := zold.property.2
      rw [Fin.sum_univ_succAbove (fun j : Fin (n + 2) => zold.val j) i,
        hiold, zero_add] at hs
      exact hs⟩
  refine ⟨ULift.up ((TopologicalSingular.simplexCoordinates n).symm w), ?_⟩
  apply ULift.ext
  apply (TopologicalSingular.simplexCoordinates (n + 1)).injective
  change TopologicalSingular.simplexCoordinates (n + 1)
    (Convexity.StdSimplex.map i.succAbove ((TopologicalSingular.simplexCoordinates n).symm w)) = zold
  rw [TopologicalSingular.simplexCoordinates_map, Homeomorph.apply_symm_apply]
  apply Subtype.ext
  funext k
  change (FunOnFinite.linearMap ℝ ℝ i.succAbove w.val) k = zold.val k
  rw [FunOnFinite.linearMap_apply_apply]
  by_cases hk : k = i
  · subst k
    simp [Fin.succAbove_ne, hiold]
  · obtain ⟨j, rfl⟩ := Fin.exists_succAbove_eq hk
    simp [w, Finset.sum_filter]

/-- Every point on a nondegenerate simplex belongs to the interior of a
nondegenerate face of no larger dimension. -/
theorem orderNerveRealizationSimplex_interior_representative (P : Type) [PartialOrder P]
    (n : ℕ) (s : (nerve P).nonDegenerate n) (z : SimplexCategory.toTop.obj ⦋n⦌) :
    ∃ (m : ℕ) (_ : m ≤ n) (t : (nerve P).nonDegenerate m)
      (w : SimplexCategory.toTop.obj ⦋m⦌),
      (∀ i, 0 < w.down.weights i) ∧
        orderNerveRealizationSimplex P t.val w = orderNerveRealizationSimplex P s.val z := by
  induction n with
  | zero =>
    refine ⟨0, le_rfl, s, z, ?_, rfl⟩
    intro i
    haveI : Subsingleton (Fin (⦋0⦌.len + 1)) := by
      simpa only [SimplexCategory.len_mk] using (inferInstance : Subsingleton (Fin 1))
    have h := z.down.total_of_fintype
    change (∑ j : Fin 1, z.down.weights j) = 1 at h
    simp only [Fintype.sum_unique] at h
    have he : z.down.weights i = 1 :=
      (congrArg z.down.weights (Subsingleton.elim i default)).trans h
    rw [he]
    norm_num
  | succ n ih =>
    by_cases hz : ∀ i, 0 < z.down.weights i
    · exact ⟨n + 1, le_rfl, s, z, hz, rfl⟩
    · push_neg at hz
      obtain ⟨i, hi⟩ := hz
      have hi0 : z.down.weights i = 0 := le_antisymm hi (z.down.weights_nonneg i)
      obtain ⟨w, hw⟩ := topologicalSimplex_zero_coordinate_face z i hi0
      have hs := (PartialOrder.mem_nerve_nonDegenerate_iff_injective s.val).mp s.property
      have ht : (nerve P).map (SimplexCategory.δ i).op s.val ∈
          (nerve P).nonDegenerate n := by
        rw [PartialOrder.mem_nerve_nonDegenerate_iff_injective]
        change Function.Injective (fun j => s.val.obj (i.succAbove j))
        exact hs.comp Fin.succAbove_right_injective
      obtain ⟨m, hm, t, u, hu, he⟩ := ih ⟨_, ht⟩ w
      refine ⟨m, hm.trans (Nat.le_succ n), t, u, hu, he.trans ?_⟩
      have h := congrArg (fun k => k w)
        (orderNerveRealizationSimplex_operator P (SimplexCategory.δ i) s.val)
      change orderNerveRealizationSimplex P s.val
        (SimplexCategory.toTop.map (SimplexCategory.δ i) w) = _ at h
      rw [hw] at h
      exact h.symm

/-- Every actual realization point lies in an actual nondegenerate simplex interior. -/
theorem orderNerveRealization_interior_cover (P : Type) [PartialOrder P]
    (x : orderNerveRealization P) :
    ∃ (n : ℕ) (s : (nerve P).nonDegenerate n)
      (z : SimplexCategory.toTop.obj ⦋n⦌),
      (∀ i, 0 < z.down.weights i) ∧ orderNerveRealizationSimplex P s.val z = x := by
  obtain ⟨n, s, z, hz⟩ := orderNerveRealization_nonDegenerate_jointly_surjective P x
  obtain ⟨m, _, t, w, hw, he⟩ := orderNerveRealizationSimplex_interior_representative P n s z
  exact ⟨m, t, w, hw, he.trans hz⟩

/-- Every boundary point of an actual simplex is represented in one of its finitely
many codimension-one faces. -/
theorem orderNerveRealizationSimplex_boundary_face {P : Type} [PartialOrder P]
    {n : ℕ} (s : (nerve P).obj (Opposite.op ⦋n + 1⦌))
    (z : SimplexCategory.toTop.obj ⦋n + 1⦌) (hz : ¬ ∀ i, 0 < z.down.weights i) :
    ∃ (i : Fin (n + 2)) (w : SimplexCategory.toTop.obj ⦋n⦌),
      orderNerveRealizationSimplex P ((nerve P).map (SimplexCategory.δ i).op s) w =
        orderNerveRealizationSimplex P s z := by
  push_neg at hz
  obtain ⟨i, hi⟩ := hz
  have hi0 : z.down.weights i = 0 := le_antisymm hi (z.down.weights_nonneg i)
  obtain ⟨w, hw⟩ := topologicalSimplex_zero_coordinate_face z i hi0
  refine ⟨i, w, ?_⟩
  have h := congrArg (fun k => k w)
    (orderNerveRealizationSimplex_operator P (SimplexCategory.δ i) s)
  change orderNerveRealizationSimplex P s
    (SimplexCategory.toTop.map (SimplexCategory.δ i) w) = _ at h
  rw [hw] at h
  exact h.symm

/-- Every face of an actual nondegenerate poset-nerve simplex remains nondegenerate. -/
theorem orderNerve_nonDegenerate_face {P : Type} [PartialOrder P]
    {n : ℕ} (s : (nerve P).nonDegenerate (n + 1)) (i : Fin (n + 2)) :
    (nerve P).map (SimplexCategory.δ i).op s.val ∈ (nerve P).nonDegenerate n := by
  rw [PartialOrder.mem_nerve_nonDegenerate_iff_injective]
  change Function.Injective (fun j => s.val.obj (i.succAbove j))
  exact ((PartialOrder.mem_nerve_nonDegenerate_iff_injective s.val).mp s.property).comp
    Fin.succAbove_right_injective

/-- The boundary of every nondegenerate simplex maps into a finite family of
actual lower-dimensional closed simplex images. -/
theorem orderNerveRealizationSimplex_boundary_finite_faces {P : Type} [PartialOrder P]
    {n : ℕ} (s : (nerve P).nonDegenerate (n + 1)) :
    ∃ I : Finset ((nerve P).nonDegenerate n),
      ∀ z : SimplexCategory.toTop.obj ⦋n + 1⦌,
        (¬ ∀ i, 0 < z.down.weights i) →
        ∃ t ∈ I, ∃ w : SimplexCategory.toTop.obj ⦋n⦌,
          orderNerveRealizationSimplex P t.val w = orderNerveRealizationSimplex P s.val z := by
  classical
  let face : Fin (n + 2) → (nerve P).nonDegenerate n := fun i =>
    ⟨(nerve P).map (SimplexCategory.δ i).op s.val, orderNerve_nonDegenerate_face s i⟩
  refine ⟨Finset.univ.image face, ?_⟩
  intro z hz
  obtain ⟨i, w, hw⟩ := orderNerveRealizationSimplex_boundary_face s.val z hz
  exact ⟨face i, Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩, w, hw⟩

end FiniteChains.Comb
