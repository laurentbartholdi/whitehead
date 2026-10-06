import RequestProject.TopologicalSingular.PointedSingularTriangle

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains.TopologicalSingular
open scoped unitInterval Topology
variable {X : Type} [TopologicalSpace X] {x : X}

theorem stickSimplex_isQuotientMap (d : ℕ) : Topology.IsQuotientMap (stickSimplex d) :=
  Topology.IsQuotientMap.of_surjective_continuous (stickSimplex_surjective d)
    (stickSimplex d).continuous

/-- The only identifications made by stick coordinates occur on the boundary,
where a based cubical map is constant. -/
theorem genLoop_constant_on_stick_fiber (d : ℕ) (p : GenLoop (Fin d) X x)
    (t u : Fin d → I) (h : stickSimplex d t = stickSimplex d u) : p t = p u := by
  have hbd : t ∈ Cube.boundary (Fin d) ↔ u ∈ Cube.boundary (Fin d) := by
    rw [← stickSimplex_mem_bdry_iff, ← stickSimplex_mem_bdry_iff, h]
  by_cases ht : t ∈ Cube.boundary (Fin d)
  · rw [GenLoop.boundary p t ht, GenLoop.boundary p u (hbd.mp ht)]
  · exact congrArg p (stickSimplex_injective_of_not_mem_boundary d t u ht
      (fun hu => ht (hbd.mpr hu)) h)

/-- Every actual based square factors continuously through the stick-coordinate
triangle, exactly rather than merely up to free homotopy. -/
theorem pointed_triangle_stick_represents_square (p : GenLoop (Fin 2) X x) :
    ∃ a : PointedSingularTriangle X x, basedTriangleStickSquare a.map a.based = p := by
  let f : Domain 2 → X := fun z => p (stickSimplex_surjective 2 z).choose
  have hf (t : Fin 2 → I) : f (stickSimplex 2 t) = p t :=
    genLoop_constant_on_stick_fiber 2 p _ t
      (stickSimplex_surjective 2 (stickSimplex 2 t)).choose_spec
  have hc : Continuous f := (stickSimplex_isQuotientMap 2).continuous_iff.mpr (by
    have he : f ∘ stickSimplex 2 = p := funext hf
    rw [he]
    exact p.val.continuous)
  let tau : Simplex X 2 := ⟨f, hc⟩
  have hbased : ∀ i : Fin 3, face i tau = ContinuousMap.const (Domain 1) x := by
    intro i
    apply ContinuousMap.ext
    intro z
    change p (stickSimplex_surjective 2 (stdSimplex.map (SimplexCategory.δ i) z)).choose = x
    apply GenLoop.boundary p
    apply (stickSimplex_mem_bdry_iff 2 _).mp
    rw [(stickSimplex_surjective 2 (stdSimplex.map (SimplexCategory.δ i) z)).choose_spec]
    exact ⟨i, simplex_face_coordinate_zero i z⟩
  refine ⟨⟨tau, hbased⟩, ?_⟩
  apply GenLoop.ext
  exact hf

theorem pointed_triangle_represents_pi2 (p : GenLoop (Fin 2) X x) :
    ∃ a : PointedSingularTriangle X x,
      a.pi2 = Additive.ofMul (Quotient.mk _ p) := by
  obtain ⟨a, ha⟩ := pointed_triangle_stick_represents_square p
  refine ⟨a, ?_⟩
  have h := basedTriangleStickSquare_pi2_eq a.map a.based
  rw [ha] at h
  exact congrArg Additive.ofMul h.symm

theorem pointed_triangle_pi2_surjective :
    Function.Surjective (PointedSingularTriangle.pi2 (X := X) (x := x)) := by
  intro q
  obtain ⟨p, hp⟩ := Quotient.exists_rep q.toMul
  obtain ⟨a, ha⟩ := pointed_triangle_represents_pi2 p
  exact ⟨a, ha.trans (congrArg Additive.ofMul hp)⟩

end FiniteChains.TopologicalSingular
