import RequestProject.QCubeFacets
import RequestProject.CutSurfaceSpine

/-! Fixed coordinate facets and the actual quotient-cube coefficient boundary. -/
namespace FiniteChains.Davis
open RACG Mirror Comb
variable {V : Type} [DecidableEq V] [Fintype V] {A : CommRel V}

theorem qCubeToCoordinate_injective : Function.Injective (qCubeToCoordinate (A := A)) := by
  intro c d h
  apply qCubeCoordinateEquiv.injective
  exact Subtype.ext h

omit [Fintype V] in
/-- Freeing the fixed coordinate of an actual facet recovers its actual cube. -/
theorem qCubeFacet_coordinate_free (c : QCube A) (v : V) (hv : v ∈ c.spx)
    (s : ZMod 2) :
    Function.update (qCubeToCoordinate (qCubeFacet c v s)) v CubeCoord.free =
      qCubeToCoordinate c := by
  funext x
  by_cases hx : x = v
  · subst x
    simp [qCubeToCoordinate, hv]
  · simp [qCubeToCoordinate, qCubeFacet, hx]

/-- A nonfree coordinate that frees to a given cube lies in that cube's free set. -/
theorem coordinate_update_free_mem (g : Cube V) (c : QCube A) (v : V)
    (he : Function.update g v CubeCoord.free = qCubeToCoordinate c) : v ∈ c.spx := by
  have hval := congrFun he v
  have hfree : qCubeToCoordinate c v = CubeCoord.free := by simpa using hval.symm
  exact (freeSet_qCubeToCoordinate c) ▸ mem_freeSet.mpr hfree

omit [Fintype V] in
/-- Every nonfree coordinate cube that frees to an actual cube is its actual fixed facet. -/
theorem coordinate_update_free_facet (g : Cube V) (c : QCube A) (v : V)
    (hv : g v ≠ CubeCoord.free)
    (he : Function.update g v CubeCoord.free = qCubeToCoordinate c) :
    ∃ s : ZMod 2, g = qCubeToCoordinate (qCubeFacet c v s) := by
  have hother (x : V) (hx : x ≠ v) : g x = qCubeToCoordinate c x := by
    have h := congrFun he x
    simpa [Function.update_of_ne hx] using h
  cases hgv : g v with
  | free => exact False.elim (hv hgv)
  | pos =>
      refine ⟨0, ?_⟩
      rw [qCubeFacet_coordinate_zero]
      funext x
      by_cases hx : x = v
      · subst x
        simp [hgv]
      · simp [Function.update_of_ne hx, hother x hx]
  | neg =>
      refine ⟨1, ?_⟩
      rw [qCubeFacet_coordinate_one]
      funext x
      by_cases hx : x = v
      · subst x
        simp [hgv]
      · simp [Function.update_of_ne hx, hother x hx]

variable [LinearOrder V]

/-- The coefficient of any actual fixed facet in the collapse's cubical boundary is
exactly its coordinate incidence. -/
theorem cubeBdry_actual_facet (c : QCube A) (v : V) (hv : v ∈ c.spx) (s : ZMod 2) :
    cubeBdry (qCubeToCoordinate c) (Sum.inl (qCubeToCoordinate (qCubeFacet c v s))) =
      incid (qCubeToCoordinate (qCubeFacet c v s)) v := by
  classical
  let g := qCubeToCoordinate (qCubeFacet c v s)
  have hfixed : g v ≠ CubeCoord.free := by
    by_cases hs : s = 0 <;> simp [g, qCubeToCoordinate, qCubeFacet, hs]
  have hmem : v ∈ Finset.univ.filter (fun x => g x ≠ CubeCoord.free) := by simp [hfixed]
  have he := qCubeFacet_coordinate_free c v hv s
  rw [cubeBdry_inl, Finset.sum_eq_single v]
  · rw [he, if_pos rfl, mul_one]
  · intro k hk hkv
    have hkfixed : g k ≠ CubeCoord.free := (Finset.mem_filter.mp hk).2
    rw [if_neg, mul_zero]
    intro hkfree
    exact hkv (update_free_injective hkfixed (hkfree.trans he.symm))
  · intro hnot
    exact False.elim (hnot hmem)

/-- The collapse's ordinary cubical boundary has no coefficient outside actual facets. -/
theorem cubeBdry_zero_off_actual_facets (c : QCube A) (g : Cube V)
    (hg : ∀ v ∈ c.spx, ∀ s : ZMod 2, g ≠ qCubeToCoordinate (qCubeFacet c v s)) :
    cubeBdry (qCubeToCoordinate c) (Sum.inl g) = 0 := by
  classical
  rw [cubeBdry_inl]
  apply Finset.sum_eq_zero
  intro v hv
  rw [if_neg, mul_zero]
  intro he
  obtain ⟨s, hs⟩ := coordinate_update_free_facet g c v (Finset.mem_filter.mp hv).2 he
  exact hg v (coordinate_update_free_mem g c v he) s hs

end FiniteChains.Davis
