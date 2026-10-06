import RequestProject.QCubeCanonicalTwoCycles
import RequestProject.QCubeFacetIncidence

/-! Decreasing square frames agree with the actual ordered coordinate directions. -/
namespace FiniteChains.Davis
open RACG Mirror Comb
variable {V : Type} [DecidableEq V] [LinearOrder V] {A : CommRel V}

theorem qSquare_frame_unique (c : QSquare A) {a b : V}
    (h : b < a) (hs : c.1.spx = {a, b}) : qSquareLeft c = a ∧ qSquareRight c = b := by
  have hl : qSquareLeft c ∈ ({a, b} : Finset V) := by
    rw [← hs, qSquare_free_directions]
    simp
  have hr : qSquareRight c ∈ ({a, b} : Finset V) := by
    rw [← hs, qSquare_free_directions]
    simp
  simp only [Finset.mem_insert, Finset.mem_singleton] at hl hr
  have horder := qSquare_directions_decreasing c
  rcases hl with hl | hl <;> rcases hr with hr | hr
  · rw [hl, hr] at horder
    exact False.elim ((lt_irrefl a) horder)
  · exact ⟨hl, hr⟩
  · rw [hl, hr] at horder
    exact False.elim ((not_lt_of_ge h.le) horder)
  · rw [hl, hr] at horder
    exact False.elim ((lt_irrefl b) horder)

theorem qSquare_subdivision_ordered (c : QSquare A) {a b : V}
    (h : b < a) (hs : c.1.spx = {a, b}) :
    cubeSquareSubdivision c.1 (qSquareLeft c) (qSquareRight c)
      (qSquare_directions_ne c) (qSquare_free_directions c) =
      cubeSquareSubdivision c.1 a b (Ne.symm h.ne) hs := by
  obtain ⟨hl, hr⟩ := qSquare_frame_unique c h hs
  subst a
  subst b
  rfl

theorem qSquare_edge_boundary_ordered (c : QSquare A) {a b : V}
    (h : b < a) (hs : c.1.spx = {a, b}) :
    cubeSquareEdgeBoundary c.1 (qSquareLeft c) (qSquareRight c)
      (qSquare_directions_ne c) (qSquare_free_directions c) =
      cubeSquareEdgeBoundary c.1 a b (Ne.symm h.ne) hs := by
  obtain ⟨hl, hr⟩ := qSquare_frame_unique c h hs
  subst a
  subst b
  rfl

theorem qSquare_subdivision_single (c : QSquare A) (n : ℤ) {a b : V}
    (h : b < a) (hs : c.1.spx = {a, b}) :
    qSquareChainSubdivision (Finsupp.single c n) =
      n • cubeSquareSubdivision c.1 a b (Ne.symm h.ne) hs := by
  rw [qSquareChainSubdivision, squareChainSubdivision, Finsupp.linearCombination_single,
    qSquare_subdivision_ordered c h hs]

theorem qSquare_boundary_single (c : QSquare A) (n : ℤ) {a b : V}
    (h : b < a) (hs : c.1.spx = {a, b}) :
    qSquareFacetBoundary (Finsupp.single c n) =
      n • cubeSquareEdgeBoundary c.1 a b (Ne.symm h.ne) hs := by
  rw [qSquareFacetBoundary, squareChainEdgeBoundary, Finsupp.linearCombination_single,
    qSquare_edge_boundary_ordered c h hs]

end FiniteChains.Davis
