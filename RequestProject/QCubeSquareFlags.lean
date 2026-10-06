import RequestProject.QCubeSquareSubdivision
import RequestProject.QCubeImmediateFaces

/-! The eight actual nondegenerate vertex-edge-square flags of a square subdivision. -/
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains.Davis
open RACG Mirror Comb
variable {V : Type} [DecidableEq V] {A : CommRel V}

def squarePositiveFlag (c : QCube A) (a b : V) (hne : a ≠ b)
    (hs : c.spx = {a, b}) (s : ZMod 2) : (strictOrderCx (QCube A)).F :=
  ⟨(cubePositiveVertex (qCubeFacet c a s), qCubeFacet c a s, c),
    cubePositiveVertex_lt _ b (by rw [squareFacet_w_spx c hne hs s]; simp),
    qCubeFacet_lt c a s (by rw [hs]; simp)⟩

def squareNegativeFlag (c : QCube A) (a b : V) (hne : a ≠ b)
    (hs : c.spx = {a, b}) (s : ZMod 2) : (strictOrderCx (QCube A)).F :=
  ⟨(cubeNegativeVertex (qCubeFacet c a s) b, qCubeFacet c a s, c),
    cubeNegativeVertex_lt _ b (by rw [squareFacet_w_spx c hne hs s]; simp),
    qCubeFacet_lt c a s (by rw [hs]; simp)⟩

/-- The actual cone filling is the signed sum of its eight genuine square flags. -/
theorem cubeSquareSubdivision_flags (c : QCube A) (v w : V) (hne : v ≠ w)
    (hs : c.spx = {v, w}) :
    cubeSquareSubdivision c v w hne hs =
      Finsupp.single (squareNegativeFlag c w v (Ne.symm hne)
        (by simpa [Finset.pair_comm] using hs) 0) 1 -
      Finsupp.single (squarePositiveFlag c w v (Ne.symm hne)
        (by simpa [Finset.pair_comm] using hs) 0) 1 -
      (Finsupp.single (squareNegativeFlag c w v (Ne.symm hne)
        (by simpa [Finset.pair_comm] using hs) 1) 1 -
       Finsupp.single (squarePositiveFlag c w v (Ne.symm hne)
        (by simpa [Finset.pair_comm] using hs) 1) 1) -
      (Finsupp.single (squareNegativeFlag c v w hne hs 0) 1 -
       Finsupp.single (squarePositiveFlag c v w hne hs 0) 1) +
      (Finsupp.single (squareNegativeFlag c v w hne hs 1) 1 -
       Finsupp.single (squarePositiveFlag c v w hne hs 1) 1) := by
  simp [cubeSquareSubdivision, lowerSquareEdgeBoundary, lowerFacetEdgeChain,
    strictTopConeEdgeChain, strictTopConeEdgeTriangle, squarePositiveFlag, squareNegativeFlag]

/-- Every strict triangle with this square as its top cell is one of the eight actual flags. -/
theorem squareFlags_exhaustive (c : QCube A) (v w : V) (hne : v ≠ w)
    (hs : c.spx = {v, w}) (t : (strictOrderCx (QCube A)).F) (ht : t.1.2.2 = c) :
    ∃ s : ZMod 2,
      t = squarePositiveFlag c v w hne hs s ∨
      t = squareNegativeFlag c v w hne hs s ∨
      t = squarePositiveFlag c w v (Ne.symm hne) (by simpa [Finset.pair_comm] using hs) s ∨
      t = squareNegativeFlag c w v (Ne.symm hne) (by simpa [Finset.pair_comm] using hs) s := by
  obtain ⟨⟨x, y, z⟩, hxy, hyz⟩ := t
  change z = c at ht
  subst z
  change x < y at hxy
  change y < c at hyz
  have hc : c.spx.card = 2 := by rw [hs]; simp [hne]
  have hy : y.spx.card = 1 := by
    have hx := qCube_card_lt_of_lt hxy
    have hy := qCube_card_lt_of_lt hyz
    omega
  obtain ⟨a, ha, hface⟩ := exists_qCube_zero_or_one_facet y c hyz.le (by omega)
  rw [hs, Finset.mem_insert, Finset.mem_singleton] at ha
  rcases ha with rfl | rfl
  · rcases hface with rfl | rfl
    · rcases qCube_vertex_below_edge x _ hxy w (squareFacet_w_spx c hne hs 0) with rfl | rfl
      · exact ⟨0, Or.inl rfl⟩
      · exact ⟨0, Or.inr (Or.inl rfl)⟩
    · rcases qCube_vertex_below_edge x _ hxy w (squareFacet_w_spx c hne hs 1) with rfl | rfl
      · exact ⟨1, Or.inl rfl⟩
      · exact ⟨1, Or.inr (Or.inl rfl)⟩
  · rcases hface with rfl | rfl
    · rcases qCube_vertex_below_edge x _ hxy v (squareFacet_v_spx c hne hs 0) with rfl | rfl
      · exact ⟨0, Or.inr (Or.inr (Or.inl rfl))⟩
      · exact ⟨0, Or.inr (Or.inr (Or.inr rfl))⟩
    · rcases qCube_vertex_below_edge x _ hxy v (squareFacet_v_spx c hne hs 1) with rfl | rfl
      · exact ⟨1, Or.inr (Or.inr (Or.inl rfl))⟩
      · exact ⟨1, Or.inr (Or.inr (Or.inr rfl))⟩

end FiniteChains.Davis
