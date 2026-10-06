module

public import RequestProject.PosetCoverZigzagCycles
public import RequestProject.OrdinaryTruncatedBoundary
public import RequestProject.PosetCoverRestriction

@[expose] public section

/-! Finite one- and two-cycle fillings in the actual covered punctured cube boundaries. -/
namespace FiniteChains.Davis
open RACG Mirror Comb
variable {V P : Type} [DecidableEq V] [PartialOrder P]

theorem puncturedCubeBoundary_cover_fillings (t : Cube V) (j : V) (b z : CubeCoord)
    (hb : b ≠ CubeCoord.free) (hz : z ≠ CubeCoord.free) (hbz : b ≠ z)
    (ht : t j = CubeCoord.free) {f : P → PuncturedCubeFace t j b} (hf : IsPosetCover f) :
    (∀ c : StrictOrdEdge P →₀ ℤ, Comb.bdry1 (strictOrderCx P) c = 0 →
      ∃ d : StrictOrdTri P →₀ ℤ, Comb.bdry2 (strictOrderCx P) d = c) ∧
    (∀ c : StrictOrdTri P →₀ ℤ, Comb.bdry2 (strictOrderCx P) c = 0 →
      ∃ d : StrictOrdTet P →₀ ℤ, strictOrdBoundary3 d = c) := by
  have hupper : ∀ c : PuncturedCubeFace t j b,
      c ≤ punctureOpen t j b z hb hz hbz ht c :=
    fun c => coordinate_face_open j z c.1
  have hmiddle : ∀ c : PuncturedCubeFace t j b,
      punctureProject t j b z hz hbz ht c ≤ punctureOpen t j b z hb hz hbz ht c :=
    fun c => coordinate_fix_face_open j z c.1
  have hend : ∀ c : PuncturedCubeFace t j b,
      punctureProject t j b z hz hbz ht c ≤ punctureOpposite t j b z hz hbz ht :=
    fun c => coordinateFix_face_opposite_facet j z c.2.1
  exact ⟨strict_oneCycle_cover_zigzag hf _ _
    (punctureProject_monotone t j b z hz hbz ht)
    (punctureOpen_monotone t j b z hb hz hbz ht) hupper hmiddle _ hend,
    strict_twoCycle_cover_zigzag hf _ _
    (punctureProject_monotone t j b z hz hbz ht)
    (punctureOpen_monotone t j b z hb hz hbz ht) hupper hmiddle _ hend⟩

/-- A genuine facet puncture supplies its own contraction, with no filling input. -/
theorem ordinary_puncturedCubeBoundary_cover_fillings (t : Cube V) (j : V) (b : CubeCoord)
    (hb : b ≠ CubeCoord.free) (ht : t j = CubeCoord.free)
    {f : P → PuncturedCubeFace t j b} (hf : IsPosetCover f) :
    (∀ c : StrictOrdEdge P →₀ ℤ, Comb.bdry1 (strictOrderCx P) c = 0 →
      ∃ d : StrictOrdTri P →₀ ℤ, Comb.bdry2 (strictOrderCx P) d = c) ∧
    (∀ c : StrictOrdTri P →₀ ℤ, Comb.bdry2 (strictOrderCx P) c = 0 →
      ∃ d : StrictOrdTet P →₀ ℤ, strictOrdBoundary3 d = c) := by
  cases b with
  | free => exact False.elim (hb rfl)
  | pos =>
      exact puncturedCubeBoundary_cover_fillings t j .pos .neg hb
        (by decide) (by decide) ht hf
  | neg =>
      exact puncturedCubeBoundary_cover_fillings t j .neg .pos hb
        (by decide) (by decide) ht hf

variable [Fintype V] {A : CommRel V}

/-- The actual ordinary truncated-cell boundary has the same covered fillings. -/
theorem ordinaryTruncatedBoundary_cover_fillings {L : ASC V} {s t : QOld A}
    (ht : t.1.sgn ≠ 0)
    (hi : qCubeToCoordinate t.1 ∈ spineInc L (Sum.inl (qCubeToCoordinate s.1)))
    {f : P → OldPuncturedBoundary s t} (hf : IsPosetCover f) :
    (∀ c : StrictOrdEdge P →₀ ℤ, Comb.bdry1 (strictOrderCx P) c = 0 →
      ∃ d : StrictOrdTri P →₀ ℤ, Comb.bdry2 (strictOrderCx P) d = c) ∧
    (∀ c : StrictOrdTri P →₀ ℤ, Comb.bdry2 (strictOrderCx P) c = 0 →
      ∃ d : StrictOrdTet P →₀ ℤ, strictOrdBoundary3 d = c) := by
  obtain ⟨j, b, hb, htj, hs⟩ := exists_facet_coordinates_of_inc s t hi
  exact ordinary_puncturedCubeBoundary_cover_fillings _ j b hb htj
    (hf.postcomp_orderIso (ordinaryTruncatedBoundaryOrderIso ht j b hs))

/-- These fillings stay inside the actual inverse image of the punctured boundary. -/
theorem ordinaryTruncatedBoundary_preimage_fillings {L : ASC V} {s t : QOld A}
    (ht : t.1.sgn ≠ 0)
    (hi : qCubeToCoordinate t.1 ∈ spineInc L (Sum.inl (qCubeToCoordinate s.1)))
    {f : P → TruncatedCell A} (hf : IsPosetCover f) :
    let B := {p : P // f p < Sum.inl t ∧ f p ≠ Sum.inl s}
    (∀ c : StrictOrdEdge B →₀ ℤ, Comb.bdry1 (strictOrderCx B) c = 0 →
      ∃ d : StrictOrdTri B →₀ ℤ, Comb.bdry2 (strictOrderCx B) d = c) ∧
    (∀ c : StrictOrdTri B →₀ ℤ, Comb.bdry2 (strictOrderCx B) c = 0 →
      ∃ d : StrictOrdTet B →₀ ℤ, strictOrdBoundary3 d = c) := by
  exact ordinaryTruncatedBoundary_cover_fillings ht hi
    (IsPosetCover.restriction f {c | c < Sum.inl t ∧ c ≠ Sum.inl s} hf)

end FiniteChains.Davis
