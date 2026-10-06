module

public import RequestProject.TruncatedCubePoset
public import RequestProject.TruncatedCellIncidence
public import RequestProject.PuncturedCubeBoundary
public import RequestProject.OrderComplexPi1Transfer

@[expose] public section

/-! Ordinary punctured cube boundaries inside the actual truncated-cell face poset. -/
namespace FiniteChains.Davis
open RACG Mirror Comb
variable {V : Type} [Fintype V] [DecidableEq V] {A : CommRel V}

def OldPuncturedBoundary (f t : QOld A) :=
  {c : TruncatedCell A // c < Sum.inl t ∧ c ≠ Sum.inl f}

instance (f t : QOld A) : PartialOrder (OldPuncturedBoundary f t) := Subtype.partialOrder _

def boundaryOldCell {f t : QOld A} (ht : t.1.sgn ≠ 0)
    (c : OldPuncturedBoundary f t) : QOld A := by
  rcases c with ⟨c, hc⟩
  cases c with
  | inl d => exact d
  | inr σ => exact False.elim (ht hc.1.le.2)

omit [Fintype V] in
theorem boundaryOldCell_eq {f t : QOld A} (ht : t.1.sgn ≠ 0)
    (c : OldPuncturedBoundary f t) : c.1 = Sum.inl (boundaryOldCell ht c) := by
  rcases c with ⟨c, hc⟩
  cases c with
  | inl d => rfl
  | inr σ => exact False.elim (ht hc.1.le.2)

def ordinaryBoundaryToCoordinate {f t : QOld A} (ht : t.1.sgn ≠ 0)
    (j : V) (b : CubeCoord) (hf : qCubeToCoordinate f.1 = coordinateFix j b (qCubeToCoordinate t.1))
    (c : OldPuncturedBoundary f t) : PuncturedCubeFace (qCubeToCoordinate t.1) j b := by
  let d := boundaryOldCell ht c
  have hd := boundaryOldCell_eq ht c
  have hle : d.1 ≤ t.1 := by
    have h := c.2.1.le
    rw [hd] at h
    exact h
  refine ⟨qCubeToCoordinate d.1, (qCubeToCoordinate_face_iff d.1 t.1).mp hle, ?_, ?_⟩
  · intro he
    have hdt : d = t := Subtype.ext
      (qCubeCoordinateEquiv.injective (Subtype.ext he))
    exact c.2.1.ne (hd.trans (congrArg Sum.inl hdt))
  · intro he
    have hdf : d = f := Subtype.ext
      (qCubeCoordinateEquiv.injective (Subtype.ext (he.trans hf.symm)))
    exact c.2.2 (hd.trans (congrArg Sum.inl hdf))

def coordinateBoundaryToOrdinary {f t : QOld A} (ht : t.1.sgn ≠ 0)
    (j : V) (b : CubeCoord) (hf : qCubeToCoordinate f.1 = coordinateFix j b (qCubeToCoordinate t.1))
    (c : PuncturedCubeFace (qCubeToCoordinate t.1) j b) : OldPuncturedBoundary f t := by
  have hs : freeSet c.1 ⊆ t.1.spx := by
    intro v hv
    have hvc := mem_freeSet.mp hv
    have hvt : v ∈ freeSet (qCubeToCoordinate t.1) := by
      rcases c.2.1 v with he | he
      · exact mem_freeSet.mpr he
      · exact mem_freeSet.mpr (he.symm.trans hvc)
    simpa using hvt
  let d : QCube A := coordinateToQCube ⟨c.1, isSimplex_subset A hs t.1.isSimplex⟩
  have hd : qCubeToCoordinate d = c.1 := coordinateToQCube_toCoordinate _
  have hdt : d ≤ t.1 := (qCubeToCoordinate_face_iff d t.1).mpr (hd ▸ c.2.1)
  have hold : ¬ (d.spx = ∅ ∧ d.sgn = 0) := by
    rintro ⟨_, hz⟩
    exact ht (qCube_sgn_zero_of_face hdt hz)
  let w : QOld A := ⟨d, hold⟩
  refine ⟨Sum.inl w, lt_of_le_of_ne hdt ?_, ?_⟩
  · intro he
    have hw : w = t := Sum.inl.inj he
    have hh : c.1 = qCubeToCoordinate t.1 := hd.symm.trans
      (congrArg (fun x : QOld A => qCubeToCoordinate x.1) hw)
    exact c.2.2.1 hh
  · intro he
    have hw : w = f := Sum.inl.inj he
    have hh : c.1 = coordinateFix j b (qCubeToCoordinate t.1) := hd.symm.trans
      ((congrArg (fun x : QOld A => qCubeToCoordinate x.1) hw).trans hf)
    exact c.2.2.2 hh

theorem coordinateBoundaryToOrdinary_coordinate {f t : QOld A} (ht : t.1.sgn ≠ 0)
    (j : V) (b : CubeCoord) (hf : qCubeToCoordinate f.1 = coordinateFix j b (qCubeToCoordinate t.1))
    (c : PuncturedCubeFace (qCubeToCoordinate t.1) j b) :
    qCubeToCoordinate (boundaryOldCell ht (coordinateBoundaryToOrdinary ht j b hf c)).1 = c.1 :=
  coordinateToQCube_toCoordinate _

/-- The actual boundary of a cube away from the cut corner has exactly the ordinary
coordinate faces, with their actual incidence order. -/
def ordinaryTruncatedBoundaryOrderIso {f t : QOld A} (ht : t.1.sgn ≠ 0)
    (j : V) (b : CubeCoord) (hf : qCubeToCoordinate f.1 = coordinateFix j b (qCubeToCoordinate t.1)) :
    OldPuncturedBoundary f t ≃o PuncturedCubeFace (qCubeToCoordinate t.1) j b where
  toFun := ordinaryBoundaryToCoordinate ht j b hf
  invFun := coordinateBoundaryToOrdinary ht j b hf
  left_inv c := by
    apply Subtype.ext
    rw [boundaryOldCell_eq ht (coordinateBoundaryToOrdinary ht j b hf
      (ordinaryBoundaryToCoordinate ht j b hf c)), boundaryOldCell_eq ht c]
    apply congrArg Sum.inl
    apply Subtype.ext
    apply qCubeCoordinateEquiv.injective
    apply Subtype.ext
    exact coordinateBoundaryToOrdinary_coordinate ht j b hf
      (ordinaryBoundaryToCoordinate ht j b hf c)
  right_inv c := by
    apply Subtype.ext
    exact coordinateBoundaryToOrdinary_coordinate ht j b hf c
  map_rel_iff' := by
    intro c d
    change CoordinateFace (qCubeToCoordinate (boundaryOldCell ht c).1)
      (qCubeToCoordinate (boundaryOldCell ht d).1) ↔ c.1 ≤ d.1
    rw [boundaryOldCell_eq ht c, boundaryOldCell_eq ht d]
    exact (qCubeToCoordinate_face_iff (boundaryOldCell ht c).1 (boundaryOldCell ht d).1).symm

theorem ordinaryTruncatedBoundary_connected {f t : QOld A} (ht : t.1.sgn ≠ 0)
    (j : V) (b : CubeCoord) (hb : b ≠ CubeCoord.free)
    (htj : qCubeToCoordinate t.1 j = CubeCoord.free)
    (hf : qCubeToCoordinate f.1 = coordinateFix j b (qCubeToCoordinate t.1)) :
    IsConnected (orderCx (OldPuncturedBoundary f t)) :=
  isConnected_orderCx_of_orderIso (ordinaryTruncatedBoundaryOrderIso ht j b hf)
    (ordinary_puncturedCubeBoundary_connected _ j b hb htj)

theorem ordinaryTruncatedBoundary_simplyConnected {f t : QOld A} (ht : t.1.sgn ≠ 0)
    (j : V) (b : CubeCoord) (hb : b ≠ CubeCoord.free)
    (htj : qCubeToCoordinate t.1 j = CubeCoord.free)
    (hf : qCubeToCoordinate f.1 = coordinateFix j b (qCubeToCoordinate t.1)) :
    SimplyConnected (orderCx (OldPuncturedBoundary f t)) :=
  simplyConnected_orderCx_of_orderIso (ordinaryTruncatedBoundaryOrderIso ht j b hf)
    (ordinary_puncturedCubeBoundary_simplyConnected _ j b hb htj)

theorem exists_facet_coordinates_of_inc {L : ASC V} (f t : QOld A)
    (hi : qCubeToCoordinate t.1 ∈ spineInc L (Sum.inl (qCubeToCoordinate f.1))) :
    ∃ j : V, ∃ b : CubeCoord, b ≠ CubeCoord.free ∧
      qCubeToCoordinate t.1 j = CubeCoord.free ∧
      qCubeToCoordinate f.1 = coordinateFix j b (qCubeToCoordinate t.1) := by
  classical
  have hm : qCubeToCoordinate t.1 ∈ cofaces L (qCubeToCoordinate f.1) := by
    simp only [spineInc] at hi
    split at hi
    · exact hi
    · simp at hi
  obtain ⟨j, hj, _, he⟩ := mem_cofaces.mp hm
  refine ⟨j, qCubeToCoordinate f.1 j, hj, ?_, ?_⟩
  · rw [he]
    exact Function.update_self _ _ _
  · funext v
    by_cases hv : v = j
    · subst v
      change qCubeToCoordinate f.1 j =
        Function.update (qCubeToCoordinate t.1) j (qCubeToCoordinate f.1 j) j
      exact (Function.update_self j (qCubeToCoordinate f.1 j) (qCubeToCoordinate t.1)).symm
    · simp only [coordinateFix, Function.update_of_ne hv, he]

theorem ordinaryTruncatedBoundary_connected_of_inc {L : ASC V} {f t : QOld A}
    (ht : t.1.sgn ≠ 0)
    (hi : qCubeToCoordinate t.1 ∈ spineInc L (Sum.inl (qCubeToCoordinate f.1))) :
    IsConnected (orderCx (OldPuncturedBoundary f t)) := by
  obtain ⟨j, b, hb, htj, hf⟩ := exists_facet_coordinates_of_inc f t hi
  exact ordinaryTruncatedBoundary_connected ht j b hb htj hf

theorem ordinaryTruncatedBoundary_simplyConnected_of_inc {L : ASC V} {f t : QOld A}
    (ht : t.1.sgn ≠ 0)
    (hi : qCubeToCoordinate t.1 ∈ spineInc L (Sum.inl (qCubeToCoordinate f.1))) :
    SimplyConnected (orderCx (OldPuncturedBoundary f t)) := by
  obtain ⟨j, b, hb, htj, hf⟩ := exists_facet_coordinates_of_inc f t hi
  exact ordinaryTruncatedBoundary_simplyConnected ht j b hb htj hf

def swappedBoundaryOrderIso (f t : QOld A) :
    {x : TruncatedCell A // x ≠ Sum.inl f ∧ x < Sum.inl t} ≃o OldPuncturedBoundary f t where
  toFun x := ⟨x.1, x.2.2, x.2.1⟩
  invFun x := ⟨x.1, x.2.2, x.2.1⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_rel_iff' := by intros; rfl

theorem ordinaryTruncatedBoundary_connectedIn {L : ASC V} {f t : QOld A}
    (ht : t.1.sgn ≠ 0)
    (hi : qCubeToCoordinate t.1 ∈ spineInc L (Sum.inl (qCubeToCoordinate f.1))) :
    ConnectedIn (fun x : TruncatedCell A => x ≠ Sum.inl f ∧ x < Sum.inl t) := by
  apply connectedIn_of_isConnected
  exact isConnected_orderCx_of_orderIso (swappedBoundaryOrderIso f t)
    (ordinaryTruncatedBoundary_connected_of_inc ht hi)

theorem ordinaryTruncatedBoundary_simplyConnectedIn {L : ASC V} {f t : QOld A}
    (ht : t.1.sgn ≠ 0)
    (hi : qCubeToCoordinate t.1 ∈ spineInc L (Sum.inl (qCubeToCoordinate f.1))) :
    SimplyConnectedIn (fun x : TruncatedCell A => x ≠ Sum.inl f ∧ x < Sum.inl t) := by
  apply simplyConnectedIn_of_simplyConnected
  exact simplyConnected_orderCx_of_orderIso (swappedBoundaryOrderIso f t)
    (ordinaryTruncatedBoundary_simplyConnected_of_inc ht hi)

end FiniteChains.Davis
