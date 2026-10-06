module

public import RequestProject.QCubeCoordinateBoundaryChain
public import RequestProject.QCubeCubicalThreeBoundary

@[expose] public section

/-! The six-face coefficient orientation agrees with the collapse's actual incidences. -/
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains.Davis
open RACG Mirror Comb
variable {V : Type} [DecidableEq V] [Fintype V] [LinearOrder V] {A : CommRel V}

theorem qThreeFace_coordinate_boundary_coefficient (c : QCube A) (u v w : V)
    (huv : v < u) (hvw : w < v) (hs : c.spx = {u, v, w}) (i : Fin 3 × ZMod 2) :
    cubeBdry (qCubeToCoordinate c)
      (Sum.inl (qCubeToCoordinate
        (qThreeFaceSquare c u v w (Ne.symm huv.ne) (Ne.symm (hvw.trans huv).ne)
          (Ne.symm hvw.ne) hs i).1)) = threeFacetOrientation i := by
  change cubeBdry (qCubeToCoordinate c)
    (Sum.inl (qCubeToCoordinate (qCubeFacet c (qThreeDirection u v w i.1) i.2))) = _
  rw [cubeBdry_actual_facet c _ (qThreeDirection_mem c u v w hs i.1) i.2]
  obtain ⟨hw0, hv0, hu0⟩ := threeFacet_incidence_zero c huv hvw hs
  obtain ⟨hw1, hv1, hu1⟩ := threeFacet_incidence_one c huv hvw hs
  obtain ⟨e, s⟩ := i
  fin_cases e <;> fin_cases s <;>
    norm_num [qThreeDirection, threeFacetOrientation, fixedCoordinateSign, Fin.ext_iff] at * <;> assumption

/-- Every coefficient of the actual indexed oriented face chain is the collapse's
ordinary boundary coefficient. -/
theorem qThreeOrientedFaces_coordinate_apply (c : QCube A) (u v w : V)
    (huv : v < u) (hvw : w < v) (hs : c.spx = {u, v, w}) (g : Cube V) :
    Finsupp.mapDomain (fun i => qCubeToCoordinate
      (qThreeFaceSquare c u v w (Ne.symm huv.ne) (Ne.symm (hvw.trans huv).ne)
        (Ne.symm hvw.ne) hs i).1) threeOrientedFaces g =
      cubeBdry (qCubeToCoordinate c) (Sum.inl g) := by
  classical
  let f := fun i => qCubeToCoordinate
    (qThreeFaceSquare c u v w (Ne.symm huv.ne) (Ne.symm (hvw.trans huv).ne)
      (Ne.symm hvw.ne) hs i).1
  have hinj : Function.Injective f := by
    intro i j h
    apply qThreeFaceSquare_injective c u v w (Ne.symm huv.ne)
      (Ne.symm (hvw.trans huv).ne) (Ne.symm hvw.ne) hs
    exact Subtype.ext (qCubeToCoordinate_injective h)
  change Finsupp.mapDomain f threeOrientedFaces g = _
  by_cases hg : g ∈ Set.range f
  · obtain ⟨i, rfl⟩ := hg
    rw [Finsupp.mapDomain_apply_of_injective hinj, threeOrientedFaces_apply]
    exact (qThreeFace_coordinate_boundary_coefficient c u v w huv hvw hs i).symm
  · have hzero : cubeBdry (qCubeToCoordinate c) (Sum.inl g) = 0 := by
      apply cubeBdry_zero_off_actual_facets
      intro a ha s he
      rw [hs, Finset.mem_insert, Finset.mem_insert, Finset.mem_singleton] at ha
      rcases ha with ha | ha | ha
      · subst a
        exact hg ⟨(0, s), he.symm⟩
      · subst a
        exact hg ⟨(1, s), he.symm⟩
      · subst a
        exact hg ⟨(2, s), he.symm⟩
    rw [Finsupp.mapDomain_notin_range _ _ hg, hzero]

/-- Coordinate transport of the actual six-facet boundary is the finite ordinary
coordinate boundary used by the collapse. -/
theorem qThreeCubicalFaceBoundary_coordinate (c : QThreeCube A) :
    Finsupp.lmapDomain ℤ ℤ (fun s : QSquare A => qCubeToCoordinate s.1)
      (qThreeCubicalFaceBoundary c) = qCubeCoordinateFacetChain c.1 := by
  change Finsupp.mapDomain (fun s : QSquare A => qCubeToCoordinate s.1)
    (Finsupp.mapDomain _ threeOrientedFaces) = _
  rw [← Finsupp.mapDomain_comp]
  ext g
  rw [qCubeCoordinateFacetChain_apply]
  exact qThreeOrientedFaces_coordinate_apply c.1 _ _ _ (qThree_middle_lt_upper c)
    (qThree_lower_lt_middle c) (qThree_free_directions c) g

/-- Coordinate boundary naturality for all genuine finite cubical three-chains. -/
theorem qThreeCubicalBoundary_coordinate (r : QThreeCube A →₀ ℤ) :
    Finsupp.lmapDomain ℤ ℤ (fun s : QSquare A => qCubeToCoordinate s.1)
      (qThreeCubicalBoundary r) =
      Finsupp.linearCombination ℤ (fun c : QThreeCube A => qCubeCoordinateFacetChain c.1) r := by
  induction r using Finsupp.induction_linear with
  | zero => simp
  | add r s hr hs => rw [map_add, map_add, hr, hs, map_add]
  | single c n =>
      rw [qThreeCubicalBoundary, Finsupp.linearCombination_single, map_smul,
        qThreeCubicalFaceBoundary_coordinate, Finsupp.linearCombination_single]

/-- Ordinary coordinate transport of every dimension-bounded strict three-boundary is
an actual finite combination of the cube boundaries used by the collapse. -/
theorem qCube_three_coordinate_boundary_reconstruction (y : StrictOrdTet (QCube A) →₀ ℤ)
    (hy : ∀ t ∈ y.support, t.1.2.2.2.spx.card ≤ 3)
    (hb : ∀ s ∈ (strictOrdBoundary3 y).support, s.1.2.2.spx.card ≤ 2) :
    ∃ r : QThreeCube A →₀ ℤ,
      Finsupp.lmapDomain ℤ ℤ (fun s : QSquare A => qCubeToCoordinate s.1)
        (qSquareCycleCoefficients (strictOrdBoundary3 y)) =
      Finsupp.linearCombination ℤ (fun c : QThreeCube A => qCubeCoordinateFacetChain c.1) r := by
  obtain ⟨r, _, hr⟩ := qCube_three_cubical_boundary_reconstruction y hy hb
  refine ⟨r, ?_⟩
  rw [hr, qThreeCubicalBoundary_coordinate]

end FiniteChains.Davis
