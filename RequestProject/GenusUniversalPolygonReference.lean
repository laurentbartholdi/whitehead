import RequestProject.GenusUniversalCoveredSpine
import RequestProject.GenusQuotientReceiver
import RequestProject.BarycentricCocycleCover
import RequestProject.CoveredPolygonBarycentricBoundary

/-! An explicit degree-one polygon in actual pre-substitution old-cover
sheets. No arbitrary surface nullhomotopy is used to select its class.
Pending final Lean verification. -/

noncomputable section
open scoped Classical
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains.Davis.Genus
open RACG Mirror Comb Cell
variable (q : ℕ) [NeZero q]

local instance : Nonempty (GenusVertex q) := ⟨cV (gc q) (cyc (8 * q) 0)⟩

def universalSpineOldReceiverEquiv :
    PresGroup (namedSpinePresentation q) ≃*
      Pi1 (orderCx (QOld (cmpRel (GenusVertex q)))) (universalSpineOldBase q) :=
  MulEquiv.ofBijective (universalSpineOldReceiver q) (universalSpineOldReceiver_bijective q)

theorem universalSpineOldBase_eq : universalSpineOldBase q = posQCube (gBase q) := by
  change (genusSpineToOld q).onV ((markedSpineTree q).root).1 = _
  rw (config := { transparency := .default }) [markedSpineTree_root]
  rfl

theorem exists_universalOldCocycle :
    ∃ c : OrdCocycle (QOld (cmpRel (GenusVertex q))) (PresGroup (namedSpinePresentation q)),
      ∀ p : Loop (orderCx (QOld (cmpRel (GenusVertex q)))) (universalSpineOldBase q),
        c.readPath p.1 = (universalSpineOldReceiverEquiv q).symm (Pi1.mk p) :=
  OrdCocycle.exists_of_monodromy isConnected_orderCx_qOld (universalSpineOldBase q)
    (universalSpineOldReceiverEquiv q).symm.toMonoidHom

def universalOldCocycle := Classical.choose (exists_universalOldCocycle q)

theorem universalOldCocycle_monodromy :
    (universalOldCocycle q).monodromy (universalSpineOldBase q) =
      (universalSpineOldReceiverEquiv q).symm.toMonoidHom := by
  apply MonoidHom.ext
  intro z
  induction z using Quotient.inductionOn with
  | h p => exact Classical.choose_spec (exists_universalOldCocycle q) p

theorem universalOldCocycle_monodromy_bijective :
    Function.Bijective ((universalOldCocycle q).monodromy (universalSpineOldBase q)) := by
  rw (config := { transparency := .default }) [universalOldCocycle_monodromy]
  exact (universalSpineOldReceiverEquiv q).symm.bijective

abbrev UniversalPolygonCover :=
  DescendedSurfaceCover (posQCube (A := cmpRel (GenusVertex q)))
    posQCube_monotone (universalOldCocycle q)

def universalPolygonProjection : UniversalPolygonCover q → GenusVertex q :=
  descendedSurfaceProjection posQCube posQCube_monotone (universalOldCocycle q)

theorem universalPolygonProjection_isPosetCover : IsPosetCover (universalPolygonProjection q) :=
  descendedSurfaceProjection_isPosetCover posQCube posQCube_monotone (universalOldCocycle q)

def universalPolygonRawPole : PolygonCoverPole (gc q) (universalPolygonProjection q) :=
  ⟨⟨cC (gc q), 1⟩, rfl⟩

def universalPolygonRaw := coveredPolygon (gc q) (universalPolygonProjection q)
  (universalPolygonProjection_isPosetCover q) (universalPolygonRawPole q)

def universalPolygonShift : UniversalPolygonCover q ≃o UniversalPolygonCover q :=
  (descendedSurfaceCocycle posQCube posQCube_monotone (universalOldCocycle q)).coverDeck
    ((universalPolygonRaw q).V (cyc (8 * q) 0)).sheet⁻¹

def universalPolygonPole : PolygonCoverPole (gc q) (universalPolygonProjection q) :=
  CoveredPolygon.mapPole (gc q) (universalPolygonProjection q) (universalPolygonProjection q)
    (universalPolygonShift q) (fun _ => rfl) (v := universalPolygonRawPole q)

/-- All polygon positions are translated together so the first boundary
vertex is in the identity sheet. The actual polygon orientation is retained. -/
def universalPolygon : CoveredPolygon (gc q) (universalPolygonProjection q)
    (universalPolygonPole q) :=
  (universalPolygonRaw q).map (gc q) (universalPolygonProjection q)
    (universalPolygonProjection q) (universalPolygonShift q)
    (universalPolygonShift q).monotone (fun _ => rfl)

theorem universalPolygon_initial_sheet :
    ((universalPolygon q).V (cyc (8 * q) 0)).sheet = 1 := by
  change ((universalPolygonRaw q).V (cyc (8 * q) 0)).sheet⁻¹ *
    ((universalPolygonRaw q).V (cyc (8 * q) 0)).sheet = 1
  exact inv_mul_cancel _

/-- The degree-one assertion is an actual coefficient identity at the
actual lifted pole, before any substitution of the marked words. -/
theorem universalPolygon_coefficient_one :
    polygonCoverPoleCoefficients (gc q) (universalPolygonProjection q)
      (universalPolygonProjection_isPosetCover q) (universalPolygon q).cellularFundamental =
        Finsupp.single (universalPolygonPole q) 1 := by
  apply CoveredPolygon.cellularFundamental_pole_coefficients
  have := NeZero.pos q
  omega

def universalPolygonRealization :
    NeSpx (cmpRel (UniversalPolygonCover q)) → universalOldOrder q :=
  barycentricCoverRealization posQCube posQCube_monotone (universalOldCocycle q)
    (universalSpineOldBase q) isConnected_orderCx_qOld
    (universalOldCocycle_monodromy_bijective q)

theorem universalPolygonRealization_monotone : Monotone (universalPolygonRealization q) :=
  barycentricCoverRealization_monotone posQCube posQCube_monotone (universalOldCocycle q)
    (universalSpineOldBase q) isConnected_orderCx_qOld
    (universalOldCocycle_monodromy_bijective q)

def universalPolygonLift :
    Hom (orderCx (NeSpx (cmpRel (UniversalPolygonCover q))))
      (uCover (orderCx (QOld (cmpRel (GenusVertex q)))) (universalSpineOldBase q)) :=
  uOrderHom.comp (orderCxMap (universalPolygonRealization q) (universalPolygonRealization_monotone q))

theorem universalPolygonRealization_end (σ : NeSpx (cmpRel (UniversalPolygonCover q))) :
    uOrderEnd (universalPolygonRealization q σ) =
      posQCube (barycentricMap (universalPolygonProjection q)
        (universalPolygonProjection_isPosetCover q).mono σ) :=
  barycentricCoverRealization_end posQCube posQCube_monotone (universalOldCocycle q)
    (universalSpineOldBase q) isConnected_orderCx_qOld
    (universalOldCocycle_monodromy_bijective q) σ

theorem universalPolygonLift_projects :
    (univProj (orderCx (QOld (cmpRel (GenusVertex q)))) (universalSpineOldBase q)).comp
      (universalPolygonLift q) =
      (surfCx (cmpRel (GenusVertex q))).comp
        (orderCxMap (barycentricMap (universalPolygonProjection q)
          (universalPolygonProjection_isPosetCover q).mono)
          (barycentricMap_monotone _ (universalPolygonProjection_isPosetCover q).mono)) := by
  apply Hom.ext'
  · funext σ
    exact universalPolygonRealization_end q σ
  · funext e
    apply Subtype.ext
    exact Prod.ext (universalPolygonRealization_end q e.1.1)
      (universalPolygonRealization_end q e.1.2)
  · funext t
    apply Subtype.ext
    exact Prod.ext (universalPolygonRealization_end q t.1.1)
      (Prod.ext (universalPolygonRealization_end q t.1.2.1)
        (universalPolygonRealization_end q t.1.2.2))

theorem universalPolygonLift_initial :
    (universalPolygonLift q).onV (spx1 ((universalPolygon q).V (cyc (8 * q) 0))) =
      UV.base _ (universalSpineOldBase q) := by
  apply (universalOldCocycle q).readVertex_fibre_injective (universalSpineOldBase q)
    (universalOldCocycle_monodromy_bijective q).1
  · change uOrderEnd (universalPolygonRealization q _) = _
    rw (config := { transparency := .default }) [universalPolygonRealization_end, barycentricMap_spx1,
      (universalPolygon q).projV, endV_base, universalSpineOldBase_eq]
    rfl
  · change (universalOldCocycle q).readVertex (universalSpineOldBase q)
      (barycentricCoverRealization posQCube posQCube_monotone (universalOldCocycle q)
        (universalSpineOldBase q) isConnected_orderCx_qOld
        (universalOldCocycle_monodromy_bijective q) _) = _
    rw (config := { transparency := .default }) [barycentricCoverRealization_read]
    simp only [barycentricCoverReading, chainMax_spx1, descendedSurfaceSimplex,
      barycentricMap_spx1, descendedSurfaceProjection, OrdCocycle.val_refl, mul_one,
      universalPolygon_initial_sheet, OrdCocycle.readVertex_base]

/-- The subdivided source polygon, now in actual old universal-cover cells. -/
def universalOldPolygonChain :
    (uCover (orderCx (QOld (cmpRel (GenusVertex q)))) (universalSpineOldBase q)).F →₀ ℤ :=
  chain2 (universalPolygonLift q)
    (barycentricChain2 (decodeOrdNerve2 (universalPolygon q).fundamental))

theorem universalOldPolygonChain_boundary :
    Comb.bdry2 _ (universalOldPolygonChain q) =
      pathChain (uLiftPath (mapPath (surfCx (cmpRel (GenusVertex q))) (bdPath (gc q) (8 * q)))
        (UV.base _ (universalSpineOldBase q))) := by
  rw (config := { transparency := .default }) [universalOldPolygonChain, bdry2_chain2,
    (universalPolygon q).subdivisionFundamental_boundary (gc q) (universalPolygonProjection q)]
  change Finsupp.mapDomain (universalPolygonLift q).onE (pathChain _) = _
  rw (config := { transparency := .default }) [← pathChain_map]
  apply congrArg pathChain
  have hp := isPath_mapPath (universalPolygonLift q)
    ((universalPolygon q).subdivisionBoundaryPath_isPath (gc q) (universalPolygonProjection q) (8 * q))
  rw (config := { transparency := .default }) [universalPolygonLift_initial] at hp
  have he := eq_uLiftPath_of_isPath _ _ _ hp
  have hproj : mapPath (univProj (orderCx (QOld (cmpRel (GenusVertex q)))) (universalSpineOldBase q))
      (mapPath (universalPolygonLift q)
        ((universalPolygon q).subdivisionBoundaryPath (gc q) (universalPolygonProjection q) (8 * q))) =
      mapPath (surfCx (cmpRel (GenusVertex q))) (bdPath (gc q) (8 * q)) := by
    rw (config := { transparency := .default }) [mapPath_comp, universalPolygonLift_projects, ← mapPath_comp,
      (universalPolygon q).subdivisionBoundaryPath_projection (gc q)
        (universalPolygonProjection q) (universalPolygonProjection_isPosetCover q)]
    congr 2 <;> exact Subsingleton.elim _ _
  rw (config := { transparency := .default }) [hproj] at he
  exact he

end FiniteChains.Davis.Genus
