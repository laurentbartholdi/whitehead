import RequestProject.OrderCocycleCoverPi1
import RequestProject.PresPosetReading
import RequestProject.PresCoverRelatorLetterCoefficients
import RequestProject.PresCoverRoseFibreEquiv

noncomputable section
namespace FiniteChains.PresModel.PresCocycleCover
open Comb
universe u
variable {α J G : Type u} [Group G] (w : J → List (α × Bool))
  (gen : α → G) (hrel : ∀ j, wordVal gen (w j) = 1)

abbrev Coc := presCoc w gen hrel
abbrev Space := (Coc w gen hrel).Cover
abbrev projection : Space w gen hrel → PresPos w := OrdCocycle.Cover.point
abbrev covering : IsPosetCover (projection w gen hrel) :=
  (Coc w gen hrel).coverProjection_isPosetCover
abbrev Cylinder := {p : Space w gen hrel //
  projection w gen hrel p ∈ coneAdjBaseSet (S := circSet w)}
abbrev cylinderProjection := coneAdjCoverBaseEnd (projection w gen hrel)
abbrev cylinderCovering := coneAdjCoverBaseEnd_isPosetCover
  (projection w gen hrel) (covering w gen hrel)
abbrev RoseSpace := cylinderCoverRoseSet w (cylinderProjection w gen hrel)
abbrev roseProjection := cylinderCoverRoseEnd w (cylinderProjection w gen hrel)
abbrev roseCovering := cylinderCoverRoseEnd_isPosetCover w
  (cylinderProjection w gen hrel) (cylinderCovering w gen hrel)

/-- An actual lifted relator is exactly an apex sheet together with a relator label. -/
def relatorEquiv : PresCoverRelator w (projection w gen hrel) ≃ G × J where
  toFun p := (p.val.1.sheet, p.val.2)
  invFun p := ⟨(⟨apexOf w p.2, p.1⟩, p.2), rfl⟩
  left_inv p := by
    apply Subtype.ext
    refine Prod.ext ?_ rfl
    cases p with
    | mk p hp => cases p with
      | mk v j => cases v with
        | mk x g => dsimp only at hp; cases hp; rfl
  right_inv _ := rfl

noncomputable def roseFibreEquiv (x : Rose α) :
    {p : RoseSpace w gen hrel // roseProjection w gen hrel p = x} ≃ G :=
  (presCoverRoseFibreEquiv w (projection w gen hrel) x).trans
    ((Coc w gen hrel).coverFibreEquiv (iRose w x))

theorem roseFibreEquiv_apply (x : Rose α)
    (p : {p : RoseSpace w gen hrel // roseProjection w gen hrel p = x}) :
    roseFibreEquiv w gen hrel x p = p.val.val.val.sheet := rfl

/-- The sheet of an actual lifted midpoint is the initial sheet of its positive generator. -/
noncomputable def midpointEquiv : roseCoverMidpoints (roseProjection w gen hrel) ≃ G × α where
  toFun p := (roseFibreEquiv w gen hrel (Rose.mid p.val.2) ⟨p.val.1, p.property⟩, p.val.2)
  invFun p := ⟨(((roseFibreEquiv w gen hrel (Rose.mid p.2)).symm p.1).val, p.2),
    ((roseFibreEquiv w gen hrel (Rose.mid p.2)).symm p.1).property⟩
  left_inv p := by
    apply Subtype.ext
    refine Prod.ext ?_ rfl
    exact congrArg Subtype.val ((roseFibreEquiv w gen hrel (Rose.mid p.val.2)).symm_apply_apply
      ⟨p.val.1, p.property⟩)
  right_inv p := by
    refine Prod.ext ?_ rfl
    exact (roseFibreEquiv w gen hrel (Rose.mid p.2)).apply_symm_apply p.1

noncomputable def generatorEquiv :
    roseCoverGeneratorEdges (roseProjection w gen hrel) (roseCovering w gen hrel) ≃ G × α :=
  (roseCoverMidpointEdgeEquiv (roseProjection w gen hrel)
    (roseCovering w gen hrel)).symm.trans (midpointEquiv w gen hrel)

theorem generatorEquiv_midpoint (p : roseCoverMidpoints (roseProjection w gen hrel)) :
    generatorEquiv w gen hrel
      (roseCoverMidpointEdge (roseProjection w gen hrel) (roseCovering w gen hrel) p) =
        (p.val.1.val.val.sheet, p.val.2) := by
  change midpointEquiv w gen hrel
    ((roseCoverMidpointEdgeEquiv _ _).symm ((roseCoverMidpointEdgeEquiv _ _) p)) = _
  rw [Equiv.symm_apply_apply]
  rfl

/-- The genuine lifted cylinder collapse preserves the cocycle sheet. -/
theorem cylinderCollapse_sheet (p : Cylinder w gen hrel) :
    (cylinderCoverCollapse w (cylinderCovering w gen hrel) p).val.sheet = p.val.sheet := by
  let r := cylinderCoverCollapse w (cylinderCovering w gen hrel) p
  have hle : p ≤ r := (cylinderCovering w gen hrel).le_upTransform
    (cylCollapse (aHom w)) (le_cylIn_cylRetr (aHom w)) p
  have he := hle.2
  have hp := coneAdjCoverBaseEnd_spec (projection w gen hrel) p
  have hr := coneAdjCoverBaseEnd_spec (projection w gen hrel) r
  change p.val.sheet * (Coc w gen hrel).val p.val.point r.val.point = r.val.sheet at he
  change ConeAdj.inc (cylinderProjection w gen hrel p) = p.val.point at hp
  change ConeAdj.inc (cylinderProjection w gen hrel r) = r.val.point at hr
  have hr2 : cylinderProjection w gen hrel r =
      cylCollapse (aHom w) (cylinderProjection w gen hrel p) :=
    cylinderCoverCollapse_projection w (cylinderCovering w gen hrel) p
  rw [← hp, ← hr, hr2] at he
  change p.val.sheet * roseVal gen
    (cylRetr (aHom w) (cylinderProjection w gen hrel p))
    (cylRetr (aHom w) (cylCollapse (aHom w) (cylinderProjection w gen hrel p))) =
      r.val.sheet at he
  simpa only [cylCollapse, cylRetr, cylIn, Sum.elim_inl, id_eq, roseVal_self, mul_one] using he.symm

/-- The actual cone trivialisation determines every lifted circle sheet. -/
theorem circleInclusion_sheet (p : PresCoverRelator w (projection w gen hrel))
    (x : RelatorCircle w p.val.2) :
    (presCoverCircleInclusion w (projection w gen hrel) (covering w gen hrel) p x).sheet =
      p.val.1.sheet * (trivFun w gen p.val.2 (cylOuter (aHom w) x.val))⁻¹ := by
  have hle := (presCoverCircleInclusion_lt_apex w (projection w gen hrel)
    (covering w gen hrel) p x).le
  have he := hle.2
  have hx := presCoverConeCircleOrderIso_symm_projection w (projection w gen hrel)
    (covering w gen hrel) p.val.1 p.val.2 p.property x
  change _ * (Coc w gen hrel).val _ _ = p.val.1.sheet at he
  change (presCoverCircleInclusion w (projection w gen hrel) (covering w gen hrel) p x).point =
    iCirc w x.val at hx
  have hp : p.val.1.point = apexOf w p.val.2 := p.property
  rw [hx, hp] at he
  change _ * trivFun w gen p.val.2 (cylOuter (aHom w) x.val) = p.val.1.sheet at he
  rw [← he]
  simp only [mul_assoc, mul_inv_cancel, mul_one]

/-- Actual midpoint sheet equals the signed-letter Fox prefix, including inverse letters. -/
theorem relatorLetterMidpoint_sheet (p : PresCoverRelator w (projection w gen hrel))
    (k : Fin (w p.val.2).length) :
    generatorEquiv w gen hrel
      (roseCoverMidpointEdge (roseProjection w gen hrel) (roseCovering w gen hrel)
        (presCoverRelatorLetterMidpoint w (projection w gen hrel) (covering w gen hrel) p k)) =
      (p.val.1.sheet * prefixVal w gen p.val.2 k.val *
        (if ((w p.val.2)[k.val]).2 then 1 else (gen ((w p.val.2)[k.val]).1)⁻¹),
        ((w p.val.2)[k.val]).1) := by
  rw [generatorEquiv_midpoint]
  refine Prod.ext ?_ rfl
  change (cylinderCoverCollapse w (cylinderCovering w gen hrel)
    (presCoverCircleCylinderInclusion w (projection w gen hrel) (covering w gen hrel) p
      (relatorCirclePoint w p.val.2 k CPos.cmid))).val.sheet = _
  rw [cylinderCollapse_sheet]
  change (presCoverCircleInclusion w (projection w gen hrel) (covering w gen hrel) p
    (relatorCirclePoint w p.val.2 k CPos.cmid)).sheet = _
  rw [circleInclusion_sheet]
  have ha := aFun_pt_cedgL_of_get w (List.getElem?_eq_getElem k.isLt)
  change p.val.1.sheet *
    ((roseVal gen Rose.base (aFun w (TCirc.pt w p.val.2 k.val CPos.cedgL)))⁻¹ *
      (prefixVal w gen p.val.2 k.val)⁻¹)⁻¹ = _
  rw [ha]
  cases hb : ((w p.val.2)[k.val]).2 <;>
    simp [roseVal, mul_inv_rev, mul_assoc]

/-- All coordinate changes are linear equivalences of finitely supported chains. -/
noncomputable def relatorCoordinates :
    (PresCoverRelator w (projection w gen hrel) →₀ ℤ) ≃ₗ[ℤ] ((G × J) →₀ ℤ) :=
  Finsupp.domLCongr (relatorEquiv w gen hrel)

noncomputable def generatorCoordinates :
    (roseCoverGeneratorEdges (roseProjection w gen hrel) (roseCovering w gen hrel) →₀ ℤ)
      ≃ₗ[ℤ] ((G × α) →₀ ℤ) := Finsupp.domLCongr (generatorEquiv w gen hrel)

theorem relatorCoordinates_single (p : PresCoverRelator w (projection w gen hrel)) (n : ℤ) :
    relatorCoordinates w gen hrel (Finsupp.single p n) =
      Finsupp.single (p.val.1.sheet, p.val.2) n :=
  Finsupp.domLCongr_single _ _ _

theorem generatorCoordinates_single
    (p : roseCoverGeneratorEdges (roseProjection w gen hrel) (roseCovering w gen hrel)) (n : ℤ) :
    generatorCoordinates w gen hrel (Finsupp.single p n) =
      Finsupp.single (generatorEquiv w gen hrel p) n :=
  Finsupp.domLCongr_single _ _ _

end FiniteChains.PresModel.PresCocycleCover
