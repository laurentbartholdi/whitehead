module

public import RequestProject.PresCoverRoseFibreEquiv
public import RequestProject.PresUniversalGroupCoordinates
public import RequestProject.PresUniversalRelatorDeck
public import RequestProject.RoseCoverGeneratorEquiv

@[expose] public section

namespace FiniteChains.PresModel
open Comb
universe u
variable {α J : Type u} (ρ : J → FreeGroup α) (w : J → List (α × Bool))
  (hw : ∀ j, FreeGroup.mk (w j) = ρ j) (hpos : ∀ j, 0 < (w j).length)

/-- Reading coordinates on an actual universal rose-cover midpoint fibre. -/
noncomputable def presUniversalRoseMidpointFibreEquiv (i : α) :
    {p : cylinderCoverRoseSet w
      (coneAdjCoverBaseEnd (uOrderEnd (P := PresPos w) (a := ptBase w))) //
      cylinderCoverRoseEnd w (coneAdjCoverBaseEnd uOrderEnd) p = Rose.mid i} ≃ PresGroup ρ :=
  (presCoverRoseFibreEquiv w uOrderEnd (Rose.mid i)).trans
    (presUniversalFibreGroupEquiv ρ w hw hpos (iRose w (Rose.mid i)))

/-- Actual universal lifted midpoints are indexed by their reading and generator label. -/
noncomputable def presUniversalMidpointGroupEquiv :
    roseCoverMidpoints (cylinderCoverRoseEnd w
      (coneAdjCoverBaseEnd (uOrderEnd (P := PresPos w) (a := ptBase w)))) ≃ PresGroup ρ × α where
  toFun p := (presUniversalRoseMidpointFibreEquiv ρ w hw hpos p.val.2
    ⟨p.val.1, p.property⟩, p.val.2)
  invFun q :=
    let p := (presUniversalRoseMidpointFibreEquiv ρ w hw hpos q.2).symm q.1
    ⟨(p.val, q.2), p.property⟩
  left_inv p := by
    apply Subtype.ext
    apply Prod.ext
    · exact congrArg Subtype.val
        ((presUniversalRoseMidpointFibreEquiv ρ w hw hpos p.val.2).symm_apply_apply
          ⟨p.val.1, p.property⟩)
    · rfl
  right_inv q := by
    apply Prod.ext
    · exact (presUniversalRoseMidpointFibreEquiv ρ w hw hpos q.2).apply_symm_apply q.1
    · rfl

/-- Selected actual universal rose edges have the same genuine group-generator coordinates. -/
noncomputable def presUniversalGeneratorGroupEquiv :
    roseCoverGeneratorEdges (cylinderCoverRoseEnd w
      (coneAdjCoverBaseEnd (uOrderEnd (P := PresPos w) (a := ptBase w))))
      (cylinderCoverRoseEnd_isPosetCover w _
        (coneAdjCoverBaseEnd_isPosetCover _ (presUniversalEnd_isPosetCover w hpos))) ≃
      PresGroup ρ × α :=
  (roseCoverMidpointEdgeEquiv _
    (cylinderCoverRoseEnd_isPosetCover w _
      (coneAdjCoverBaseEnd_isPosetCover _ (presUniversalEnd_isPosetCover w hpos)))).symm.trans
    (presUniversalMidpointGroupEquiv ρ w hw hpos)

/-- Finite selected-edge coefficients in actual group-generator coordinates. -/
noncomputable def presUniversalGeneratorGroupChainEquiv :
    (roseCoverGeneratorEdges (cylinderCoverRoseEnd w
      (coneAdjCoverBaseEnd (uOrderEnd (P := PresPos w) (a := ptBase w))))
      (cylinderCoverRoseEnd_isPosetCover w _
        (coneAdjCoverBaseEnd_isPosetCover _ (presUniversalEnd_isPosetCover w hpos))) →₀ ℤ) ≃ₗ[ℤ]
      (PresGroup ρ × α →₀ ℤ) :=
  Finsupp.domLCongr (R := ℤ) (M := ℤ) (presUniversalGeneratorGroupEquiv ρ w hw hpos)

end FiniteChains.PresModel
