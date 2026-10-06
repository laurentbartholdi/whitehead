module

public import RequestProject.CylinderCoverCollapsedLetterCoefficients
public import RequestProject.PresCoverRelatorGeneratorBoundary

@[expose] public section

namespace FiniteChains.PresModel
open Comb
universe u
variable {α J P : Type u} [PartialOrder P] (w : J → List (α × Bool))
  (f : P → PresPos w) (hf : IsPosetCover f)

/-- The genuine cylinder projection of a lifted attaching circle is the actual outer circle. -/
theorem presCoverCircleCylinderInclusion_projection (p : PresCoverRelator w f)
    (x : RelatorCircle w p.val.2) :
    coneAdjCoverBaseEnd f (presCoverCircleCylinderInclusion w f hf p x) =
      cylOuter (aHom w) x.val := by
  apply Sum.inl.inj
  exact (coneAdjCoverBaseEnd_spec f _).trans
    (presCoverConeCircleOrderIso_symm_projection w f hf p.val.1 p.val.2 p.property x)

/-- Actual collapsed lifted-letter midpoints for a genuine lifted relator. -/
noncomputable def presCoverRelatorLetterMidpoint (p : PresCoverRelator w f)
    (k : Fin (w p.val.2).length) :=
  cylinderCoverCollapsedLetterMidpoint w p.val.2 (coneAdjCoverBaseEnd f)
    (coneAdjCoverBaseEnd_isPosetCover f hf) (presCoverCircleCylinderInclusion w f hf p)
      (presCoverCircleCylinderInclusion_projection w f hf p) k

/-- The actual relator generator-boundary column is its signed actual lifted-letter sum. -/
theorem presCoverRelatorGeneratorBoundary_single (p : PresCoverRelator w f) :
    presCoverRelatorGeneratorBoundary w f hf (Finsupp.single p 1) =
      ∑ k : Fin (w p.val.2).length,
        (if ((w p.val.2)[k.val]).2 then (1 : ℤ) else -1) •
          Finsupp.single (roseCoverMidpointEdge
            (cylinderCoverRoseEnd w (coneAdjCoverBaseEnd f))
            (cylinderCoverRoseEnd_isPosetCover w (coneAdjCoverBaseEnd f)
              (coneAdjCoverBaseEnd_isPosetCover f hf))
            (presCoverRelatorLetterMidpoint w f hf p k)) 1 := by
  classical
  change cylinderCoverCollapsedGeneratorCoordinates w (coneAdjCoverBaseEnd f)
    (coneAdjCoverBaseEnd_isPosetCover f hf)
      (presCoverCylinderRelatorBoundaryChain w f hf (Finsupp.single p 1)) = _
  rw [presCoverCylinderRelatorBoundaryChain, Finsupp.linearCombination_single, one_smul]
  exact cylinderCoverCollapsedCircle_coordinates w p.val.2 (coneAdjCoverBaseEnd f)
    (coneAdjCoverBaseEnd_isPosetCover f hf) (presCoverCircleCylinderInclusion w f hf p)
    (presCoverCircleCylinderInclusion_strictMono w f hf p)
    (presCoverCircleCylinderInclusion_projection w f hf p)

end FiniteChains.PresModel
