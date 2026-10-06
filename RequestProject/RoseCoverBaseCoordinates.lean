module

public import RequestProject.PosetCoverEdgeFibreEquiv
public import RequestProject.RoseCoverGeneratorEquiv

@[expose] public section

namespace FiniteChains.PresModel
open Comb
universe u
variable {α P : Type u} [PartialOrder P] (f : P → Rose α) (hf : IsPosetCover f)

/-- The actual fibre over the unique rose base vertex. -/
def roseCoverBaseFibre := {p : P // f p = Rose.base}

/-- Transport from a midpoint to a base point along the two false-end incidences. -/
noncomputable def roseCoverMidpointBaseEquiv (i : α) :
    {p : P // f p = Rose.mid i} ≃ roseCoverBaseFibre f :=
  (hf.strictEdgeFibreEquiv (roseMidEdge i false)).trans
    (hf.strictEdgeFibreEquiv (roseBaseEdge i false)).symm

/-- Actual lifted midpoint coordinates are indexed by the actual base fibre and generators. -/
noncomputable def roseCoverMidpointsBaseEquiv :
    roseCoverMidpoints f ≃ roseCoverBaseFibre f × α where
  toFun p := (roseCoverMidpointBaseEquiv f hf p.val.2 ⟨p.val.1, p.property⟩, p.val.2)
  invFun p := ⟨((roseCoverMidpointBaseEquiv f hf p.2).symm p.1, p.2),
    ((roseCoverMidpointBaseEquiv f hf p.2).symm p.1).property⟩
  left_inv p := by
    apply Subtype.ext
    apply Prod.ext
    · exact congrArg Subtype.val ((roseCoverMidpointBaseEquiv f hf p.val.2).symm_apply_apply
        ⟨p.val.1, p.property⟩)
    · rfl
  right_inv p := by
    apply Prod.ext
    · exact (roseCoverMidpointBaseEquiv f hf p.2).apply_symm_apply p.1
    · rfl

/-- Actual finite generator coefficients indexed by the actual base fibre and generator set. -/
noncomputable def roseCoverBaseCoordinates :
    (StrictOrdEdge P →₀ ℤ) →ₗ[ℤ] ((roseCoverBaseFibre f × α) →₀ ℤ) :=
  (Finsupp.domLCongr (R := ℤ) (M := ℤ) (roseCoverMidpointsBaseEquiv f hf)).toLinearMap.comp
    (roseCoverMidpointCoordinates f hf)

/-- Base-fibre generator coordinates detect genuine one-cycles without a choice of group model. -/
theorem roseCoverBaseCoordinates_cycle_injective :
    Function.Injective ((roseCoverBaseCoordinates f hf).comp
      (LinearMap.ker (FiniteChains.Comb.bdry1 (strictOrderCx P))).subtype) := by
  intro c d h
  apply roseCoverMidpointCoordinates_cycle_injective f hf
  apply (Finsupp.domLCongr (R := ℤ) (M := ℤ) (roseCoverMidpointsBaseEquiv f hf)).injective
  exact h

end FiniteChains.PresModel
