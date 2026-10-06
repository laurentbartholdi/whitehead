import RequestProject.PresCylinderRoseCover
import RequestProject.ConeAdjBaseCover

namespace FiniteChains.PresModel
open Comb
universe u
variable {α J P : Type u} [PartialOrder P] (w : J → List (α × Bool))
  (f : P → PresPos w)

/-- The actual rose-preimage fibre is exactly the corresponding presentation-cover fibre. -/
noncomputable def presCoverRoseFibreEquiv (x : Rose α) :
    {p : cylinderCoverRoseSet w (coneAdjCoverBaseEnd f) //
      cylinderCoverRoseEnd w (coneAdjCoverBaseEnd f) p = x} ≃
    {p : P // f p = iRose w x} where
  toFun p := ⟨p.val.val.val, by
    have h := cylinderCoverRoseEnd_projection w (coneAdjCoverBaseEnd f) p.val
    rw [p.property] at h
    exact (coneAdjCoverBaseEnd_spec f p.val.val).symm.trans (congrArg ConeAdj.inc h.symm)⟩
  invFun p := by
    let b : {p : P // f p ∈ coneAdjBaseSet (S := circSet w)} :=
      ⟨p.val, cylIn (aHom w) x, p.property.symm⟩
    have hb : coneAdjCoverBaseEnd f b = cylIn (aHom w) x :=
      Sum.inl.inj ((coneAdjCoverBaseEnd_spec f b).trans p.property)
    let q : cylinderCoverRoseSet w (coneAdjCoverBaseEnd f) := ⟨b, x, hb⟩
    refine ⟨q, ?_⟩
    exact cylIn_injective (aHom w)
      ((cylinderCoverRoseEnd_projection w (coneAdjCoverBaseEnd f) q).trans hb)
  left_inv p := by
    apply Subtype.ext
    apply Subtype.ext
    apply Subtype.ext
    rfl
  right_inv p := by
    apply Subtype.ext
    rfl

end FiniteChains.PresModel
