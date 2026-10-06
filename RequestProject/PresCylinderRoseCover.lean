module

public import RequestProject.PresCylinderCoverRose
public import RequestProject.PosetCoverRestriction
public import RequestProject.PosetCoverTargetIso

@[expose] public section

namespace FiniteChains.PresModel
open Comb
universe u
variable {α J : Type u} (w : J → List (α × Bool))

def cylinderRoseSet : Set (CylBase w) := {p | ∃ x : Rose α, p = cylIn (aHom w) x}

def cylinderRoseInclusion (x : Rose α) : cylinderRoseSet w :=
  ⟨cylIn (aHom w) x, x, rfl⟩

theorem cylinderRoseInclusion_injective : Function.Injective (cylinderRoseInclusion w) := by
  intro x y h
  exact Sum.inl.inj (congrArg Subtype.val h)

theorem cylinderRoseInclusion_surjective : Function.Surjective (cylinderRoseInclusion w) := by
  rintro ⟨p, x, hx⟩
  exact ⟨x, Subtype.ext hx.symm⟩

/-- The actual inner end of the cylinder is order isomorphic to the actual rose. -/
noncomputable def cylinderRoseOrderIso : Rose α ≃o cylinderRoseSet w where
  toEquiv := Equiv.ofBijective (cylinderRoseInclusion w)
    ⟨cylinderRoseInclusion_injective w, cylinderRoseInclusion_surjective w⟩
  map_rel_iff' := by intro x y; rfl

variable {P : Type u} [PartialOrder P] (f : P → CylBase w)

/-- The actual projection from the actual rose preimage to the actual rose. -/
noncomputable def cylinderCoverRoseEnd (p : cylinderCoverRoseSet w f) : Rose α :=
  (cylinderRoseOrderIso w).symm ⟨f p.val, p.property⟩

theorem cylinderCoverRoseEnd_isPosetCover (hf : IsPosetCover f) :
    IsPosetCover (cylinderCoverRoseEnd w f) :=
  (hf.restriction f (cylinderRoseSet w)).postcompose_orderIso (cylinderRoseOrderIso w).symm

omit [PartialOrder P] in
theorem cylinderCoverRoseEnd_projection (p : cylinderCoverRoseSet w f) :
    cylIn (aHom w) (cylinderCoverRoseEnd w f p) = f p.val := by
  exact congrArg Subtype.val ((cylinderRoseOrderIso w).apply_symm_apply ⟨f p.val, p.property⟩)

end FiniteChains.PresModel
