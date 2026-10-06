module

public import RequestProject.OrderUniversalTetLift
public import RequestProject.PresPosetCoverDimension
public import RequestProject.PresUniversalRelatorCoordinates
public import RequestProject.OrderNormalizationHomotopy
public import RequestProject.OrderUniversalPosetThree

@[expose] public section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

set_option maxHeartbeats 800000

namespace FiniteChains.Comb
universe u
variable {P : Type u} [PartialOrder P] {a : P}

/-- An actual cover cycle differs from its genuine strict normalization by an
explicit genuine lifted nerve three-boundary. -/
theorem uOrderNormalizeChain2_cycle_boundary (c : UF (orderCx P) a →₀ ℤ)
    (hc : bdry2 (uCover (orderCx P) a) c = 0) :
    ∃ y : UOrdTet P a →₀ ℤ,
      uOrdBoundary3 y = c - Finsupp.mapDomain uOrderFace (ordStrictInclusion2 (uOrderNormalizeChain2 c)) := by
  let d := uOrderChain2Equiv.symm c
  have he : chain2 uOrderHom d = c := uOrderChain2Equiv.apply_symm_apply c
  have hd : FiniteChains.Comb.bdry2 (orderCx (UOrder P a)) d = 0 :=
    (uOrderHom_cycle_iff d).mp (he.symm ▸ hc)
  have h := congrArg (chain2 (uOrderHom (P := P) (a := a)))
    (ordNormalization_cycle_boundary d hd)
  rw (config := { transparency := .default }) [map_sub, uOrderHom_ordBoundary3, he] at h
  exact ⟨Finsupp.mapDomain uOrderTet (ordNormalizationHomotopy2 d), h.symm⟩

end FiniteChains.Comb

namespace FiniteChains.PresModel
open Comb
universe u
variable {α J : Type u} (w : J → List (α × Bool))
  (hpos : ∀ j, 0 < (w j).length)

/-- Equal finite actual relator coordinates of cover cycles give an actual
three-boundary for their difference. -/
theorem presUniversalRelatorCoordinates_equal_boundary
    (c d : UF (orderCx (PresPos w)) (ptBase w) →₀ ℤ)
    (hc : Comb.bdry2 (uCover (orderCx (PresPos w)) (ptBase w)) c = 0)
    (hd : Comb.bdry2 (uCover (orderCx (PresPos w)) (ptBase w)) d = 0)
    (he : presUniversalRelatorCoordinates w hpos c =
      presUniversalRelatorCoordinates w hpos d) :
    ∃ y : UOrdTet (PresPos w) (ptBase w) →₀ ℤ, uOrdBoundary3 y = c - d := by
  have hn := presUniversalRelatorCoordinates_cycle_ext w hpos c d hc hd he
  have hcd : Comb.bdry2 (uCover (orderCx (PresPos w)) (ptBase w)) (c - d) = 0 := by
    rw (config := { transparency := .default }) [map_sub, hc, hd, sub_self]
  obtain ⟨y, hy⟩ := uOrderNormalizeChain2_cycle_boundary (c - d) hcd
  rw (config := { transparency := .default }) [map_sub, hn, sub_self, map_zero, Finsupp.mapDomain_zero, sub_zero] at hy
  exact ⟨y, hy⟩

/-- Genuine lifted three-boundaries have zero actual relator coordinates. -/
theorem presUniversalRelatorCoordinates_boundary_zero
    (y : UOrdTet (PresPos w) (ptBase w) →₀ ℤ) :
    presUniversalRelatorCoordinates w hpos (uOrdBoundary3 y) = 0 := by
  obtain ⟨d, rfl⟩ := exists_uOrder_three_chain y
  rw (config := { transparency := .default }) [← uOrderHom_ordBoundary3]
  change presCoverRelatorChain w uOrderEnd (presUniversalEnd_isPosetCover w hpos) hpos
    (normalizeOrdChain2 (uOrderChain2Equiv.symm (uOrderChain2Equiv (ordBoundary3 d)))) = 0
  rw (config := { transparency := .default }) [uOrderChain2Equiv.symm_apply_apply,
    presPos_cover_normalized_three_boundary_zero w (ptBase w), map_zero]

/-- Actual cover cycles have zero relator coordinates exactly when they are
actual finite lifted nerve three-boundaries. -/
theorem presUniversalRelatorCoordinates_zero_iff_boundary
    (c : UF (orderCx (PresPos w)) (ptBase w) →₀ ℤ)
    (hc : Comb.bdry2 (uCover (orderCx (PresPos w)) (ptBase w)) c = 0) :
    presUniversalRelatorCoordinates w hpos c = 0 ↔
      ∃ y : UOrdTet (PresPos w) (ptBase w) →₀ ℤ, uOrdBoundary3 y = c := by
  constructor
  · intro he
    have hz : Comb.bdry2 (uCover (orderCx (PresPos w)) (ptBase w)) 0 = 0 := map_zero _
    obtain ⟨y, hy⟩ := presUniversalRelatorCoordinates_equal_boundary w hpos c 0 hc hz
      (he.trans (map_zero _).symm)
    exact ⟨y, by simpa only [sub_zero] using hy⟩
  · rintro ⟨y, rfl⟩
    exact presUniversalRelatorCoordinates_boundary_zero w hpos y

/-- Actual relator coordinates distinguish precisely the actual degree-two cycle classes. -/
theorem presUniversalRelatorCoordinates_eq_iff_boundary
    (c d : UF (orderCx (PresPos w)) (ptBase w) →₀ ℤ)
    (hc : Comb.bdry2 (uCover (orderCx (PresPos w)) (ptBase w)) c = 0)
    (hd : Comb.bdry2 (uCover (orderCx (PresPos w)) (ptBase w)) d = 0) :
    presUniversalRelatorCoordinates w hpos c = presUniversalRelatorCoordinates w hpos d ↔
      ∃ y : UOrdTet (PresPos w) (ptBase w) →₀ ℤ, uOrdBoundary3 y = c - d := by
  have hcd : Comb.bdry2 (uCover (orderCx (PresPos w)) (ptBase w)) (c - d) = 0 := by
    rw (config := { transparency := .default }) [map_sub, hc, hd, sub_self]
  rw (config := { transparency := .default }) [← sub_eq_zero, ← map_sub]
  exact presUniversalRelatorCoordinates_zero_iff_boundary w hpos (c - d) hcd

end FiniteChains.PresModel
