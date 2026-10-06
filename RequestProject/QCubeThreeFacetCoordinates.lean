module

public import RequestProject.QCubeFacetIndex

@[expose] public section

/-! Exact coefficient coordinates for finite chains on the six actual facets of a three-cube. -/
namespace FiniteChains.Davis
open RACG Mirror Comb
variable {V : Type} [DecidableEq V] {A : CommRel V}

noncomputable def qThreeFacetCoordinates (c : QCube A) (hc : c.spx.card = 3) :
    (QSquare A →₀ ℤ) →ₗ[ℤ] (({v : V // v ∈ c.spx} × ZMod 2) →₀ ℤ) :=
  Finsupp.lcomapDomain (qThreeFacetSquare c hc) (qThreeFacetSquare_injective c hc)

theorem qThreeFacetCoordinates_apply (c : QCube A) (hc : c.spx.card = 3)
    (r : QSquare A →₀ ℤ) (i : {v : V // v ∈ c.spx} × ZMod 2) :
    qThreeFacetCoordinates c hc r i = r (qThreeFacetSquare c hc i) := rfl

/-- The six actual facet coefficients reconstruct every chain supported below the three-cube. -/
theorem qThreeFacetCoordinates_reconstruct (c : QCube A) (hc : c.spx.card = 3)
    (r : QSquare A →₀ ℤ) (hr : ∀ s ∈ r.support, s.1 < c) :
    Finsupp.mapDomain (qThreeFacetSquare c hc) (qThreeFacetCoordinates c hc r) = r := by
  apply Finsupp.mapDomain_comapDomain _ (qThreeFacetSquare_injective c hc)
  intro s hs
  exact qThreeFacetSquare_exhaustive c hc s (hr s hs)

theorem qThreeFacetCoordinates_single (c : QCube A) (hc : c.spx.card = 3)
    (i : {v : V // v ∈ c.spx} × ZMod 2) (n : ℤ) :
    qThreeFacetCoordinates c hc (Finsupp.single (qThreeFacetSquare c hc i) n) =
      Finsupp.single i n :=
  Finsupp.comapDomain_single _ _ _ (qThreeFacetSquare_injective c hc).injOn

/-- Coefficient extraction is a left inverse on all finite indexed facet chains. -/
theorem qThreeFacetCoordinates_mapDomain (c : QCube A) (hc : c.spx.card = 3)
    (r : ({v : V // v ∈ c.spx} × ZMod 2) →₀ ℤ) :
    qThreeFacetCoordinates c hc (Finsupp.mapDomain (qThreeFacetSquare c hc) r) = r :=
  Finsupp.comapDomain_mapDomain _ (qThreeFacetSquare_injective c hc) _

omit [DecidableEq V] in
theorem qThreeFacetIndex_card (c : QCube A) (hc : c.spx.card = 3) :
    Fintype.card ({v : V // v ∈ c.spx} × ZMod 2) = 6 := by
  simp [hc]

end FiniteChains.Davis
