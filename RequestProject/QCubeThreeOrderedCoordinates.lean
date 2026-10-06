import RequestProject.QCubeThreeGeometricKernel

/-! Exact coefficient coordinates for finite chains on the six actual facets of a three-cube. -/
namespace FiniteChains.Davis
open RACG Mirror Comb
variable {V : Type} [DecidableEq V] {A : CommRel V}

noncomputable def qThreeOrderedCoordinates (c : QCube A) (u v w : V) (huv : u ≠ v) (huw : u ≠ w) (hvw : v ≠ w) (hs : c.spx = {u, v, w}) :
    (QSquare A →₀ ℤ) →ₗ[ℤ] ((Fin 3 × ZMod 2) →₀ ℤ) :=
  Finsupp.lcomapDomain (qThreeFaceSquare c u v w huv huw hvw hs) (qThreeFaceSquare_injective c u v w huv huw hvw hs)

theorem qThreeOrderedCoordinates_apply (c : QCube A) (u v w : V) (huv : u ≠ v) (huw : u ≠ w) (hvw : v ≠ w) (hs : c.spx = {u, v, w})
    (r : QSquare A →₀ ℤ) (i : Fin 3 × ZMod 2) :
    qThreeOrderedCoordinates c u v w huv huw hvw hs r i = r (qThreeFaceSquare c u v w huv huw hvw hs i) := rfl

/-- The six actual facet coefficients reconstruct every chain supported below the three-cube. -/
theorem qThreeOrderedCoordinates_reconstruct (c : QCube A) (u v w : V) (huv : u ≠ v) (huw : u ≠ w) (hvw : v ≠ w) (hs : c.spx = {u, v, w})
    (r : QSquare A →₀ ℤ) (hr : ∀ s ∈ r.support, s.1 < c) :
    Finsupp.mapDomain (qThreeFaceSquare c u v w huv huw hvw hs) (qThreeOrderedCoordinates c u v w huv huw hvw hs r) = r := by
  apply Finsupp.mapDomain_comapDomain _ (qThreeFaceSquare_injective c u v w huv huw hvw hs)
  intro s hmem
  exact qThreeFaceSquare_exhaustive c u v w huv huw hvw hs s (hr s hmem)

theorem qThreeOrderedCoordinates_single (c : QCube A) (u v w : V) (huv : u ≠ v) (huw : u ≠ w) (hvw : v ≠ w) (hs : c.spx = {u, v, w})
    (i : Fin 3 × ZMod 2) (n : ℤ) :
    qThreeOrderedCoordinates c u v w huv huw hvw hs (Finsupp.single (qThreeFaceSquare c u v w huv huw hvw hs i) n) =
      Finsupp.single i n :=
  Finsupp.comapDomain_single _ _ _ (qThreeFaceSquare_injective c u v w huv huw hvw hs).injOn

/-- Coefficient extraction is a left inverse on all finite indexed facet chains. -/
theorem qThreeOrderedCoordinates_mapDomain (c : QCube A) (u v w : V) (huv : u ≠ v) (huw : u ≠ w) (hvw : v ≠ w) (hs : c.spx = {u, v, w})
    (r : (Fin 3 × ZMod 2) →₀ ℤ) :
    qThreeOrderedCoordinates c u v w huv huw hvw hs (Finsupp.mapDomain (qThreeFaceSquare c u v w huv huw hvw hs) r) = r :=
  Finsupp.comapDomain_mapDomain _ (qThreeFaceSquare_injective c u v w huv huw hvw hs) _

end FiniteChains.Davis
