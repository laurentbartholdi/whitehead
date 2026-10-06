import RequestProject.CombPi2
import RequestProject.CellularHomotopyChain

/-! Lifted finite chain witnesses for actual path homotopies and their cellular images. -/
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains.Comb
universe u
variable {X Y : Complex2.{u}} (a : X.V) (f : Hom X Y)

/-- Projection of an actual lifted two-chain agrees with the ordinary cellular image. -/
theorem hurewicz_univLift_chain2 (d : (uCover X a).F →₀ ℤ) :
    hurewicz Y (f.onV a) (chain2 (univLift X f a) d) =
      chain2 f (hurewicz X a d) := by
  change Finsupp.mapDomain (univProj Y (f.onV a)).onF
    (Finsupp.mapDomain (univLift X f a).onF d) =
      Finsupp.mapDomain f.onF (Finsupp.mapDomain (univProj X a).onF d)
  rw [← Finsupp.mapDomain_comp, ← Finsupp.mapDomain_comp]
  rfl

/-- A homotopy lifts to a finite chain correction, whose cellular image has the exact boundary. -/
theorem exists_mapped_lifted_homotopy_chain {v : UV X a} {p q : List (X.E × Bool)} {b : X.V}
    (hp : IsPath X.src X.tgt p (endV v) b) (h : Htpy X (endV v) b p q) :
    ∃ d : (uCover X a).F →₀ ℤ,
      bdry2 (uCover Y (f.onV a)) (chain2 (univLift X f a) d) =
        pathChain (uLiftPath (mapPath f p) (univLiftV a f v)) -
          pathChain (uLiftPath (mapPath f q) (univLiftV a f v)) := by
  obtain ⟨d, hd⟩ := (htpy_uLiftPath hp h).exists_boundary
  refine ⟨d, ?_⟩
  rw [bdry2_chain2, hd, map_sub]
  have key (r : List (X.E × Bool)) (hr : IsPath X.src X.tgt r (endV v) b) :
      chain1 (univLift X f a) (pathChain (uLiftPath r v)) =
        pathChain (uLiftPath (mapPath f r) (univLiftV a f v)) := by
    change Finsupp.mapDomain (univLift X f a).onE (pathChain _) = _
    rw [← pathChain_map]
    exact congrArg pathChain (uLiftPath_univLiftV a f r v b hr).symm
  rw [key p hp, key q (h.isPath hp)]

end FiniteChains.Comb
