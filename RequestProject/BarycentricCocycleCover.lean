import RequestProject.OrderCocycleCover
import RequestProject.BarycentricCocycleDescent
import RequestProject.BarycentricTwoChains
import RequestProject.ConeAdjPoset
import RequestProject.UniversalOrderChainBridge

/-! The actual barycentric realization of a descended surface cover in the
original universal order cover. Pending final Lean verification. -/

noncomputable section
open scoped Classical
namespace FiniteChains.Davis
open RACG Mirror Comb
universe u
variable {P Q G : Type u} [PartialOrder P] [PartialOrder Q] [Group G]
  (f : NeSpx (cmpRel P) → Q) (hf : Monotone f)
  (c : OrdCocycle Q G) (a : Q) (hc : IsConnected (orderCx Q))
  (hm : Function.Bijective (c.monodromy a))

def descendedSurfaceCocycle : OrdCocycle P G :=
  barycentricCocycle (c.comap f hf)

abbrev DescendedSurfaceCover := (descendedSurfaceCocycle f hf c).Cover

def descendedSurfaceProjection : DescendedSurfaceCover f hf c → P :=
  OrdCocycle.Cover.point

theorem descendedSurfaceProjection_isPosetCover :
    IsPosetCover (descendedSurfaceProjection f hf c) :=
  (descendedSurfaceCocycle f hf c).coverProjection_isPosetCover

def descendedSurfaceSimplex
    (σ : NeSpx (cmpRel (DescendedSurfaceCover f hf c))) : NeSpx (cmpRel P) :=
  barycentricMap (descendedSurfaceProjection f hf c)
    (descendedSurfaceProjection_isPosetCover f hf c).mono σ

theorem descendedSurfaceSimplex_monotone : Monotone (descendedSurfaceSimplex f hf c) :=
  barycentricMap_monotone _ (descendedSurfaceProjection_isPosetCover f hf c).mono

theorem descendedSurfaceSimplex_top
    (σ : NeSpx (cmpRel (DescendedSurfaceCover f hf c))) :
    (chainMax σ).point ∈ (descendedSurfaceSimplex f hf c σ).1 :=
  Finset.mem_image.mpr ⟨chainMax σ, chainMax_mem σ, rfl⟩

def barycentricCoverReading
    (σ : NeSpx (cmpRel (DescendedSurfaceCover f hf c))) : G :=
  (chainMax σ).sheet * c.val (f (spx1 (chainMax σ).point))
    (f (descendedSurfaceSimplex f hf c σ))

/-- The top of each lifted simplex fixes the sheet of the whole flag. -/
def barycentricCoverRealization
    (σ : NeSpx (cmpRel (DescendedSurfaceCover f hf c))) : UOrder Q a :=
  c.pointReading a hc hm (f (descendedSurfaceSimplex f hf c σ))
    (barycentricCoverReading f hf c σ)

theorem barycentricCoverRealization_end
    (σ : NeSpx (cmpRel (DescendedSurfaceCover f hf c))) :
    uOrderEnd (barycentricCoverRealization f hf c a hc hm σ) =
      f (descendedSurfaceSimplex f hf c σ) :=
  c.pointReading_end a hc hm _ _

theorem barycentricCoverRealization_read
    (σ : NeSpx (cmpRel (DescendedSurfaceCover f hf c))) :
    c.readVertex a (barycentricCoverRealization f hf c a hc hm σ) =
      barycentricCoverReading f hf c σ :=
  c.pointReading_read a hc hm _ _

theorem barycentricCoverRealization_monotone :
    Monotone (barycentricCoverRealization f hf c a hc hm) := by
  intro σ τ hστ
  have htop := chainMax_monotone hστ
  have hσ : spx1 (chainMax σ).point ≤ descendedSurfaceSimplex f hf c σ := by
    intro p hp
    simp only [spx1_val, Finset.mem_singleton] at hp
    subst p
    exact descendedSurfaceSimplex_top f hf c σ
  have hτ : descendedSurfaceSimplex f hf c σ ≤ descendedSurfaceSimplex f hf c τ :=
    descendedSurfaceSimplex_monotone f hf c hστ
  have hmσ : (chainMax σ).point ∈ (descendedSurfaceSimplex f hf c τ).1 :=
    hτ (descendedSurfaceSimplex_top f hf c σ)
  have hread := edgeHop_read_via (c.comap f hf) htop.1
    (descendedSurfaceSimplex f hf c τ) hmσ (descendedSurfaceSimplex_top f hf c τ)
  have hval : (descendedSurfaceCocycle f hf c).val (chainMax σ).point (chainMax τ).point =
      c.val (f (spx1 (chainMax σ).point)) (f (descendedSurfaceSimplex f hf c τ)) *
        (c.val (f (spx1 (chainMax τ).point)) (f (descendedSurfaceSimplex f hf c τ)))⁻¹ := by
    exact (barycentricCocycle_val (c.comap f hf) htop.1).trans hread
  apply c.pointReading_le a hc hm (hf hτ)
  change ((chainMax σ).sheet * c.val (f (spx1 (chainMax σ).point))
      (f (descendedSurfaceSimplex f hf c σ))) *
      c.val (f (descendedSurfaceSimplex f hf c σ)) (f (descendedSurfaceSimplex f hf c τ)) =
    (chainMax τ).sheet * c.val (f (spx1 (chainMax τ).point))
      (f (descendedSurfaceSimplex f hf c τ))
  calc
    _ = (chainMax σ).sheet * c.val (f (spx1 (chainMax σ).point))
        (f (descendedSurfaceSimplex f hf c τ)) := by rw [mul_assoc, c.comp (hf hσ) (hf hτ)]
    _ = ((chainMax σ).sheet *
        (descendedSurfaceCocycle f hf c).val (chainMax σ).point (chainMax τ).point) *
        c.val (f (spx1 (chainMax τ).point)) (f (descendedSurfaceSimplex f hf c τ)) := by
      rw [hval]
      group
    _ = _ := by rw [htop.2]

/-- Explicit six-triangle subdivision, in actual old-cover sheets. -/
def barycentricCoverChain2 :
    (OrdTri (DescendedSurfaceCover f hf c) →₀ ℤ) →ₗ[ℤ] (OrdTri (UOrder Q a) →₀ ℤ) :=
  (chain2 (orderCxMap (barycentricCoverRealization f hf c a hc hm)
    (barycentricCoverRealization_monotone f hf c a hc hm))).comp barycentricChain2

def barycentricCoverChain1 :
    (OrdEdge (DescendedSurfaceCover f hf c) →₀ ℤ) →ₗ[ℤ] (OrdEdge (UOrder Q a) →₀ ℤ) :=
  (chain1 (orderCxMap (barycentricCoverRealization f hf c a hc hm)
    (barycentricCoverRealization_monotone f hf c a hc hm))).comp barycentricChain1

set_option maxHeartbeats 800000 in
theorem barycentricCoverChain2_boundary
    (z : OrdTri (DescendedSurfaceCover f hf c) →₀ ℤ) :
    Comb.bdry2 (orderCx (UOrder Q a)) (barycentricCoverChain2 f hf c a hc hm z) =
      barycentricCoverChain1 f hf c a hc hm (Comb.bdry2 (orderCx (DescendedSurfaceCover f hf c)) z) := by
  let k := orderCxMap (barycentricCoverRealization f hf c a hc hm)
    (barycentricCoverRealization_monotone f hf c a hc hm)
  exact (bdry2_chain2 k (barycentricChain2 z)).trans
    (congrArg (chain1 k) (barycentricChain2_boundary z))

end FiniteChains.Davis
