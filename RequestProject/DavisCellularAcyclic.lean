import RequestProject.DavisChainAcyclic
import RequestProject.OrderNerveDecoding

/-! Exactness in degree two of the full cellular nerve of the actual Davis poset. -/

namespace FiniteChains.Davis
open RACG Mirror Comb Nerve
universe u
variable {V : Type u} [DecidableEq V] [Fintype V]

/-- Every cellular two-cycle in the actual Davis complex is the boundary of a finitely
 supported cellular three-chain. This keeps the three-cells of the full nerve. -/
theorem exists_cellular_bdry3_of_cycle_davis (A : CommRel V)
    (z : OrdTri (Sph A) →₀ ℤ) (hz : Comb.bdry2 (orderCx (Sph A)) z = 0) :
    ∃ y : OrdTet (Sph A) →₀ ℤ, ordBoundary3 y = z := by
  obtain ⟨y, hy, hdy⟩ := exists_bdry_eq_of_cycle_davis A (ordNerveChain2_mem_inc z)
    ((ordNerveChain2_cycle_iff z).mpr hz)
  refine ⟨decodeOrdNerve3 y, ?_⟩
  apply ordNerveChain2_injective
  rw [ordNerveChain2_ordBoundary3, ordNerveChain3_decode hy,
    ← lengthProjection_bdry, hdy, ordNerveChain2_lengthProjection]

end FiniteChains.Davis
