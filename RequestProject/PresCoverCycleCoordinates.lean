import RequestProject.PresCoverConeCircleChains
import RequestProject.PresCoverCylinderElimination

namespace FiniteChains.PresModel
open Comb
universe u
variable {α J P : Type u} [PartialOrder P] (w : J → List (α × Bool))
  (f : P → PresPos w) (hf : IsPosetCover f)

/-- Actual two-cycles are detected by one genuine coefficient at each lifted relator apex. -/
theorem presCover_cycles_eq_of_first_coefficients
    (hpos : ∀ j, 0 < (w j).length) (c d : StrictOrdTri P →₀ ℤ)
    (hc : Comb.bdry2 (strictOrderCx P) c = 0)
    (hd : Comb.bdry2 (strictOrderCx P) d = 0)
    (he : ∀ (v : P) (j : J) (hv : f v = apexOf w j),
      presCoverConeCircleChain w f hf v j hv c
        (relatorCircleEdge0 w j ⟨0, hpos j⟩) =
      presCoverConeCircleChain w f hf v j hv d
        (relatorCircleEdge0 w j ⟨0, hpos j⟩)) : c = d := by
  apply presCover_cycles_eq_of_cone_coefficients w f hf c d hc hd
  intro t ht
  cases hft : f t.1.2.2 with
  | inl x =>
    exfalso
    apply ht
    exact ⟨x, hft.symm⟩
  | inr j =>
    let e : StrictOrdEdge (StrictBelow t.1.2.2) :=
      ⟨(⟨t.1.1, t.2.1.trans t.2.2⟩, ⟨t.1.2.1, t.2.2⟩), t.2.1⟩
    exact presCoverConeTriangles_eq_of_first_coefficient w f hf t.1.2.2 j hft
      c d hc hd (hpos j) (he _ j hft) e

end FiniteChains.PresModel
