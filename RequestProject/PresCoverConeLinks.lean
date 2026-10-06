import RequestProject.StrictTopLinkChains
import RequestProject.PresConeIntervals
import RequestProject.PosetCoverUpTransform

namespace FiniteChains.PresModel
open Comb
universe u
variable {α J P : Type u} [PartialOrder P] (w : J → List (α × Bool))

theorem presPos_apex_maximal (j : J) (p : PresPos w) (hp : apexOf w j ≤ p) :
    p = apexOf w j := by
  cases p with
  | inl p => exact hp.elim
  | inr k => exact congrArg Sum.inr hp.symm

theorem presCover_apex_maximal (f : P → PresPos w) (hf : IsPosetCover f)
    (v : P) (j : J) (hv : f v = apexOf w j) : ∀ p, v ≤ p → p = v := by
  intro p hp
  have hfp := hf.mono hp
  rw [hv] at hfp
  have he := presPos_apex_maximal w j (f p) hfp
  exact hf.up_inj hp (le_refl v) (he.trans hv.symm)

/-- The actual coefficients around every lifted relator apex form a genuine link one-cycle. -/
theorem presCover_cone_link_cycle (f : P → PresPos w) (hf : IsPosetCover f)
    (v : P) (j : J) (hv : f v = apexOf w j)
    (c : StrictOrdTri P →₀ ℤ) (hc : Comb.bdry2 (strictOrderCx P) c = 0) :
    Comb.bdry1 (strictOrderCx (StrictBelow v)) (strictTopLinkChain v c) = 0 :=
  strictTopLink_cycle v (presCover_apex_maximal w f hf v j hv) c hc

end FiniteChains.PresModel
