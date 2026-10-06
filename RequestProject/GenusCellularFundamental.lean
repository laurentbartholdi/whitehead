module

public import RequestProject.GenusFundamentalChain
public import RequestProject.OrderNerveDecoding
public import RequestProject.StrictChainCoefficients

@[expose] public section

/-! Cellular coordinates of the explicit genus fundamental cycle. -/

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains.Davis
open Genus Comb
variable (q : ℕ) [NeZero q]

abbrev GenusCellPoset := SCell (gvc q) (gec q) (gc q)

/-- The actual finitely supported two-cell chain, decoded from the oriented polygon. -/
noncomputable def genusCellularFundamentalChain : OrdTri (GenusCellPoset q) →₀ ℤ :=
  decodeOrdNerve2 (genusFundamentalChain q)

theorem ordNerve_genusCellularFundamentalChain :
    ordNerveChain2 (genusCellularFundamentalChain q) = genusFundamentalChain q := by
  rw (config := { transparency := .default }) [genusCellularFundamentalChain,
    ordNerveChain2_decode (genusFundamentalChain_mem_inc q), genusFundamentalChain_degree]

/-- The explicit surface chain is a cycle for the actual cellular two-boundary. -/
theorem genusCellularFundamentalChain_cycle :
    Comb.bdry2 (orderCx (GenusCellPoset q)) (genusCellularFundamentalChain q) = 0 := by
  apply (ordNerveChain2_cycle_iff _).mp
  rw (config := { transparency := .default }) [ordNerve_genusCellularFundamentalChain, genusFundamentalChain_cycle]

theorem genusCellularFundamentalChain_ne_zero : genusCellularFundamentalChain q ≠ 0 := by
  intro h
  have he := ordNerve_genusCellularFundamentalChain q
  rw (config := { transparency := .default }) [h, map_zero] at he
  exact genusFundamentalChain_ne_zero q he.symm

/-- The inner flag used to detect the surface orientation is genuinely nondegenerate. -/
def genusInnerFlag : StrictOrdTri (GenusCellPoset q) :=
  ⟨(cC (gc q), cR (gc q) 0, cI (gc q) 0),
    lt_of_le_of_ne (cC_le_cR (gc q) 0) (by intro h; cases h),
    lt_of_le_of_ne (cR_le_cI (gc q) 0) (by intro h; cases h)⟩

theorem genusCellularFundamentalChain_inner_coefficient :
    genusCellularFundamentalChain q
      ((strictOrderIncl (GenusCellPoset q)).onF (genusInnerFlag q)) = 1 := by
  rw (config := { transparency := .default }) [← ordTriangleCoefficient_encode]
  have he : ordTriangleCoefficient
      ((strictOrderIncl (GenusCellPoset q)).onF (genusInnerFlag q)) =
      innerFlagCoefficient (gc q) := by
    apply Nerve.hom_ext
    intro l
    simp [ordTriangleCoefficient, innerFlagCoefficient, FreeAbelianGroup.lift_apply_of,
      strictOrderIncl, genusInnerFlag]
  rw (config := { transparency := .default }) [he]
  rw (config := { transparency := .default }) [ordNerve_genusCellularFundamentalChain]
  apply innerFlagCoefficient_polygon (gc q)
  have := Nat.pos_of_neZero q
  omega

/-- The surface chain in the genuine simplicial two-skeleton, without degenerate cells. -/
noncomputable def genusStrictFundamentalChain : StrictOrdTri (GenusCellPoset q) →₀ ℤ :=
  normalizeOrdChain2 (genusCellularFundamentalChain q)

theorem genusStrictFundamentalChain_cycle :
    Comb.bdry2 (strictOrderCx (GenusCellPoset q)) (genusStrictFundamentalChain q) = 0 :=
  normalizeOrdChain2_cycle _ (genusCellularFundamentalChain_cycle q)

theorem genusStrictFundamentalChain_inner_coefficient :
    genusStrictFundamentalChain q (genusInnerFlag q) = 1 := by
  rw (config := { transparency := .default }) [genusStrictFundamentalChain, normalizeOrdChain2_apply,
    genusCellularFundamentalChain_inner_coefficient]

theorem genusStrictFundamentalChain_ne_zero : genusStrictFundamentalChain q ≠ 0 := by
  intro h
  have he := genusStrictFundamentalChain_inner_coefficient q
  rw (config := { transparency := .default }) [h, Finsupp.zero_apply] at he
  exact zero_ne_one he

end FiniteChains.Davis
