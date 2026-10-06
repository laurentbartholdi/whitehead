import RequestProject.RelatorCircleFundamentalChain
import RequestProject.StrictTopConeInjectivity
import RequestProject.PresCoverConeCircleProjection

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains.PresModel
open Comb
universe u
variable {α J : Type u} (w : J → List (α × Bool)) (j : J)

def relatorCirclePresInclusion (x : RelatorCircle w j) : PresPos w := iCirc w x.val

theorem relatorCirclePresInclusion_strictMono : StrictMono (relatorCirclePresInclusion w j) :=
  fun _ _ h => iCirc_strictMono w h

theorem relatorCirclePresInclusion_injective :
    Function.Injective (relatorCirclePresInclusion w j) := by
  intro x y he
  apply Subtype.ext
  exact Sum.inr.inj (Sum.inl.inj he)

theorem relatorCirclePresInclusion_lt_apex (x : RelatorCircle w j) :
    relatorCirclePresInclusion w j x < apexOf w j := (relatorCircleToBelow w j x).property

/-- The genuine finite fan of triangles representing the actual relator cone. -/
noncomputable def relatorConeFundamentalChain : StrictOrdTri (PresPos w) →₀ ℤ :=
  strictTopConeEdgeChain (relatorCirclePresInclusion w j)
    (relatorCirclePresInclusion_strictMono w j) (apexOf w j)
    (relatorCirclePresInclusion_lt_apex w j) (relatorCircleFundamentalChain w j)

/-- The genuine cone fan has exactly the genuine attaching-circle boundary. -/
theorem relatorConeFundamentalChain_boundary :
    Comb.bdry2 (strictOrderCx (PresPos w)) (relatorConeFundamentalChain w j) =
      chain1 (strictOrderCxMap (relatorCirclePresInclusion w j)
        (relatorCirclePresInclusion_strictMono w j)) (relatorCircleFundamentalChain w j) :=
  strictTopConeEdgeChain_cycle_boundary _ _ _ _ _ (relatorCircleFundamentalChain_cycle w j)

/-- The first actual relator incidence has coefficient one in the genuine cone fan. -/
theorem relatorConeFundamentalChain_first (hpos : ∀ j, 0 < (w j).length) :
    relatorConeFundamentalChain w j (presRelatorFirstTriangle w hpos j) = 1 := by
  rw (config := { transparency := .default }) [relatorConeFundamentalChain, strictTopConeEdgeChain_eq_mapDomain]
  have he := Finsupp.mapDomain_apply_of_injective
    (strictTopConeEdgeTriangle_injective (relatorCirclePresInclusion w j)
      (relatorCirclePresInclusion_strictMono w j) (apexOf w j)
      (relatorCirclePresInclusion_lt_apex w j) (relatorCirclePresInclusion_injective w j))
    (relatorCircleFundamentalChain w j) (relatorCircleEdge0 w j ⟨0, hpos j⟩)
  exact he.trans (relatorCircleFundamentalChain_edge0 w j _)

end FiniteChains.PresModel
