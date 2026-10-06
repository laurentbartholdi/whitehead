import RequestProject.PresCoverRelatorProjectionCoordinates

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains.PresModel
open Comb
universe u
variable {α J P : Type u} [PartialOrder P] (w : J → List (α × Bool))
  (f : P → PresPos w) (hf : IsPosetCover f) (hpos : ∀ j, 0 < (w j).length)

/-- Zero base relator coordinates force the actual pushdown of a genuine two-cycle to vanish. -/
theorem presCover_cycle_pushdown_zero
    (c : StrictOrdTri P →₀ ℤ) (hc : Comb.bdry2 (strictOrderCx P) c = 0)
    (ha : Finsupp.mapDomain (fun p => p.val.2) (presCoverRelatorChain w f hf hpos c) = 0) :
    chain2 (strictOrderCxMap f hf.strictMono) c = 0 := by
  let hi : IsPosetCover (id : PresPos w → PresPos w) :=
    ⟨monotone_id, Function.surjective_id,
      fun a b h => ⟨b, ⟨h, rfl⟩, fun z hz => hz.2⟩,
      fun a b h => ⟨b, ⟨h, rfl⟩, fun z hz => hz.2⟩⟩
  have hz : Comb.bdry2 (strictOrderCx (PresPos w))
      (chain2 (strictOrderCxMap f hf.strictMono) c) = 0 := by
    rw (config := { transparency := .default }) [bdry2_chain2, hc, map_zero]
  apply presCoverRelatorChain_cycle_injective w id hi hpos _ 0 hz (map_zero _)
  ext p
  rw (config := { transparency := .default }) [presCoverRelatorChain_apply, map_zero, Finsupp.zero_apply]
  have ht : presCoverRelatorTriangle w id hi hpos p =
      presRelatorFirstTriangle w hpos p.val.2 :=
    presCoverRelatorTriangle_projection w id hi hpos p
  rw (config := { transparency := .default }) [ht]
  exact (presCoverRelatorChain_projection w f hf hpos c p.val.2).trans
    (congrArg (fun z => z p.val.2) ha)

end FiniteChains.PresModel
