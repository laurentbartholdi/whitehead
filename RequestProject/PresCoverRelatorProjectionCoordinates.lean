module

public import RequestProject.PresCoverRelatorSingleCoordinates

@[expose] public section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains.PresModel
open Comb
universe u
variable {α J P : Type u} [PartialOrder P] (w : J → List (α × Bool))
  (f : P → PresPos w) (hf : IsPosetCover f) (hpos : ∀ j, 0 < (w j).length)

/-- Different actual relator labels have different actual coordinate triangles. -/
theorem presRelatorFirstTriangle_injective :
    Function.Injective (presRelatorFirstTriangle w hpos) := by
  intro j k h
  exact Sum.inr.inj (congrArg (fun t : StrictOrdTri (PresPos w) => t.val.2.2) h)

/-- Pushing genuine triangle coefficients to a base coordinate triangle sums precisely
its genuine lifted-apex relator coefficients. -/
theorem presCoverRelatorChain_projection (c : StrictOrdTri P →₀ ℤ) (j : J) :
    chain2 (strictOrderCxMap f hf.strictMono) c (presRelatorFirstTriangle w hpos j) =
      Finsupp.mapDomain (fun p => p.val.2) (presCoverRelatorChain w f hf hpos c) j := by
  classical
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd =>
    simp only [map_add, Finsupp.mapDomain_add, Finsupp.add_apply, hc, hd]
  | single t n =>
    by_cases ht : ∃ k, (strictOrderCxMap f hf.strictMono).onF t =
        presRelatorFirstTriangle w hpos k
    · obtain ⟨k, hk⟩ := ht
      rw (config := { transparency := .default }) [presCoverRelatorChain_single_over_coordinate w f hf hpos k t hk n,
        Finsupp.mapDomain_single]
      change Finsupp.mapDomain (strictOrderCxMap f hf.strictMono).onF
        (Finsupp.single t n) (presRelatorFirstTriangle w hpos j) = Finsupp.single k n j
      rw (config := { transparency := .default }) [Finsupp.mapDomain_single, hk]
      by_cases hkj : k = j
      · subst j
        simp
      · have hn := (presRelatorFirstTriangle_injective w hpos).ne hkj
        simp [ hkj, hn]
    · have hn : ∀ k, (strictOrderCxMap f hf.strictMono).onF t ≠
          presRelatorFirstTriangle w hpos k := by
        intro k he
        exact ht ⟨k, he⟩
      rw (config := { transparency := .default }) [presCoverRelatorChain_single_off_coordinates w f hf hpos t n hn]
      change Finsupp.mapDomain (strictOrderCxMap f hf.strictMono).onF
        (Finsupp.single t n) (presRelatorFirstTriangle w hpos j) =
        Finsupp.mapDomain (fun p : PresCoverRelator w f => p.val.2) 0 j
      rw (config := { transparency := .default }) [Finsupp.mapDomain_single]
      simp [ hn j]

end FiniteChains.PresModel
