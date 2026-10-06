module

public import RequestProject.PresCoverRelatorFanLinks
public import RequestProject.PresCoverCylinderElimination

@[expose] public section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

set_option maxHeartbeats 800000

namespace FiniteChains.PresModel
open Comb
universe u
variable {α J P : Type u} [PartialOrder P] (w : J → List (α × Bool))
  (f : P → PresPos w) (hf : IsPosetCover f) (hpos : ∀ j, 0 < (w j).length)

/-- The genuine relator-fan realization recovers every cone link of an actual two-cycle. -/
theorem presCover_cycle_fan_circle (c : StrictOrdTri P →₀ ℤ)
    (hc : Comb.bdry2 (strictOrderCx P) c = 0) (p : PresCoverRelator w f) :
    presCoverConeCircleChain w f hf p.1.1 p.1.2 p.2 c =
      presCoverConeCircleChain w f hf p.1.1 p.1.2 p.2
        (presCoverRelatorFanChain w f hf (presCoverRelatorChain w f hf hpos c)) := by
  rw [presCoverRelatorFanChain_circle, presCoverRelatorChain_circle]
  exact relatorCircle_cycle_eq_smul_fundamental w p.1.2 _
    (presCoverConeCircleChain_cycle w f hf p.1.1 p.1.2 p.2 c hc) (hpos p.1.2)

/-- Subtracting the explicit fan realization of its coordinates leaves a genuine
finite chain entirely in the cylinder preimage. -/
theorem presCover_cycle_minus_fans_cylinder_support (c : StrictOrdTri P →₀ ℤ)
    (hc : Comb.bdry2 (strictOrderCx P) c = 0) :
    ∀ t ∈ (c - presCoverRelatorFanChain w f hf (presCoverRelatorChain w f hf hpos c)).support,
      f t.1.2.2 ∈ coneAdjBaseSet (S := circSet w) := by
  intro t ht
  by_contra hn
  cases hft : f t.1.2.2 with
  | inl x => exact hn ⟨x, hft.symm⟩
  | inr j =>
    let p : PresCoverRelator w f := ⟨(t.1.2.2, j), hft⟩
    let e : StrictOrdEdge (StrictBelow t.1.2.2) :=
      ⟨(⟨t.1.1, t.2.1.trans t.2.2⟩, ⟨t.1.2.1, t.2.2⟩), t.2.1⟩
    have he := congrArg
      (fun z => z ((presCoverConeCircleHom w f hf p.1.1 p.1.2 p.2).onE e))
      (presCover_cycle_fan_circle w f hf hpos c hc p)
    rw (config := { transparency := .default }) [presCoverConeCircleChain_apply, presCoverConeCircleChain_apply] at he
    have hz : (c - presCoverRelatorFanChain w f hf (presCoverRelatorChain w f hf hpos c)) t = 0 := by
      rw (config := { transparency := .default }) [Finsupp.sub_apply]
      exact sub_eq_zero.mpr he
    exact (Finsupp.mem_support_iff.mp ht) hz

/-- Every actual cover two-cycle is its explicit finite relator fan plus an actual
finite triangle chain in the cylinder preimage. -/
theorem exists_presCover_cycle_cone_cylinder_decomposition (c : StrictOrdTri P →₀ ℤ)
    (hc : Comb.bdry2 (strictOrderCx P) c = 0) :
    ∃ d : StrictOrdTri {p : P // f p ∈ coneAdjBaseSet (S := circSet w)} →₀ ℤ,
      Finsupp.mapDomain
        (fun t : StrictOrdTri {p : P // f p ∈ coneAdjBaseSet (S := circSet w)} =>
          ((strictSubposetIncl {p : P | f p ∈ coneAdjBaseSet (S := circSet w)}).onF t :
            StrictOrdTri P)) d =
      c - presCoverRelatorFanChain w f hf (presCoverRelatorChain w f hf hpos c) := by
  let S : Set P := {p | f p ∈ coneAdjBaseSet (S := circSet w)}
  let r := c - presCoverRelatorFanChain w f hf (presCoverRelatorChain w f hf hpos c)
  have hs : ∀ t ∈ r.support, t.1.1 ∈ S ∧ t.1.2.1 ∈ S ∧ t.1.2.2 ∈ S := by
    intro t ht
    have hlast := presCover_cycle_minus_fans_cylinder_support w f hf hpos c hc t ht
    exact ⟨coneAdjBaseSet_down_closed hlast (hf.mono (t.2.1.le.trans t.2.2.le)),
      coneAdjBaseSet_down_closed hlast (hf.mono t.2.2.le), hlast⟩
  let d := Finsupp.comapDomain (strictSubposetIncl S).onF r
    (strictSubposetIncl_onF_injective S).injOn
  refine ⟨d, ?_⟩
  exact Finsupp.mapDomain_comapDomain _ (strictSubposetIncl_onF_injective S) r
    (fun t ht => (strictSubposetIncl_onF_range S t).mpr (hs t ht))

/-- The actual finite cylinder remainder has boundary equal to the negative actual
attaching-circle boundary of the coordinate fans. -/
theorem exists_presCover_cycle_cylinder_boundary (c : StrictOrdTri P →₀ ℤ)
    (hc : Comb.bdry2 (strictOrderCx P) c = 0) :
    ∃ d : StrictOrdTri {p : P // f p ∈ coneAdjBaseSet (S := circSet w)} →₀ ℤ,
      chain2 (strictSubposetIncl {p : P | f p ∈ coneAdjBaseSet (S := circSet w)}) d =
        c - presCoverRelatorFanChain w f hf (presCoverRelatorChain w f hf hpos c) ∧
      chain1 (strictSubposetIncl {p : P | f p ∈ coneAdjBaseSet (S := circSet w)})
        (Comb.bdry2 (strictOrderCx {p : P // f p ∈ coneAdjBaseSet (S := circSet w)}) d) =
          -Comb.bdry2 (strictOrderCx P)
            (presCoverRelatorFanChain w f hf (presCoverRelatorChain w f hf hpos c)) := by
  obtain ⟨d, hd⟩ := exists_presCover_cycle_cone_cylinder_decomposition w f hf hpos c hc
  refine ⟨d, hd, ?_⟩
  exact (bdry2_chain2
    (strictSubposetIncl {p : P | f p ∈ coneAdjBaseSet (S := circSet w)}) d).symm.trans (by
      change Comb.bdry2 (strictOrderCx P)
        (Finsupp.mapDomain (strictSubposetIncl {p : P | f p ∈ coneAdjBaseSet (S := circSet w)}).onF d) = _
      rw (config := { transparency := .default }) [hd, map_sub, hc, zero_sub])

end FiniteChains.PresModel
