import RequestProject.PresCoverRelatorGeneratorBoundary

/-! Cone-coordinate reduction for chains whose boundary lies in the cylinder.
This is a relative statement: the chain itself need not be a cycle. -/
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

set_option maxHeartbeats 1600000

namespace FiniteChains.PresModel
open Comb
universe u
variable {α J P : Type u} [PartialOrder P] (w : J → List (α × Bool))
  (f : P → PresPos w) (hf : IsPosetCover f) (hpos : ∀ j, 0 < (w j).length)

theorem presCoverConeCircleChain_cycle_of_cylinder_boundary
    (c : StrictOrdTri P →₀ ℤ)
    (b : StrictOrdEdge {p : P // f p ∈ coneAdjBaseSet (S := circSet w)} →₀ ℤ)
    (hb : Comb.bdry2 (strictOrderCx P) c =
      chain1 (strictSubposetIncl {p : P | f p ∈ coneAdjBaseSet (S := circSet w)}) b)
    (p : PresCoverRelator w f) :
    Comb.bdry1 (strictOrderCx (RelatorCircle w p.1.2))
      (presCoverConeCircleChain w f hf p.1.1 p.1.2 p.2 c) = 0 := by
  have hr : strictRayChain p.1.1
      (chain1 (strictSubposetIncl {q : P | f q ∈ coneAdjBaseSet (S := circSet w)}) b) = 0 := by
    classical
    clear hb
    induction b using Finsupp.induction_linear with
    | zero => simp
    | add b d hb hd => simp only [map_add, hb, hd, add_zero]
    | single e n =>
      have hn : e.1.2.val ≠ p.1.1 := by
        intro he
        have hm := e.1.2.property
        rw (config := { transparency := .default }) [he, p.2] at hm
        rcases hm with ⟨a, ha⟩
        cases ha
      simp [chain1, strictSubposetIncl, strictOrderCxMap, strictRayChain, strictRayEdge, hn]
  change Comb.bdry1 _ (chain1 (presCoverConeCircleHom w f hf p.1.1 p.1.2 p.2)
    (strictTopLinkChain p.1.1 c)) = 0
  rw (config := { transparency := .default }) [bdry1_chain1, ← strictTopLink_boundary p.1.1
    (presCover_apex_maximal w f hf p.1.1 p.1.2 p.2), hb, hr, map_zero]

/-- A chain with boundary in the cylinder has exactly one coefficient at each
actual relator apex, just as an absolute two-cycle does. -/
theorem presCover_relative_fan_circle
    (c : StrictOrdTri P →₀ ℤ)
    (b : StrictOrdEdge {p : P // f p ∈ coneAdjBaseSet (S := circSet w)} →₀ ℤ)
    (hb : Comb.bdry2 (strictOrderCx P) c =
      chain1 (strictSubposetIncl {p : P | f p ∈ coneAdjBaseSet (S := circSet w)}) b)
    (p : PresCoverRelator w f) :
    presCoverConeCircleChain w f hf p.1.1 p.1.2 p.2 c =
      presCoverConeCircleChain w f hf p.1.1 p.1.2 p.2
        (presCoverRelatorFanChain w f hf (presCoverRelatorChain w f hf hpos c)) := by
  rw [presCoverRelatorFanChain_circle, presCoverRelatorChain_circle]
  exact relatorCircle_cycle_eq_smul_fundamental w p.1.2 _
    (presCoverConeCircleChain_cycle_of_cylinder_boundary w f hf c b hb p) (hpos p.1.2)

/-- Subtracting the actual coordinate fans leaves an actual finite cylinder chain. -/
theorem exists_presCover_relative_cone_cylinder_decomposition
    (c : StrictOrdTri P →₀ ℤ)
    (b : StrictOrdEdge {p : P // f p ∈ coneAdjBaseSet (S := circSet w)} →₀ ℤ)
    (hb : Comb.bdry2 (strictOrderCx P) c =
      chain1 (strictSubposetIncl {p : P | f p ∈ coneAdjBaseSet (S := circSet w)}) b) :
    ∃ d : StrictOrdTri {p : P // f p ∈ coneAdjBaseSet (S := circSet w)} →₀ ℤ,
      chain2 (strictSubposetIncl {p : P | f p ∈ coneAdjBaseSet (S := circSet w)}) d =
        c - presCoverRelatorFanChain w f hf (presCoverRelatorChain w f hf hpos c) := by
  let S : Set P := {p | f p ∈ coneAdjBaseSet (S := circSet w)}
  let r := c - presCoverRelatorFanChain w f hf (presCoverRelatorChain w f hf hpos c)
  have hs : ∀ t ∈ r.support, t.1.1 ∈ S ∧ t.1.2.1 ∈ S ∧ t.1.2.2 ∈ S := by
    intro t ht
    have hlast : t.1.2.2 ∈ S := by
      by_contra hn
      cases hft : f t.1.2.2 with
      | inl x => exact hn ⟨x, hft.symm⟩
      | inr j =>
        let p : PresCoverRelator w f := ⟨(t.1.2.2, j), hft⟩
        let e : StrictOrdEdge (StrictBelow t.1.2.2) :=
          ⟨(⟨t.1.1, t.2.1.trans t.2.2⟩, ⟨t.1.2.1, t.2.2⟩), t.2.1⟩
        have he := congrArg
          (fun z => z ((presCoverConeCircleHom w f hf p.1.1 p.1.2 p.2).onE e))
          (presCover_relative_fan_circle w f hf hpos c b hb p)
        rw (config := { transparency := .default }) [presCoverConeCircleChain_apply, presCoverConeCircleChain_apply] at he
        exact (Finsupp.mem_support_iff.mp ht) (sub_eq_zero.mpr he)
    exact ⟨coneAdjBaseSet_down_closed hlast (hf.mono (t.2.1.le.trans t.2.2.le)),
      coneAdjBaseSet_down_closed hlast (hf.mono t.2.2.le), hlast⟩
  refine ⟨Finsupp.comapDomain (strictSubposetIncl S).onF r
    (strictSubposetIncl_onF_injective S).injOn, ?_⟩
  exact Finsupp.mapDomain_comapDomain _ (strictSubposetIncl_onF_injective S) r
    (fun t ht => (strictSubposetIncl_onF_range S t).mpr (hs t ht))

/-- Relative fillings recover exactly the collapsed attaching boundary of their
actual relator coefficients. -/
theorem presCover_relative_collapsed_boundary
    (c : StrictOrdTri P →₀ ℤ)
    (b : StrictOrdEdge {p : P // f p ∈ coneAdjBaseSet (S := circSet w)} →₀ ℤ)
    (hb : Comb.bdry2 (strictOrderCx P) c =
      chain1 (strictSubposetIncl {p : P | f p ∈ coneAdjBaseSet (S := circSet w)}) b) :
    normalizedStrictChain1 (presCoverCylinderCollapse w f hf)
      (presCoverCylinderCollapse_monotone w f hf) b =
    normalizedStrictChain1 (presCoverCylinderCollapse w f hf)
      (presCoverCylinderCollapse_monotone w f hf)
      (presCoverCylinderRelatorBoundaryChain w f hf (presCoverRelatorChain w f hf hpos c)) := by
  obtain ⟨d, hd⟩ := exists_presCover_relative_cone_cylinder_decomposition w f hf hpos c b hb
  have he : Comb.bdry2 (strictOrderCx _) d =
      b - presCoverCylinderRelatorBoundaryChain w f hf (presCoverRelatorChain w f hf hpos c) := by
    apply Finsupp.mapDomain_injective (strictSubposetIncl_onE_injective
      {p : P | f p ∈ coneAdjBaseSet (S := circSet w)})
    change chain1 (strictSubposetIncl {p : P | f p ∈ coneAdjBaseSet (S := circSet w)})
      (Comb.bdry2 (strictOrderCx {p : P // f p ∈ coneAdjBaseSet (S := circSet w)}) d) =
      chain1 (strictSubposetIncl {p : P | f p ∈ coneAdjBaseSet (S := circSet w)}) _
    calc
      _ = Comb.bdry2 (strictOrderCx P)
          (chain2 (strictSubposetIncl {p : P | f p ∈ coneAdjBaseSet (S := circSet w)}) d) :=
        (bdry2_chain2 (strictSubposetIncl {p : P | f p ∈ coneAdjBaseSet (S := circSet w)}) d).symm
      _ = _ := by
        rw [hd, map_sub, hb, map_sub, presCoverCylinderRelatorBoundaryChain_inclusion]
  have hz := cylinderCover_collapse_boundary_zero w (coneAdjCoverBaseEnd_isPosetCover f hf) d
  rw [he, map_sub] at hz
  exact sub_eq_zero.mp hz

end FiniteChains.PresModel
