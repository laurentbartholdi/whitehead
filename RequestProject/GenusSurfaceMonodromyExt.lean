import RequestProject.GenusSurfaceMonodromy
import RequestProject.OrderCocycleComparisonAction

/-! Agreement on the genuine genus markings determines all surface monodromy. -/
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains.Davis.Genus
open RACG Mirror Comb
universe v
variable (q : ℕ) [NeZero q] {G : Type v} [Group G]
  (c d : OrdCocycle (NeSpx (cmpRel (SCell (gvc q) (gec q) (gc q)))) G)

local instance genusSurfacePi1Group : Group
    (Pi1 (orderCx (NeSpx (cmpRel (SCell (gvc q) (gec q) (gc q))))) (gBase q)) :=
  @Pi1.instGroup (orderCx (NeSpx (cmpRel (SCell (gvc q) (gec q) (gc q))))) (gBase q)

/-- The marked equalities give the actual vertex gauge needed to glue the old
and base cocycles along the surface in the geometric mapping cylinder. -/
theorem genus_cocycle_gauge_of_marked
    (hm : ∀ x : Fin q × Bool,
      c.readPath (gSig q (x.1.val, x.2)) = d.readPath (gSig q (x.1.val, x.2))) :
    ∃ k : NeSpx (cmpRel (SCell (gvc q) (gec q) (gc q))) → G,
      k (gBase q) = 1 ∧ ∀ {a b}, a ≤ b → c.val a b * k b = k a * d.val a b := by
  have hf : ∀ x : Fin q × Bool, (OrdCocycle.product c d).readPath (gSig q (x.1.val, x.2)) •
      (OrdCocycle.comparisonOne : OrdCocycle.ComparisonPoint G) = OrdCocycle.comparisonOne := by
    intro x
    rw [OrdCocycle.product_readPath, OrdCocycle.comparisonOne_fixed_iff]
    exact hm x
  obtain ⟨s, hs, hb⟩ := genus_exists_flat_section q
    (OrdCocycle.comparisonOne : OrdCocycle.ComparisonPoint G) (OrdCocycle.product c d) hf
  refine ⟨fun a => (s a).val, congrArg OrdCocycle.ComparisonPoint.val hb, ?_⟩
  intro a b hab
  have h := congrArg OrdCocycle.ComparisonPoint.val (hs hab)
  change c.val a b * (s b).val * (d.val a b)⁻¹ = (s a).val at h
  exact (mul_inv_eq_iff_eq_mul).mp h

/-- Two nonabelian cocycles with equal readings on the actual marked loops
have equal readings on every based loop of the actual surface. -/
theorem genus_readPath_eq_of_marked
    (hm : ∀ x : Fin q × Bool,
      c.readPath (gSig q (x.1.val, x.2)) = d.readPath (gSig q (x.1.val, x.2)))
    (p : Loop (sdCx (gc q)) (gBase q)) : c.readPath p.1 = d.readPath p.1 := by
  have hf : ∀ x : Fin q × Bool, (OrdCocycle.product c d).readPath (gSig q (x.1.val, x.2)) •
      (OrdCocycle.comparisonOne : OrdCocycle.ComparisonPoint G) = OrdCocycle.comparisonOne := by
    intro x
    rw [OrdCocycle.product_readPath, OrdCocycle.comparisonOne_fixed_iff]
    exact hm x
  have h := genus_loop_fixed_of_marked_fixed q
    (OrdCocycle.comparisonOne : OrdCocycle.ComparisonPoint G) (OrdCocycle.product c d) hf p
  rwa [OrdCocycle.product_readPath, OrdCocycle.comparisonOne_fixed_iff] at h

/-- This is equality of the complete fundamental-group homomorphisms, not
only equality on homology or on a postulated presentation of the surface. -/
theorem genus_monodromy_eq_of_marked
    (hm : ∀ x : Fin q × Bool,
      c.readPath (gSig q (x.1.val, x.2)) = d.readPath (gSig q (x.1.val, x.2))) :
    c.monodromy (gBase q) = d.monodromy (gBase q) := by
  apply MonoidHom.ext
  intro g
  refine Quotient.inductionOn g ?_
  intro p
  exact genus_readPath_eq_of_marked q c d hm p

end FiniteChains.Davis.Genus
