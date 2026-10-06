module

public import RequestProject.ChamberQuotientCover
public import RequestProject.BlockFamilySubst
public import RequestProject.TreePresentation

@[expose] public section

/-!
# What is still needed to turn the covering into the algebraic `hinj`

The geometric half of the comparison is now proved without hypotheses:
`FiniteChains.Davis.pi1Map_qNew_injective` says that the inclusion of the base poset `X` into
the quotient `Q = Z/Γ` is injective on fundamental groups, the covering `Z → Q` being supplied
by the construction of `RequestProject/ChamberQuotientCover.lean`.

The algebraic statement `hinj` of the relative route is the injectivity of
`FiniteChains.BlockFamily.substHomF`, the structural homomorphism of the substitution (3.4).
`RequestProject/SubstHomFNotInjective.lean` shows that this injectivity does **not** follow from
the substitution data together with the filling hypothesis, so it has to be imported from the
geometry through a *based comparison of the two pictures*:

    alpha : G(E)   ≃ π₁(X)          (source presentation ↔ base poset),
    beta  : π₁(Q)  ≃ G(E')          (quotient ↔ substituted presentation),

subject to the single equation

    beta ∘ (inclusion of the base)_* ∘ alpha = substHomF.

This file records exactly that reduction, and nothing more: given the two comparison
isomorphisms and the equation, the actual `hinj` follows.  **The comparison isomorphisms are not
constructed here**, so the theorem below is not a proof of `hinj` for the article's block; what
it does is to isolate the one missing identification.  Constructing `alpha` and `beta` requires
a dictionary between fundamental groups of order complexes of posets and presentation groups
(the poset model of a presentation complex), which the project does not yet contain.
-/

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains
namespace Davis

open RACG Mirror Comb

universe u

variable {V : Type u} [DecidableEq V] [Fintype V] {A : CommRel V} {X : Type u} [Preorder X]
  {att : NeSpx A →o X}

/-- **The reduction of `hinj` to the based comparison.**  If the source presentation group is
identified with `π₁` of the base poset, the substituted presentation group with `π₁` of the
quotient `Q = Z/Γ`, and if under these identifications the structural homomorphism of the
substitution is the map induced by the inclusion of the base, then `substHomF` is injective.

The injectivity used is the unconditional one of `pi1Map_qNew_injective`; the hypotheses of this
theorem are exactly the two comparison isomorphisms and the compatibility equation. -/
theorem injective_substHomF_of_pi1Comparison
    {a Jr Sx : Type u} {Zt Mt : Sx → Type u}
    (rho : Jr ⊕ Sx → FreeGroup a) (bsub : ∀ s : Sx, Mt s → FreeGroup (a ⊕ Zt s))
    (hfill : BlockFamily.FilledF rho bsub) (x : X)
    (al : PresGroup rho ≃* Comb.Pi1 (orderCx X) x)
    (be : Comb.Pi1 (orderCx (Qpos A X att)) (qNew (A := A) (att := att) x) ≃*
      PresGroup (BlockFamily.substPresF rho bsub))
    (hcomp : be.toMonoidHom.comp
        ((Comb.pi1Map (orderCxMap (qNew (A := A) (X := X) (att := att)) qNew_monotone) x).comp
          al.toMonoidHom) = BlockFamily.substHomF rho bsub hfill) :
    Function.Injective (BlockFamily.substHomF rho bsub hfill) := by
  have hinj : Function.Injective (be.toMonoidHom.comp
      ((Comb.pi1Map (orderCxMap (qNew (A := A) (X := X) (att := att)) qNew_monotone) x).comp
        al.toMonoidHom)) := by
    simp only [MonoidHom.coe_comp]
    exact be.injective.comp ((pi1Map_qNew_injective x).comp al.injective)
  rwa [hcomp] at hinj

/-! ### The same statement for the actual presentations read off spanning trees -/

/-- **The inclusion of the base in the quotient is injective on the presentations read off
spanning trees.**  `RequestProject/TreePresentation.lean` presents the fundamental group of any
two-complex by the non-tree edges and the attaching words; for a spanning tree `TX` of the order
complex of the base and a spanning tree `TQ` of the order complex of the quotient whose root is
the image of the root of `TX`, the based homomorphism between these two actual presentations is
injective.

This is a statement about honest presentations of the two complexes, with no comparison
isomorphism assumed; identifying these tree presentations with the article's `E` and `E'`
is the remaining step towards `hinj`. -/
theorem injective_presMap_qNew (TX : Comb.SpanningTree (orderCx X))
    (TQ : Comb.SpanningTree (orderCx (Qpos A X att)))
    (hroot : qNew (A := A) (att := att) TX.root = TQ.root) :
    Function.Injective (fun g : PresGroup (Comb.SpanningTree.treeRel TX) =>
      Comb.SpanningTree.pi1EquivPres TQ
        (Equiv.cast (show Comb.Pi1 (orderCx (Qpos A X att))
              (qNew (A := A) (att := att) TX.root)
            = Comb.Pi1 (orderCx (Qpos A X att)) TQ.root from by rw [hroot])
          (Comb.pi1Map (orderCxMap (qNew (A := A) (X := X) (att := att)) qNew_monotone)
            TX.root ((Comb.SpanningTree.pi1EquivPres TX).symm g)))) := by
  intro g g' h
  exact (Comb.SpanningTree.pi1EquivPres TX).symm.injective
    (pi1Map_qNew_injective (A := A) (att := att) (show X from TX.root)
      ((Equiv.cast _).injective ((Comb.SpanningTree.pi1EquivPres TQ).injective h)))

end Davis
end FiniteChains
