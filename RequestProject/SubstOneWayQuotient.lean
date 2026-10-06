module

public import RequestProject.SubstOneWay
public import RequestProject.PresPosetReading
public import RequestProject.ChamberQuotientCover

@[expose] public section

/-!
# The one-way comparison over the quotient of the model of modified chambers

This file puts together the two halves of the comparison which make the structural homomorphism
of a substitution injective.

* The **base side is constructed**, not assumed.  The base of the chamber construction is taken
  to be the poset model `FiniteChains.PresModel.presModelPos ρ` of the presentation complex of
  the source presentation `ρ`, and `FiniteChains.PresModel.alphaHom` is the marked comparison
  homomorphism of `ρ` with the fundamental group of that model: it carries the class of a
  generator to the loop of that generator, it is defined because every relator is filled by the
  cone point of its two-cell, and it is **injective** because the reading homomorphism of the
  model is a left inverse of it (`FiniteChains.PresModel.alphaHom_injective`).  No faithfulness
  is assumed as an interface parameter and the input presentation is not restricted: `ρ` and its
  attaching words are arbitrary.

* The **geometric side is the proved covering**: the inclusion of the base copy in the quotient
  `Q = Z/Γ` of the model of modified chambers is injective on fundamental groups
  (`FiniteChains.Davis.pi1Map_qNew_injective`).

Their composite `FiniteChains.Davis.baseToQuotient` is therefore an injective homomorphism

    `j : PresGroup ρ →* π₁(orderCx Q, base point)`

of the source presentation group into the fundamental group of the quotient, **constructed** for
an arbitrary presentation and an arbitrary attaching map of the chambers.

The remaining input of the one-way comparison is the family of marked block maps `b s` of
`FiniteChains.BlockFamily.BlockMaps`: one homomorphism per substituted block, defined on the
generators of that block, sending an old generator to its image under `j` and killing the block
relators.  Given them — and nothing else — the structural homomorphism `substHomF` of the actual
simultaneous substitution is injective: `FiniteChains.Davis.injective_substHomF_of_blockMaps`.
-/

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains
namespace Davis

open RACG Mirror Comb PresModel

universe u

variable {V : Type u} [DecidableEq V] [Fintype V] {A : CommRel V}

/-- **The base of the chamber construction attached to a presentation**: the poset model of the
presentation complex of `ρ`, with the base point of its rose. -/
noncomputable abbrev presBasePt {α J : Type u} (ρ : J → FreeGroup α) : presModelPos ρ :=
  ptBase (presWords ρ)

/-- **The constructed comparison of the source presentation with the quotient**: the marked
comparison of `ρ` with the fundamental group of the poset model of its presentation complex,
followed by the map induced by the inclusion of the base copy in the quotient `Q = Z/Γ`. -/
noncomputable def baseToQuotient {α J : Type u} (ρ : J → FreeGroup α)
    (att : NeSpx A →o presModelPos ρ) :
    PresGroup ρ →*
      Comb.Pi1 (orderCx (Qpos A (presModelPos ρ) att)) (qNew (A := A) (att := att)
        (presBasePt ρ)) :=
  (Comb.pi1Map (orderCxMap (qNew (A := A) (X := presModelPos ρ) (att := att)) qNew_monotone)
      (presBasePt ρ)).comp (alphaHom ρ)

/-- **The comparison is injective.**  Both factors are: the marked comparison of the
presentation with its poset model by `FiniteChains.PresModel.alphaHom_injective`, and the
inclusion of the base copy in the quotient by `FiniteChains.Davis.pi1Map_qNew_injective`. -/
theorem baseToQuotient_injective {α J : Type u} (ρ : J → FreeGroup α)
    (att : NeSpx A →o presModelPos ρ) :
    Function.Injective (baseToQuotient (A := A) ρ att) := by
  intro x y h
  exact alphaHom_injective ρ
    (pi1Map_qNew_injective (A := A) (att := att) (presBasePt ρ) h)

/-- **The one-way comparison, applied to the actual substitution.**  Let `ρ` be an arbitrary
source presentation, let the base of the chamber construction be the poset model of its
presentation complex with an arbitrary attaching map `att`, and let `bsub` be the substituted
blocks.  If every block carries a marked homomorphism into the fundamental group of the quotient
`Q = Z/Γ` — sending an old generator to its image under the constructed comparison
`baseToQuotient` and killing the block relators — then the structural homomorphism of the
simultaneous substitution is injective.

This is the hypothesis `hinj` of the relative route for the actual
`FiniteChains.BlockFamily.substHomF`; the comparison isomorphisms of
`FiniteChains.Davis.injective_substHomF_of_pi1Comparison` are no longer assumed: the base
comparison is constructed and only the block maps remain as data. -/
theorem injective_substHomF_of_blockMaps {α Jr Sx : Type u} {Zt Mt : Sx → Type u}
    (ρ : Jr ⊕ Sx → FreeGroup α) (att : NeSpx A →o presModelPos ρ)
    (bsub : ∀ s : Sx, Mt s → FreeGroup (α ⊕ Zt s))
    (hfill : BlockFamily.FilledF ρ bsub)
    (B : BlockFamily.BlockMaps ρ bsub (baseToQuotient (A := A) ρ att)) :
    Function.Injective (BlockFamily.substHomF ρ bsub hfill) :=
  B.injective_substHomF hfill (baseToQuotient_injective (A := A) ρ att)

/-- **The same statement for the article's marked blocks.**  The block at `s` is given by its own
presentation `B_q = ⟨s_h, t_h, Z ∣ β_m⟩` with distinguished generators `Su s`, and the
substitution reads the distinguished generators as the prescribed words `u` in the old
generators.  The input is, for each block, a homomorphism `bq s` out of the free group on the
generators of the block which kills the block relators and whose value on a distinguished
generator is the image under the constructed comparison of the prescribed old word — the two
marking equalities `b [s_h] = j [u_h]`, `b [t_h] = j [v_h]`. -/
theorem injective_substHomF_of_markedBlocks {α Jr Sx : Type u} {Zt Mt Su : Sx → Type u}
    (ρ : Jr ⊕ Sx → FreeGroup α) (att : NeSpx A →o presModelPos ρ)
    (u : ∀ s : Sx, Su s → FreeGroup α)
    (beta : ∀ s : Sx, Mt s → FreeGroup (Su s ⊕ Zt s))
    (hfill : BlockFamily.FilledF ρ (fun s m => BlockFamily.blockSubst u s (beta s m)))
    (bq : ∀ s : Sx, FreeGroup (Su s ⊕ Zt s) →*
      Comb.Pi1 (orderCx (Qpos A (presModelPos ρ) att))
        (qNew (A := A) (att := att) (presBasePt ρ)))
    (hmark : ∀ (s : Sx) (x : Su s),
      bq s (FreeGroup.of (Sum.inl x)) = baseToQuotient (A := A) ρ att (QuotientGroup.mk (u s x)))
    (hrel : ∀ (s : Sx) (m : Mt s), bq s (beta s m) = 1) :
    Function.Injective
      (BlockFamily.substHomF ρ (fun s m => BlockFamily.blockSubst u s (beta s m)) hfill) :=
  BlockFamily.injective_substHomF_of_markedBlock u beta hfill (baseToQuotient (A := A) ρ att)
    (baseToQuotient_injective (A := A) ρ att) bq hmark hrel

end Davis
end FiniteChains
