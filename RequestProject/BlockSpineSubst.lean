module

public import RequestProject.BlockSpinePres

@[expose] public section

/-!
# The substitution by the block of the article, applied

`RequestProject/BlockSpinePres.lean` constructs the marked presentation of the block out of its
own geometry and proves the two fillings — the two-cells of the block for its relators and the
mapping cylinder for the marking relators.  This file draws the conclusion for the actual
structural homomorphism of the simultaneous substitution.
-/

namespace FiniteChains
namespace Davis

open RACG Mirror Comb PresModel BlockFamily

universe u

variable {V : Type u} [DecidableEq V] [Fintype V] {A : CommRel V}

/-- **The application: the injectivity of the actual structural homomorphism for the block read
off its own geometry.**  The blocks of the substitution are the marked presentations
`spineBeta` of the truncated cube complex: internal generators are the edges of the block
outside a spanning tree, relators are its two-cells together with the marking relators of the
distinguished generators.  The only geometric hypothesis is `hread`: the attaching map spells
the prescribed old word `u_h` along the chosen loop `sig h` of the cut surface.  Everything
else — the loops of the internal generators, the fillings of the relators by the two-cells and
the fillings of the marking relators by the cylinder — is constructed. -/
theorem injective_substHomF_of_spine {α Jr Sx : Type u} {Su : Sx → Type u}
    (ρ : Jr ⊕ Sx → FreeGroup α) (att : NeSpx A →o presModelPos ρ) (σ₀ : NeSpx A)
    (cb : List ((orderCx (presModelPos ρ)).E × Bool))
    (hcb : IsPath (orderCx (presModelPos ρ)).src (orderCx (presModelPos ρ)).tgt cb
      (ptBase (presWords ρ)) (att σ₀))
    (T : SpanningTree (orderCx (QOld A)))
    (sig : ∀ s : Sx, Su s → List ((orderCx (NeSpx A)).E × Bool))
    (hsig : ∀ (s : Sx) (x : Su s),
      IsPath (orderCx (NeSpx A)).src (orderCx (NeSpx A)).tgt (sig s x) σ₀ σ₀)
    (lw : ∀ s : Sx, Su s → List (α × Bool))
    (hread : ∀ (s : Sx) (x : Su s),
      Htpy (orderCx (presModelPos ρ)) (ptBase (presWords ρ)) (ptBase (presWords ρ))
        (cb ++ mapPath (orderCxMap att att.monotone) (sig s x) ++ revPath cb)
        (wordLoop (presWords ρ) (lw s x)))
    (hfill : BlockFamily.FilledF ρ (fun s m =>
      BlockFamily.blockSubst (Zt := fun _ => spineGens T)
        (fun s x => FreeGroup.mk (lw s x)) s (spineBeta T (sig s) m))) :
    Function.Injective (BlockFamily.substHomF ρ (fun s m =>
      BlockFamily.blockSubst (Zt := fun _ => spineGens T)
        (fun s x => FreeGroup.mk (lw s x)) s (spineBeta T (sig s) m))
      hfill) := by
  refine injective_substHomF_of_markedBlocks ρ att (fun s x => FreeGroup.mk (lw s x))
    (fun s m => spineBeta T (sig s) m) hfill
    (fun s => bqHom ρ att σ₀ cb T hcb (fun x : Su s => FreeGroup.mk (lw s x))) ?_ ?_
  · intro s x
    simp [bqHom]
  · intro s m
    cases m with
    | inl f =>
        show bqHom ρ att σ₀ cb T hcb _ (FreeGroup.map Sum.inr (SpanningTree.treeRel T f)) = 1
        exact bqHom_treeRel ρ att σ₀ cb T hcb _ f
    | inr x => exact bqHom_markRel ρ att σ₀ cb T hcb (lw s) (sig s) (hsig s) (hread s) x


end Davis
end FiniteChains
