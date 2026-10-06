module

public import RequestProject.BlockSpinePresW
public import RequestProject.BlockSurfaceFilling

@[expose] public section

/-!
# The substitution by a block over a model built on prescribed relator words

`RequestProject/BlockSpinePresW.lean` carries the construction of the block over the model
`PresPos w` built on a prescribed family of relator words.  This file draws the same two
conclusions as `RequestProject/BlockSpineSubst.lean` and
`RequestProject/BlockSurfaceFilling.lean` over that model:

* `FiniteChains.Davis.injective_substHomF_of_spineW` — the structural homomorphism of the
  substitution is injective, given the reading hypothesis and the hypothesis (B1);
* `FiniteChains.Davis.injective_substHomF_of_surfaceW` — the same with (B1) derived from a
  filling of the surface relator in the cut surface of the block.
-/

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains
namespace Davis

open RACG Mirror Comb PresModel BlockFamily

universe u

variable {V : Type u} [DecidableEq V] [Fintype V] {A : CommRel V}

/-- **The injectivity of the structural homomorphism for the block read off its own geometry**,
over the model built on the prescribed relator words. -/
theorem injective_substHomF_of_spineW {α Jr Sx : Type u} {Su : Sx → Type u}
    (ρ : Jr ⊕ Sx → FreeGroup α) (w : Jr ⊕ Sx → List (α × Bool))
    (hw : ∀ j, FreeGroup.mk (w j) = ρ j) (att : NeSpx A →o PresPos w) (σ₀ : NeSpx A)
    (cb : List ((orderCx (PresPos w)).E × Bool))
    (hcb : IsPath (orderCx (PresPos w)).src (orderCx (PresPos w)).tgt cb (ptBase w) (att σ₀))
    (T : SpanningTree (orderCx (QOld A)))
    (sig : ∀ s : Sx, Su s → List ((orderCx (NeSpx A)).E × Bool))
    (hsig : ∀ (s : Sx) (x : Su s),
      IsPath (orderCx (NeSpx A)).src (orderCx (NeSpx A)).tgt (sig s x) σ₀ σ₀)
    (lw : ∀ s : Sx, Su s → List (α × Bool))
    (hread : ∀ (s : Sx) (x : Su s),
      Htpy (orderCx (PresPos w)) (ptBase w) (ptBase w)
        (cb ++ mapPath (orderCxMap att att.monotone) (sig s x) ++ revPath cb)
        (wordLoop w (lw s x)))
    (hfill : BlockFamily.FilledF ρ (fun s m =>
      BlockFamily.blockSubst (Zt := fun _ => spineGens T)
        (fun s x => FreeGroup.mk (lw s x)) s (spineBeta T (sig s) m))) :
    Function.Injective (BlockFamily.substHomF ρ (fun s m =>
      BlockFamily.blockSubst (Zt := fun _ => spineGens T)
        (fun s x => FreeGroup.mk (lw s x)) s (spineBeta T (sig s) m))
      hfill) := by
  refine injective_substHomF_of_markedBlocksW ρ w hw att (fun s x => FreeGroup.mk (lw s x))
    (fun s m => spineBeta T (sig s) m) hfill
    (fun s => bqHomW ρ w hw att σ₀ cb T hcb (fun x : Su s => FreeGroup.mk (lw s x))) ?_ ?_
  · intro s x
    simp [bqHomW]
  · intro s m
    cases m with
    | inl f =>
        show bqHomW ρ w hw att σ₀ cb T hcb _
          (FreeGroup.map Sum.inr (SpanningTree.treeRel T f)) = 1
        exact bqHomW_treeRel ρ w hw att σ₀ cb T hcb _ f
    | inr x => exact bqHomW_markRel ρ w hw att σ₀ cb T hcb (lw s) (sig s) (hsig s) (hread s) x

/-- **The theorem applied to the block, with `hfill` derived from the filling of the surface
relator**, over the model built on the prescribed relator words. -/
theorem injective_substHomF_of_surfaceW {α Jr Sx : Type u} {Su : Sx → Type u}
    (ρ : Jr ⊕ Sx → FreeGroup α) (w : Jr ⊕ Sx → List (α × Bool))
    (hw : ∀ j, FreeGroup.mk (w j) = ρ j) (att : NeSpx A →o PresPos w) (σ₀ : NeSpx A)
    (cb : List ((orderCx (PresPos w)).E × Bool))
    (hcb : IsPath (orderCx (PresPos w)).src (orderCx (PresPos w)).tgt cb (ptBase w) (att σ₀))
    (T : SpanningTree (orderCx (QOld A)))
    (sig : ∀ s : Sx, Su s → List ((orderCx (NeSpx A)).E × Bool))
    (hsig : ∀ (s : Sx) (x : Su s),
      IsPath (orderCx (NeSpx A)).src (orderCx (NeSpx A)).tgt (sig s x) σ₀ σ₀)
    (lw : ∀ s : Sx, Su s → List (α × Bool)) (ps : ∀ s : Sx, List (Su s × Su s))
    (hread : ∀ (s : Sx) (x : Su s),
      Htpy (orderCx (PresPos w)) (ptBase w) (ptBase w)
        (cb ++ mapPath (orderCxMap att att.monotone) (sig s x) ++ revPath cb)
        (wordLoop w (lw s x)))
    (hrho : ∀ s : Sx, ρ (Sum.inr s) = commWord (fun x => FreeGroup.mk (lw s x)) (ps s))
    (hfilling : ∀ s : Sx,
      commWord (fun x => Pi1.mk (⟨sig s x, hsig s x⟩ : Loop (orderCx (NeSpx A)) σ₀)) (ps s) = 1) :
    Function.Injective (BlockFamily.substHomF ρ (fun s m =>
      BlockFamily.blockSubst (Zt := fun _ => spineGens T)
        (fun s x => FreeGroup.mk (lw s x)) s (spineBeta T (sig s) m))
      (filledF_of_surface_filling ρ T σ₀ sig hsig lw ps hrho hfilling)) :=
  injective_substHomF_of_spineW ρ w hw att σ₀ cb hcb T sig hsig lw hread
    (filledF_of_surface_filling ρ T σ₀ sig hsig lw ps hrho hfilling)

end Davis
end FiniteChains
