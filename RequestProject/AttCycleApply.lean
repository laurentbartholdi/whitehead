module

public import RequestProject.AttCycleLoop
public import RequestProject.BlockSpineSubst

@[expose] public section

/-!
# The concrete block: the theorem applied

This file puts the two halves together.  `RequestProject/BlockSpinePres.lean` and
`RequestProject/BlockSpineSubst.lean` construct, for an arbitrary nerve and an arbitrary
attaching map, the spine of the block, its marked presentation, its geometric loops and the
fillings of its relators, and deduce the injectivity of the structural homomorphism of the
simultaneous substitution.  `RequestProject/AttCycle.lean` and
`RequestProject/AttCycleLoop.lean` produce a concrete attaching map: the labelled cycle with
`2·|u|` vertices, mapped onto the subdivided rose so that going once around the cycle spells the
prescribed word `u`.

The result is `FiniteChains.Davis.injective_substHomF_cycle`: for the block whose nerve is that
cycle, whose internal generators are the edges of its cube complex outside a spanning tree and
whose relators are the two-cells of the cube complex together with the marking relator of the
distinguished generator, the structural homomorphism of the substitution is injective.  The only
hypothesis left is `hfill`, the hypothesis (B1) of the substitution itself, which is an input of
the construction and not of the geometry.

The nerve here is a cycle, that is, a triangulation of the circle; the general theorem it is fed
into holds for every nerve, so replacing the cycle by a flag triangulation of the closed surface
of genus `q` carrying the same labels — the nerve of the article's block `B_q` — changes nothing
in the argument below.
-/

namespace FiniteChains
namespace Davis

open RACG Mirror Comb PresModel BlockFamily

/-- The cut surface of the concrete block is nonempty, and the block carries a spanning tree
rooted at the cell of the cut surface which carries the base point of the loop. -/
theorem exists_spanningTree_cycle {α : Type} (l : List (α × Bool)) (hl : 2 ≤ l.length) :
    ∃ T : SpanningTree (orderCx (QOld (cycA l hl))), T.root = posQCube (vtxSpx l hl 0) := by
  haveI : Nonempty (Fin (2 * l.length)) := ⟨⟨0, by omega⟩⟩
  exact exists_spanningTree_qOld _

/-- **The concrete block, and the theorem applied to it.**

The nerve is the cycle with `2·|u|` vertices labelled by the word `u = l`; the block is the
truncated cube complex of that nerve; its internal generators `Z` are the edges of the
two-dimensional order complex of the block outside the spanning tree `T`, and its relators are
the two-cells of the block together with one marking relator, which says that the distinguished
generator is the word spelled inside the block by the loop that goes once around the cycle.  The
attaching map `attCyc` reads exactly the word `u` along that loop, so the marking relator is
filled by the mapping cylinder and the two-cells fill the remaining relators.  Consequently the
structural homomorphism of the simultaneous substitution by this block is injective. -/
theorem injective_substHomF_cycle {α Jr : Type} (ρ : Jr ⊕ PUnit → FreeGroup α)
    (l : List (α × Bool)) (hl : 2 ≤ l.length)
    (T : SpanningTree (orderCx (QOld (cycA l hl))))
    (hfill : BlockFamily.FilledF ρ (fun s m =>
      BlockFamily.blockSubst (Zt := fun _ => spineGens T)
        (fun (_ : PUnit) (_ : PUnit) => FreeGroup.mk l) s
        (spineBeta T (fun _ : PUnit => sigLoop l hl l.length) m))) :
    Function.Injective (BlockFamily.substHomF ρ (fun s m =>
      BlockFamily.blockSubst (Zt := fun _ => spineGens T)
        (fun (_ : PUnit) (_ : PUnit) => FreeGroup.mk l) s
        (spineBeta T (fun _ : PUnit => sigLoop l hl l.length) m)) hfill) := by
  refine injective_substHomF_of_spine ρ (attCyc (presWords ρ) l hl) (vtxSpx l hl 0) []
    ((att_base (presWords ρ) l hl).symm) T (fun _ _ => sigLoop l hl l.length)
    (fun _ _ => isPath_sigLoop_full l hl) (fun _ _ => l) ?_ hfill
  intro s x
  have h := mapPath_sigLoop_full (presWords ρ) l hl
  simp only [List.nil_append, List.append_nil, revPath, List.map_nil, List.reverse_nil, h]
  exact Htpy.refl _

end Davis
end FiniteChains
