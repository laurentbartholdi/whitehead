module

public import RequestProject.GenusFullCubeCoverFillings
public import RequestProject.DeckChainTransport

@[expose] public section

/-! Equivariant cap fillings obtained by translating one actual filling per disk. -/
namespace FiniteChains.Davis.Genus
open RACG Mirror Comb
variable (q : ℕ) [NeZero q]

noncomputable abbrev fullCubeMarkBase := (markedSpineToFullCube q).onV (markedSpineBase q)
noncomputable abbrev fullCubeMarkCover := uCover (orderCx (QCube (cmpRel (GenusVertex q)))) (fullCubeMarkBase q)

noncomputable def fullCubeBaseCapChain (x : Fin q × Bool) : (fullCubeMarkCover q).F →₀ ℤ :=
  fullCubeCoverCapChain q x (UV.base _ (fullCubeMarkBase q)) rfl

noncomputable def equivariantCapChain
    (g : Pi1 (orderCx (QCube (cmpRel (GenusVertex q)))) (fullCubeMarkBase q))
    (x : Fin q × Bool) : (fullCubeMarkCover q).F →₀ ℤ :=
  (univDeck _ (fullCubeMarkBase q)).faceChains g (fullCubeBaseCapChain q x)

/-- A translated cap chain fills precisely the lift at the translated base vertex. -/
theorem equivariantCapChain_boundary
    (g : Pi1 (orderCx (QCube (cmpRel (GenusVertex q)))) (fullCubeMarkBase q))
    (x : Fin q × Bool) :
    Comb.bdry2 _ (equivariantCapChain q g x) = pathChain
      (uLiftPath (mapPath (markedSpineToFullCube q) (markedSpineLoop q x).1)
        (deckV g (UV.base _ (fullCubeMarkBase q)))) := by
  have h := (univDeck _ (fullCubeMarkBase q)).transport_filling g
    (fullCubeBaseCapChain q x) _
    (fullCubeCoverCapChain_boundary q x (UV.base _ (fullCubeMarkBase q)) rfl)
  have he := uLiftPath_deckV g
    (mapPath (markedSpineToFullCube q) (markedSpineLoop q x).1)
    (UV.base _ (fullCubeMarkBase q)) (fullCubeMarkBase q)
    (isPath_mapPath (markedSpineToFullCube q) (markedSpineLoop q x).2)
  change Comb.bdry2 _ (equivariantCapChain q g x) = _ at h
  rw [he]
  exact h

/-- The chosen family is equivariant by construction, rather than by a choice assumption. -/
theorem equivariantCapChain_mul
    (g h : Pi1 (orderCx (QCube (cmpRel (GenusVertex q)))) (fullCubeMarkBase q))
    (x : Fin q × Bool) :
    equivariantCapChain q (g * h) x =
      (univDeck _ (fullCubeMarkBase q)).faceChains g (equivariantCapChain q h x) :=
  DeckAction.faceChains_mul _ _ _ _

/-- Every lift of a cap base is represented by the constructed deck-indexed family. -/
theorem equivariantCapChain_covers_fiber
    (v : UV (orderCx (QCube (cmpRel (GenusVertex q)))) (fullCubeMarkBase q))
    (hv : endV v = fullCubeMarkBase q) :
    ∃! g : Pi1 (orderCx (QCube (cmpRel (GenusVertex q)))) (fullCubeMarkBase q),
      deckV g (UV.base _ (fullCubeMarkBase q)) = v := by
  exact (isRegular_univProj (X := orderCx (QCube (cmpRel (GenusVertex q))))
    (x₀ := fullCubeMarkBase q)).simply_transitive _ _ hv.symm

/-- Augmentation of each translated cap filling is the augmentation of its base filling. -/
theorem equivariantCapChain_hurewicz
    (g : Pi1 (orderCx (QCube (cmpRel (GenusVertex q)))) (fullCubeMarkBase q))
    (x : Fin q × Bool) :
    hurewicz (orderCx (QCube (cmpRel (GenusVertex q)))) (fullCubeMarkBase q)
      (equivariantCapChain q g x) =
    hurewicz (orderCx (QCube (cmpRel (GenusVertex q)))) (fullCubeMarkBase q)
      (fullCubeBaseCapChain q x) :=
  hurewicz_deck_faceChains _ _ _

end FiniteChains.Davis.Genus
