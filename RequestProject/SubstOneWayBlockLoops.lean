import RequestProject.SubstOneWayQuotient
import RequestProject.CombLoopWord

/-!
# The block maps as concrete loops on the generators

`RequestProject/SubstOneWayQuotient.lean` reduces the injectivity of the structural homomorphism
`FiniteChains.BlockFamily.substHomF` of the actual substitution to the existence of the marked
block maps `FiniteChains.BlockFamily.BlockMaps` over the constructed comparison
`FiniteChains.Davis.baseToQuotient`.  This file removes the last piece of abstraction from that
input: a block map is **built here from concrete edge loops on the generators of the block**, and
the marking equalities are **proved**, not assumed.

Concretely, for the quotient `Q = Z/Γ` of the model of modified chambers over the poset model of
the presentation complex of `ρ`:

* `FiniteChains.Davis.oldLoop a` — the actual edge loop of the old generator `a` in
  `orderCx Q`: the loop of `a` in the rose of the base copy, pushed into the quotient;
* `FiniteChains.Davis.pi1_mk_oldLoop` — **the marking equality is verified**: the class of that
  loop is the image of `a` under the constructed comparison `baseToQuotient`;
* `FiniteChains.Davis.oldWordLoop s x` — the loop spelling the prescribed old word `u s x`
  (the article's `u_h`, `v_h`), and `FiniteChains.Davis.pi1_mk_oldWordLoop`, again a proved
  marking equality `[loop of u_h] = j [u_h]`;
* `FiniteChains.Davis.blockLoopHom` — the block homomorphism determined by the loops: old
  generators get `oldLoop`, the internal generators `Zt s` get the loops supplied for them;
* `FiniteChains.Davis.injective_substHomF_of_blockLoops` and
  `FiniteChains.Davis.injective_substHomF_of_markedBlockLoops` — **the injectivity of the actual
  `substHomF`** from that data.

After this file the only input left for the article's blocks is genuinely geometric and is
exactly one item per block generator and per block relator: an edge loop in `orderCx Q` for each
internal generator `z ∈ Zt s`, and a combinatorial null-homotopy of the concatenated loop of
each block relator `β_m`.  Nothing else about the blocks is assumed: the maps on the old and on
the distinguished generators are written down, and all their marked relations are checked.
-/

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains
namespace Davis

open RACG Mirror Comb PresModel BlockFamily

universe u

variable {V : Type u} [DecidableEq V] [Fintype V] {A : CommRel V}

section Loops

variable {α J : Type u} (ρ : J → FreeGroup α) (att : NeSpx A →o presModelPos ρ)

omit [Fintype V]

/-- The cellular map of the inclusion of the base copy in the quotient `Q = Z/Γ`. -/
noncomputable abbrev qInclCx : Hom (orderCx (presModelPos ρ)) (orderCx (Qpos A (presModelPos ρ) att)) :=
  orderCxMap (qNew (A := A) (X := presModelPos ρ) (att := att)) qNew_monotone

/-- The base point of the quotient: the base point of the rose of the base copy. -/
noncomputable abbrev qBasePt : (orderCx (Qpos A (presModelPos ρ) att)).V := qNew (A := A) (att := att)
  (presBasePt ρ)

/-- **The loop of an old generator in the quotient**: the four-edge loop of the generator in the
rose of the base copy, pushed into `Q`. -/
noncomputable def oldLoop (a : α) : Loop (orderCx (Qpos A (presModelPos ρ) att)) (qBasePt (A := A) ρ att) :=
  ⟨mapPath (qInclCx (A := A) ρ att) (genLoop (presWords ρ) a),
    isPath_mapPath _ (isPath_genLoop (presWords ρ) a)⟩

/-- **The marking equality for a generator is verified**: the class of the concrete loop of the
old generator `a` is its image under the constructed comparison. -/
theorem pi1_mk_oldLoop (a : α) :
    Pi1.mk (oldLoop (A := A) ρ att a)
      = baseToQuotient (A := A) ρ att (QuotientGroup.mk (FreeGroup.of a)) := by
  have h : baseToQuotient (A := A) ρ att (QuotientGroup.mk (FreeGroup.of a))
      = Comb.pi1Map (qInclCx (A := A) ρ att) (presBasePt ρ)
          (alphaHom ρ (QuotientGroup.mk (FreeGroup.of a))) := rfl
  rw [h, alphaHom_gen]
  rfl

/-- The homomorphism of the free group on the old generators given by their loops. -/
noncomputable def oldLoopHom :
    FreeGroup α →* Pi1 (orderCx (Qpos A (presModelPos ρ) att)) (qBasePt (A := A) ρ att) :=
  loopHom (oldLoop (A := A) ρ att)

/-- The homomorphism given by the loops of the old generators is the constructed comparison
composed with the projection to the presentation group. -/
theorem oldLoopHom_eq (x : FreeGroup α) :
    oldLoopHom (A := A) ρ att x = baseToQuotient (A := A) ρ att (QuotientGroup.mk x) := by
  have key : oldLoopHom (A := A) ρ att
      = (baseToQuotient (A := A) ρ att).comp (QuotientGroup.mk' (relSub ρ)) := by
    refine FreeGroup.ext_hom _ _ fun a => ?_
    rw [oldLoopHom, loopHom_of, MonoidHom.comp_apply]
    exact pi1_mk_oldLoop (A := A) ρ att a
  exact DFunLike.congr_fun key x

variable {Sx : Type u} {Su : Sx → Type u}

/-- **The loop spelling a prescribed old word.**  For the article's markings `s_h ↦ u_h`,
`t_h ↦ v_h` this is the actual edge loop of the word `u_h` in the base copy of the quotient. -/
noncomputable def oldWordLoop (u : ∀ s : Sx, Su s → FreeGroup α) (s : Sx) (x : Su s) :
    Loop (orderCx (Qpos A (presModelPos ρ) att)) (qBasePt (A := A) ρ att) :=
  wordLoopOf (oldLoop (A := A) ρ att) (Quot.out (u s x))

/-- **The marking equality of the article is verified**: the class of the concrete loop
spelling `u_h` is the image of `[u_h]` under the constructed comparison. -/
theorem pi1_mk_oldWordLoop (u : ∀ s : Sx, Su s → FreeGroup α) (s : Sx) (x : Su s) :
    Pi1.mk (oldWordLoop (A := A) ρ att u s x)
      = baseToQuotient (A := A) ρ att (QuotientGroup.mk (u s x)) := by
  rw [oldWordLoop, ← loopHom_mk, ← oldLoopHom, oldLoopHom_eq,
    show FreeGroup.mk (Quot.out (u s x)) = u s x from Quot.out_eq _]

end Loops

section BlockLoops

variable {α Jr Sx : Type u} {Zt Mt : Sx → Type u} (ρ : Jr ⊕ Sx → FreeGroup α)
  (att : NeSpx A →o presModelPos ρ)

/-- The loops of the generators of the substituted block at `s`: an old generator carries its
own loop in the base copy, an internal generator the loop supplied for it. -/
noncomputable def blockGenLoop
    (lz : ∀ s : Sx, Zt s → Loop (orderCx (Qpos A (presModelPos ρ) att))
      (qBasePt (A := A) ρ att)) (s : Sx) :
    α ⊕ Zt s → Loop (orderCx (Qpos A (presModelPos ρ) att)) (qBasePt (A := A) ρ att) :=
  Sum.elim (oldLoop (A := A) ρ att) (lz s)

/-- **The block homomorphism determined by the loops of the generators.** -/
noncomputable def blockLoopHom
    (lz : ∀ s : Sx, Zt s → Loop (orderCx (Qpos A (presModelPos ρ) att))
      (qBasePt (A := A) ρ att)) (s : Sx) :
    FreeGroup (α ⊕ Zt s) →*
      Pi1 (orderCx (Qpos A (presModelPos ρ) att)) (qBasePt (A := A) ρ att) :=
  loopHom (blockGenLoop (A := A) ρ att lz s)

/-- **The block maps built from loops.**  The marking on the old generators is proved; the only
hypothesis is that the concatenated loop of every block relator is null-homotopic. -/
noncomputable def blockMapsOfLoops
    (bsub : ∀ s : Sx, Mt s → FreeGroup (α ⊕ Zt s))
    (lz : ∀ s : Sx, Zt s → Loop (orderCx (Qpos A (presModelPos ρ) att))
      (qBasePt (A := A) ρ att))
    (bw : ∀ (s : Sx), Mt s → List ((α ⊕ Zt s) × Bool))
    (hbw : ∀ (s : Sx) (m : Mt s), FreeGroup.mk (bw s m) = bsub s m)
    (hfillLoop : ∀ (s : Sx) (m : Mt s),
      Htpy (orderCx (Qpos A (presModelPos ρ) att)) (qBasePt (A := A) ρ att)
        (qBasePt (A := A) ρ att) (wordPath (blockGenLoop (A := A) ρ att lz s) (bw s m)) []) :
    BlockMaps ρ bsub (baseToQuotient (A := A) ρ att) where
  b := blockLoopHom (A := A) ρ att lz
  mark := by
    intro s a
    rw [blockLoopHom, loopHom_of]
    exact pi1_mk_oldLoop (A := A) ρ att a
  rel := by
    intro s m
    rw [blockLoopHom, ← hbw s m]
    exact loopHom_eq_one_of_htpy _ (hfillLoop s m)

/-- **The injectivity of the actual `substHomF` from concrete loops and fillings.**  The input
is: one edge loop in `orderCx Q` for each internal generator of each block, a word spelling each
block relator, and a combinatorial null-homotopy of the loop that this word spells.  Everything
else — the maps on the old generators and their marking equalities — is constructed here. -/
theorem injective_substHomF_of_blockLoops
    (bsub : ∀ s : Sx, Mt s → FreeGroup (α ⊕ Zt s))
    (hfill : FilledF ρ bsub)
    (lz : ∀ s : Sx, Zt s → Loop (orderCx (Qpos A (presModelPos ρ) att))
      (qBasePt (A := A) ρ att))
    (bw : ∀ (s : Sx), Mt s → List ((α ⊕ Zt s) × Bool))
    (hbw : ∀ (s : Sx) (m : Mt s), FreeGroup.mk (bw s m) = bsub s m)
    (hfillLoop : ∀ (s : Sx) (m : Mt s),
      Htpy (orderCx (Qpos A (presModelPos ρ) att)) (qBasePt (A := A) ρ att)
        (qBasePt (A := A) ρ att) (wordPath (blockGenLoop (A := A) ρ att lz s) (bw s m)) []) :
    Function.Injective (substHomF ρ bsub hfill) :=
  (blockMapsOfLoops (A := A) ρ att bsub lz bw hbw hfillLoop).injective_substHomF hfill
    (baseToQuotient_injective (A := A) ρ att)

end BlockLoops

section MarkedBlockLoops

variable {α Jr Sx : Type u} {Zt Mt Su : Sx → Type u} (ρ : Jr ⊕ Sx → FreeGroup α)
  (att : NeSpx A →o presModelPos ρ)

/-- The loops of the generators of the **article's block** `B_q = ⟨s_h, t_h, Z ∣ β_m⟩`: a
distinguished generator carries the loop of the old word prescribed for it, an internal
generator the loop supplied for it. -/
noncomputable def markedGenLoop (u : ∀ s : Sx, Su s → FreeGroup α)
    (lz : ∀ s : Sx, Zt s → Loop (orderCx (Qpos A (presModelPos ρ) att))
      (qBasePt (A := A) ρ att)) (s : Sx) :
    Su s ⊕ Zt s → Loop (orderCx (Qpos A (presModelPos ρ) att)) (qBasePt (A := A) ρ att) :=
  Sum.elim (oldWordLoop (A := A) ρ att u s) (lz s)

/-- **The injectivity of the actual `substHomF` for the article's marked blocks, from concrete
loops.**  The block at `s` is `⟨Su s, Zt s ∣ β_m⟩` and the substitution reads the distinguished
generators as the prescribed old words `u s`.  The only input is one edge loop per internal
generator and one null-homotopy per block relator; the loops of the distinguished generators are
the loops of the prescribed words, and the two marking equalities `[s_h] ↦ j [u_h]`,
`[t_h] ↦ j [v_h]` are proved here. -/
theorem injective_substHomF_of_markedBlockLoops
    (u : ∀ s : Sx, Su s → FreeGroup α)
    (beta : ∀ s : Sx, Mt s → FreeGroup (Su s ⊕ Zt s))
    (hfill : FilledF ρ (fun s m => blockSubst u s (beta s m)))
    (lz : ∀ s : Sx, Zt s → Loop (orderCx (Qpos A (presModelPos ρ) att))
      (qBasePt (A := A) ρ att))
    (bw : ∀ (s : Sx), Mt s → List ((Su s ⊕ Zt s) × Bool))
    (hbw : ∀ (s : Sx) (m : Mt s), FreeGroup.mk (bw s m) = beta s m)
    (hfillLoop : ∀ (s : Sx) (m : Mt s),
      Htpy (orderCx (Qpos A (presModelPos ρ) att)) (qBasePt (A := A) ρ att)
        (qBasePt (A := A) ρ att) (wordPath (markedGenLoop (A := A) ρ att u lz s) (bw s m)) []) :
    Function.Injective (substHomF ρ (fun s m => blockSubst u s (beta s m)) hfill) := by
  refine injective_substHomF_of_markedBlocks (A := A) ρ att u beta hfill
    (fun s => loopHom (markedGenLoop (A := A) ρ att u lz s)) ?_ ?_
  · intro s x
    rw [loopHom_of]
    exact pi1_mk_oldWordLoop (A := A) ρ att u s x
  · intro s m
    rw [← hbw s m]
    exact loopHom_eq_one_of_htpy _ (hfillLoop s m)

end MarkedBlockLoops

end Davis
end FiniteChains
