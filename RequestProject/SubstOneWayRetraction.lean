module

public import RequestProject.SubstOneWayBlockLoops

@[expose] public section

/-!
# Block maps which are actually written down: the retracting blocks

The loop-level interface of `RequestProject/SubstOneWayBlockLoops.lean` needs, per block, one
edge loop for every internal generator and one filling for every block relator.  This file
exhibits a family of substitutions for which **those loops are written down explicitly** and the
block maps are therefore constructed unconditionally, with no geometric hypothesis left:

* the block at `s` **retracts to the base** if every internal generator `z ∈ Zt s` is given a
  word `zw s z` in the old generators such that every block relator becomes trivial in the source
  presentation group after the substitution `z ↦ zw s z`;
* `FiniteChains.BlockFamily.blockMapsOfRetraction` — the block maps, algebraically, over the
  identity of the source presentation group;
* `FiniteChains.BlockFamily.injective_substHomF_of_retraction` — hence **the structural
  homomorphism of the actual substitution is injective**, unconditionally;
* `FiniteChains.Davis.retractionLoop`, `FiniteChains.Davis.blockMapsOfRetractionLoops` — the same
  block maps realised geometrically over the quotient `Q = Z/Γ` of the model of modified
  chambers: the internal generator `z` is carried by the concrete edge loop in `orderCx Q`
  spelling the word `zw s z` in the rose of the base copy, and both the marking equalities and
  the block relations are checked for these actual loops;
* `FiniteChains.Davis.injective_substHomF_of_retractionLoops` — the resulting injectivity, this
  time through the geometric comparison `FiniteChains.Davis.baseToQuotient`.

This is the case in which the geometric input of the one-way comparison can be produced from the
substitution data alone.  It is not vacuous — `RequestProject/SubstOneWayNoVacuity.lean` shows
that no such data exists for a substitution whose structural map fails to be injective — and it
shows the loop interface of `SubstOneWayBlockLoops` is instantiable by explicit loops.
-/

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains

universe u v

namespace BlockFamily

variable {α Jr Sx : Type u} {Zt Mt : Sx → Type u}

/-- The substitution of the retraction: an old generator is kept, an internal generator of the
block at `s` is read as the prescribed old word. -/
def retractSubst (zw : ∀ s : Sx, Zt s → FreeGroup α) (s : Sx) :
    FreeGroup (α ⊕ Zt s) →* FreeGroup α :=
  FreeGroup.lift (Sum.elim FreeGroup.of (zw s))

@[simp] theorem retractSubst_inl (zw : ∀ s : Sx, Zt s → FreeGroup α) (s : Sx) (a : α) :
    retractSubst (Zt := Zt) zw s (FreeGroup.of (Sum.inl a)) = FreeGroup.of a := by
  simp [retractSubst]

@[simp] theorem retractSubst_inr (zw : ∀ s : Sx, Zt s → FreeGroup α) (s : Sx) (z : Zt s) :
    retractSubst zw s (FreeGroup.of (Sum.inr z)) = zw s z := by
  simp [retractSubst]

/-- **The block maps of a retracting block**, over the identity of the source presentation
group: the generator `z` of the block goes to the class of the word prescribed for it. -/
def blockMapsOfRetraction {ρ : Jr ⊕ Sx → FreeGroup α}
    (bsub : ∀ s : Sx, Mt s → FreeGroup (α ⊕ Zt s)) (zw : ∀ s : Sx, Zt s → FreeGroup α)
    (hret : ∀ (s : Sx) (m : Mt s),
      (QuotientGroup.mk (retractSubst zw s (bsub s m)) : PresGroup ρ) = 1) :
    BlockMaps ρ bsub (MonoidHom.id (PresGroup ρ)) where
  b s := (QuotientGroup.mk' (relSub ρ)).comp (retractSubst zw s)
  mark s a := by simp
  rel s m := by
    show (QuotientGroup.mk (retractSubst zw s (bsub s m)) : PresGroup ρ) = 1
    exact hret s m

/-- **The structural homomorphism of a retracting substitution is injective**, with no further
input: the block maps are produced from the retraction words. -/
theorem injective_substHomF_of_retraction {ρ : Jr ⊕ Sx → FreeGroup α}
    (bsub : ∀ s : Sx, Mt s → FreeGroup (α ⊕ Zt s)) (hfill : FilledF ρ bsub)
    (zw : ∀ s : Sx, Zt s → FreeGroup α)
    (hret : ∀ (s : Sx) (m : Mt s),
      (QuotientGroup.mk (retractSubst zw s (bsub s m)) : PresGroup ρ) = 1) :
    Function.Injective (substHomF ρ bsub hfill) :=
  (blockMapsOfRetraction bsub zw hret).injective_substHomF hfill Function.injective_id

/-! ### A worked example: a block with an internal generator -/

section Example

/-- One old generator `a`. -/
abbrev retAlpha : Type u := PUnit.{u + 1}

/-- No retained relator entries. -/
abbrev retJr : Type u := PEmpty.{u + 1}

/-- One replaced relator entry. -/
abbrev retSx : Type u := PUnit.{u + 1}

/-- The block has one internal generator `z`. -/
abbrev retZt : retSx.{u} → Type u := fun _ => PUnit.{u + 1}

/-- The block has one relator. -/
abbrev retMt : retSx.{u} → Type u := fun _ => PUnit.{u + 1}

/-- The source presentation `⟨a ∣ 1⟩`. -/
def retRho : retJr.{u} ⊕ retSx.{u} → FreeGroup retAlpha.{u} := fun _ => 1

/-- The substituted block `⟨a, z ∣ z a⁻¹⟩`: its internal generator is identified with the old
generator. -/
def retBsub : ∀ s : retSx.{u}, retMt.{u} s → FreeGroup (retAlpha.{u} ⊕ retZt.{u} s) :=
  fun _ _ => FreeGroup.of (Sum.inr PUnit.unit) * (FreeGroup.of (Sum.inl PUnit.unit))⁻¹

theorem retFilled : FilledF retRho.{u} retBsub.{u} := by
  intro s
  have h : FreeGroup.map (Sum.inl (β := Σ s : retSx.{u}, retZt.{u} s)) (retRho (Sum.inr s))
      = 1 := by simp [retRho]
  rw [h]
  exact one_mem _

/-- The retraction of the block: the internal generator is read as the old generator. -/
def retZw : ∀ s : retSx.{u}, retZt.{u} s → FreeGroup retAlpha.{u} :=
  fun _ _ => FreeGroup.of PUnit.unit

/-- **The worked example**: the block has a genuine internal generator, the retraction words
are written down, and the structural homomorphism of the substitution is injective. -/
theorem injective_substHomF_retraction_example :
    Function.Injective (substHomF retRho.{u} retBsub.{u} retFilled.{u}) := by
  refine injective_substHomF_of_retraction retBsub.{u} retFilled.{u} retZw.{u} ?_
  intro s m
  have h : retractSubst retZw.{u} s (retBsub.{u} s m) = 1 := by
    simp [retBsub, retZw, retractSubst]
  rw [h, QuotientGroup.mk_one]

end Example

end BlockFamily

namespace Davis

open RACG Mirror Comb PresModel BlockFamily

variable {V : Type u} [DecidableEq V] [Fintype V] {A : CommRel V}
  {α Jr Sx : Type u} {Zt Mt : Sx → Type u} (ρ : Jr ⊕ Sx → FreeGroup α)
  (att : NeSpx A →o presModelPos ρ)

/-- **The concrete loop of an internal generator of a retracting block**: the edge loop of
`orderCx Q` spelling, in the rose of the base copy, the word prescribed for that generator. -/
noncomputable def retractionLoop (zw : ∀ s : Sx, Zt s → FreeGroup α) (s : Sx) (z : Zt s) :
    Loop (orderCx (Qpos A (presModelPos ρ) att)) (qBasePt (A := A) ρ att) :=
  oldWordLoop (A := A) ρ att zw s z

omit [Fintype V] in
/-- The block homomorphism carried by those loops is the composite of the projection to the
source presentation group with the constructed geometric comparison. -/
theorem blockLoopHom_retractionLoop (zw : ∀ s : Sx, Zt s → FreeGroup α) (s : Sx)
    (x : FreeGroup (α ⊕ Zt s)) :
    blockLoopHom (A := A) ρ att (retractionLoop (A := A) ρ att zw) s x
      = baseToQuotient (A := A) ρ att (QuotientGroup.mk (retractSubst zw s x)) := by
  have key : blockLoopHom (A := A) ρ att (retractionLoop (A := A) ρ att zw) s
      = ((baseToQuotient (A := A) ρ att).comp (QuotientGroup.mk' (relSub ρ))).comp
          (retractSubst zw s) := by
    refine FreeGroup.ext_hom _ _ ?_
    rintro (a | z)
    · rw [blockLoopHom, loopHom_of]
      simpa [blockGenLoop] using pi1_mk_oldLoop (A := A) ρ att a
    · rw [blockLoopHom, loopHom_of]
      simpa [blockGenLoop, retractionLoop] using pi1_mk_oldWordLoop (A := A) ρ att zw s z
  exact DFunLike.congr_fun key x

/-- **The block maps of a retracting block, realised by explicit loops in the quotient.**  Every
generator of the block carries an actual edge loop of `orderCx Q`: an old generator its loop in
the rose of the base copy, an internal generator the loop of the word prescribed for it.  The
marking equalities hold for these loops, and every block relator dies. -/
noncomputable def blockMapsOfRetractionLoops
    (bsub : ∀ s : Sx, Mt s → FreeGroup (α ⊕ Zt s)) (zw : ∀ s : Sx, Zt s → FreeGroup α)
    (hret : ∀ (s : Sx) (m : Mt s),
      (QuotientGroup.mk (retractSubst zw s (bsub s m)) : PresGroup ρ) = 1) :
    BlockMaps ρ bsub (baseToQuotient (A := A) ρ att) where
  b := blockLoopHom (A := A) ρ att (retractionLoop (A := A) ρ att zw)
  mark s a := by
    rw [blockLoopHom, loopHom_of]
    exact pi1_mk_oldLoop (A := A) ρ att a
  rel s m := by
    rw [blockLoopHom_retractionLoop (A := A) ρ att zw s (bsub s m), hret s m, map_one]

include A att in
/-- **The injectivity of the actual `substHomF` through the geometric comparison**, for a
retracting block family: the block maps are the explicit loops of
`FiniteChains.Davis.retractionLoop`. -/
theorem injective_substHomF_of_retractionLoops
    (bsub : ∀ s : Sx, Mt s → FreeGroup (α ⊕ Zt s)) (hfill : FilledF ρ bsub)
    (zw : ∀ s : Sx, Zt s → FreeGroup α)
    (hret : ∀ (s : Sx) (m : Mt s),
      (QuotientGroup.mk (retractSubst zw s (bsub s m)) : PresGroup ρ) = 1) :
    Function.Injective (substHomF ρ bsub hfill) :=
  (blockMapsOfRetractionLoops (A := A) ρ att bsub zw hret).injective_substHomF hfill
    (baseToQuotient_injective (A := A) ρ att)

end Davis
end FiniteChains
