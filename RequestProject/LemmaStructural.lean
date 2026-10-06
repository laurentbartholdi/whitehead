import RequestProject.SlideMor
import RequestProject.TietzeElimination
import RequestProject.BlockSubstitutionMor

/-!
# Lemma 3.9: the structural operation `T`

Lemma 3.9 of the paper states, for the replacement operation `T` of Section 3.4 and for every
presentation `P` containing the fixed core `D`,

  `π₂(T(P)) = ℤ[G(T(P))] · η_{P*} π₂(P)`,                                        (3.3)

and draws from it the two consequences: `T` preserves the Cockcroft property, and `T`
preserves the vanishing of the maps induced on `π₂` by the labelled inclusions.

The operation `T` is a *finite sequence of elementary moves*: for every extra generator `z`
rule 1 performs three moves (freely adjoin `b_z`; adjoin the stable letter `a_z` with the
relator `a_z b_z a_z⁻¹ = z b_z`; eliminate `z` by `z = [a_z,b_z]`), rule 2 slides an extra
relator over retained core relators, and rule 3 substitutes a block for an extra relator.
The proof of the lemma treats each move separately and ends with the words "Composing
proves (3.3)".

This file carries out exactly that scheme.

* `FiniteChains.PresPoint` — a finite presentation, bundled with its finiteness data;
* `FiniteChains.TMove` — **one elementary move of the operation `T`**: the moves of rule 1,
  the slide of rule 2, and the block substitution of rule 3.  The block move carries
  the generation property (B2) of the block as data: (B2) is the one input of Lemma 3.9 which
  the paper takes from Theorem 3.2 (its proof is the cubical geometry of Section 3.3), and it
  is the only hypothesis left in this file.  All the other moves carry no hypothesis beyond
  the elementary facts checked in the paper itself;
* `FiniteChains.TMove.generates` — **equation (3.3) for one move**;
* `FiniteChains.TPath` — a finite sequence of moves, that is, the operation `T` itself, and
  `FiniteChains.TPath.mor` its structural map `η_P`;
* `FiniteChains.TPath.generates` — **equation (3.3) for `T`** ("composing proves (3.3)");
* `FiniteChains.TPath.isCockcroft` — **`T` preserves the Cockcroft property**;
* `FiniteChains.TPath.cells_eq_zero` — **the last paragraph of Lemma 3.9**: for a labelled
  inclusion `j : P ⊂ P'` with `T(j) ∘ η_P = η_{P'} ∘ j`, if `j` is zero on `π₂` then `T(j)`
  is zero on the whole of `π₂(T(P))`.
-/

namespace FiniteChains

open MonoidAlgebra

universe u

/-- A finite presentation, bundled with the finiteness data used by the Fox calculus. -/
structure PresPoint : Type (u + 1) where
  /-- The generators. -/
  gens : Type u
  /-- The two-cells, i.e. the relator labels. -/
  cells : Type u
  [fintypeGens : Fintype gens]
  [decEqGens : DecidableEq gens]
  [fintypeCells : Fintype cells]
  [decEqCells : DecidableEq cells]
  /-- The relators. -/
  rel : cells → FreeGroup gens

attribute [instance] PresPoint.fintypeGens PresPoint.decEqGens PresPoint.fintypeCells
  PresPoint.decEqCells

namespace PresPoint

/-- The presentation as a point of the above type. -/
def ofPres {α J : Type u} [Fintype α] [DecidableEq α] [Fintype J] [DecidableEq J]
    (ρ : J → FreeGroup α) : PresPoint.{u} where
  gens := α
  cells := J
  rel := ρ

/-- Freely adjoining one generator. -/
def free (P : PresPoint.{u}) : PresPoint.{u} where
  gens := Option P.gens
  cells := P.cells
  rel := extFree P.rel

/-- Adjoining one generator together with one relator. -/
def ext (P : PresPoint.{u}) (w₀ : FreeGroup (Option P.gens)) : PresPoint.{u} where
  gens := Option P.gens
  cells := Option P.cells
  rel := extRel P.rel w₀

/-- Sliding the relator `j₀` over the other relators. -/
def slide (P : PresPoint.{u}) (j₀ : P.cells) (w : FreeGroup P.gens) : PresPoint.{u} where
  gens := P.gens
  cells := P.cells
  rel := slideRel P.rel j₀ w

end PresPoint

/-- **One elementary move of the operation `T` of Lemma 3.9.**

The constructors `freeGen`, `hnn`, `tietze` and `elim` are the moves of rule 1 (the last two
are the Tietze relation `z = s` read in the two possible directions), `slide` is rule 2, and
`block` is rule 3.  Only the last one carries a hypothesis: the generation
property (B2) of the block, which Lemma 3.9 quotes from Theorem 3.2.  That hypothesis is
exactly what `FiniteChains.generates_of_block_chain_model` produces from the chain model of
the double mapping cylinder together with the relative vanishing `H₂(W̃, U) = 0`, the cubical
input of Section 3.3. -/
inductive TMove : PresPoint.{u} → PresPoint.{u} → Type (u + 1) where
  /-- Rule 1, first move: freely adjoin a generator. -/
  | freeGen (P : PresPoint.{u}) : TMove P P.free
  /-- Rule 1, second move: adjoin a stable letter `z` with `z u z⁻¹ = v`, where the images of
  `u` and `v` have infinite order. -/
  | hnn (P : PresPoint.{u}) (u v : FreeGroup P.gens)
      (hu : ¬ IsOfFinOrder (QuotientGroup.mk u : PresGroup P.rel))
      (hv : ¬ IsOfFinOrder (QuotientGroup.mk v : PresGroup P.rel)) :
      TMove P (P.ext (hnnWord u v))
  /-- Rule 1, third move: the Tietze relator `z = s`. -/
  | tietze (P : PresPoint.{u}) (s : FreeGroup P.gens) : TMove P (P.ext (tietzeWord s))
  /-- Rule 1, third move in the direction used by `T`: *eliminate* the generator `z` through
  its defining relation `z = s`. -/
  | elim (P : PresPoint.{u}) (s : FreeGroup P.gens) : TMove (P.ext (tietzeWord s)) P
  /-- Rule 2: slide the relator `j₀` over the retained relators. -/
  | slide (P : PresPoint.{u}) (j₀ : P.cells) (w : FreeGroup P.gens)
      (hw : w ∈ Subgroup.normalClosure (Set.range (coreRel P.rel j₀)))
      (lam : P.cells → MonoidAlgebra ℤ (PresGroup P.rel)) (hlam0 : lam j₀ = 0)
      (hlam : bdry2 (relSub P.rel) P.rel lam = foxVec (relSub P.rel) w) :
      TMove P (P.slide j₀ w)
  /-- Rule 3: substitute a block for the relator, with its filling and with the generation
  property (B2). -/
  | block {α Z J M : Type u} [Fintype α] [DecidableEq α] [Fintype Z] [DecidableEq Z]
      [Fintype J] [DecidableEq J] [Fintype M] [DecidableEq M]
      (ρ : Option J → FreeGroup α) (bsub : M → FreeGroup (α ⊕ Z))
      (hfill : BlockMor.Filled ρ bsub)
      (c : M → MonoidAlgebra ℤ (PresGroup (BlockMor.substPres ρ bsub)))
      (hc : BlockMor.IsFilling ρ bsub hfill c)
      (hB2 : Generates (BlockMor.substMor ρ bsub hfill c hc)) :
      TMove (PresPoint.ofPres ρ) (PresPoint.ofPres (BlockMor.substPres ρ bsub))

namespace TMove

/-- The structural map of one elementary move. -/
noncomputable def mor : ∀ {P Q : PresPoint.{u}}, TMove P Q → PresMor P.rel Q.rel
  | _, _, .freeGen P => freeMor P.rel
  | _, _, .hnn P u v _ _ => extMor P.rel (hnnWord u v)
  | _, _, .tietze P s => extMor P.rel (tietzeWord s)
  | _, _, .elim P s => elimMor P.rel s
  | _, _, .slide P j₀ w hw lam hlam0 hlam => slideMor P.rel j₀ w hw lam hlam0 hlam
  | _, _, @TMove.block α Z J M _ instDa instFz instDz instFj instDj instFm instDm
      ρ bsub hfill c hc _ =>
      @BlockMor.substMor α Z J M ρ bsub hfill instDa instDz instFj instFm c hc

/-- **Equation (3.3) for one elementary move of `T`.**  For the moves of rules 1 and 2 this
is a theorem of the present development; for the move of rule 3 it is the property (B2)
carried by the move. -/
theorem generates {P Q : PresPoint.{u}} (m : TMove P Q) : Generates m.mor := by
  cases m with
  | freeGen P => exact generates_freeMor P.rel
  | hnn P u v hu hv => exact generates_hnnMor P.rel u v hu hv
  | tietze P s => exact generates_tietzeMor P.rel s
  | elim P s => exact generates_elimMor _ _
  | slide P j₀ w hw lam hlam0 hlam => exact generates_slideMor P.rel j₀ w hw lam hlam0 hlam
  | block ρ bsub hfill c hc hB2 => exact hB2

end TMove

/-- **The operation `T`**: a finite sequence of elementary moves. -/
inductive TPath : PresPoint.{u} → PresPoint.{u} → Type (u + 1) where
  /-- The empty sequence. -/
  | nil (P : PresPoint.{u}) : TPath P P
  /-- One move followed by a sequence of moves. -/
  | cons {P Q R : PresPoint.{u}} (m : TMove P Q) (t : TPath Q R) : TPath P R

namespace TPath

/-- The structural map `η_P : P → T(P)` of the whole sequence of moves. -/
noncomputable def mor : ∀ {P Q : PresPoint.{u}}, TPath P Q → PresMor P.rel Q.rel
  | _, _, .nil P => PresMor.id P.rel
  | _, _, .cons m t => (mor t).comp m.mor

/-- **Equation (3.3) for the operation `T`.**  "Composing proves (3.3)": the generation
property holds for every finite sequence of elementary moves. -/
theorem generates {P Q : PresPoint.{u}} (t : TPath P Q) : Generates t.mor := by
  induction t with
  | nil P => exact fun v hv => Submodule.subset_span ⟨v, hv, rfl⟩
  | cons m t ih => exact ih.comp m.generates

/-- **The operation `T` preserves the Cockcroft property** (the second assertion of
Lemma 3.9). -/
theorem isCockcroft {P Q : PresPoint.{u}} (t : TPath P Q) (hP : IsCockcroft P.rel) :
    IsCockcroft Q.rel :=
  isCockcroft_of_generates t.mor t.generates hP

/-- **The last paragraph of Lemma 3.9.**  Let `j : P ⊂ P'` be a labelled inclusion, let `t`
be the sequence of moves performed on `P` and `T(j)` the induced map, so that
`T(j) ∘ η_P = η_{P'} ∘ j`.  If `j` is zero on `π₂`, then `T(j)` is zero on the whole of
`π₂(T(P))`. -/
theorem cells_eq_zero {P P' Q Q' : PresPoint.{u}} (t : TPath P Q) (t' : TPath P' Q')
    (jm : PresMor P.rel P'.rel) (Tj : PresMor Q.rel Q'.rel)
    (hsq : ∀ y, Tj.cells (t.mor.cells y) = t'.mor.cells (jm.cells y))
    (hzero : ∀ y, IsFoxCycle P.rel y → jm.cells y = 0)
    {v : Q.cells → MonoidAlgebra ℤ (PresGroup Q.rel)} (hv : IsFoxCycle Q.rel v) :
    Tj.cells v = 0 :=
  cells_eq_zero_of_generates t.mor t'.mor jm Tj hsq hzero t.generates hv

end TPath

end FiniteChains
