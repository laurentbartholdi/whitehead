module

public import Mathlib

@[expose] public section

/-!
# The substituted block presentation and its fundamental group

Rule 3 of the operation `T` of Section 3.4 replaces a single labelled relator entry `r` of a
presentation `E = ⟨X | R, r⟩`, together with a chosen factorization
`r = ∏_{h=1}^q [u_h, v_h]`, by a substituted copy of the block `B_q`:

  `E' = ⟨X, Z | R, β_j(u_1, v_1, …, u_q, v_q, Z)⟩`,                                   (3.4)

and the paper justifies (3.4) by the homotopy pushout of `K(E) ← Σ_q → K(B_q)`, whose
fundamental group is computed by van Kampen.  This file proves the group-theoretic content of
that computation *directly from the presentations*, with no finiteness assumption whatsoever
(the paper allows infinite complexes and infinitely many substitutions):

* `FiniteChains.BlockSubst.mk_map_inl_relator_eq_one` — the replaced relator `r` is a
  consequence of the substituted block relators, provided the surface word is a consequence of
  the block relators (the algebraic content of the chosen filling `b_q` of property (B1)).
  Hence deleting the entry `r` in (3.4) does not change the presented group;
* `FiniteChains.BlockSubst.baseHom` and `FiniteChains.BlockSubst.blockHom` — the two structural
  maps `π₁(K(E)) → π₁(K(E'))` and `π₁(K(B_q)) → π₁(K(E'))`;
* `FiniteChains.BlockSubst.isPushout` — **the van Kampen conclusion**: `π₁(K(E'))` is the
  pushout of `π₁(K(E)) ← F(s, t) → π₁(K(B_q))`, the two legs being `s_h ↦ u_h, t_h ↦ v_h` and
  the inclusion of the distinguished generators of the block.  Equivalently, homomorphisms out
  of `π₁(K(E'))` are exactly the pairs of homomorphisms out of `π₁(K(E))` and out of
  `π₁(K(B_q))` agreeing on the distinguished generators.

The pushout may equivalently be taken over the surface group `π₁(Σ_q) = ⟨s, t | ω_q⟩` rather
than over the free group on the distinguished generators: both legs kill the surface word, by
the filling hypothesis on the block side and by the relator `r` on the base side
(`FiniteChains.BlockSubst.legs_agree_on_surfaceWord`).

What is *not* proved here — and what the paper obtains from the CAT(0) geometry of the block,
not from the presentation — is that the structural map `π₁(K(E)) → π₁(K(E'))` is injective and
that `π₂(K(E'))` is generated over `ℤ[π₁(K(E'))]` by the image of `π₂(K(E))`.  A pushout of
groups along a map which is injective on one side is in general *not* injective on the other
side, so the injectivity statement of property (B2) genuinely needs the geometric retraction
argument of Lemma 3.6, step 1.
-/

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open scoped commutatorElement

namespace FiniteChains
namespace BlockSubst

open PresentedGroup

universe u v

variable {α Z : Type u} {S : Type v}

/-! ### The substitution homomorphism -/

/-- The substitution `σ : F(S ⊔ Z) → F(X ⊔ Z)` which sends the distinguished generator `s` of
the block to the chosen word `u s` in the generators of `E`, and is the identity on the
internal generators of the block. -/
def subst (u : S → FreeGroup α) : FreeGroup (S ⊕ Z) →* FreeGroup (α ⊕ Z) :=
  FreeGroup.lift
    (Sum.elim (fun s => FreeGroup.map Sum.inl (u s)) (fun z => FreeGroup.of (Sum.inr z)))

@[simp] theorem subst_of_inl (u : S → FreeGroup α) (s : S) :
    subst (Z := Z) u (FreeGroup.of (Sum.inl s)) = FreeGroup.map Sum.inl (u s) := by
  simp [subst]

@[simp] theorem subst_of_inr (u : S → FreeGroup α) (z : Z) :
    subst (α := α) u (FreeGroup.of (Sum.inr z)) = FreeGroup.of (Sum.inr z) := by
  simp [subst]

/-- The relators of the substituted presentation (3.4): the retained relators `R` of `E`, read
in the larger free group, together with the substituted block relators. -/
def substRels (R : Set (FreeGroup α)) (B : Set (FreeGroup (S ⊕ Z))) (u : S → FreeGroup α) :
    Set (FreeGroup (α ⊕ Z)) :=
  (FreeGroup.map (Sum.inl (β := Z)) '' R) ∪ (subst u '' B)

variable (R : Set (FreeGroup α)) (B : Set (FreeGroup (S ⊕ Z))) (u : S → FreeGroup α)

/-- The presented group of (3.4). -/
abbrev SubstGroup : Type u := PresentedGroup (substRels R B u)

/-! ### Elementary consequences of the two families of relators -/

theorem mk_map_inl_mem_relator {w : FreeGroup α} (hw : w ∈ R) :
    mk (substRels R B u) (FreeGroup.map Sum.inl w) = 1 :=
  one_of_mem (Or.inl ⟨w, hw, rfl⟩)

theorem mk_subst_mem_block {w : FreeGroup (S ⊕ Z)} (hw : w ∈ B) :
    mk (substRels R B u) (subst u w) = 1 :=
  one_of_mem (Or.inr ⟨w, hw, rfl⟩)

/-- Every consequence of the block relators becomes, after substitution, a consequence of the
relators of (3.4). -/
theorem mk_subst_eq_one_of_mem_normalClosure {w : FreeGroup (S ⊕ Z)}
    (hw : w ∈ Subgroup.normalClosure B) :
    mk (substRels R B u) (subst u w) = 1 := by
  have hle : Subgroup.normalClosure B ≤
      (Subgroup.normalClosure (substRels R B u)).comap (subst u) := by
    refine Subgroup.normalClosure_le_normal ?_
    intro x hx
    exact Subgroup.subset_normalClosure (Or.inr ⟨x, hx, rfl⟩)
  exact mk_eq_one_iff.2 (hle hw)

/-- **The replaced relator is a consequence of the substituted block.**  If the word `ω` of the
block (the surface word, filled by the chosen map `b_q` of (B1)) is a consequence of the block
relators and substitutes to `r`, then `r` maps to `1` in the group presented by (3.4).  This is
why the entry `r` may be deleted from the relator list. -/
theorem mk_map_inl_relator_eq_one {r : FreeGroup α} {w : FreeGroup (S ⊕ Z)}
    (hw : w ∈ Subgroup.normalClosure B) (hsub : subst u w = FreeGroup.map Sum.inl r) :
    mk (substRels R B u) (FreeGroup.map Sum.inl r) = 1 := by
  rw [← hsub]
  exact mk_subst_eq_one_of_mem_normalClosure R B u hw

/-! ### The two structural maps -/

/-- The image of a word of `F(X)` under the canonical map to the group of (3.4). -/
theorem lift_of_inl (w : FreeGroup α) :
    FreeGroup.lift (fun a : α => (of (Sum.inl a) : SubstGroup R B u)) w
      = mk (substRels R B u) (FreeGroup.map Sum.inl w) :=
  (FreeGroup.lift_unique ((mk (substRels R B u)).comp (FreeGroup.map (Sum.inl (β := Z))))
    (fun a => by simp [PresentedGroup.of]) (x := w)).symm

/-- The image of a word of `F(S ⊔ Z)` under the canonical map to the group of (3.4). -/
theorem lift_subst (w : FreeGroup (S ⊕ Z)) :
    FreeGroup.lift
        (Sum.elim
          (fun s : S => FreeGroup.lift (fun a : α => (of (Sum.inl a) : SubstGroup R B u)) (u s))
          (fun z : Z => (of (Sum.inr z) : SubstGroup R B u))) w
      = mk (substRels R B u) (subst u w) := by
  refine (FreeGroup.lift_unique ((mk (substRels R B u)).comp (subst u)) ?_ (x := w)).symm
  rintro (s | z)
  · simp [lift_of_inl]
  · simp [PresentedGroup.of]

/-- **The structural map `π₁(K(E)) → π₁(K(E'))`.**  Here `E = ⟨X | R, r⟩`, and the hypotheses
say that the replaced relator `r` is filled by the block, so that it is a consequence of the
substituted block relators. -/
def baseHom {r : FreeGroup α} {w : FreeGroup (S ⊕ Z)} (hw : w ∈ Subgroup.normalClosure B)
    (hsub : subst u w = FreeGroup.map Sum.inl r) :
    PresentedGroup (insert r R) →* SubstGroup R B u :=
  toGroup (f := fun a : α => (of (Sum.inl a) : SubstGroup R B u)) <| by
    rintro x (rfl | hx)
    · rw [lift_of_inl]
      exact mk_map_inl_relator_eq_one R B u hw hsub
    · rw [lift_of_inl]
      exact mk_map_inl_mem_relator R B u hx

@[simp] theorem baseHom_of {r : FreeGroup α} {w : FreeGroup (S ⊕ Z)}
    (hw : w ∈ Subgroup.normalClosure B) (hsub : subst u w = FreeGroup.map Sum.inl r) (a : α) :
    baseHom R B u hw hsub (of a) = of (Sum.inl a) :=
  toGroup.of _

/-- **The structural map `π₁(K(B_q)) → π₁(K(E'))`** given by the substitution. -/
def blockHom : PresentedGroup B →* SubstGroup R B u :=
  toGroup (f := Sum.elim
      (fun s : S => FreeGroup.lift (fun a : α => (of (Sum.inl a) : SubstGroup R B u)) (u s))
      (fun z : Z => (of (Sum.inr z) : SubstGroup R B u))) <| by
    intro x hx
    rw [lift_subst]
    exact mk_subst_mem_block R B u hx

@[simp] theorem blockHom_of_inl (s : S) :
    blockHom R B u (of (Sum.inl s))
      = FreeGroup.lift (fun a : α => (of (Sum.inl a) : SubstGroup R B u)) (u s) :=
  toGroup.of _

@[simp] theorem blockHom_of_inr (z : Z) :
    blockHom R B u (of (Sum.inr z)) = (of (Sum.inr z) : SubstGroup R B u) :=
  toGroup.of _

/-- The two structural maps agree on the distinguished generators: the block generator `s` and
the word `u s` of `E` have the same image in the group of (3.4).  These are the two legs of the
pushout square. -/
theorem baseHom_mk_eq_blockHom_of_inl {r : FreeGroup α} {w : FreeGroup (S ⊕ Z)}
    (hw : w ∈ Subgroup.normalClosure B) (hsub : subst u w = FreeGroup.map Sum.inl r) (s : S) :
    baseHom R B u hw hsub (mk (insert r R) (u s)) = blockHom R B u (of (Sum.inl s)) := by
  rw [blockHom_of_inl]
  have key : (baseHom R B u hw hsub).comp (mk (insert r R))
      = FreeGroup.lift (fun a : α => (of (Sum.inl a) : SubstGroup R B u)) :=
    FreeGroup.ext_hom _ _ fun a => baseHom_of R B u hw hsub a
  exact (DFunLike.congr_fun key (u s)).symm

/-! ### The van Kampen conclusion -/

/-- **The group of (3.4) is the pushout.**  Given a group `H`, a homomorphism `φ` from the group
of `E = ⟨X | R, r⟩` and a homomorphism `ψ` from the group of the block which agree on the
distinguished generators (`φ(u s) = ψ(s)`), there is a unique homomorphism out of the group of
(3.4) restricting to `φ` and to `ψ` along the two structural maps. -/
theorem isPushout {H : Type*} [Group H] {r : FreeGroup α} {w : FreeGroup (S ⊕ Z)}
    (hw : w ∈ Subgroup.normalClosure B) (hsub : subst u w = FreeGroup.map Sum.inl r)
    (phi : PresentedGroup (insert r R) →* H) (psi : PresentedGroup B →* H)
    (hagree : ∀ s : S, phi (mk (insert r R) (u s)) = psi (of (Sum.inl s))) :
    ∃! chi : SubstGroup R B u →* H,
      chi.comp (baseHom R B u hw hsub) = phi ∧ chi.comp (blockHom R B u) = psi := by
  classical
  set f : α ⊕ Z → H := Sum.elim (fun a => phi (of a)) (fun z => psi (of (Sum.inr z))) with hf
  have keyphi : (FreeGroup.lift f).comp (FreeGroup.map (Sum.inl (β := Z)))
      = phi.comp (mk (insert r R)) :=
    FreeGroup.ext_hom _ _ fun a => by simp [hf, PresentedGroup.of]
  have hphi : ∀ x : FreeGroup α,
      FreeGroup.lift f (FreeGroup.map (Sum.inl (β := Z)) x) = phi (mk (insert r R) x) :=
    fun x => DFunLike.congr_fun keyphi x
  have keypsi : (FreeGroup.lift f).comp (subst u) = psi.comp (mk B) := by
    refine FreeGroup.ext_hom _ _ ?_
    rintro (s | z)
    · simp only [MonoidHom.coe_comp, Function.comp_apply, subst_of_inl]
      rw [hphi (u s)]
      exact hagree s
    · simp [hf, PresentedGroup.of]
  have hpsi : ∀ x : FreeGroup (S ⊕ Z), FreeGroup.lift f (subst u x) = psi (mk B x) :=
    fun x => DFunLike.congr_fun keypsi x
  have hrel : ∀ x ∈ substRels R B u, FreeGroup.lift f x = 1 := by
    rintro x (⟨y, hy, rfl⟩ | ⟨y, hy, rfl⟩)
    · rw [hphi y, one_of_mem (Set.mem_insert_iff.2 (Or.inr hy)), map_one]
    · rw [hpsi y, one_of_mem hy, map_one]
  refine ⟨toGroup hrel, ⟨?_, ?_⟩, ?_⟩
  · ext a
    simp only [MonoidHom.coe_comp, Function.comp_apply, baseHom_of, toGroup.of, hf, Sum.elim_inl]
  · ext x
    rcases x with s | z
    · rw [MonoidHom.comp_apply, blockHom_of_inl, lift_of_inl]
      show FreeGroup.lift f (FreeGroup.map (Sum.inl (β := Z)) (u s)) = _
      rw [hphi (u s)]
      exact hagree s
    · rw [MonoidHom.comp_apply, blockHom_of_inr, toGroup.of]
      simp [hf]
  · rintro chi ⟨h1, h2⟩
    ext x
    rcases x with a | z
    · have := congrArg (fun g : PresentedGroup (insert r R) →* H => g (of a)) h1
      simp only [MonoidHom.coe_comp, Function.comp_apply, baseHom_of] at this
      rw [this, toGroup.of]
      simp [hf]
    · have := congrArg (fun g : PresentedGroup B →* H => g (of (Sum.inr z))) h2
      simp only [MonoidHom.coe_comp, Function.comp_apply, blockHom_of_inr] at this
      rw [this, toGroup.of]
      simp [hf]

/-! ### The surface word -/

section Surface

variable (q : ℕ)

/-- The distinguished generators of the block `B_q`: the `2q` surface generators
`s_1, t_1, …, s_q, t_q`. -/
abbrev SurfGen : Type := Fin q × Bool

/-- The surface word `ω_q = ∏_{h=1}^q [s_h, t_h]` in the free group on the generators of the
block. -/
def surfaceWord (Z : Type u) : FreeGroup ((SurfGen q) ⊕ Z) :=
  (List.ofFn fun h : Fin q =>
    ⁅(FreeGroup.of (Sum.inl (h, false)) : FreeGroup ((SurfGen q) ⊕ Z)),
      FreeGroup.of (Sum.inl (h, true))⁆).prod

/-- The substitution `s_h ↦ u_h`, `t_h ↦ v_h` of rule 3. -/
def surfSubst (uu vv : Fin q → FreeGroup α) : SurfGen q → FreeGroup α :=
  fun p => if p.2 then vv p.1 else uu p.1

/-- **The surface word substitutes to the chosen factorization of the replaced relator.** -/
theorem subst_surfaceWord (uu vv : Fin q → FreeGroup α) :
    subst (Z := Z) (surfSubst q uu vv) (surfaceWord q Z)
      = FreeGroup.map Sum.inl (List.ofFn fun h : Fin q => ⁅uu h, vv h⁆).prod := by
  classical
  rw [surfaceWord, map_list_prod, map_list_prod, List.map_ofFn, List.map_ofFn]
  refine congrArg List.prod (congrArg List.ofFn (funext fun h => ?_))
  simp [commutatorElement_def, surfSubst]

/-- The two legs of the pushout square kill the surface word, so the pushout may equivalently be
taken over the surface group `π₁(Σ_q) = ⟨s, t | ω_q⟩`: on the base side the substituted surface
word is the replaced relator `r`, on the block side it is the chosen filling. -/
theorem legs_agree_on_surfaceWord {uu vv : Fin q → FreeGroup α}
    {Bq : Set (FreeGroup ((SurfGen q) ⊕ Z))}
    (hfill : surfaceWord q Z ∈ Subgroup.normalClosure Bq)
    (r : FreeGroup α) (hr : r = (List.ofFn fun h : Fin q => ⁅uu h, vv h⁆).prod)
    (R : Set (FreeGroup α)) :
    mk (insert r R) r = 1 ∧ mk Bq (surfaceWord q Z) = 1 ∧
      subst (surfSubst q uu vv) (surfaceWord q Z) = FreeGroup.map Sum.inl r := by
  refine ⟨one_of_mem (Set.mem_insert _ _), mk_eq_one_iff.2 hfill, ?_⟩
  rw [hr, subst_surfaceWord]

end Surface

/-! ### The pushout alone does not give injectivity

The pushout description of (3.4) is *all* that the presentations give.  In particular it does
not give the injectivity statement of property (B2): the following data satisfy every
hypothesis of `FiniteChains.BlockSubst.isPushout`, and yet the structural map
`π₁(K(E)) → π₁(K(E'))` kills a nontrivial element.  This is why the paper proves (B2) by the
geometric retraction argument in the CAT(0) universal cover of the block, and why that step
cannot be replaced by presentation bookkeeping. -/

section Sharpness

/-- A two-generator base complex `E = ⟨a, b | 1⟩`. -/
def sharpRels : Set (FreeGroup Bool) := ∅

/-- A block with two distinguished generators, no internal generator, and the single relator
which kills the second distinguished generator. -/
def sharpBlock : Set (FreeGroup (Bool ⊕ Empty)) := {FreeGroup.of (Sum.inl true)}

/-- The substitution sending the distinguished generators to the two generators of `E`. -/
def sharpSubst : Bool → FreeGroup Bool := fun c => FreeGroup.of c

theorem sharp_hypotheses :
    (1 : FreeGroup (Bool ⊕ Empty)) ∈ Subgroup.normalClosure sharpBlock ∧
      subst (Z := Empty) sharpSubst 1 = FreeGroup.map Sum.inl (1 : FreeGroup Bool) :=
  ⟨one_mem _, by simp⟩

/-- The generator `b` is nontrivial in `E = ⟨a, b | 1⟩`. -/
theorem sharp_ne_one :
    (of true : PresentedGroup (insert (1 : FreeGroup Bool) sharpRels)) ≠ 1 := by
  intro hcontra
  have hrel : ∀ x ∈ insert (1 : FreeGroup Bool) sharpRels,
      FreeGroup.lift (fun c : Bool => cond c (Multiplicative.ofAdd (1 : ℤ)) 1) x = 1 := by
    rintro x (rfl | hx)
    · simp
    · exact absurd hx (Set.notMem_empty _)
  have hval := congrArg (toGroup hrel) hcontra
  rw [toGroup.of] at hval
  simp at hval

/-- **Sharpness of `isPushout`.**  The structural map of the substitution is not injective in
general, even though the replaced relator is filled by the block. -/
theorem baseHom_not_injective :
    ¬ Function.Injective
      (baseHom sharpRels sharpBlock sharpSubst sharp_hypotheses.1 sharp_hypotheses.2) := by
  intro hinj
  refine sharp_ne_one (hinj ?_)
  rw [baseHom_of, map_one]
  exact one_of_mem (Or.inr ⟨FreeGroup.of (Sum.inl true), rfl, by simp [subst, sharpSubst]⟩)

end Sharpness

end BlockSubst
end FiniteChains
