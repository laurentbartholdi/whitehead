import RequestProject.BlockFamilySubst

/-!
# The one-way comparison which makes the structural map of a substitution injective

`RequestProject/SubstHomFNotInjective.lean` shows that the injectivity of
`FiniteChains.BlockFamily.substHomF` — the hypothesis `hinj` of the relative route — does not
follow from the substitution data.  It has to come from a comparison with a space in which the
blocks are realised.  The comparison needed is, however, much weaker than a Tietze equivalence
of the substituted presentation with a model: **one homomorphism in one direction suffices**.

The data is:

* a group `H` (in the application `H = π₁` of the quotient of the model of modified chambers);
* an **injective** homomorphism `j : PresGroup ρ →* H` out of the source presentation group
  (in the application the composite of the marked comparison of the base with the map induced
  by the inclusion of the base copy, whose injectivity is
  `FiniteChains.Davis.pi1Map_qNew_injective`);
* for every replaced entry `s` a homomorphism `b s` out of the free group on the generators of
  the substituted block, sending every old generator to its image under `j` (`mark`) and
  killing every block relator (`rel`).

Out of this the universal property of the substituted presentation produces
`FiniteChains.BlockFamily.BlockMaps.psi : PresGroup (substPresF ρ bsub) →* H` with

    psi ∘ substHomF = j,

whence `substHomF` is injective (`FiniteChains.BlockFamily.BlockMaps.injective_substHomF`).
Neither injectivity nor surjectivity of `psi` is used, and no isomorphism is assumed anywhere.

The marked form of the article's block is the corollary `injective_substHomF_of_markedBlock`
at the end of the file: there the block is given by its own presentation
`B_q = ⟨s_h, t_h, Z | β_m⟩` and the substitution `s_h ↦ u_h`, `t_h ↦ v_h`, and the input is a
marked homomorphism `bq s : FreeGroup (Su s ⊕ Zt s) →* H` of the block itself satisfying the
two marking equalities `bq s (of (inl h)) = j [u_h]` of the surface generators.
-/

namespace FiniteChains
namespace BlockFamily

universe u v

variable {α Jr Sx : Type u} {Zt Mt : Sx → Type u}

/-- **The data of the one-way comparison.**  A homomorphism `j` out of the source presentation
group and, for every replaced entry, a homomorphism of the free group on the generators of the
substituted block which is marked by `j` on the old generators and kills the block relators. -/
structure BlockMaps (ρ : Jr ⊕ Sx → FreeGroup α) (bsub : ∀ s : Sx, Mt s → FreeGroup (α ⊕ Zt s))
    {H : Type v} [Group H] (j : PresGroup ρ →* H) where
  /-- The homomorphism carried by the block substituted at the entry `s`. -/
  b : ∀ s : Sx, FreeGroup (α ⊕ Zt s) →* H
  /-- On an old generator the block map is the marking given by `j`. -/
  mark : ∀ (s : Sx) (a : α),
    b s (FreeGroup.of (Sum.inl a)) = j (QuotientGroup.mk (FreeGroup.of a))
  /-- Every relator of the substituted block dies. -/
  rel : ∀ (s : Sx) (m : Mt s), b s (bsub s m) = 1

namespace BlockMaps

variable {ρ : Jr ⊕ Sx → FreeGroup α} {bsub : ∀ s : Sx, Mt s → FreeGroup (α ⊕ Zt s)}
  {H : Type v} [Group H] {j : PresGroup ρ →* H} (B : BlockMaps ρ bsub j)

/-- The assignment of the generators of the substituted presentation: an old generator goes to
its image under `j`, an internal generator of the block at `s` to its image under `b s`. -/
def gen : α ⊕ (Σ s : Sx, Zt s) → H :=
  Sum.elim (fun a => j (QuotientGroup.mk (FreeGroup.of a)))
    (fun p => B.b p.1 (FreeGroup.of (Sum.inr p.2)))

@[simp] theorem gen_inl (a : α) : B.gen (Sum.inl a) = j (QuotientGroup.mk (FreeGroup.of a)) := rfl

@[simp] theorem gen_inr (s : Sx) (z : Zt s) :
    B.gen (Sum.inr ⟨s, z⟩) = B.b s (FreeGroup.of (Sum.inr z)) := rfl

/-- On the old generators the lift of `gen` is `j`. -/
theorem lift_gen_map_inl (w : FreeGroup α) :
    FreeGroup.lift B.gen (FreeGroup.map (Sum.inl (β := Σ s : Sx, Zt s)) w)
      = j (QuotientGroup.mk w) := by
  have key : (FreeGroup.lift B.gen).comp (FreeGroup.map (Sum.inl (β := Σ s : Sx, Zt s)))
      = j.comp (QuotientGroup.mk' (relSub ρ)) := by
    refine FreeGroup.ext_hom _ _ fun a => ?_
    simp [gen]
  exact DFunLike.congr_fun key w

/-- On the generators of the block at `s` the lift of `gen` is `b s`. -/
theorem lift_gen_map_genEmb (s : Sx) (w : FreeGroup (α ⊕ Zt s)) :
    FreeGroup.lift B.gen (FreeGroup.map (genEmb (Zt := Zt) s) w) = B.b s w := by
  have key : (FreeGroup.lift B.gen).comp (FreeGroup.map (genEmb (Zt := Zt) s)) = B.b s := by
    refine FreeGroup.ext_hom _ _ ?_
    rintro (a | z)
    · simpa [gen] using (B.mark s a).symm
    · simp [gen]
  exact DFunLike.congr_fun key w

/-- Every relator of the substituted presentation dies under the lift of `gen`. -/
theorem lift_gen_relator (k : Jr ⊕ (Σ s : Sx, Mt s)) :
    FreeGroup.lift B.gen (substPresF ρ bsub k) = 1 := by
  cases k with
  | inl i =>
      rw [substPresF_inl, lift_gen_map_inl]
      have h1 : (QuotientGroup.mk (ρ (Sum.inl i)) : PresGroup ρ) = 1 :=
        (QuotientGroup.eq_one_iff _).2
          (Subgroup.subset_normalClosure (Set.mem_range.2 ⟨Sum.inl i, rfl⟩))
      rw [h1, map_one]
  | inr p =>
      rw [substPresF_inr, lift_gen_map_genEmb]
      exact B.rel p.1 p.2

/-- **The homomorphism `ψ` out of the substituted presentation group** produced by the
universal property.  No injectivity or surjectivity of `ψ` is claimed. -/
def psi : PresGroup (substPresF ρ bsub) →* H :=
  QuotientGroup.lift _ (FreeGroup.lift B.gen) (by
    refine Subgroup.normalClosure_le_normal ?_
    rintro _ ⟨k, rfl⟩
    exact B.lift_gen_relator k)

@[simp] theorem psi_mk (w : FreeGroup (α ⊕ (Σ s : Sx, Zt s))) :
    B.psi (QuotientGroup.mk w) = FreeGroup.lift B.gen w := rfl

/-- **The comparison triangle.**  The composite of the structural map of the substitution with
`ψ` is the given homomorphism `j`. -/
theorem psi_comp_substHomF (hfill : FilledF ρ bsub) :
    B.psi.comp (substHomF ρ bsub hfill) = j := by
  refine MonoidHom.ext ?_
  intro x
  induction x using QuotientGroup.induction_on with
  | _ w =>
      show B.psi (substHomF ρ bsub hfill (QuotientGroup.mk w)) = j (QuotientGroup.mk w)
      rw [substHomF_mk, psi_mk, lift_gen_map_inl]

include B in
/-- **The one-way comparison proves `hinj`.**  If the marked block maps exist over an injective
`j`, the structural homomorphism of the simultaneous substitution is injective. -/
theorem injective_substHomF (hfill : FilledF ρ bsub) (hj : Function.Injective j) :
    Function.Injective (substHomF ρ bsub hfill) := by
  intro x y hxy
  refine hj ?_
  have hx : B.psi (substHomF ρ bsub hfill x) = j x :=
    DFunLike.congr_fun (B.psi_comp_substHomF hfill) x
  have hy : B.psi (substHomF ρ bsub hfill y) = j y :=
    DFunLike.congr_fun (B.psi_comp_substHomF hfill) y
  rw [← hx, ← hy, hxy]

end BlockMaps

/-! ### The marked form: the block with its own distinguished generators -/

section Marked

variable {Su : Sx → Type u}

/-- The substitution which reads the distinguished generators of the block at `s` as the
prescribed words in the old generators, and is the identity on the internal generators. -/
def blockSubst (u : ∀ s : Sx, Su s → FreeGroup α) (s : Sx) :
    FreeGroup (Su s ⊕ Zt s) →* FreeGroup (α ⊕ Zt s) :=
  FreeGroup.lift (Sum.elim (fun x => FreeGroup.map Sum.inl (u s x))
    (fun z => FreeGroup.of (Sum.inr z)))

@[simp] theorem blockSubst_of_inl (u : ∀ s : Sx, Su s → FreeGroup α) (s : Sx) (x : Su s) :
    blockSubst (Zt := Zt) u s (FreeGroup.of (Sum.inl x)) = FreeGroup.map Sum.inl (u s x) := by
  simp [blockSubst]

@[simp] theorem blockSubst_of_inr (u : ∀ s : Sx, Su s → FreeGroup α) (s : Sx) (z : Zt s) :
    blockSubst (Zt := Zt) u s (FreeGroup.of (Sum.inr z)) = FreeGroup.of (Sum.inr z) := by
  simp [blockSubst]

/-- **The one-way comparison in the marked form of the article.**  The block at `s` is given by
its own presentation with distinguished generators `Su s` and internal generators `Zt s`, and
the substituted relators are `β_m(u, Z)`.  The input is a homomorphism `bq s` out of the free
group on the generators of the block which kills the block relators and whose value on a
distinguished generator is the image under `j` of the prescribed old word (the two marking
equalities `b [s_h] = j [u_h]`, `b [t_h] = j [v_h]` of the article).  The conclusion is the
injectivity of the actual structural homomorphism of the substitution. -/
theorem injective_substHomF_of_markedBlock {H : Type v} [Group H]
    {ρ : Jr ⊕ Sx → FreeGroup α} (u : ∀ s : Sx, Su s → FreeGroup α)
    (beta : ∀ s : Sx, Mt s → FreeGroup (Su s ⊕ Zt s))
    (hfill : FilledF ρ (fun s m => blockSubst u s (beta s m)))
    (j : PresGroup ρ →* H) (hj : Function.Injective j)
    (bq : ∀ s : Sx, FreeGroup (Su s ⊕ Zt s) →* H)
    (hmark : ∀ (s : Sx) (x : Su s),
      bq s (FreeGroup.of (Sum.inl x)) = j (QuotientGroup.mk (u s x)))
    (hrel : ∀ (s : Sx) (m : Mt s), bq s (beta s m) = 1) :
    Function.Injective (substHomF ρ (fun s m => blockSubst u s (beta s m)) hfill) := by
  classical
  -- the block map on the substituted generators: old generators go to their `j`-images,
  -- internal generators to their images under the marked block map
  set bb : ∀ s : Sx, FreeGroup (α ⊕ Zt s) →* H := fun s => FreeGroup.lift (Sum.elim
      (fun a : α => j (QuotientGroup.mk (FreeGroup.of a)))
      (fun z : Zt s => bq s (FreeGroup.of (Sum.inr z)))) with hbb
  -- the block map factors the substitution: both sides agree on the generators of the block
  have key : ∀ s : Sx, (bb s).comp (blockSubst (Zt := Zt) u s) = bq s := by
    intro s
    refine FreeGroup.ext_hom _ _ ?_
    rintro (x | z)
    · rw [MonoidHom.comp_apply, blockSubst_of_inl, hmark s x]
      have hcomp : (bb s).comp (FreeGroup.map (Sum.inl (β := Zt s)))
          = j.comp (QuotientGroup.mk' (relSub ρ)) := by
        refine FreeGroup.ext_hom _ _ fun a => ?_
        simp [hbb]
      exact DFunLike.congr_fun hcomp (u s x)
    · simp [hbb]
  have hmark' : ∀ (s : Sx) (a : α),
      bb s (FreeGroup.of (Sum.inl a)) = j (QuotientGroup.mk (FreeGroup.of a)) := by
    intro s a
    simp [hbb]
  have hrel' : ∀ (s : Sx) (m : Mt s), bb s (blockSubst (Zt := Zt) u s (beta s m)) = 1 := by
    intro s m
    rw [← MonoidHom.comp_apply, key s]
    exact hrel s m
  have hmaps : BlockMaps ρ (fun s m => blockSubst u s (beta s m)) j :=
    { b := bb, mark := hmark', rel := hrel' }
  exact BlockMaps.injective_substHomF hmaps hfill hj

end Marked

end BlockFamily
end FiniteChains
