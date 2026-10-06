import RequestProject.WedgeSigma
import RequestProject.GenerationStep

/-!
# Collapsing the acyclic core: the Hurewicz image is detected on the extra cells

The second half of the proof of Lemma 3.10 collapses the acyclic core `D` of the presentation
`Q(P)`, uses the induced isomorphism `H₂(Q(P)) ≅ H₂(Q(P)/D)`, identifies the quotient with a
wedge of block complexes and quotes property (B3) for the factors.  In
`RequestProject/LemmaTerminal.lean` the collapse isomorphism is a hypothesis (`hinj` of
`FiniteChains.isCockcroft_of_collapse_to_wedge`): it says that a Fox cycle whose Hurewicz image
vanishes after the collapse has vanishing Hurewicz image already.

This file proves that statement in the presentation model, from the acyclicity of the core
alone.  A presentation containing the core has core generators and core relators (words in the
core generators) together with extra generators and extra relators.  The Hurewicz image of a
Fox cycle is a vector killed by the exponent-sum matrix; reading that relation at the core
generators only, the extra coordinates drop out as soon as they vanish, and what is left is the
exponent-sum matrix of the core applied to the core coordinates.  For an acyclic core that
matrix is injective, so the core coordinates vanish too.

* `FiniteChains.corePres` — a presentation containing the core: the core relators, read in the
  larger free group, together with the extra relators;
* `FiniteChains.expSum_map_inl` — the exponent sum of a core generator in a core relator is the
  same computed in the core and in the larger presentation;
* `FiniteChains.augPres_eq_zero_of_extra` — **the collapse statement**: if the Hurewicz image of
  a Fox cycle vanishes on the extra cells, and the exponent-sum matrix of the core is injective
  (which holds for an acyclic core), then it vanishes on all cells;
* `FiniteChains.isCockcroft_of_core_of_extra` — consequently, a presentation with an acyclic
  core is Cockcroft as soon as the Hurewicz image of every Fox cycle vanishes on the extra
  cells, which is what property (B3) for the block factors provides;
* `FiniteChains.isCockcroft_of_core_of_wedge` — **the second half of Lemma 3.10 with the
  collapse isomorphism discharged**: if the collapse records every extra cell as a cell of the
  wedge of the blocks, and each block is Cockcroft by (B3), then the whole presentation is
  Cockcroft; the acyclicity of the core replaces the quoted isomorphism on `H₂`.
-/

namespace FiniteChains

open MonoidAlgebra

universe u

variable {γ δ Mc Ex : Type u} [Fintype γ] [DecidableEq γ] [Fintype δ] [DecidableEq δ]
  [Fintype Mc] [Fintype Ex]

/-- A presentation containing the core `D`: the relators of the core, read in the free group on
the core and the extra generators, together with the extra relators. -/
def corePres (core : Mc → FreeGroup γ) (extra : Ex → FreeGroup (γ ⊕ δ)) :
    Mc ⊕ Ex → FreeGroup (γ ⊕ δ) :=
  Sum.elim (fun m => FreeGroup.map Sum.inl (core m)) extra

omit [Fintype γ] [DecidableEq γ] [Fintype δ] [DecidableEq δ] [Fintype Mc] [Fintype Ex] in
@[simp] theorem corePres_inl (core : Mc → FreeGroup γ) (extra : Ex → FreeGroup (γ ⊕ δ))
    (m : Mc) : corePres core extra (Sum.inl m) = FreeGroup.map Sum.inl (core m) := rfl

omit [Fintype γ] [DecidableEq γ] [Fintype δ] [DecidableEq δ] [Fintype Mc] [Fintype Ex] in
@[simp] theorem corePres_inr (core : Mc → FreeGroup γ) (extra : Ex → FreeGroup (γ ⊕ δ))
    (e : Ex) : corePres core extra (Sum.inr e) = extra e := rfl

omit [Fintype γ] [Fintype δ] in
/-- The exponent sum of a core generator in a word of the core does not change when the word is
read in the larger free group. -/
theorem expSum_map_inl (i : γ) (w : FreeGroup γ) :
    Multiplicative.toAdd (expSum (Sum.inl i : γ ⊕ δ) (FreeGroup.map (Sum.inl : γ → γ ⊕ δ) w))
      = Multiplicative.toAdd (expSum i w) := by
  have h : (expSum (Sum.inl i : γ ⊕ δ)).comp (FreeGroup.map (Sum.inl : γ → γ ⊕ δ))
      = expSum i := by
    refine FreeGroup.ext_hom _ _ fun k => ?_
    have h1 : FreeGroup.map (Sum.inl : γ → γ ⊕ δ) (FreeGroup.of k)
        = FreeGroup.of (Sum.inl k) := by simp
    have h2 : Multiplicative.toAdd (expSum (Sum.inl i : γ ⊕ δ) (FreeGroup.of (Sum.inl k)))
        = Multiplicative.toAdd (expSum i (FreeGroup.of k)) := by
      rw [expSum_of, expSum_of]
      simp
    exact Multiplicative.toAdd.injective (by simp [h1, h2])
  exact congrArg Multiplicative.toAdd (DFunLike.congr_fun h w)

omit [Fintype γ] [Fintype δ] [Fintype Mc] [Fintype Ex] in
/-- The entries of the exponent-sum matrix at a core generator and a core relator are the
entries of the exponent-sum matrix of the core. -/
theorem expEntry_corePres_inl (core : Mc → FreeGroup γ) (extra : Ex → FreeGroup (γ ⊕ δ))
    (i : γ) (m : Mc) :
    expEntry (corePres core extra) (Sum.inl i) (Sum.inl m) = expEntry core i m :=
  expSum_map_inl i (core m)

omit [Fintype γ] [Fintype δ] in
/-- **The collapse of the acyclic core detects the Hurewicz image.**  If the exponent-sum matrix
of the core is injective — which is exactly the acyclicity of the core complex — then a Fox
cycle whose augmentation vanishes on the extra cells has vanishing augmentation on all cells.
This is the isomorphism `H₂(Q(P)) ≅ H₂(Q(P)/D)` in the only form in which Lemma 3.10 uses
it. -/
theorem augPres_eq_zero_of_extra (core : Mc → FreeGroup γ) (extra : Ex → FreeGroup (γ ⊕ δ))
    (hcore : ExpInjective core)
    {v : Mc ⊕ Ex → MonoidAlgebra ℤ (PresGroup (corePres core extra))}
    (hv : IsFoxCycle (corePres core extra) v)
    (hextra : ∀ e : Ex, augPres (corePres core extra) (v (Sum.inr e)) = 0) :
    ∀ j, augPres (corePres core extra) (v j) = 0 := by
  classical
  set c : Mc → ℤ := fun m => augPres (corePres core extra) (v (Sum.inl m)) with hc
  have hkill : ∀ i : γ, ∑ m, c m * expEntry core i m = 0 := by
    intro i
    have h := expEntry_augPres_eq_zero (corePres core extra) hv (Sum.inl i)
    rw [Fintype.sum_sum_type] at h
    have h2 : ∑ e : Ex, augPres (corePres core extra) (v (Sum.inr e)) *
        expEntry (corePres core extra) (Sum.inl i) (Sum.inr e) = 0 :=
      Finset.sum_eq_zero fun e _ => by rw [hextra e, zero_mul]
    have h1 : ∑ m : Mc, augPres (corePres core extra) (v (Sum.inl m)) *
        expEntry (corePres core extra) (Sum.inl i) (Sum.inl m)
        = ∑ m, c m * expEntry core i m :=
      Finset.sum_congr rfl fun m _ => by rw [expEntry_corePres_inl]
    rw [h1, h2, add_zero] at h
    exact h
  intro j
  rcases j with m | e
  · exact hcore c hkill m
  · exact hextra e

omit [Fintype γ] [Fintype δ] in
/-- **A presentation with an acyclic core is Cockcroft as soon as its extra cells are.**  The
extra cells are the ones which survive the collapse of the core, so this is the assembly of the
second half of Lemma 3.10: property (B3) for the block factors gives the vanishing on the extra
cells, and the acyclicity of the core propagates it to the whole Hurewicz image. -/
theorem isCockcroft_of_core_of_extra (core : Mc → FreeGroup γ) (extra : Ex → FreeGroup (γ ⊕ δ))
    (hcore : ExpInjective core)
    (hblocks : ∀ v : Mc ⊕ Ex → MonoidAlgebra ℤ (PresGroup (corePres core extra)),
      IsFoxCycle (corePres core extra) v →
        ∀ e : Ex, augPres (corePres core extra) (v (Sum.inr e)) = 0) :
    IsCockcroft (corePres core extra) :=
  fun v hv => augPres_eq_zero_of_extra core extra hcore hv (hblocks v hv)

/-! ### The collapse onto the wedge of the blocks -/

section Wedge

variable {S : Type u} {β K : S → Type u} [Fintype S] [DecidableEq S] [∀ s, Fintype (β s)]
  [∀ s, DecidableEq (β s)] [∀ s, Fintype (K s)]

omit [Fintype γ] [Fintype δ] [∀ s, Fintype (β s)] in
/-- **The second half of Lemma 3.10 with the collapse isomorphism discharged.**  The paper
collapses the acyclic core, identifies the quotient with a wedge of block complexes and quotes
property (B3) for the factors.  Here the identification is recorded by a structural map `kappa`
onto the wedge for which every extra cell has the augmentation of some cell of the wedge
(`hcells`); property (B3) makes the wedge Cockcroft
(`FiniteChains.isCockcroft_sigmaWedgeRel`), hence the extra cells carry no Hurewicz image, and
the acyclicity of the core propagates this to the core cells. -/
theorem isCockcroft_of_core_of_wedge (core : Mc → FreeGroup γ) (extra : Ex → FreeGroup (γ ⊕ δ))
    (hcore : ExpInjective core) (blk : ∀ s, K s → FreeGroup (β s))
    (hB3 : ∀ s, IsCockcroft (blk s)) (kappa : PresMor (corePres core extra) (sigmaWedgeRel blk))
    (hcells : ∀ (v : Mc ⊕ Ex → MonoidAlgebra ℤ (PresGroup (corePres core extra))) (e : Ex),
      ∃ p, augPres (corePres core extra) (v (Sum.inr e))
        = augPres (sigmaWedgeRel blk) (kappa.cells v p)) :
    IsCockcroft (corePres core extra) := by
  refine isCockcroft_of_core_of_extra core extra hcore fun v hv e => ?_
  obtain ⟨p, hp⟩ := hcells v e
  rw [hp]
  exact isCockcroft_sigmaWedgeRel blk hB3 (kappa.cells v) (kappa.cells_cycle v hv) p

end Wedge

end FiniteChains
