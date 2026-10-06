import RequestProject.LemmaTerminal
import RequestProject.TietzeElimination
import RequestProject.BlockSubstitutionPi1

/-!
# Property (B3): Cockcroftness after capping

Theorem 3.2 of the paper asks three properties of the marked replacement blocks `B_q`.  Two
of them, (B1) and (B2), enter the development as data and as a hypothesis of rule 3; the
third,

> **(B3)** the presentation obtained from `B_q` by setting all distinguished generators equal
> to `1` is Cockcroft,

is the one input of Lemma 3.10 which is quoted as `hB3` in
`RequestProject/LemmaTerminal.lean` (`FiniteChains.isCockcroft_of_collapse_to_wedge`,
`FiniteChains.lemma_terminal`).  This file proves (B3) from the two geometric facts which the
paper's own proof of it uses, and from nothing else.

## The paper's argument

The capped block is the presentation complex `V_q` of `B_q` together with disks along the
distinguished generators `s_h, t_h`.  Coning the remaining surface polygon attaches *one*
three-cell and gives a model of the cube complex `C_q`, which is aspherical because its
universal cover is CAT(0).  The ordinary (downstairs) boundary of that three-cell is zero:

* on the newly added disks its coefficients are the exponent sums of the surface word
  `ω_q = ∏_h [s_h, t_h]`, and those vanish;
* on the cells of the block it is the image of the fundamental class `[Σ_q]`, which vanishes
  in `H₂(M_q)` by Lemma 3.3 (iii).

Hence every spherical class of `V_q` is a multiple of a chain with zero augmentation, so the
Hurewicz map of `V_q` is zero.  Eliminating the distinguished generators by their defining
pairs turns `V_q` into the capped presentation.

## What is proved here

Everything above except the two geometric inputs, which appear as explicit hypotheses:
asphericity of the cone model (`hasph`: every Fox cycle is a group-ring multiple of the
boundary chain of the three-cell) and the vanishing of the fundamental class
(`hsigma`: that chain has zero augmentation on the cells of the block).

* `FiniteChains.zeroAugChains` — the chains with zero augmentation in every coordinate, as a
  submodule over the group ring: this is the kernel of the Hurewicz map;
* `FiniteChains.isCockcroft_of_span_zeroAug`, `FiniteChains.isCockcroft_of_threeCells`,
  `FiniteChains.isCockcroft_of_h2_cover_vanishing`,
  `FiniteChains.isCockcroft_of_single_threeCell` — **a two-complex whose spherical classes are
  spanned over the group ring by boundaries of three-cells with zero downstairs boundary is
  Cockcroft**; this is the homological core of the capping argument;
* `FiniteChains.surfaceWord_mem_commutator`, `FiniteChains.expSum_surfaceWord` — the surface
  word `ω_q = ∏_h [s_h, t_h]` is a product of commutators, so its exponent sums vanish;
* `FiniteChains.isCockcroft_cappedBlock`, `FiniteChains.isCockcroft_cappedBlock_of_commutator`
  — **property (B3)**: the capped block is Cockcroft, given the cone model of `C_q` and the
  vanishing of `[Σ_q]`;
* `FiniteChains.isCockcroft_of_elim`, `FiniteChains.isCockcroft_capped_of_coneModel` —
  Cockcroftness passes along the elimination of a generator by its defining pair, and along a
  whole sequence of such eliminations, which is the last sentence of the paper's proof
  ("eliminating the distinguished generators gives precisely the capped presentation");
* `FiniteChains.lemma_terminal_of_coneModels` — **Lemma 3.10 with the hypothesis (B3)
  discharged**: the blocks need only be presented with their cone models.
-/

namespace FiniteChains

open MonoidAlgebra

universe u

/-! ### Spherical classes spanned by three-cells -/

section Span

variable {α J : Type u} [Fintype α] [DecidableEq α] [Fintype J] {ρ : J → FreeGroup α}

/-- The two-chains all of whose coefficients have zero augmentation, as a submodule over the
group ring.  A Fox cycle lies in it exactly when its Hurewicz image vanishes, so the Cockcroft
property says that every Fox cycle lies in it. -/
noncomputable def zeroAugChains (ρ : J → FreeGroup α) :
    Submodule (MonoidAlgebra ℤ (PresGroup ρ)) (J → MonoidAlgebra ℤ (PresGroup ρ)) where
  carrier := {w | ∀ j, augPres ρ (w j) = 0}
  add_mem' := by
    intro a b ha hb j
    rw [Pi.add_apply, map_add, ha j, hb j, add_zero]
  zero_mem' := by
    intro j
    simp
  smul_mem' := by
    intro c a ha j
    rw [Pi.smul_apply, smul_eq_mul, map_mul, ha j, mul_zero]

omit [Fintype α] [DecidableEq α] [Fintype J] in
theorem mem_zeroAugChains_iff {w : J → MonoidAlgebra ℤ (PresGroup ρ)} :
    w ∈ zeroAugChains ρ ↔ ∀ j, augPres ρ (w j) = 0 := Iff.rfl

omit [Fintype α] in
/-- **The homological core of the capping argument.**  If every Fox cycle is a group-ring
combination of chains with vanishing augmentation, then the presentation complex is
Cockcroft. -/
theorem isCockcroft_of_span_zeroAug (S : Set (J → MonoidAlgebra ℤ (PresGroup ρ)))
    (hS : ∀ w ∈ S, ∀ j, augPres ρ (w j) = 0)
    (hspan : ∀ v, IsFoxCycle ρ v → v ∈ Submodule.span (MonoidAlgebra ℤ (PresGroup ρ)) S) :
    IsCockcroft ρ := by
  intro v hv
  have hle : Submodule.span (MonoidAlgebra ℤ (PresGroup ρ)) S ≤ zeroAugChains ρ :=
    Submodule.span_le.2 fun w hw => hS w hw
  exact hle (hspan v hv)

omit [Fintype α] in
/-- **Three-cells with zero downstairs boundary make a complex Cockcroft.**  Here `bdry k` is
the cellular boundary, in the universal cover, of the `k`-th three-cell of a three-dimensional
model whose second homology vanishes, so that the two-cycles of the two-skeleton are exactly
the group-ring combinations of the `bdry k`. -/
theorem isCockcroft_of_threeCells {Cb : Type u}
    (bdry : Cb → J → MonoidAlgebra ℤ (PresGroup ρ))
    (hbdry : ∀ k j, augPres ρ (bdry k j) = 0)
    (hasph : ∀ v, IsFoxCycle ρ v →
      v ∈ Submodule.span (MonoidAlgebra ℤ (PresGroup ρ)) (Set.range bdry)) :
    IsCockcroft ρ :=
  isCockcroft_of_span_zeroAug _ (by rintro _ ⟨k, rfl⟩; exact hbdry k) hasph

omit [Fintype α] in
/-- **The vanishing of the second homology of the universal cover of the three-dimensional
model makes the two-skeleton Cockcroft.**  Over the group ring the three-chains of the
universal cover are free on the three-cells of the model, so the statement `H₂ = 0` reads: a
two-chain `v` is a cycle only if `v_j = ∑_k c_k · ∂(e_k)_j` for coefficients `c_k` in the group
ring.  If, in addition, the ordinary boundary of each three-cell vanishes (zero augmentation),
the Hurewicz map of the two-skeleton is zero. -/
theorem isCockcroft_of_h2_cover_vanishing {Cb : Type u} [Fintype Cb]
    (bdry : Cb → J → MonoidAlgebra ℤ (PresGroup ρ))
    (hbdry : ∀ k j, augPres ρ (bdry k j) = 0)
    (hasph : ∀ v, IsFoxCycle ρ v → ∃ c : Cb → MonoidAlgebra ℤ (PresGroup ρ),
      ∀ j, v j = ∑ k, c k * bdry k j) :
    IsCockcroft ρ := by
  intro v hv j
  obtain ⟨c, hc⟩ := hasph v hv
  rw [hc j, map_sum]
  refine Finset.sum_eq_zero fun k _ => ?_
  rw [map_mul, hbdry k j, mul_zero]

omit [Fintype α] in
/-- The case of a single three-cell, which is the one occurring in the capping argument:
coning the surface polygon attaches exactly one three-cell. -/
theorem isCockcroft_of_single_threeCell (t : J → MonoidAlgebra ℤ (PresGroup ρ))
    (ht : ∀ j, augPres ρ (t j) = 0)
    (hasph : ∀ v, IsFoxCycle ρ v →
      ∃ lam : MonoidAlgebra ℤ (PresGroup ρ), ∀ j, v j = lam * t j) :
    IsCockcroft ρ := by
  intro v hv j
  obtain ⟨lam, hlam⟩ := hasph v hv
  rw [hlam j, map_mul, ht j, mul_zero]

end Span

/-! ### The exponent sums of the surface word -/

section SurfaceWord

variable (q : ℕ) (Z : Type u) [DecidableEq Z]

omit [DecidableEq Z] in
/-- **The surface word `ω_q = ∏_{h=1}^q [s_h, t_h]` lies in the commutator subgroup.** -/
theorem surfaceWord_mem_commutator :
    BlockSubst.surfaceWord q Z ∈ commutator (FreeGroup (BlockSubst.SurfGen q ⊕ Z)) := by
  classical
  rw [BlockSubst.surfaceWord]
  refine Subgroup.list_prod_mem _ ?_
  intro y hy
  obtain ⟨h, rfl⟩ := List.mem_ofFn.1 hy
  exact Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)

/-- **The exponent sums of the surface word all vanish.**  These are the coefficients of the
boundary of the cone three-cell on the disks added by the capping. -/
theorem expSum_surfaceWord (i : BlockSubst.SurfGen q ⊕ Z) :
    Multiplicative.toAdd (expSum i (BlockSubst.surfaceWord q Z)) = 0 :=
  expSum_eq_zero_of_mem_commutator _ (surfaceWord_mem_commutator q Z) i

end SurfaceWord

/-! ### Property (B3) -/

section Capped

variable {α Kb D : Type u} [Fintype α] [DecidableEq α] [Fintype Kb] [Fintype D]
variable (ρ : Kb ⊕ D → FreeGroup α)

/-- The boundary chain, in the universal cover, of the three-cell obtained by coning the
surface polygon: on the cells of the block it is the image of the fundamental chain of
`Σ_q`, and on the disks added by the capping it is the constant given by the exponent sum of
the surface word in the corresponding distinguished generator. -/
noncomputable def coneChain (sigmaChain : Kb → MonoidAlgebra ℤ (PresGroup ρ))
    (capCoeff : D → ℤ) : Kb ⊕ D → MonoidAlgebra ℤ (PresGroup ρ) :=
  Sum.elim sigmaChain fun d => ((capCoeff d : ℤ) : MonoidAlgebra ℤ (PresGroup ρ))

omit [Fintype α] in
/-- **Property (B3): the capped block is Cockcroft.**

The presentation `ρ` is the capped block: its cells are those of the block (`Kb`) together
with the disks adjoined along the distinguished generators (`D`).  The hypotheses are the two
facts about the pair `Σ_q ⊂ M_q` used in the paper's proof:

* `hsigma` — the image of the fundamental class `[Σ_q]` vanishes in second homology, i.e. the
  block part of the boundary of the cone three-cell has zero augmentation (Lemma 3.3 (iii));
* `hcap` — the coefficients of that boundary on the capping disks, the exponent sums of the
  surface word, vanish (`FiniteChains.expSum_surfaceWord`);
* `hasph` — the cone model `C_q` is aspherical: its universal cover has vanishing second
  homology and one orbit of three-cells, so every Fox cycle of the two-skeleton is a
  group-ring multiple of the boundary chain of that three-cell. -/
theorem isCockcroft_cappedBlock (sigmaChain : Kb → MonoidAlgebra ℤ (PresGroup ρ))
    (capCoeff : D → ℤ) (hsigma : ∀ j, augPres ρ (sigmaChain j) = 0)
    (hcap : ∀ d, capCoeff d = 0)
    (hasph : ∀ v, IsFoxCycle ρ v →
      ∃ lam : MonoidAlgebra ℤ (PresGroup ρ),
        ∀ j, v j = lam * coneChain ρ sigmaChain capCoeff j) :
    IsCockcroft ρ := by
  refine isCockcroft_of_single_threeCell _ ?_ hasph
  rintro (j | d)
  · exact hsigma j
  · show augPres ρ ((capCoeff d : ℤ) : MonoidAlgebra ℤ (PresGroup ρ)) = 0
    rw [map_intCast, hcap d, Int.cast_zero]

end Capped

section CappedSurface

variable {α Kb D : Type u} [Fintype α] [DecidableEq α] [Fintype Kb] [Fintype D]
variable (ρ : Kb ⊕ D → FreeGroup α)

omit [Fintype α] in
/-- **Property (B3) with the coefficients on the capping disks computed.**  The disks adjoined
by the capping run along the distinguished generators `dist d`, and the coefficient of the cone
three-cell on such a disk is the exponent sum of the surface word `ω` in that generator.  Since
`ω = ∏_h [s_h, t_h]` is a product of commutators (`FiniteChains.surfaceWord_mem_commutator`),
these coefficients vanish, and the only hypothesis left is the geometry of the pair
`Σ_q ⊂ M_q`: the asphericity of the cone model and the vanishing of the fundamental class. -/
theorem isCockcroft_cappedBlock_of_commutator (dist : D → α) (w : FreeGroup α)
    (hw : w ∈ commutator (FreeGroup α)) (sigmaChain : Kb → MonoidAlgebra ℤ (PresGroup ρ))
    (hsigma : ∀ j, augPres ρ (sigmaChain j) = 0)
    (hasph : ∀ v, IsFoxCycle ρ v → ∃ lam : MonoidAlgebra ℤ (PresGroup ρ), ∀ j,
      v j = lam * coneChain ρ sigmaChain
        (fun d => Multiplicative.toAdd (expSum (dist d) w)) j) :
    IsCockcroft ρ :=
  isCockcroft_cappedBlock ρ sigmaChain _ hsigma
    (fun d => expSum_eq_zero_of_mem_commutator w hw (dist d)) hasph

end CappedSurface

/-! ### Eliminating the distinguished generators -/

section Elim

variable {α : Type u} [Fintype α] [DecidableEq α] {J : Type u} [Fintype J] [DecidableEq J]
variable (ρ : J → FreeGroup α) (s : FreeGroup α)

omit [Fintype α] [DecidableEq J] in
/-- **Cockcroftness passes along the elimination of a generator by its defining pair.**  This
is the last sentence of the proof of (B3): the capped presentation `⟨Z_q | β_{q,j}(1,…,1,Z_q)⟩`
is obtained from the complex `V_q` by eliminating the distinguished generators using their
defining relators, and the elimination satisfies the generation equation (3.3)
(`FiniteChains.generates_elimMor`), hence transports the Cockcroft property. -/
theorem isCockcroft_of_elim (h : IsCockcroft (extRel ρ (tietzeWord s))) : IsCockcroft ρ :=
  isCockcroft_of_generates (elimMor ρ s) (generates_elimMor ρ s) h

section ElimPath

/-- **The capping argument end to end.**  Let `V` be the two-complex `V_q` — the block with a
disk along each distinguished generator — with the cone model of `C_q` over it, and let `t` be
the sequence of elimination moves which removes the distinguished generators by their defining
pairs, so that its target `C` is the capped presentation (3.2).  Then the capped presentation
is Cockcroft.  Both steps are theorems: the cone model makes `V` Cockcroft, and a sequence of
moves satisfying the generation equation (3.3) — in particular a sequence of eliminations —
transports Cockcroftness (`FiniteChains.TPath.isCockcroft`). -/
theorem isCockcroft_capped_of_coneModel {V C : PresPoint.{u}} (t : TPath V C)
    (bdry : V.cells → MonoidAlgebra ℤ (PresGroup V.rel))
    (hbdry : ∀ j, augPres V.rel (bdry j) = 0)
    (hasph : ∀ v, IsFoxCycle V.rel v →
      ∃ lam : MonoidAlgebra ℤ (PresGroup V.rel), ∀ j, v j = lam * bdry j) :
    IsCockcroft C.rel :=
  t.isCockcroft (isCockcroft_of_single_threeCell bdry hbdry hasph)

end ElimPath

end Elim

/-! ### Lemma 3.10 with (B3) discharged -/

section Terminal

variable {P Q : PresPoint.{u}} {L : Type u} [Fintype L] [DecidableEq L]
variable {S : Type u} [Fintype S] [DecidableEq S] {β K : S → Type u}
  [∀ s, Fintype (β s)] [∀ s, DecidableEq (β s)] [∀ s, Fintype (K s)]

omit [DecidableEq L] [∀ s, Fintype (β s)] in
/-- **Lemma 3.10 with property (B3) replaced by the geometry that proves it.**  Instead of
assuming that every block factor is Cockcroft, one supplies for each factor the boundary chain
of the cone three-cell of its cube model, the vanishing of its augmentation and the
asphericity of that model; (B3) is then a theorem
(`FiniteChains.isCockcroft_of_single_threeCell`). -/
theorem lemma_terminal_of_coneModels (t : TPath P Q) (ν : L → FreeGroup Q.gens)
    (hP : IsCockcroft P.rel)
    (hkill : ∀ a : P.gens,
      (addRelsMor Q.rel ν).hom (t.mor.hom (QuotientGroup.mk (FreeGroup.of a))) = 1)
    (blk : ∀ s, K s → FreeGroup (β s))
    (cone : ∀ s, K s → MonoidAlgebra ℤ (PresGroup (blk s)))
    (hcone : ∀ s j, augPres (blk s) (cone s j) = 0)
    (hasph : ∀ s, ∀ v, IsFoxCycle (blk s) v →
      ∃ lam : MonoidAlgebra ℤ (PresGroup (blk s)), ∀ j, v j = lam * cone s j)
    (kappa : PresMor (addRels Q.rel ν) (sigmaWedgeRel blk))
    (hinj : ∀ v, IsFoxCycle (addRels Q.rel ν) v →
      (∀ p, augPres (sigmaWedgeRel blk) (kappa.cells v p) = 0) →
      ∀ m, augPres (addRels Q.rel ν) (v m) = 0) :
    IsCockcroft (addRels Q.rel ν) ∧
      (∀ v : Q.cells → MonoidAlgebra ℤ (PresGroup Q.rel), IsFoxCycle Q.rel v →
        (addRelsMor Q.rel ν).cells v = 0) ∧
      (∀ x : P.gens, (QuotientGroup.mk (FreeGroup.of x) : PresGroup P.rel) = 1 →
        t.mor.hom (QuotientGroup.mk (FreeGroup.of x)) = 1 ∧
          (addRelsMor Q.rel ν).hom (t.mor.hom (QuotientGroup.mk (FreeGroup.of x))) = 1) :=
  lemma_terminal t ν hP hkill blk
    (fun s => isCockcroft_of_single_threeCell (cone s) (hcone s) (hasph s)) kappa hinj

end Terminal

end FiniteChains
