import RequestProject.CappedBlock
import RequestProject.CutSurfaceSpine

/-!
# Property (B3) with Lemma 3.3 (iii) discharged

`RequestProject/CappedBlock.lean` proves property (B3) of Theorem 3.2 — *the capped block is
Cockcroft* — from the two geometric facts about the pair `Σ_q ⊂ M_q` which the paper's own
proof uses:

* (iii) the image of the fundamental class `[Σ_q]` vanishes in `H₂(M_q)`, which enters as the
  hypothesis `hsigma` saying that the block part of the boundary of the cone three-cell has
  zero augmentation;
* (i) the asphericity of the cone model `C_q`, which enters as the hypothesis `hasph`.

`RequestProject/CutSurfaceSpine.lean` now proves the first of the two in the explicit model:
after the collapse of Lemma 3.3 (ii) the cellular chain of the cut surface is the **zero**
chain of the two-dimensional spine (`FiniteChains.cutSurface_cmap_eq_zero`).

This file feeds that theorem into (B3).  What is left at this point of the argument is the
labelling of the cells: the two-cells of the block are the two-cells surviving the collapse,
and the augmentation of the block part of the cone three-cell is read off from the collapsed
cut surface chain along that labelling (`hdict`).  With this dictionary, hypothesis (iii)
disappears from (B3): only the asphericity of the cone model remains.
-/

namespace FiniteChains

open Finset

variable {V : Type} [Fintype V] [DecidableEq V] [LinearOrder V]

universe u

variable {α Kb D : Type u} [Fintype α] [DecidableEq α] [Fintype Kb] [Fintype D]

omit [Fintype α] in
/-- **Property (B3) with Lemma 3.3 (iii) proved rather than assumed.**

The presentation `ρ` is the capped block `V_q`: its two-cells are those of the block (`Kb`),
labelled by `lab` with the two-cells of the spine of `M_q` surviving the collapse, together
with the disks adjoined along the distinguished generators (`D`).  The hypotheses are:

* the collapse of the truncated cube complex of the closed surface `L` and the fact that it
  is a chain collapse (`hl`, `hmap`, `hchain`) — both supplied by
  `RequestProject/SpineCollapse.lean` and `RequestProject/CutSurfaceSpine.lean`, the first of
  them being Lemma 3.3 (ii);
* `hcyc`, `hsupp`, `hfaces` — `o` is the fundamental cycle of `L`;
* `hdict` — the labelling: the augmentation of the block part of the boundary of the cone
  three-cell is the collapsed cut surface chain read at the corresponding cell;
* `hcap` — the coefficients on the capping disks vanish, which is the statement that the
  exponent sums of the surface word `ω_q = ∏_h [s_h, t_h]` are zero
  (`FiniteChains.expSum_surfaceWord`);
* `hasph` — the asphericity of the cone model `C_q`, i.e. Lemma 3.3 (i).

The conclusion is (B3): the capped block is Cockcroft.  Lemma 3.3 (iii) is no longer assumed:
it is the theorem `FiniteChains.cutSurface_cmap_eq_zero`. -/
theorem isCockcroft_cappedBlock_of_cutSurface {L : ASC V}
    {o : Finset V → ℤ} (hcyc : simpBdry o = 0)
    (hsupp : ∀ σ : Finset V, σ.card ≠ 3 → o σ = 0)
    (hfaces : ∀ σ : Finset V, σ ∉ L.faces → o σ = 0)
    {l : List (Cube V)} (hl : Collapse.IsCollapse (spineInc L) l (topCubes L))
    {lp : List (Cube V × (Cube V ⊕ Finset V))} (hmap : lp.map Prod.fst = l)
    (hchain : CollapseChain.IsChainCollapse (cubeBdry (V := V)) lp)
    (ρ : Kb ⊕ D → FreeGroup α) (sigmaChain : Kb → MonoidAlgebra ℤ (PresGroup ρ))
    (capCoeff : D → ℤ) (hcap : ∀ d, capCoeff d = 0)
    (lab : Kb → Cube V ⊕ Finset V)
    (hdict : ∀ j, augPres ρ (sigmaChain j)
      = CollapseChain.cmap (cubeBdry (V := V)) lp (Sum.elim 0 (fun τ => -o τ)) (lab j))
    (hasph : ∀ v, IsFoxCycle ρ v →
      ∃ lam : MonoidAlgebra ℤ (PresGroup ρ),
        ∀ j, v j = lam * coneChain ρ sigmaChain capCoeff j) :
    IsCockcroft ρ := by
  refine isCockcroft_cappedBlock ρ sigmaChain capCoeff ?_ hcap hasph
  intro j
  rw [hdict j, cutSurface_cmap_eq_zero hcyc hsupp hfaces hl hmap hchain]
  rfl

/-! ### The asphericity hypothesis from the cube model -/

omit [Fintype α] in
/-- **The asphericity hypothesis of (B3) from the vanishing of the second homology of the cube
model.**  Let `dcov` be the boundary of the three-cells of the universal cover of the cube
model `C_q`, as a matrix over the group ring (over the group ring the chains of the universal
cover are free on the cells of the model).  Assume

* `hlp`, `hcoll` — a chain collapse of the model removing every three-cell except the cone
  cell `e`: this is Lemma 3.3 (ii), the collapse of `M_q` onto its spine, the cone cell being
  the one left by the truncation;
* `hH2` — every two-cycle of the model bounds, i.e. `H₂` of the universal cover vanishes.
  For a CAT(0) cube complex this is the Cartan–Hadamard input of the paper, proved in the
  project for cube complexes with median one-skeleton;
* `lab`, `chainOf`, `hchainOf`, `hcycleCov`, `hspine` — the dictionary between the Fox
  coordinates of the capped block and the cellular chains of the collapsed model: a Fox cycle
  is a two-cycle of the model, supported on the surviving cells, whose coordinate at `lab j`
  is the `j`-th Fox coordinate;
* `hcone` — the boundary of the cone cell, read after the collapse, is the boundary chain used
  by the capping argument.

Then every Fox cycle of the capped block is a group-ring multiple of the boundary chain of
the cone cell, which is exactly the hypothesis `hasph` of
`FiniteChains.isCockcroft_cappedBlock`. -/
theorem exists_mul_coneChain_of_cubeModel {T Fcov : Type u} [DecidableEq T]
    (ρ : Kb ⊕ D → FreeGroup α)
    (dcov : T → Fcov → MonoidAlgebra ℤ (PresGroup ρ))
    {lp : List (T × Fcov)} (hlp : CollapseChain.IsChainCollapse dcov lp)
    (e : T) (hcoll : ∀ t : T, t ≠ e → ∃ f, (t, f) ∈ lp)
    (IsCycleCov : (Fcov → MonoidAlgebra ℤ (PresGroup ρ)) → Prop)
    (hH2 : ∀ x, IsCycleCov x → ∃ (s : Finset T) (c : T → MonoidAlgebra ℤ (PresGroup ρ)),
      ∀ g, x g = ∑ t ∈ s, c t * dcov t g)
    (lab : Kb ⊕ D → Fcov)
    (chainOf : (Kb ⊕ D → MonoidAlgebra ℤ (PresGroup ρ)) → Fcov → MonoidAlgebra ℤ (PresGroup ρ))
    (hchainOf : ∀ v j, chainOf v (lab j) = v j)
    (hcycleCov : ∀ v, IsFoxCycle ρ v → IsCycleCov (chainOf v))
    (hspine : ∀ v, IsFoxCycle ρ v → ∀ p ∈ lp, chainOf v p.2 = 0)
    (bdry : Kb ⊕ D → MonoidAlgebra ℤ (PresGroup ρ))
    (hcone : ∀ j, CollapseChain.cmap dcov lp (dcov e) (lab j) = bdry j) :
    ∀ v, IsFoxCycle ρ v →
      ∃ lam : MonoidAlgebra ℤ (PresGroup ρ), ∀ j, v j = lam * bdry j := by
  intro v hv
  obtain ⟨lam, hlam⟩ := CollapseChain.exists_mul_bdry_of_cycles_bound hlp e IsCycleCov hH2
    hcoll (hcycleCov v hv) (hspine v hv)
  refine ⟨lam, fun j => ?_⟩
  rw [← hchainOf v j, hlam (lab j), hcone j]

omit [Fintype α] in
/-- **Property (B3) from the cube model.**  Both geometric inputs of the capping argument are
now theorems of the combinatorial model: Lemma 3.3 (iii) is
`FiniteChains.cutSurface_cmap_eq_zero` (the cut surface collapses to the zero chain), and
Lemma 3.3 (i) enters only through the vanishing of the second homology of the universal cover
of the cube model, transported to the collapsed cone model by
`FiniteChains.exists_mul_coneChain_of_cubeModel`.  What the statement still takes as data is
the dictionary between the cells of the model and the Fox coordinates of the capped
block. -/
theorem isCockcroft_cappedBlock_of_cubeModel {L : ASC V}
    {o : Finset V → ℤ} (hcyc : simpBdry o = 0)
    (hsupp : ∀ σ : Finset V, σ.card ≠ 3 → o σ = 0)
    (hfaces : ∀ σ : Finset V, σ ∉ L.faces → o σ = 0)
    {l : List (Cube V)} (hl : Collapse.IsCollapse (spineInc L) l (topCubes L))
    {lz : List (Cube V × (Cube V ⊕ Finset V))} (hmap : lz.map Prod.fst = l)
    (hchain : CollapseChain.IsChainCollapse (cubeBdry (V := V)) lz)
    (ρ : Kb ⊕ D → FreeGroup α) (sigmaChain : Kb → MonoidAlgebra ℤ (PresGroup ρ))
    (capCoeff : D → ℤ) (hcap : ∀ d, capCoeff d = 0)
    (labz : Kb → Cube V ⊕ Finset V)
    (hdict : ∀ j, augPres ρ (sigmaChain j)
      = CollapseChain.cmap (cubeBdry (V := V)) lz (Sum.elim 0 (fun τ => -o τ)) (labz j))
    {T Fcov : Type u} [DecidableEq T] (dcov : T → Fcov → MonoidAlgebra ℤ (PresGroup ρ))
    {lp : List (T × Fcov)} (hlp : CollapseChain.IsChainCollapse dcov lp)
    (e : T) (hcoll : ∀ t : T, t ≠ e → ∃ f, (t, f) ∈ lp)
    (IsCycleCov : (Fcov → MonoidAlgebra ℤ (PresGroup ρ)) → Prop)
    (hH2 : ∀ x, IsCycleCov x → ∃ (s : Finset T) (c : T → MonoidAlgebra ℤ (PresGroup ρ)),
      ∀ g, x g = ∑ t ∈ s, c t * dcov t g)
    (lab : Kb ⊕ D → Fcov)
    (chainOf : (Kb ⊕ D → MonoidAlgebra ℤ (PresGroup ρ)) → Fcov → MonoidAlgebra ℤ (PresGroup ρ))
    (hchainOf : ∀ v j, chainOf v (lab j) = v j)
    (hcycleCov : ∀ v, IsFoxCycle ρ v → IsCycleCov (chainOf v))
    (hspine : ∀ v, IsFoxCycle ρ v → ∀ p ∈ lp, chainOf v p.2 = 0)
    (hcone : ∀ j, CollapseChain.cmap dcov lp (dcov e) (lab j)
      = coneChain ρ sigmaChain capCoeff j) :
    IsCockcroft ρ :=
  isCockcroft_cappedBlock_of_cutSurface hcyc hsupp hfaces hl hmap hchain ρ sigmaChain capCoeff
    hcap labz hdict
    (exists_mul_coneChain_of_cubeModel ρ dcov hlp e hcoll IsCycleCov hH2 lab chainOf hchainOf
      hcycleCov hspine _ hcone)

end FiniteChains
