module

public import RequestProject.PresUnivCoverIso
public import RequestProject.PresentationChain
public import RequestProject.PresentationConsistency
public import RequestProject.CombData

@[expose] public section

/-!
# Chains of presentation complexes with the topological hypothesis

`FiniteChains.PresChain` describes a chain `K = X₀ ⊂ X₁ ⊂ ⋯ ⊂ Xₙ` of presentation complexes
whose inclusions are zero on `π₂`, but states that last condition in the *algebraic* model of
the universal cover (the one whose chain complex is the Fox complex).

`RequestProject/PresUnivCoverIso.lean` identifies that model with the homotopy-theoretic
universal cover of `RequestProject/CombUniversalCover.lean`, the one used by
`FiniteChains.Comb.ZeroPi2` and hence by the instance `FiniteChains.combData` of the interface
of Theorem A.  This file records the resulting statement of condition (1) of Theorem A:

* `FiniteChains.PresChainTop` — the same chain of presentation complexes, but with the
  hypothesis "the inclusion `X_r ⊂ X_{r+1}` is zero on `π₂`" written with
  `FiniteChains.Comb.ZeroPi2`, i.e. in the homotopy-theoretic model;
* `FiniteChains.PresChainTop.toPresChain` — such a chain is a `FiniteChains.PresChain`;
* `FiniteChains.presComplex_hasAcyclicRegularCover_of_topChains` — **`(1) ⇒ (2)` of Theorem A
  for a finite presentation, with condition (1) in its topological form**: if chains of
  presentation complexes of every length exist over `K`, each inclusion being zero on `π₂`,
  then `K` has a connected acyclic regular cover.
-/

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains

universe u

variable {α J : Type u}

/-- A chain `K = X₀ ⊂ X₁ ⊂ ⋯ ⊂ Xₙ` of presentation complexes over `⟨α | ρ⟩` whose inclusions
are zero on `π₂` in the homotopy-theoretic sense (`FiniteChains.Comb.ZeroPi2`). -/
structure PresChainTop (ρ : J → FreeGroup α) (n : ℕ) where
  /-- The generators of the stage `X_r`. -/
  gen : ℕ → Type u
  /-- The two-cells of the stage `X_r`. -/
  cell : ℕ → Type u
  decGen : ∀ r, DecidableEq (gen r)
  finGen : ∀ r, Fintype (gen r)
  finCell : ∀ r, Fintype (cell r)
  /-- The attaching word of a two-cell of `X_r`. -/
  rel : ∀ r, cell r → FreeGroup (gen r)
  /-- The generators of `X_r` are generators of `X_{r+1}`. -/
  genIncl : ∀ r, gen r → gen (r + 1)
  genIncl_injective : ∀ r, Function.Injective (genIncl r)
  /-- The two-cells of `X_r` are two-cells of `X_{r+1}`. -/
  cellIncl : ∀ r, cell r → cell (r + 1)
  cellIncl_injective : ∀ r, Function.Injective (cellIncl r)
  /-- An old two-cell is attached along the same word. -/
  rel_incl : ∀ r c, rel (r + 1) (cellIncl r c) = FreeGroup.map (genIncl r) (rel r c)
  /-- The generators of `K` are generators of `X₀`. -/
  baseGen : α → gen 0
  baseGen_injective : Function.Injective baseGen
  /-- The two-cells of `K` are two-cells of `X₀`. -/
  baseCell : J → cell 0
  baseCell_injective : Function.Injective baseCell
  /-- The two-cells of `K` are attached along the relators of the presentation. -/
  rel_base : ∀ j, rel 0 (baseCell j) = FreeGroup.map baseGen (ρ j)
  /-- **The inclusion `X_r ⊂ X_{r+1}` is zero on `π₂`**, in the homotopy-theoretic model: the
  map of two-chains induced on the universal covers built from homotopy classes of edge paths
  kills every two-cycle. -/
  zero_pi2 : ∀ r, r < n →
      letI := decGen r
      letI := decGen (r + 1)
      Comb.ZeroPi2 (Comb.presInclHom (genIncl r) (genIncl_injective r) (rel r) (rel (r + 1))
        (cellIncl r) (rel_incl r))

namespace PresChainTop

variable {ρ : J → FreeGroup α} {n : ℕ} (h : PresChainTop ρ n)

/-- **A chain with the topological hypothesis is a chain in the sense of
`FiniteChains.PresChain`**: the two readings of "zero on `π₂`" agree. -/
def toPresChain : PresChain ρ n where
  gen := h.gen
  cell := h.cell
  decGen := h.decGen
  finGen := h.finGen
  finCell := h.finCell
  rel := h.rel
  genIncl := h.genIncl
  genIncl_injective := h.genIncl_injective
  cellIncl := h.cellIncl
  cellIncl_injective := h.cellIncl_injective
  rel_incl := h.rel_incl
  baseGen := h.baseGen
  baseGen_injective := h.baseGen_injective
  baseCell := h.baseCell
  baseCell_injective := h.baseCell_injective
  rel_base := h.rel_base
  zero_pi2 := by
    intro r hr
    letI := h.decGen r
    letI := h.decGen (r + 1)
    exact (Comb.zeroPi2_presInclHom_iff (ρ := h.rel r) (σ := h.rel (r + 1)) (h.genIncl r)
      (h.genIncl_injective r) (h.cellIncl r) (h.rel_incl r)).1 (h.zero_pi2 r hr)

end PresChainTop

/-- **`(1) ⇒ (2)` of Theorem A for a finite presentation, with condition (1) in its
topological form.**  If over the presentation complex `K` there are chains
`K = X₀ ⊂ ⋯ ⊂ Xₙ` of presentation complexes of every length whose inclusions are zero on
`π₂` — in the homotopy-theoretic model of the universal cover — then `K` has a connected
acyclic regular cover. -/
theorem presComplex_hasAcyclicRegularCover_of_topChains [Fintype α] [DecidableEq α]
    [Fintype J] [DecidableEq J] (ρ : J → FreeGroup α)
    (hchains : ∀ n : ℕ, Nonempty (PresChainTop ρ n)) :
    Comb.HasAcyclicRegularCover (Comb.presComplex ρ) :=
  presComplex_hasAcyclicRegularCover_of_presChains ρ
    (fun n => (hchains n).map PresChainTop.toPresChain)

/-! ### The hypothesis of the interface `combData` implies the one used here -/

/-- Condition (1) of Theorem A, read in the instance `FiniteChains.combData`, applies in
particular to the inclusion of presentation complexes: `combData.ZeroPi2` quantifies over all
cellular maps injective on cells, and the inclusion of an inclusion of presentations is one of
them. -/
theorem Comb.zeroPi2_presInclHom_of_combData {β K : Type u} [DecidableEq β]
    {σ : K → FreeGroup β} (f : α → β) (hf : Function.Injective f) (ρ : J → FreeGroup α)
    [DecidableEq α] (g : J → K) (hgi : Function.Injective g)
    (hg : ∀ j, σ (g j) = FreeGroup.map f (ρ j))
    (hz : combData.ZeroPi2 (Comb.presComplex ρ) (Comb.presComplex σ)) :
    Comb.ZeroPi2 (Comb.presInclHom f hf ρ σ g hg) :=
  hz _ (fun a b _ => Subsingleton.elim a b) hf hgi

namespace PresChainTop

/-- **A chain with the hypothesis of the interface.**  If the stages are presentation complexes
and each inclusion satisfies condition (1) of Theorem A as stated in
`FiniteChains.combData`, the chain is a `FiniteChains.PresChainTop`. -/
def ofCombData {ρ : J → FreeGroup α} {n : ℕ}
    (gen : ℕ → Type u) (cell : ℕ → Type u)
    (decGen : ∀ r, DecidableEq (gen r)) (finGen : ∀ r, Fintype (gen r))
    (finCell : ∀ r, Fintype (cell r))
    (rel : ∀ r, cell r → FreeGroup (gen r))
    (genIncl : ∀ r, gen r → gen (r + 1))
    (genIncl_injective : ∀ r, Function.Injective (genIncl r))
    (cellIncl : ∀ r, cell r → cell (r + 1))
    (cellIncl_injective : ∀ r, Function.Injective (cellIncl r))
    (rel_incl : ∀ r c, rel (r + 1) (cellIncl r c) = FreeGroup.map (genIncl r) (rel r c))
    (baseGen : α → gen 0) (baseGen_injective : Function.Injective baseGen)
    (baseCell : J → cell 0) (baseCell_injective : Function.Injective baseCell)
    (rel_base : ∀ j, rel 0 (baseCell j) = FreeGroup.map baseGen (ρ j))
    (hz : ∀ r, r < n →
      letI := decGen r
      letI := decGen (r + 1)
      combData.ZeroPi2 (Comb.presComplex (rel r)) (Comb.presComplex (rel (r + 1)))) :
    PresChainTop ρ n where
  gen := gen
  cell := cell
  decGen := decGen
  finGen := finGen
  finCell := finCell
  rel := rel
  genIncl := genIncl
  genIncl_injective := genIncl_injective
  cellIncl := cellIncl
  cellIncl_injective := cellIncl_injective
  rel_incl := rel_incl
  baseGen := baseGen
  baseGen_injective := baseGen_injective
  baseCell := baseCell
  baseCell_injective := baseCell_injective
  rel_base := rel_base
  zero_pi2 := by
    intro r hr
    letI := decGen r
    letI := decGen (r + 1)
    exact Comb.zeroPi2_presInclHom_of_combData (genIncl r) (genIncl_injective r) (rel r)
      (cellIncl r) (cellIncl_injective r) (rel_incl r) (hz r hr)

end PresChainTop

/-! ### The topological hypothesis is satisfiable -/

/-- **The presentation `⟨x | x⟩` has no second homotopy**: its Fox matrix is the unit of the
group ring, so the universal cover of its complex has no two-cycles. -/
theorem pi2_presRho_eq_zero (u : (Comb.uCover (Comb.presComplex presRho) PUnit.unit).F →₀ ℤ)
    (hu : u ∈ Comb.Pi2 (Comb.presComplex presRho) PUnit.unit) : u = 0 := by
  classical
  have hv : Comb.bdry2 (Comb.univCover presRho) (Comb.chain2 (Comb.presUnivHom presRho) u) = 0 :=
    (Comb.mem_pi2_iff_bdry2_eq_zero presRho u).1 hu
  have h := (Comb.univCover_bdry2_eq_zero_iff presRho _).1 hv ()
  rw [foxMatrixPres_presRho] at h
  simp only [unitB, mul_one, Finset.univ_unique] at h
  rw [Finset.sum_singleton] at h
  have hcoords :
      Comb.coords (relSub presRho) Unit (Comb.chain2 (Comb.presUnivHom presRho) u) = 0 := by
    funext j
    show Comb.coords (relSub presRho) Unit (Comb.chain2 (Comb.presUnivHom presRho) u) j = 0
    rw [Subsingleton.elim j default]
    exact h
  have hzero : Comb.chain2 (Comb.presUnivHom presRho) u = 0 :=
    (Comb.coords (relSub presRho) Unit).injective (by rw [hcoords, map_zero])
  refine Finsupp.mapDomain_injective (Comb.uvFace_bijective presRho).1 ?_
  rw [Finsupp.mapDomain_zero]
  exact hzero

/-- The constant chain over the presentation `⟨x | x⟩`: every inclusion is zero on `π₂`
because `π₂` itself vanishes. -/
noncomputable def presRhoTopChain (n : ℕ) : PresChainTop presRho n where
  gen _ := Unit
  cell _ := Unit
  decGen _ := inferInstance
  finGen _ := inferInstance
  finCell _ := inferInstance
  rel _ := presRho
  genIncl _ := id
  genIncl_injective _ := Function.injective_id
  cellIncl _ := id
  cellIncl_injective _ := Function.injective_id
  rel_incl _ c := by simp
  baseGen := id
  baseGen_injective := Function.injective_id
  baseCell := id
  baseCell_injective := Function.injective_id
  rel_base j := by simp
  zero_pi2 := by
    intro r _ x₀ u hu
    rw [pi2_presRho_eq_zero u hu, map_zero]

/-- Consequently the topological form of condition (1) is not vacuous, and the conclusion
holds for `⟨x | x⟩`. -/
theorem presComplex_presRho_hasAcyclicRegularCover_top :
    Comb.HasAcyclicRegularCover (Comb.presComplex presRho) :=
  presComplex_hasAcyclicRegularCover_of_topChains presRho
    (fun n => ⟨presRhoTopChain n⟩)

end FiniteChains
