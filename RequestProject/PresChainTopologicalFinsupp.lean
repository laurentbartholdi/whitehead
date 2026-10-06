module

public import RequestProject.PresUnivCoverIso
public import RequestProject.PresentationChainFinsupp

@[expose] public section

/-! Arbitrary presentation chains in the cellular edge-path model. -/

namespace FiniteChains

universe u

variable {α J : Type u}

/-- A chain `K = X₀ ⊂ X₁ ⊂ ⋯ ⊂ Xₙ` of presentation complexes over `⟨α | ρ⟩` whose inclusions
are zero on `π₂` in the cellular edge-path sense (`FiniteChains.Comb.ZeroPi2`). -/
structure PresChainTopFS (ρ : J → FreeGroup α) (n : ℕ) where
  /-- The generators of the stage `X_r`. -/
  gen : ℕ → Type u
  /-- The two-cells of the stage `X_r`. -/
  cell : ℕ → Type u
  decGen : ∀ r, DecidableEq (gen r)
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
  /-- **The inclusion `X_r ⊂ X_{r+1}` is zero on `π₂`**, in the cellular edge-path model: the
  map of two-chains induced on the universal covers built from homotopy classes of edge paths
  kills every two-cycle. -/
  zero_pi2 : ∀ r, r < n →
      letI := decGen r
      letI := decGen (r + 1)
      Comb.ZeroPi2 (Comb.presInclHom (genIncl r) (genIncl_injective r) (rel r) (rel (r + 1))
        (cellIncl r) (rel_incl r))

namespace PresChainTopFS

variable {ρ : J → FreeGroup α} {n : ℕ} (h : PresChainTopFS ρ n)

/-- **A chain with the cellular hypothesis is a chain in the sense of
`FiniteChains.PresChainFS`**: the two readings of "zero on `π₂`" agree. -/
def toPresChainFS : PresChainFS ρ n where
  gen := h.gen
  cell := h.cell
  decGen := h.decGen
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

end PresChainTopFS

/-- **`(1) ⇒ (2)` of Theorem A for a arbitrary presentation, with condition (1) in its
cellular form.**  If over the presentation complex `K` there are chains
`K = X₀ ⊂ ⋯ ⊂ Xₙ` of presentation complexes of every length whose inclusions are zero on
`π₂` — in the cellular edge-path model of the universal cover — then `K` has a connected
acyclic regular cover. -/
theorem fs_presComplex_hasAcyclicRegularCover_of_topChains [DecidableEq α] (ρ : J → FreeGroup α)
    (hchains : ∀ n : ℕ, Nonempty (PresChainTopFS ρ n)) :
    Comb.HasAcyclicRegularCover (Comb.presComplex ρ) :=
  presComplex_hasAcyclicRegularCover_of_presChainsFS ρ
    (fun n => (hchains n).map PresChainTopFS.toPresChainFS)

end FiniteChains
