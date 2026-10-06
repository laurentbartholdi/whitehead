import RequestProject.PresentationChain

/-!
# The stages of a chain of presentations are subcomplexes

`RequestProject/PresentationChain.lean` describes a chain `K = X₀ ⊂ ⋯ ⊂ Xₙ` of
presentation complexes by an inclusion of generating sets and of two-cells such that an old
two-cell is attached along the same word.  This file checks that this is really an
inclusion of subcomplexes in the combinatorial model of
`RequestProject/CellComplex.lean`: such data induce a cellular map of the presentation
complexes which is injective on edges and on two-cells
(`FiniteChains.Comb.presInclHom`), and in particular every stage of a
`FiniteChains.PresChain` includes into the next one
(`FiniteChains.PresChain.stageHomIncl`) and `K` includes into `X₀`
(`FiniteChains.PresChain.baseHomIncl`).

The only nontrivial ingredient is that the reduced word of the image of `w` under an
injective map of generating sets is the image of the reduced word of `w`
(`FiniteChains.toWord_map`).
-/

namespace FiniteChains

open List

variable {α β : Type*} [DecidableEq α] [DecidableEq β]

/-- The reduced word of the image of `w` under an injective map of generating sets is the
image of the reduced word of `w`. -/
theorem toWord_map (f : α → β) (hf : Function.Injective f) (w : FreeGroup α) :
    (FreeGroup.map f w).toWord = w.toWord.map (fun p => (f p.1, p.2)) := by
  have hmk : FreeGroup.map f w = FreeGroup.mk (w.toWord.map (fun p => (f p.1, p.2))) := by
    conv_lhs => rw [← FreeGroup.mk_toWord (x := w)]
    rfl
  have hred : FreeGroup.IsReduced (w.toWord.map (fun p => (f p.1, p.2))) :=
    isChain_map_of_isChain _ (fun a b hab hfa => hab (hf hfa))
      (FreeGroup.isReduced_toWord (x := w))
  rw [hmk, FreeGroup.toWord_mk, hred.reduce_eq]

namespace Comb

universe u

variable {α β : Type u} [DecidableEq α] [DecidableEq β] {J K : Type u}

/-- An inclusion of presentations — an injective map of generators and an injective map of
two-cells carrying a two-cell to one attached along the same word — is a cellular map of
the presentation complexes. -/
def presInclHom (f : α → β) (hf : Function.Injective f) (ρ : J → FreeGroup α)
    (σ : K → FreeGroup β) (g : J → K) (hg : ∀ j, σ (g j) = FreeGroup.map f (ρ j)) :
    Hom (presComplex ρ) (presComplex σ) where
  onV _ := PUnit.unit
  onE := f
  onF := g
  src_onE _ := rfl
  tgt_onE _ := rfl
  base_onF _ := rfl
  att_onF j := by
    show FreeGroup.toWord (σ (g j)) = (FreeGroup.toWord (ρ j)).map (fun p => (f p.1, p.2))
    rw [hg j, toWord_map f hf]

@[simp] theorem presInclHom_onE (f : α → β) (hf : Function.Injective f) (ρ : J → FreeGroup α)
    (σ : K → FreeGroup β) (g : J → K) (hg : ∀ j, σ (g j) = FreeGroup.map f (ρ j)) :
    (presInclHom f hf ρ σ g hg).onE = f := rfl

@[simp] theorem presInclHom_onF (f : α → β) (hf : Function.Injective f) (ρ : J → FreeGroup α)
    (σ : K → FreeGroup β) (g : J → K) (hg : ∀ j, σ (g j) = FreeGroup.map f (ρ j)) :
    (presInclHom f hf ρ σ g hg).onF = g := rfl

end Comb

namespace PresChain

universe u

variable {α J : Type u} {ρ : J → FreeGroup α} {n : ℕ} (h : PresChain ρ n)

/-- The stage `X_r` is a subcomplex of `X_{r+1}`. -/
def stageHomIncl (r : ℕ) :
    letI := h.decGen r
    letI := h.decGen (r + 1)
    Comb.Hom (Comb.presComplex (h.rel r)) (Comb.presComplex (h.rel (r + 1))) :=
  letI := h.decGen r
  letI := h.decGen (r + 1)
  Comb.presInclHom (h.genIncl r) (h.genIncl_injective r) (h.rel r) (h.rel (r + 1))
    (h.cellIncl r) (h.rel_incl r)

variable [DecidableEq α]

/-- `K` is a subcomplex of the first stage `X₀`. -/
def baseHomIncl :
    letI := h.decGen 0
    Comb.Hom (Comb.presComplex ρ) (Comb.presComplex (h.rel 0)) :=
  letI := h.decGen 0
  Comb.presInclHom h.baseGen h.baseGen_injective ρ (h.rel 0) h.baseCell h.rel_base

end PresChain
end FiniteChains
