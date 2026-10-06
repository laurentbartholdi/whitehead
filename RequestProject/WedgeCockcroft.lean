module

public import RequestProject.BlockCockcroft

@[expose] public section

/-!
# A wedge of Cockcroft complexes is Cockcroft

Lemma 3.10 finishes with: "A wedge of Cockcroft complexes is Cockcroft: its `H₂` is the
direct sum of those of the factors, and the factor retractions detect every coordinate of a
Hurewicz image."

In the combinatorial model the wedge of the presentation complexes of `⟨x_i | r_j⟩` and
`⟨y_a | s_k⟩` is the presentation complex of the disjoint union of the generators and of the
relators.  Each factor is a retract block of the wedge in the sense of
`RequestProject/BlockCockcroft.lean` — the retraction kills the generators of the other
factor — so every coordinate of a Fox cycle of the wedge has zero augmentation:

`FiniteChains.isCockcroft_wedgeRel`.
-/

namespace FiniteChains

open MonoidAlgebra

universe u

variable {α β : Type u} {J K : Type u}
variable (ρ : J → FreeGroup α) (σ : K → FreeGroup β)

/-- The presentation of the wedge: the generators and the relators of the two presentations
side by side. -/
def wedgeRel : J ⊕ K → FreeGroup (α ⊕ β)
  | Sum.inl j => FreeGroup.map Sum.inl (ρ j)
  | Sum.inr k => FreeGroup.map Sum.inr (σ k)

@[simp] theorem wedgeRel_inl (j : J) : wedgeRel ρ σ (Sum.inl j) = FreeGroup.map Sum.inl (ρ j) :=
  rfl

@[simp] theorem wedgeRel_inr (k : K) : wedgeRel ρ σ (Sum.inr k) = FreeGroup.map Sum.inr (σ k) :=
  rfl

/-- The retraction of the ambient free group onto the first factor. -/
def killR : FreeGroup (α ⊕ β) →* FreeGroup α :=
  FreeGroup.lift (Sum.elim FreeGroup.of (fun _ => 1))

/-- The retraction of the ambient free group onto the second factor. -/
def killL : FreeGroup (α ⊕ β) →* FreeGroup β :=
  FreeGroup.lift (Sum.elim (fun _ => 1) FreeGroup.of)

@[simp] theorem killR_map_inl (w : FreeGroup α) :
    killR (β := β) (FreeGroup.map Sum.inl w) = w := by
  have h : (killR (α := α) (β := β)).comp (FreeGroup.map Sum.inl) = MonoidHom.id _ :=
    FreeGroup.ext_hom _ _ fun a => by simp [killR]
  exact congrArg (fun f : FreeGroup α →* FreeGroup α => f w) h

@[simp] theorem killR_map_inr (w : FreeGroup β) :
    killR (α := α) (FreeGroup.map Sum.inr w) = 1 := by
  have h : (killR (α := α) (β := β)).comp (FreeGroup.map Sum.inr) = 1 :=
    FreeGroup.ext_hom _ _ fun b => by simp [killR]
  exact congrArg (fun f : FreeGroup β →* FreeGroup α => f w) h

@[simp] theorem killL_map_inr (w : FreeGroup β) :
    killL (α := α) (FreeGroup.map Sum.inr w) = w := by
  have h : (killL (α := α) (β := β)).comp (FreeGroup.map Sum.inr) = MonoidHom.id _ :=
    FreeGroup.ext_hom _ _ fun b => by simp [killL]
  exact congrArg (fun f : FreeGroup β →* FreeGroup β => f w) h

@[simp] theorem killL_map_inl (w : FreeGroup α) :
    killL (β := β) (FreeGroup.map Sum.inl w) = 1 := by
  have h : (killL (α := α) (β := β)).comp (FreeGroup.map Sum.inl) = 1 :=
    FreeGroup.ext_hom _ _ fun a => by simp [killL]
  exact congrArg (fun f : FreeGroup α →* FreeGroup β => f w) h

section Blocks

variable [DecidableEq α] [DecidableEq β]

/-- The first factor is a retract block of the wedge. -/
theorem isBlock_wedge_left : IsBlock ρ (wedgeRel ρ σ) Sum.inl Sum.inl killR where
  gen_injective := Sum.inl_injective
  cell_injective := Sum.inl_injective
  rel_eq _ := rfl
  fox_outside i l hl := by
    cases l with
    | inl j => exact absurd ⟨j, rfl⟩ hl
    | inr k =>
        rw [wedgeRel_inr]
        exact fox_map_of_not_mem_range Sum.inr (by simp) (σ k)
  retract_map w := killR_map_inl w
  retract_rel l := by
    cases l with
    | inl j =>
        rw [wedgeRel_inl, killR_map_inl]
        exact Subgroup.subset_normalClosure (Set.mem_range_self _)
    | inr k =>
        rw [wedgeRel_inr, killR_map_inr]
        exact one_mem _

/-- The second factor is a retract block of the wedge. -/
theorem isBlock_wedge_right : IsBlock σ (wedgeRel ρ σ) Sum.inr Sum.inr killL where
  gen_injective := Sum.inr_injective
  cell_injective := Sum.inr_injective
  rel_eq _ := rfl
  fox_outside i l hl := by
    cases l with
    | inl j =>
        rw [wedgeRel_inl]
        exact fox_map_of_not_mem_range Sum.inl (by simp) (ρ j)
    | inr k => exact absurd ⟨k, rfl⟩ hl
  retract_map w := killL_map_inr w
  retract_rel l := by
    cases l with
    | inl j =>
        rw [wedgeRel_inl, killL_map_inl]
        exact one_mem _
    | inr k =>
        rw [wedgeRel_inr, killL_map_inr]
        exact Subgroup.subset_normalClosure (Set.mem_range_self _)

variable [Fintype J] [Fintype K]

/-- **A wedge of Cockcroft complexes is Cockcroft** (the last step of Lemma 3.10). -/
theorem isCockcroft_wedgeRel (hρ : IsCockcroft ρ) (hσ : IsCockcroft σ) :
    IsCockcroft (wedgeRel ρ σ) := by
  intro v hv jk
  cases jk with
  | inl j => exact augPres_block_eq_zero (isBlock_wedge_left ρ σ) hρ hv j
  | inr k => exact augPres_block_eq_zero (isBlock_wedge_right ρ σ) hσ hv k

end Blocks

end FiniteChains
