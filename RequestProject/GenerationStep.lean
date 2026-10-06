module

public import RequestProject.Pi2Generation

@[expose] public section

/-!
# Structural maps with the generation property, and their composites

Lemma 3.9 of the paper states the generation equation

  `π₂(T(P)) = ℤ[G(T(P))] · η_{P*} π₂(P)`                                          (3.3)

for the operation `T`, and then *composes*: `T` is a finite sequence of elementary moves
(rules 1–3), each of which has the generation property, and the paper concludes with
"Composing proves (3.3)".  The two consequences drawn from (3.3) are also formal:
Cockcroftness is inherited by the target, and a map which is zero on `π₂` upstairs stays
zero on `π₂` after applying `T`.

This file isolates that formal layer.  A **structural map** `PresMor ρ ρ'` between two
presentations is a homomorphism of the presented groups together with the induced map of
two-chains, semilinear over it and carrying Fox cycles to Fox cycles and zero augmentations
to zero augmentations.  `FiniteChains.Generates` is equation (3.3) for such a map.  The
results are:

* `FiniteChains.Generates.comp` — the generation property is stable under composition,
  which is exactly the step "composing proves (3.3)";
* `FiniteChains.isCockcroft_of_generates` — a structural map with the generation property
  transports the Cockcroft property (`P` Cockcroft ⟹ `T(P)` Cockcroft);
* `FiniteChains.cells_eq_zero_of_generates` — the last paragraph of Lemma 3.9: for a
  commuting square `T(j) ∘ η_P = η_{P'} ∘ j`, if `j` is zero on `π₂` and (3.3) holds for
  `η_P`, then `T(j)` is zero on all of `π₂(T(P))`.

The elementary move of rule 1 is packaged as a `PresMor` in
`RequestProject/GenerationIterate.lean`, where the composite of finitely many moves is
treated.
-/

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains

open MonoidAlgebra

universe u

section

variable {α J α' J' α'' J'' : Type u}
  [Fintype α] [DecidableEq α] [Fintype J]
  [Fintype α'] [DecidableEq α'] [Fintype J']
  [Fintype α''] [DecidableEq α''] [Fintype J'']

/-- A **structural map** between presentation complexes: the induced homomorphism of
fundamental groups together with the induced map on two-chains of the universal covers.
The map on chains is additive, semilinear over the group homomorphism, carries Fox cycles
(elements of `π₂`) to Fox cycles, and carries chains with zero augmentation to chains with
zero augmentation (naturality of the Hurewicz map). -/
structure PresMor (ρ : J → FreeGroup α) (ρ' : J' → FreeGroup α') where
  /-- The induced map of fundamental groups. -/
  hom : PresGroup ρ →* PresGroup ρ'
  /-- The induced map of two-chains. -/
  cells : (J → MonoidAlgebra ℤ (PresGroup ρ)) → (J' → MonoidAlgebra ℤ (PresGroup ρ'))
  cells_add : ∀ y z, cells (y + z) = cells y + cells z
  cells_smul : ∀ (c : MonoidAlgebra ℤ (PresGroup ρ)) (y : J → MonoidAlgebra ℤ (PresGroup ρ)),
    cells (c • y) = MonoidAlgebra.mapDomainRingHom ℤ hom c • cells y
  /-- The map carries `π₂` into `π₂`. -/
  cells_cycle : ∀ y, IsFoxCycle ρ y → IsFoxCycle ρ' (cells y)
  /-- Naturality of the Hurewicz map: zero augmentations go to zero augmentations. -/
  cells_aug : ∀ y, (∀ j, augPres ρ (y j) = 0) → ∀ j', augPres ρ' (cells y j') = 0

namespace PresMor

variable {ρ : J → FreeGroup α} {ρ' : J' → FreeGroup α'} {ρ'' : J'' → FreeGroup α''}

omit [Fintype α] [Fintype α'] in
@[simp] theorem cells_zero (f : PresMor ρ ρ') : f.cells 0 = 0 := by
  have h := f.cells_smul 0 0
  rw [zero_smul, map_zero, zero_smul] at h
  exact h

omit [Fintype α] [DecidableEq α] [Fintype J] [Fintype α'] [DecidableEq α'] [Fintype J']
  [Fintype α''] [DecidableEq α''] [Fintype J''] in
/-- Pushing coefficients along a composite of group homomorphisms. -/
theorem mapDomainRingHom_comp (g : PresGroup ρ' →* PresGroup ρ'') (f : PresGroup ρ →* PresGroup ρ')
    (c : MonoidAlgebra ℤ (PresGroup ρ)) :
    MonoidAlgebra.mapDomainRingHom ℤ (g.comp f) c
      = MonoidAlgebra.mapDomainRingHom ℤ g (MonoidAlgebra.mapDomainRingHom ℤ f c) := by
  change MonoidAlgebra.mapDomain (g.comp f) c = MonoidAlgebra.mapDomain g (MonoidAlgebra.mapDomain f c)
  rw [← MonoidAlgebra.mapDomain_comp]
  rfl

/-- The composite of two structural maps. -/
def comp (g : PresMor ρ' ρ'') (f : PresMor ρ ρ') : PresMor ρ ρ'' where
  hom := g.hom.comp f.hom
  cells := fun y => g.cells (f.cells y)
  cells_add := fun y z => by rw [f.cells_add, g.cells_add]
  cells_smul := fun c y => by
    rw [f.cells_smul, g.cells_smul, mapDomainRingHom_comp]
  cells_cycle := fun y hy => g.cells_cycle _ (f.cells_cycle _ hy)
  cells_aug := fun y hy => g.cells_aug _ (f.cells_aug _ hy)

omit [Fintype α] [Fintype α'] [Fintype α''] in
@[simp] theorem comp_cells (g : PresMor ρ' ρ'') (f : PresMor ρ ρ')
    (y : J → MonoidAlgebra ℤ (PresGroup ρ)) : (g.comp f).cells y = g.cells (f.cells y) := rfl

omit [Fintype α'] [Fintype α''] in
/-- The image of a span under a structural map lands in the span of the image. -/
theorem cells_mem_span (g : PresMor ρ' ρ'')
    {S : Set (J' → MonoidAlgebra ℤ (PresGroup ρ'))} {y : J' → MonoidAlgebra ℤ (PresGroup ρ')}
    (hy : y ∈ Submodule.span (MonoidAlgebra ℤ (PresGroup ρ')) S) :
    g.cells y ∈ Submodule.span (MonoidAlgebra ℤ (PresGroup ρ'')) (g.cells '' S) := by
  induction hy using Submodule.span_induction with
  | mem x hx => exact Submodule.subset_span ⟨x, hx, rfl⟩
  | zero => simp
  | add x z _ _ hx hz => rw [g.cells_add]; exact Submodule.add_mem _ hx hz
  | smul c x _ hx => rw [g.cells_smul]; exact Submodule.smul_mem _ _ hx

end PresMor

/-- **Equation (3.3)** for a structural map: the second homotopy group of the target is
generated, over the group ring of the target, by the image of the second homotopy group of
the source. -/
def Generates {ρ : J → FreeGroup α} {ρ' : J' → FreeGroup α'} (f : PresMor ρ ρ') : Prop :=
  ∀ v : J' → MonoidAlgebra ℤ (PresGroup ρ'), IsFoxCycle ρ' v →
    v ∈ Submodule.span (MonoidAlgebra ℤ (PresGroup ρ'))
      {w : J' → MonoidAlgebra ℤ (PresGroup ρ') | ∃ y, IsFoxCycle ρ y ∧ w = f.cells y}

variable {ρ : J → FreeGroup α} {ρ' : J' → FreeGroup α'} {ρ'' : J'' → FreeGroup α''}

omit [Fintype α] [Fintype α'] [Fintype α''] in
/-- **"Composing proves (3.3)".**  The generation property of Lemma 3.9 is stable under
composition of structural maps, so it holds for the composite operation `T` as soon as it
holds for each elementary move. -/
theorem Generates.comp {g : PresMor ρ' ρ''} {f : PresMor ρ ρ'}
    (hg : Generates g) (hf : Generates f) : Generates (g.comp f) := by
  intro v hv
  refine Submodule.span_le.2 ?_ (hg v hv)
  rintro _ ⟨y', hy', rfl⟩
  refine Submodule.span_le.2 ?_ (g.cells_mem_span (hf y' hy'))
  rintro _ ⟨_, ⟨y, hy, rfl⟩, rfl⟩
  exact Submodule.subset_span ⟨y, hy, rfl⟩

omit [Fintype α] [Fintype α'] in
/-- **A structural map with the generation property transports Cockcroftness** (the
corresponding step of Lemma 3.9): the augmentation of a `ℤ[G']`-combination of images of Fox
cycles is the corresponding integer combination of their augmentations, hence zero. -/
theorem isCockcroft_of_generates (f : PresMor ρ ρ') (hgen : Generates f)
    (hP : IsCockcroft ρ) : IsCockcroft ρ' := by
  intro v hv
  set N : Submodule (MonoidAlgebra ℤ (PresGroup ρ')) (J' → MonoidAlgebra ℤ (PresGroup ρ')) :=
    { carrier := {w | ∀ j', augPres ρ' (w j') = 0}
      add_mem' := by
        intro a b ha hb j'
        rw [Pi.add_apply, map_add, ha j', hb j', add_zero]
      zero_mem' := by intro j'; simp
      smul_mem' := by
        intro c a ha j'
        rw [Pi.smul_apply, smul_eq_mul, map_mul, ha j', mul_zero] } with hN
  have hle : Submodule.span (MonoidAlgebra ℤ (PresGroup ρ'))
      {w : J' → MonoidAlgebra ℤ (PresGroup ρ') | ∃ y, IsFoxCycle ρ y ∧ w = f.cells y} ≤ N := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨y, hy, rfl⟩
    exact f.cells_aug y (fun j => hP y hy j)
  exact hle (hgen v hv)

omit [Fintype α] [Fintype α'] in
/-- **The last paragraph of Lemma 3.9.**  Let `j : P ⊂ P'` be an inclusion, `η_P`, `η_{P'}`
the structural maps and `T(j)` the induced map, so that `T(j) ∘ η_P = η_{P'} ∘ j`.  If `j` is
zero on `π₂` and the generation property (3.3) holds for `η_P`, then `T(j)` is zero on the
whole of `π₂(T(P))`. -/
theorem cells_eq_zero_of_generates {β K β' K' : Type u}
    [Fintype β] [DecidableEq β] [Fintype K] [Fintype β'] [DecidableEq β'] [Fintype K']
    {τ : K → FreeGroup β} {τ' : K' → FreeGroup β'}
    (etaP : PresMor ρ τ) (etaP' : PresMor ρ' τ') (jm : PresMor ρ ρ') (Tj : PresMor τ τ')
    (hsq : ∀ y, Tj.cells (etaP.cells y) = etaP'.cells (jm.cells y))
    (hzero : ∀ y, IsFoxCycle ρ y → jm.cells y = 0)
    (hgen : Generates etaP)
    {v : K → MonoidAlgebra ℤ (PresGroup τ)} (hv : IsFoxCycle τ v) : Tj.cells v = 0 := by
  set N : Submodule (MonoidAlgebra ℤ (PresGroup τ)) (K → MonoidAlgebra ℤ (PresGroup τ)) :=
    { carrier := {w | Tj.cells w = 0}
      add_mem' := by
        intro a b ha hb
        simp only [Set.mem_setOf_eq] at ha hb ⊢
        rw [Tj.cells_add, ha, hb, add_zero]
      zero_mem' := by simp
      smul_mem' := by
        intro c a ha
        simp only [Set.mem_setOf_eq] at ha ⊢
        rw [Tj.cells_smul, ha, smul_zero] } with hN
  have hle : Submodule.span (MonoidAlgebra ℤ (PresGroup τ))
      {w : K → MonoidAlgebra ℤ (PresGroup τ) | ∃ y, IsFoxCycle ρ y ∧ w = etaP.cells y} ≤ N := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨y, hy, rfl⟩
    show Tj.cells (etaP.cells y) = 0
    rw [hsq y, hzero y hy, etaP'.cells_zero]
  exact hle (hgen v hv)

end

end FiniteChains
