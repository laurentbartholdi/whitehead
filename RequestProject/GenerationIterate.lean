import RequestProject.GenerationStep
import RequestProject.CockcroftExtStep

/-!
# The composite operation: finitely many moves of rule 1

The operation `T` of Section 3.4 is a *finite sequence* of elementary moves, and the paper
finishes the proof of the generation equation (3.3) with the words "Composing proves (3.3)".
This file carries that out for the moves of rule 1 (one new generator together with one new
relator at a time), on top of the formal layer of `RequestProject/GenerationStep.lean`.

* `FiniteChains.extMor` — one elementary move, packaged as a structural map `PresMor`: the
  induced map of fundamental groups is `η_P`, and the induced map on two-chains pads a chain
  of the old presentation with `0` on the new two-cell.
* `FiniteChains.generates_extMor` — equation (3.3) for one move, under the two hypotheses of
  the paper (right regularity of the Fox derivative of the new relator with respect to the
  new generator, and injectivity of `η_{P*}` on fundamental groups).
* `FiniteChains.iterPres` — the presentation obtained after `n` moves, and
  `FiniteChains.iterMor` the composite structural map `P → T^n(P)`.
* `FiniteChains.generates_iterMor` — **equation (3.3) for the composite operation**.
* `FiniteChains.isCockcroft_iterPres` — the composite operation preserves Cockcroftness.
* `FiniteChains.cells_iterMor_eq_zero` — and it preserves zero maps on `π₂`: for a commuting
  square over the composite, a map which is zero on `π₂` upstairs induces zero on the whole
  of `π₂` of the transformed complex.
-/

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains

open MonoidAlgebra

universe u

section OneStep

variable {α : Type u} [Fintype α] [DecidableEq α] {J : Type u} [Fintype J] [DecidableEq J]
variable (ρ : J → FreeGroup α) (w₀ : FreeGroup (Option α))

omit [Fintype α] [DecidableEq J] in
/-- The structural map on two-chains of one elementary move carries Fox cycles to Fox
cycles: the new two-cell receives the coefficient `0`, the old ones the images of the old
coefficients. -/
theorem isFoxCycle_extCycleImage {y : J → MonoidAlgebra ℤ (PresGroup ρ)}
    (hy : IsFoxCycle ρ y) : IsFoxCycle (extRel ρ w₀) (extCycleImage ρ w₀ y) := by
  intro i
  rw [Fintype.sum_option]
  have hnone : extCycleImage ρ w₀ y none * foxMatrixPres (extRel ρ w₀) i none = 0 := by
    show (0 : MonoidAlgebra ℤ (PresGroup (extRel ρ w₀))) * _ = 0
    rw [zero_mul]
  rw [hnone, zero_add]
  cases i with
  | none =>
      refine Finset.sum_eq_zero fun j _ => ?_
      rw [foxMatrix_ext_none_some, mul_zero]
  | some i =>
      have : ∀ j : J, extCycleImage ρ w₀ y (some j) * foxMatrixPres (extRel ρ w₀) (some i) (some j)
          = extRingHom ρ w₀ (y j * foxMatrixPres ρ i j) := by
        intro j
        rw [foxMatrix_ext_some_some, map_mul]
        rfl
      rw [Finset.sum_congr rfl fun j _ => this j, ← map_sum, hy i, map_zero]

omit [Fintype α] [DecidableEq α] [Fintype J] [DecidableEq J] in
theorem extCycleImage_add (y z : J → MonoidAlgebra ℤ (PresGroup ρ)) :
    extCycleImage ρ w₀ (y + z) = extCycleImage ρ w₀ y + extCycleImage ρ w₀ z := by
  funext jo
  cases jo with
  | none => show (0 : MonoidAlgebra ℤ (PresGroup (extRel ρ w₀))) = 0 + 0; rw [add_zero]
  | some j => exact map_add (extRingHom ρ w₀) _ _

omit [Fintype α] [DecidableEq α] [Fintype J] [DecidableEq J] in
theorem extCycleImage_smul (c : MonoidAlgebra ℤ (PresGroup ρ))
    (y : J → MonoidAlgebra ℤ (PresGroup ρ)) :
    extCycleImage ρ w₀ (c • y)
      = MonoidAlgebra.mapDomainRingHom ℤ (extHom ρ w₀) c • extCycleImage ρ w₀ y := by
  funext jo
  cases jo with
  | none => show (0 : MonoidAlgebra ℤ (PresGroup (extRel ρ w₀))) = _ * 0; rw [mul_zero]
  | some j =>
      show extRingHom ρ w₀ (c * y j) = extRingHom ρ w₀ c * extRingHom ρ w₀ (y j)
      rw [map_mul]

/-- **One move of rule 1 as a structural map.**  This is the map `η_P` of (3.2) together
with its effect on two-chains. -/
noncomputable def extMor : PresMor ρ (extRel ρ w₀) where
  hom := extHom ρ w₀
  cells := extCycleImage ρ w₀
  cells_add := extCycleImage_add ρ w₀
  cells_smul := extCycleImage_smul ρ w₀
  cells_cycle := fun _ hy => isFoxCycle_extCycleImage ρ w₀ hy
  cells_aug := by
    intro y hy jo
    cases jo with
    | none => show augPres (extRel ρ w₀) 0 = 0; rw [map_zero]
    | some j => rw [show extCycleImage ρ w₀ y (some j) = extRingHom ρ w₀ (y j) from rfl,
        augPres_extRingHom, hy j]

omit [Fintype α] [DecidableEq J] in
/-- **Equation (3.3) for one elementary move**, in the form of the abstract interface: this
is `FiniteChains.extCycle_mem_span` read through `FiniteChains.extMor`. -/
theorem generates_extMor
    (hreg : ∀ x : MonoidAlgebra ℤ (PresGroup (extRel ρ w₀)),
      x * foxMatrixPres (extRel ρ w₀) none none = 0 → x = 0)
    (hinj : Function.Injective (extHom ρ w₀)) : Generates (extMor ρ w₀) :=
  fun _ hv => extCycle_mem_span ρ w₀ hreg hinj hv

end OneStep

/-! ### Iterating the elementary move -/

/-- The generators (resp. two-cells) after `n` moves: `n` new names are adjoined one at a
time. -/
abbrev optIter (α : Type u) : ℕ → Type u
  | 0 => α
  | n + 1 => Option (optIter α n)

instance optIterFintype (α : Type u) [Fintype α] : ∀ n, Fintype (optIter α n)
  | 0 => ‹Fintype α›
  | n + 1 => @instFintypeOption _ (optIterFintype α n)

instance optIterDecidableEq (α : Type u) [DecidableEq α] : ∀ n, DecidableEq (optIter α n)
  | 0 => ‹DecidableEq α›
  | n + 1 => fun a b => @Option.instDecidableEq _ (optIterDecidableEq α n) a b

section Iterate

variable {α : Type u} [Fintype α] [DecidableEq α] {J : Type u} [Fintype J] [DecidableEq J]
variable (ρ : J → FreeGroup α) (w : ∀ n : ℕ, FreeGroup (Option (optIter α n)))

/-- The presentation after `n` elementary moves: at stage `n` the new generator is the fresh
name `none` and the new relator is `w n`. -/
def iterPres : ∀ n : ℕ, optIter J n → FreeGroup (optIter α n)
  | 0 => ρ
  | n + 1 => extRel (iterPres n) (w n)

omit [Fintype α] [DecidableEq α] [Fintype J] [DecidableEq J] in
@[simp] theorem iterPres_zero : iterPres ρ w 0 = ρ := rfl

omit [Fintype α] [DecidableEq α] [Fintype J] [DecidableEq J] in
@[simp] theorem iterPres_succ (n : ℕ) :
    iterPres ρ w (n + 1) = extRel (iterPres ρ w n) (w n) := rfl

/-- The identity structural map of a presentation. -/
def PresMor.id {β K : Type u} [Fintype β] [DecidableEq β] [Fintype K] (σ : K → FreeGroup β) :
    PresMor σ σ where
  hom := MonoidHom.id _
  cells := _root_.id
  cells_add := fun _ _ => rfl
  cells_smul := fun c y => by
    have h : (MonoidAlgebra.mapDomainRingHom ℤ (MonoidHom.id (PresGroup σ)) c
        : MonoidAlgebra ℤ (PresGroup σ)) = c := MonoidAlgebra.mapDomain_id c
    show _root_.id (c • y)
      = (MonoidAlgebra.mapDomainRingHom ℤ (MonoidHom.id (PresGroup σ)) c
          : MonoidAlgebra ℤ (PresGroup σ)) • _root_.id y
    rw [h]
    rfl
  cells_cycle := fun _ hy => hy
  cells_aug := fun _ hy => hy

/-- The composite structural map `P → T^n(P)` of the first `n` elementary moves. -/
noncomputable def iterMor : ∀ n : ℕ, PresMor ρ (iterPres ρ w n)
  | 0 => PresMor.id ρ
  | n + 1 => by exact (extMor (iterPres ρ w n) (w n)).comp (iterMor n)

omit [DecidableEq J] in
/-- **Equation (3.3) for the composite operation.**  If each elementary move satisfies the
two hypotheses of the paper, then the second homotopy group of the presentation obtained
after `n` moves is generated, over its group ring, by the image of the second homotopy group
of the original presentation. -/
theorem generates_iterMor
    (hreg : ∀ k : ℕ, ∀ x : MonoidAlgebra ℤ (PresGroup (extRel (iterPres ρ w k) (w k))),
      x * foxMatrixPres (extRel (iterPres ρ w k) (w k)) none none = 0 → x = 0)
    (hinj : ∀ k : ℕ, Function.Injective (extHom (iterPres ρ w k) (w k))) :
    ∀ n : ℕ, Generates (iterMor ρ w n) := by
  intro n
  induction n with
  | zero => exact fun v hv => Submodule.subset_span ⟨v, hv, rfl⟩
  | succ n ih =>
      exact (generates_extMor (iterPres ρ w n) (w n) (hreg n) (hinj n)).comp ih

omit [DecidableEq J] in
/-- **The composite operation preserves the Cockcroft property** (Lemma 3.9 for the whole of
`T`, once `T` is a finite sequence of moves of rule 1). -/
theorem isCockcroft_iterPres
    (hreg : ∀ k : ℕ, ∀ x : MonoidAlgebra ℤ (PresGroup (extRel (iterPres ρ w k) (w k))),
      x * foxMatrixPres (extRel (iterPres ρ w k) (w k)) none none = 0 → x = 0)
    (hinj : ∀ k : ℕ, Function.Injective (extHom (iterPres ρ w k) (w k)))
    (hP : IsCockcroft ρ) (n : ℕ) : IsCockcroft (iterPres ρ w n) :=
  isCockcroft_of_generates (iterMor ρ w n) (generates_iterMor ρ w hreg hinj n) hP

omit [DecidableEq J] in
/-- **The composite operation preserves zero maps on `π₂`** (the last paragraph of
Lemma 3.9 for the whole of `T`).  For a commuting square `T(j) ∘ η_P = η_{P'} ∘ j` over the
composite operation, if the inclusion `j` is zero on `π₂`, then `T(j)` is zero on all of
`π₂(T(P))`. -/
theorem cells_iterMor_eq_zero {α' J' β' K' : Type u}
    [Fintype α'] [DecidableEq α'] [Fintype J'] [DecidableEq J']
    [Fintype β'] [DecidableEq β'] [Fintype K']
    {ρ' : J' → FreeGroup α'} {τ' : K' → FreeGroup β'}
    (n : ℕ) (etaP' : PresMor ρ' τ') (jm : PresMor ρ ρ') (Tj : PresMor (iterPres ρ w n) τ')
    (hreg : ∀ k : ℕ, ∀ x : MonoidAlgebra ℤ (PresGroup (extRel (iterPres ρ w k) (w k))),
      x * foxMatrixPres (extRel (iterPres ρ w k) (w k)) none none = 0 → x = 0)
    (hinj : ∀ k : ℕ, Function.Injective (extHom (iterPres ρ w k) (w k)))
    (hsq : ∀ y, Tj.cells ((iterMor ρ w n).cells y) = etaP'.cells (jm.cells y))
    (hzero : ∀ y, IsFoxCycle ρ y → jm.cells y = 0)
    {v : optIter J n → MonoidAlgebra ℤ (PresGroup (iterPres ρ w n))}
    (hv : IsFoxCycle (iterPres ρ w n) v) : Tj.cells v = 0 :=
  cells_eq_zero_of_generates (iterMor ρ w n) etaP' jm Tj hsq hzero
    (generates_iterMor ρ w hreg hinj n) hv

end Iterate

end FiniteChains
