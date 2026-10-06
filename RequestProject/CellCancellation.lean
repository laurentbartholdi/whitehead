module

public import Mathlib

@[expose] public section

/-!
# Cancelling the polygon-cylinder three-cell against the replaced two-cell

The substitution (3.4) of the paper is obtained from the double mapping cylinder by two
simplifications:

> In the double mapping cylinder, the polygon-cylinder three-cell cancels that old two-cell.
> Eliminating the edge-cylinder defining pairs then gives exactly (3.4).

This file proves the algebraic content of the first simplification at the level of the
equivariant cellular chain complexes.  The three-chains are free of rank one over the group
ring on the polygon-cylinder cell, and the coefficient of the replaced two-cell in its
boundary is a unit (the cell is crossed exactly once): in the notation below the two-chains
split as `P × Q` — `P` the retained two-cells, `Q` the free module on the replaced one — and
the boundary `∂₃ = (α, β)` has `β` invertible.

* `FiniteChains.Cancel.cancelMap` — the chain-level cancellation `κ(p, q) = (p - α β⁻¹ q, 0)`;
* `FiniteChains.Cancel.cancelMap_boundary` — it kills the three-boundaries;
* `FiniteChains.Cancel.cycle_sub_boundary_eq` — every two-cycle becomes, after cancellation,
  a two-cycle supported on the retained two-cells, and it differs from the original one by a
  three-boundary;
* `FiniteChains.Cancel.mem_range_boundary_iff` — a chain supported on the retained two-cells
  is a three-boundary only if it is zero, so the cancelled complex computes `H₂` on the nose;
* `FiniteChains.Cancel.generation_after_cancellation` — **the transfer of the generation
  statement**: if the two-cycles of the three-dimensional complex are spanned, modulo
  three-boundaries, by a set `S`, then the two-cycles of the cancelled two-dimensional
  complex are spanned by the cancelled images of `S`.  This is the step which turns the
  homological statement about the double mapping cylinder into the statement about the
  two-complex of the substituted presentation.
-/

namespace FiniteChains
namespace Cancel

variable {R : Type*} [Ring R]
variable {P Q B₁ B₃ : Type*}
  [AddCommGroup P] [Module R P] [AddCommGroup Q] [Module R Q]
  [AddCommGroup B₁] [Module R B₁] [AddCommGroup B₃] [Module R B₃]

variable (α : B₃ →ₗ[R] P) (β : B₃ ≃ₗ[R] Q)

/-- The boundary of the three-cells: its component on the replaced two-cell is invertible. -/
def bdry₃ : B₃ →ₗ[R] P × Q := (α.prod (β : B₃ →ₗ[R] Q))

@[simp] theorem bdry₃_apply (y : B₃) : bdry₃ α β y = (α y, β y) := rfl

/-- **The cancellation map.**  It replaces a two-chain by the two-chain supported on the
retained cells obtained after cancelling the replaced two-cell against the three-cell. -/
def cancelMap : P × Q →ₗ[R] P × Q :=
  (LinearMap.fst R P Q - α.comp ((β.symm : Q →ₗ[R] B₃).comp (LinearMap.snd R P Q))).prod 0

@[simp] theorem cancelMap_apply (z : P × Q) :
    cancelMap α β z = (z.1 - α (β.symm z.2), 0) := rfl

@[simp] theorem cancelMap_of_snd_zero (p : P) : cancelMap α β (p, 0) = (p, 0) := by
  simp [cancelMap]

/-- The cancellation map kills the boundaries of the three-cells. -/
@[simp] theorem cancelMap_boundary (y : B₃) : cancelMap α β (bdry₃ α β y) = 0 := by
  simp [cancelMap]

variable (bdry₂ : P × Q →ₗ[R] B₁)

/-- After cancellation a two-cycle is again a two-cycle, provided `∂₂ ∘ ∂₃ = 0`. -/
theorem cancelMap_cycle (hd : ∀ y : B₃, bdry₂ (bdry₃ α β y) = 0) (z : P × Q)
    (hz : bdry₂ z = 0) : bdry₂ (cancelMap α β z) = 0 := by
  have hz' : cancelMap α β z = z - bdry₃ α β (β.symm z.2) := by
    simp [cancelMap, Prod.ext_iff]
  rw [hz', map_sub, hz, hd, sub_zero]

/-- Every two-cycle differs from its cancellation by a three-boundary. -/
theorem cycle_sub_boundary_eq (z : P × Q) :
    z - cancelMap α β z = bdry₃ α β (β.symm z.2) := by
  simp [cancelMap, Prod.ext_iff]

/-- A chain supported on the retained two-cells is a three-boundary only if it vanishes:
after the cancellation no new boundaries appear, so the two-cycles of the cancelled complex
are exactly `H₂` of the original one. -/
theorem mem_range_boundary_iff (p : P) (y : B₃) (h : bdry₃ α β y = (p, 0)) : p = 0 ∧ y = 0 := by
  have hy : β y = 0 := congrArg Prod.snd h
  have hy0 : y = 0 := by
    have := congrArg β.symm hy
    simpa using this
  refine ⟨?_, hy0⟩
  have := congrArg Prod.fst h
  simpa [hy0] using this.symm

/-- **Transfer of the generation statement through the cancellation.**  If every two-cycle of
the three-dimensional complex lies, modulo three-boundaries, in the span of a set `S`, then
every two-cycle supported on the retained two-cells lies in the span of the cancelled images
of `S`. -/
theorem generation_after_cancellation (S : Set (P × Q))
    (hS : ∀ z : P × Q, bdry₂ z = 0 → ∃ y : B₃, z - bdry₃ α β y ∈ Submodule.span R S)
    (p : P) (hp : bdry₂ (p, 0) = 0) :
    (p, 0) ∈ Submodule.span R (cancelMap α β '' S) := by
  obtain ⟨y, hy⟩ := hS (p, 0) hp
  have himg : Submodule.map (cancelMap α β) (Submodule.span R S)
      ≤ Submodule.span R (cancelMap α β '' S) := by
    rw [Submodule.map_span]
  have := himg ⟨_, hy, rfl⟩
  rwa [map_sub, cancelMap_boundary, sub_zero, cancelMap_of_snd_zero] at this

end Cancel
end FiniteChains
