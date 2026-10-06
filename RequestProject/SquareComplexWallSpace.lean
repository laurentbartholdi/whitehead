module

public import RequestProject.SquareComplexWalls
public import RequestProject.WallSpaceDualConnected

@[expose] public section

/-!
# From the walls of a square complex to a wall space

`RequestProject/SquareComplexWalls.lean` produces, for a connected and simply connected square
complex carrying a system of walls, halfspace coordinates `σ i : Vx → ZMod 2`: each wall cuts
the vertex set into two sides, an edge changes exactly one coordinate, and only finitely many
walls separate two given vertices.  `RequestProject/WallSpaceDual.lean` shows that a *wall
space* has a median dual cube complex.

This file joins the two halves.  The single missing ingredient is the *separation* property —
distinct vertices are separated by some wall — which is exactly the part of Sageev's theorem
that is not proved in the project; it is therefore carried here as an explicit hypothesis.
Granting it:

* `FiniteChains.SquareComplex.wallSpaceOf` — the vertices, with the walls, form a
  `FiniteChains.WallSpace`;
* `FiniteChains.SquareComplex.wallSpaceOf_coord_injective` — the vertices embed into the
  median dual complex;
* `FiniteChains.SquareComplex.wallSpaceOf_dsym_adj` — an edge of the complex becomes an edge
  of the dual: the halfspace coordinates of its endpoints differ in exactly one wall.

Thus, granting separation, the one-skeleton of such a complex maps injectively and
edge-preservingly into a median (CAT(0) cube complex) graph.
-/

namespace FiniteChains

open RollerBridge

universe u

namespace SquareComplex

variable {Vx : Type u}

section WallSpace

variable {ι : Type*} {σ : ι → Vx → ZMod 2} {x₀ : Vx}

theorem decide_ne_of_ne {a b : ZMod 2} (h : a ≠ b) : decide (a = 1) ≠ decide (b = 1) := by
  revert h; revert a b; decide

theorem ne_of_decide_ne {a b : ZMod 2} (h : decide (a = 1) ≠ decide (b = 1)) : a ≠ b := by
  revert h; revert a b; decide

/-- **The vertices of a square complex with separating walls form a wall space.**  The
coordinates `σ` are those produced by `FiniteChains.SquareComplex.exists_rollerCoordinates`;
`hsep` is the separation property, the one step of Sageev's theorem that is not proved in the
project. -/
def wallSpaceOf (hfin : ∀ v : Vx, {i : ι | σ i v ≠ σ i x₀}.Finite)
    (hsep : ∀ u v : Vx, u ≠ v → ∃ i, σ i u ≠ σ i v) : WallSpace Vx ι where
  side i v := decide (σ i v = 1)
  sep := by
    intro u v huv
    obtain ⟨i, hi⟩ := hsep u v huv
    exact ⟨i, decide_ne_of_ne hi⟩
  fin := by
    intro u v
    refine Set.Finite.subset (separating_finite hfin u v) ?_
    intro i hi
    exact ne_of_decide_ne hi

@[simp] theorem wallSpaceOf_side (hfin : ∀ v : Vx, {i : ι | σ i v ≠ σ i x₀}.Finite)
    (hsep : ∀ u v : Vx, u ≠ v → ∃ i, σ i u ≠ σ i v) (i : ι) (v : Vx) :
    (wallSpaceOf hfin hsep).side i v = decide (σ i v = 1) := rfl

/-- The vertices embed into the dual cube complex of the wall space. -/
theorem wallSpaceOf_coord_injective [DecidableEq ι]
    (hfin : ∀ v : Vx, {i : ι | σ i v ≠ σ i x₀}.Finite)
    (hsep : ∀ u v : Vx, u ≠ v → ∃ i, σ i u ≠ σ i v) (y₀ : Vx) :
    Function.Injective ((wallSpaceOf hfin hsep).coord y₀) :=
  WallSpace.coord_injective y₀

theorem mem_coord [DecidableEq ι] (hfin : ∀ v : Vx, {i : ι | σ i v ≠ σ i x₀}.Finite)
    (hsep : ∀ u v : Vx, u ≠ v → ∃ i, σ i u ≠ σ i v) (y₀ v : Vx) (i : ι) :
    i ∈ (wallSpaceOf hfin hsep).coord y₀ v ↔ σ i v ≠ σ i y₀ := by
  simp only [WallSpace.coord, Set.Finite.mem_toFinset, Set.mem_setOf_eq, wallSpaceOf_side]
  exact ⟨ne_of_decide_ne, decide_ne_of_ne⟩

/-- A `ZMod 2` computation: two coordinates differ exactly when exactly one of them differs
from a third one. -/
theorem zmod2_sep_iff {a b c : ZMod 2} : ((a ≠ c) ↔ ¬(b ≠ c)) ↔ a ≠ b := by
  revert a b c; decide

/-- **An edge of the complex is an edge of the dual**: if exactly one wall separates two
vertices, their halfspace coordinates differ in exactly one wall, i.e. they are adjacent in
the graph of the dual cube complex. -/
theorem wallSpaceOf_dsym_adj [DecidableEq ι]
    (hfin : ∀ v : Vx, {i : ι | σ i v ≠ σ i x₀}.Finite)
    (hsep : ∀ u v : Vx, u ≠ v → ∃ i, σ i u ≠ σ i v) (y₀ : Vx) {u v : Vx} {j : ι}
    (hj : {i : ι | σ i u ≠ σ i v} = {j}) :
    dsym ((wallSpaceOf hfin hsep).coord y₀ u) ((wallSpaceOf hfin hsep).coord y₀ v) = 1 := by
  classical
  set A := (wallSpaceOf hfin hsep).coord y₀ u with hA
  set B := (wallSpaceOf hfin hsep).coord y₀ v with hB
  have hmem : ∀ i : ι, (i ∈ A ↔ i ∉ B) ↔ σ i u ≠ σ i v := by
    intro i
    rw [hA, hB]
    simp only [mem_coord]
    exact zmod2_sep_iff
  have hsing : ∀ i : ι, σ i u ≠ σ i v ↔ i = j := by
    intro i
    constructor
    · intro hi
      have : i ∈ ({j} : Set ι) := by rw [← hj]; exact hi
      simpa using this
    · intro hij
      have hmemj : i ∈ ({j} : Set ι) := by simp [hij]
      rw [← hj] at hmemj
      exact hmemj
  have hAB : A \ B ∪ B \ A = {j} := by
    ext i
    simp only [Finset.mem_union, Finset.mem_sdiff, Finset.mem_singleton]
    rw [← hsing i, ← hmem i]
    by_cases hiA : i ∈ A <;> by_cases hiB : i ∈ B <;> simp [hiA, hiB]
  have hdisj : Disjoint (A \ B) (B \ A) := by
    refine Finset.disjoint_left.2 ?_
    intro i hi hi'
    exact (Finset.mem_sdiff.1 hi').2 (Finset.mem_sdiff.1 hi).1
  have hcard : (A \ B).card + (B \ A).card = 1 := by
    rw [← Finset.card_union_of_disjoint hdisj, hAB, Finset.card_singleton]
  simpa [dsym] using hcard

end WallSpace

end SquareComplex

end FiniteChains
