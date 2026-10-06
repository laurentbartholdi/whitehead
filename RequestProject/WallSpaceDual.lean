import RequestProject.CubeRollerModel

/-!
# Wall spaces and their dual cube complex

`RequestProject/SquareComplexWalls.lean` produces, out of a simply connected square complex,
a system of walls and the associated halfspace (Roller) coordinates of its vertices.  What is
still missing there is the *median-closedness* of the resulting set of coordinates, i.e. the
fact that the coordinates describe a CAT(0) cube complex.

This file proves that median-closedness for the **dual** object, which is Sageev's
construction: starting from a *wall space* — a set `X` together with a family of two-sided
partitions of `X` (walls), such that distinct points are separated by a wall and any two
points are separated by only finitely many walls — one forms the set of *consistent
orientations* of the walls (choices of one side of each wall, any two of which meet inside
`X`) that differ from a base point in finitely many walls.  The main results are:

* `FiniteChains.WallSpace.Consistent.maj` — consistency is preserved by the majority
  (median) operation;
* `FiniteChains.WallSpace.dualW_medFinset_mem` — in the halfspace coordinates based at a
  point `x₀`, the dual vertex set is closed under `FiniteChains.medFinset`;
* `FiniteChains.WallSpace.dualModel` — hence, once the dimension is at most three, the dual
  is a `FiniteChains.RollerModel`, so
  `FiniteChains.WallSpace.dual_ker_d₂_eq_range_d₃`: `ker d₂ = im d₃` for its cellular chain
  complex;
* `FiniteChains.WallSpace.coord_injective` — the points of `X` embed in the dual.

Nothing here is assumed finite or locally finite: `X` and the index type of walls are
arbitrary.
-/

namespace FiniteChains

universe u v

/-- The majority vote of three booleans. -/
def maj3 (a b c : Bool) : Bool := (a && b) || (b && c) || (a && c)

@[simp] theorem maj3_self (a : Bool) : maj3 a a a = a := by cases a <;> rfl

/-- The majority of three booleans agrees with at least two of them; hence for two triples
there is a common index at which both majorities are attained. -/
theorem maj3_common (a₁ a₂ a₃ b₁ b₂ b₃ : Bool) :
    (maj3 a₁ a₂ a₃ = a₁ ∧ maj3 b₁ b₂ b₃ = b₁) ∨ (maj3 a₁ a₂ a₃ = a₂ ∧ maj3 b₁ b₂ b₃ = b₂) ∨
      (maj3 a₁ a₂ a₃ = a₃ ∧ maj3 b₁ b₂ b₃ = b₃) := by
  revert a₁ a₂ a₃ b₁ b₂ b₃; decide

/-- If the majority of three booleans differs from `d`, then one of the three differs
from `d`. -/
theorem maj3_ne (a b c d : Bool) (h : maj3 a b c ≠ d) : a ≠ d ∨ b ≠ d ∨ c ≠ d := by
  revert h; revert a b c d; decide

/-- A **wall space**: a family of walls on `X`, each wall `i` splitting `X` into the two
sides `side i x = true` and `side i x = false`; distinct points are separated by some wall,
and any two points are separated by only finitely many walls. -/
structure WallSpace (X : Type u) (ι : Type v) where
  /-- The side of the wall `i` on which the point `x` lies. -/
  side : ι → X → Bool
  /-- Distinct points are separated by a wall. -/
  sep : ∀ {x y : X}, x ≠ y → ∃ i, side i x ≠ side i y
  /-- Only finitely many walls separate two given points. -/
  fin : ∀ x y : X, {i | side i x ≠ side i y}.Finite

namespace WallSpace

variable {X : Type u} {ι : Type v} (S : WallSpace X ι)

/-- A **consistent orientation** of the walls: a choice `o i` of a side of each wall `i`,
such that any two of the chosen halfspaces meet, i.e. for all `i, j` some point of `X` lies
on the chosen side of both. -/
def Consistent (o : ι → Bool) : Prop := ∀ i j, ∃ x : X, S.side i x = o i ∧ S.side j x = o j

variable {S}

/-- The orientation determined by a point of `X` is consistent: the point itself lies on the
chosen side of every wall. -/
theorem consistent_side (x : X) : S.Consistent (fun i => S.side i x) := fun _ _ => ⟨x, rfl, rfl⟩

/-- **Consistency is preserved by the majority operation.**  This is the combinatorial heart
of Sageev's construction: the dual of a wall space is a median object. -/
theorem Consistent.maj {o₁ o₂ o₃ : ι → Bool} (h₁ : S.Consistent o₁) (h₂ : S.Consistent o₂)
    (h₃ : S.Consistent o₃) : S.Consistent (fun i => maj3 (o₁ i) (o₂ i) (o₃ i)) := by
  intro i j
  rcases maj3_common (o₁ i) (o₂ i) (o₃ i) (o₁ j) (o₂ j) (o₃ j) with
    ⟨hi, hj⟩ | ⟨hi, hj⟩ | ⟨hi, hj⟩
  · obtain ⟨x, hx₁, hx₂⟩ := h₁ i j
    exact ⟨x, by simpa [hi] using hx₁, by simpa [hj] using hx₂⟩
  · obtain ⟨x, hx₁, hx₂⟩ := h₂ i j
    exact ⟨x, by simpa [hi] using hx₁, by simpa [hj] using hx₂⟩
  · obtain ⟨x, hx₁, hx₂⟩ := h₃ i j
    exact ⟨x, by simpa [hi] using hx₁, by simpa [hj] using hx₂⟩

variable (S)

/-- The **dual** of a wall space based at `x₀`: the consistent orientations differing from
the orientation of `x₀` in finitely many walls.  These are the vertices of the cube complex
dual to the wall space. -/
def Dual (x₀ : X) : Set (ι → Bool) :=
  {o | S.Consistent o ∧ {i | o i ≠ S.side i x₀}.Finite}

variable {S}

/-- Every point of `X` is a vertex of the dual. -/
theorem side_mem_dual (x x₀ : X) : (fun i => S.side i x) ∈ S.Dual x₀ :=
  ⟨consistent_side x, S.fin x x₀⟩

/-- The base point is a vertex of the dual. -/
theorem base_mem_dual (x₀ : X) : (fun i => S.side i x₀) ∈ S.Dual x₀ := side_mem_dual x₀ x₀

/-- **The dual of a wall space is closed under the median (majority) operation.** -/
theorem Dual.maj_mem {x₀ : X} {o₁ o₂ o₃ : ι → Bool} (h₁ : o₁ ∈ S.Dual x₀) (h₂ : o₂ ∈ S.Dual x₀)
    (h₃ : o₃ ∈ S.Dual x₀) : (fun i => maj3 (o₁ i) (o₂ i) (o₃ i)) ∈ S.Dual x₀ := by
  refine ⟨h₁.1.maj h₂.1 h₃.1, ?_⟩
  refine ((h₁.2.union h₂.2).union h₃.2).subset ?_
  intro i hi
  have := maj3_ne (o₁ i) (o₂ i) (o₃ i) (S.side i x₀) hi
  simpa [Set.mem_union, or_assoc] using this

/-! ## Halfspace coordinates

Recording a dual vertex by the set of walls on which it differs from the base point turns the
dual into the shape required by `FiniteChains.RollerModel`.
-/

section Coordinates

variable [DecidableEq ι]

variable (S) in
/-- The orientation obtained from the base orientation of `x₀` by flipping the walls in `A`. -/
def flipOn (x₀ : X) (A : Finset ι) : ι → Bool :=
  fun i => if i ∈ A then !S.side i x₀ else S.side i x₀

@[simp] theorem flipOn_empty (x₀ : X) : S.flipOn x₀ (∅ : Finset ι) = fun i => S.side i x₀ := by
  funext i; simp [flipOn]

variable (S) in
/-- The vertex set of the dual in halfspace coordinates based at `x₀`: the finite sets `A` of
walls for which flipping the base orientation along `A` is still consistent. -/
def dualW (x₀ : X) : Set (Finset ι) := {A : Finset ι | S.Consistent (S.flipOn x₀ A)}

theorem mem_dualW {x₀ : X} {A : Finset ι} :
    A ∈ S.dualW x₀ ↔ S.Consistent (S.flipOn x₀ A) := Iff.rfl

/-- The coordinates really parametrise the dual: `A ↦ flipOn x₀ A` is a bijection from
`dualW x₀` onto `Dual x₀`, in particular it lands in the dual. -/
theorem flipOn_mem_dual {x₀ : X} {A : Finset ι} (hA : A ∈ S.dualW x₀) :
    S.flipOn x₀ A ∈ S.Dual x₀ := by
  refine ⟨hA, Set.Finite.subset A.finite_toSet ?_⟩
  intro i hi
  by_contra hiA
  simp [flipOn, hiA] at hi

/-- Distinct coordinates give distinct orientations. -/
theorem flipOn_injective (x₀ : X) : Function.Injective (S.flipOn x₀) := by
  intro A B h
  ext i
  have hi := congrFun h i
  simp only [flipOn] at hi
  constructor
  · intro hA
    by_contra hB
    rw [if_pos hA, if_neg hB] at hi
    simp at hi
  · intro hB
    by_contra hA
    rw [if_neg hA, if_pos hB] at hi
    simp at hi

/-- The base vertex has empty coordinate set. -/
theorem empty_mem_dualW (x₀ : X) : (∅ : Finset ι) ∈ S.dualW x₀ := by
  rw [mem_dualW, flipOn_empty]
  exact consistent_side x₀

/-- Flipping along the majority of three coordinate sets is the majority of the three
orientations. -/
theorem flipOn_medFinset (x₀ : X) (A B C : Finset ι) :
    S.flipOn x₀ (medFinset A B C) =
      fun i => maj3 (S.flipOn x₀ A i) (S.flipOn x₀ B i) (S.flipOn x₀ C i) := by
  funext i
  by_cases hA : i ∈ A <;> by_cases hB : i ∈ B <;> by_cases hC : i ∈ C <;>
    simp [flipOn, medFinset, maj3, hA, hB, hC]

/-- **The dual vertex set, in halfspace coordinates, is closed under `medFinset`.** -/
theorem dualW_medFinset_mem {x₀ : X} {A B C : Finset ι} (hA : A ∈ S.dualW x₀)
    (hB : B ∈ S.dualW x₀) (hC : C ∈ S.dualW x₀) : medFinset A B C ∈ S.dualW x₀ := by
  rw [mem_dualW, flipOn_medFinset]
  exact hA.maj hB hC

variable (S) in
/-- The halfspace coordinates of a point of `X`: the (finite) set of walls separating it from
the base point. -/
noncomputable def coord (x₀ x : X) : Finset ι := (S.fin x x₀).toFinset

theorem flipOn_coord (x₀ x : X) : S.flipOn x₀ (S.coord x₀ x) = fun i => S.side i x := by
  funext i
  by_cases h : S.side i x = S.side i x₀
  · simp [flipOn, coord, Set.Finite.mem_toFinset, h]
  · simp only [flipOn, coord, Set.Finite.mem_toFinset, Set.mem_setOf_eq, if_pos h]
    cases hb : S.side i x <;> simp_all

/-- Points of `X` are vertices of the dual. -/
theorem coord_mem_dualW (x₀ x : X) : S.coord x₀ x ∈ S.dualW x₀ := by
  rw [mem_dualW, flipOn_coord]
  exact consistent_side x

/-- **The points of `X` embed into the dual**: distinct points have distinct halfspace
coordinates.  This uses the separation axiom of a wall space. -/
theorem coord_injective (x₀ : X) : Function.Injective (S.coord x₀) := by
  intro x y h
  by_contra hxy
  obtain ⟨i, hi⟩ := S.sep hxy
  have h' : S.flipOn x₀ (S.coord x₀ x) = S.flipOn x₀ (S.coord x₀ y) := by rw [h]
  rw [flipOn_coord, flipOn_coord] at h'
  exact hi (congrFun h' i)

@[simp] theorem coord_self (x₀ : X) : S.coord x₀ x₀ = (∅ : Finset ι) := by
  apply flipOn_injective x₀
  rw [flipOn_coord, flipOn_empty]

/-- If there are at most three walls altogether, the dimension bound of a Roller model is
automatic. -/
theorem dualW_dim_le [Fintype ι] (hcard : Fintype.card ι ≤ 3) (x₀ : X) :
    ∀ A ∈ S.dualW x₀, ∀ s : Finset (Finset ι),
      (∀ B ∈ s, B ∈ S.dualW x₀ ∧ B ⊆ A ∧ B.card + 1 = A.card) → s.card ≤ 3 := by
  intro A _ s hs
  have h : s.card ≤ A.card :=
    RollerModel.card_dn_le (fun B hB => ⟨(hs B hB).2.1, (hs B hB).2.2⟩)
  have hA : A.card ≤ Fintype.card ι := by simpa using Finset.card_le_univ A
  omega

variable (S) in
/-- **The dual cube complex of a wall space of dimension at most three is a Roller model.**
The median-closedness — the CAT(0) input — is proved; the dimension bound is the hypothesis
`hdim` (a vertex has at most three descending neighbours). -/
noncomputable def dualModel (x₀ : X)
    (hdim : ∀ A ∈ S.dualW x₀, ∀ s : Finset (Finset ι),
      (∀ B ∈ s, B ∈ S.dualW x₀ ∧ B ⊆ A ∧ B.card + 1 = A.card) → s.card ≤ 3) :
    RollerModel ι where
  W := S.dualW x₀
  base_mem := empty_mem_dualW x₀
  med_mem := dualW_medFinset_mem
  dim_le := hdim

/-- **Every two-cycle in the dual cube complex of an at most three-dimensional wall space
bounds**: `ker d₂ = im d₃`. -/
theorem dual_ker_d₂_eq_range_d₃ (x₀ : X)
    (hdim : ∀ A ∈ S.dualW x₀, ∀ s : Finset (Finset ι),
      (∀ B ∈ s, B ∈ S.dualW x₀ ∧ B ⊆ A ∧ B.card + 1 = A.card) → s.card ≤ 3) :
    LinearMap.ker (S.dualModel x₀ hdim).toDescCubeStr.d₂ =
      LinearMap.range (S.dualModel x₀ hdim).toDescCubeStr.d₃ :=
  (S.dualModel x₀ hdim).ker_d₂_eq_range_d₃

end Coordinates

end WallSpace

end FiniteChains
