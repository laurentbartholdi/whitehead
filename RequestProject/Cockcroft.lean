module

public import RequestProject.PresentationDictionary
public import RequestProject.CoverChainComplex

@[expose] public section

/-!
# The Cockcroft property of a presentation complex

For the two-complex `K` of a finite presentation `⟨x_i (i ∈ α) | r_j (j ∈ J)⟩` the module
`π₂(K)` is the module of Fox cycles

  `{v ∈ ℤ[G]^J : ∑_j v_j · ∂r_j/∂x_i = 0 for every i}`,   `G = π₁(K)`,

(see `RequestProject/UniversalCoverPi2.lean`), and the Hurewicz map `π₂(K) → H₂(K)` is
induced by the augmentation `ℤ[G] → ℤ`, since `H₂(K)` is the kernel of the exponent-sum
matrix `M` acting on `ℤ^J`.  Hence *Cockcroft* — "the Hurewicz map of `K` is zero" — reads,
in the combinatorial model:

  every Fox cycle has zero augmentation   (`FiniteChains.IsCockcroft`).

This file sets up that definition and proves the first instance of it used in Section 3:
an **acyclic** presentation complex is Cockcroft (`FiniteChains.isCockcroft_of_expInjective`),
because the augmentation of a Fox cycle is a vector killed by the exponent-sum matrix.
-/

namespace FiniteChains

open MonoidAlgebra

variable {α : Type*} [Fintype α] [DecidableEq α] {J : Type*} [Fintype J] (ρ : J → FreeGroup α)

/-- The augmentation `ℤ[G] → ℤ` of the group ring of the presented group. -/
noncomputable abbrev augPres : MonoidAlgebra ℤ (PresGroup ρ) →+* ℤ := augQ (relSub ρ)

/-- The entries `M_{ij}` of the exponent-sum matrix of the presentation: the exponent sum of
`x_i` in the relator `r_j`. -/
noncomputable def expEntry (i : α) (j : J) : ℤ := Multiplicative.toAdd (expSum i (ρ j))

omit [Fintype α] [Fintype J] in
/-- Augmenting the Fox matrix gives the exponent-sum matrix. -/
theorem augPres_foxMatrixPres (i : α) (j : J) :
    augPres ρ (foxMatrixPres ρ i j) = expEntry ρ i j := by
  have h : foxMatrixPres ρ i j = proj (relSub ρ) (fox i (ρ j)) := rfl
  rw [h, augQ_proj, aug_fox, expEntry]

/-- A **Fox cycle**: an element of `π₂` of the presentation complex, in the coordinates of
`RequestProject/UniversalCoverPi2.lean`. -/
def IsFoxCycle (v : J → MonoidAlgebra ℤ (PresGroup ρ)) : Prop :=
  ∀ i : α, ∑ j, v j * foxMatrixPres ρ i j = 0

/-- **The Cockcroft property.**  The Hurewicz map of the presentation complex is zero: every
Fox cycle (i.e. every element of `π₂`) has zero augmentation in every coordinate. -/
def IsCockcroft : Prop :=
  ∀ v : J → MonoidAlgebra ℤ (PresGroup ρ), IsFoxCycle ρ v → ∀ j, augPres ρ (v j) = 0

/-- The exponent-sum matrix of the presentation is injective on integer vectors.  For a
finite presentation complex this says exactly that `H₂` of the complex vanishes; for an
*acyclic* complex the matrix is even bijective. -/
def ExpInjective : Prop :=
  ∀ c : J → ℤ, (∀ i : α, ∑ j, c j * expEntry ρ i j = 0) → ∀ j, c j = 0

omit [Fintype α] in
/-- The augmentation of a Fox cycle is killed by the exponent-sum matrix: this is the
statement that the Hurewicz image of `π₂` lands in `H₂ = ker M`. -/
theorem expEntry_augPres_eq_zero {v : J → MonoidAlgebra ℤ (PresGroup ρ)}
    (hv : IsFoxCycle ρ v) (i : α) :
    ∑ j, augPres ρ (v j) * expEntry ρ i j = 0 := by
  have h := congrArg (augPres ρ) (hv i)
  rw [map_sum, map_zero] at h
  rw [← h]
  exact Finset.sum_congr rfl fun j _ => by rw [map_mul, augPres_foxMatrixPres]

omit [Fintype α] in
/-- **An acyclic presentation complex is Cockcroft.**  If the exponent-sum matrix is
injective — which holds for an acyclic complex, where it is an isomorphism — then the
augmentation of every Fox cycle vanishes. -/
theorem isCockcroft_of_expInjective (hM : ExpInjective ρ) : IsCockcroft ρ := by
  intro v hv j
  exact hM (fun j => augPres ρ (v j)) (fun i => expEntry_augPres_eq_zero ρ hv i) j

end FiniteChains
