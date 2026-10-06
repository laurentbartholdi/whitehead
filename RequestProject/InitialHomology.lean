import Mathlib

/-!
# The homological computation in Lemma 3.1

The proof of Lemma 3.1 (the initial Cockcroft pair `D ⊂ Y_D`) has two halves.  Its group
half — the elimination `U_i = [a_i, b_i] = 1` — is proved in
`RequestProject/InitialPair.lean`.  Its homological half runs as follows.

After the elimination every remaining relator has zero exponent sums, so `H₂(Y_D)` is free
on the entries `r_j(U)` (`j ∈ J`) and on the cross-commutators (an index set `C`).  Mapping
the reduced presentation to the torus `𝒯` on the circles `a_i, b_i` sends, on `H₂`,

  `[r_j(U)] ↦ ∑_i M_{ij} · [(a_i,b_i)-square]`,

while each cross-commutator class goes to its own square.  "A class in the kernel therefore
has zero cross-commutator coefficients, and its remaining coefficient vector `λ` satisfies
`M λ = 0`.  Hence it is zero."  Since `π₂(𝒯) = 0`, naturality of the Hurewicz map then makes
`Y_D` Cockcroft.

This file formalizes that computation: the map induced on second homology is injective as
soon as the exponent-sum map `M` of the acyclic core is injective
(`initialH2Map_injective`), and the resulting diagram chase which kills the Hurewicz map
(`hurewicz_eq_zero_of_injective`).  What is *not* formalized here is the identification of
`H₂` with these free modules, the construction of the map to the torus, and the vanishing
`π₂(𝒯) = 0`; those are the topological inputs of the lemma.
-/

namespace FiniteChains

variable {I J C : Type*}

/-- The map induced on second homology by the comparison with the torus: the class of the
`j`-th relator goes to the `j`-th column of the exponent-sum matrix `M`, and the class of a
cross-commutator goes to its own square. -/
noncomputable def initialH2Map (M : (J →₀ ℤ) →ₗ[ℤ] (I →₀ ℤ)) :
    ((J →₀ ℤ) × (C →₀ ℤ)) →ₗ[ℤ] ((I →₀ ℤ) × (C →₀ ℤ)) :=
  M.prodMap LinearMap.id

@[simp] theorem initialH2Map_apply (M : (J →₀ ℤ) →ₗ[ℤ] (I →₀ ℤ)) (x : (J →₀ ℤ) × (C →₀ ℤ)) :
    initialH2Map (C := C) M x = (M x.1, x.2) := rfl

/-- **The kernel computation of Lemma 3.1.**  If the exponent-sum map of the core is
injective — for an acyclic core it is even bijective — then the comparison map to the second
homology of the torus is injective: a class in its kernel has zero cross-commutator
coefficients and a relator vector `λ` with `M λ = 0`, hence vanishes. -/
theorem initialH2Map_injective (M : (J →₀ ℤ) →ₗ[ℤ] (I →₀ ℤ)) (hM : Function.Injective M) :
    Function.Injective (initialH2Map (C := C) M) := by
  rintro ⟨x₁, x₂⟩ ⟨y₁, y₂⟩ hxy
  simp only [initialH2Map_apply, Prod.mk.injEq] at hxy
  rw [hM hxy.1, hxy.2]

/-- The same statement as the vanishing of the kernel. -/
theorem initialH2Map_ker (M : (J →₀ ℤ) →ₗ[ℤ] (I →₀ ℤ)) (hM : Function.Injective M) :
    LinearMap.ker (initialH2Map (C := C) M) = ⊥ :=
  LinearMap.ker_eq_bot_of_injective (initialH2Map_injective M hM)

/-- **The Cockcroft conclusion.**  Suppose the Hurewicz map `h` of `Y_D` becomes zero after
composing with the map `f` induced on `H₂` by the comparison with the torus — which holds by
naturality of Hurewicz, because `π₂(𝒯) = 0` — and suppose `f` is injective, as proved in
`initialH2Map_injective`.  Then `h` itself is zero, i.e. the complex is Cockcroft. -/
theorem hurewicz_eq_zero_of_injective {P A B : Type*} [AddCommGroup A] [AddCommGroup B]
    (h : P → A) (f : A →+ B) (hf : Function.Injective f) (hcomp : ∀ x : P, f (h x) = 0) :
    ∀ x : P, h x = 0 := by
  intro x
  exact hf (by rw [hcomp x, map_zero])

end FiniteChains
