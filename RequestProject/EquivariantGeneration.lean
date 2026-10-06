import Mathlib

/-!
# The equivariance arguments of Lemmas 3.9, 3.10 and Proposition 3.11

Three of the remaining steps of Section 3 are, once the topological input is granted,
purely module-theoretic statements about the `ℤ[G]`-module `π₂`.  They are used in the
paper in the following places.

* Lemma 3.9 (the structural operation `T`) ends with: "Generation (3.3) and equivariance
  imply `T(j)_* = 0` on the entire second homotopy group."  Here (3.3) says that `π₂(T(P))`
  is generated, as a module over the group ring of `G(T(P))`, by the image of `π₂(P)`.
* The same lemma derives Cockcroftness of `T(P)` from Cockcroftness of `P`: "Hurewicz kills
  each structural image, by naturality, and each translate, since the fundamental-group
  action becomes trivial in ordinary homology."
* Proposition 3.11 repeats the argument downstairs: "The upper arrow is zero on `π₂` and its
  images generate the lower source by (3.5).  Hence every lower arrow is zero on the whole
  of `π₂`."
* Lemma 3.10 needs that a wedge of Cockcroft complexes is Cockcroft: "its `H₂` is the direct
  sum of those of the factors, and the factor retractions detect every coordinate of a
  Hurewicz image."

All four are instances of two elementary facts, proved here: an equivariant map that
vanishes on a generating set of a module vanishes identically, and a map into a direct sum
all of whose coordinates vanish is zero.  The topological content — the identification of
`π₂` and the generation statements themselves — is not formalized.
-/

namespace FiniteChains

section Generation

variable {R M N : Type*} [Ring R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]

/-- **An equivariant map vanishing on a generating set vanishes.**  Over the group ring `R`
of the fundamental group, a map of `π₂`'s which is zero on a set of module generators is
zero. -/
theorem map_eq_zero_of_span_eq_top (f : M →ₗ[R] N) (S : Set M) (hS : Submodule.span R S = ⊤)
    (h0 : ∀ x ∈ S, f x = 0) (x : M) : f x = 0 := by
  have hker : Submodule.span R S ≤ LinearMap.ker f :=
    Submodule.span_le.mpr fun y hy => LinearMap.mem_ker.mpr (h0 y hy)
  rw [hS] at hker
  exact LinearMap.mem_ker.mp (hker Submodule.mem_top)

/-- The form in which the paper uses the previous statement: `M` (the second homotopy group
of the enlarged complex) is generated over the group ring by the image of a map `g` (the
structural map, or the map induced by `L_i ⊂ E_i`), and `f` (the map induced by the
inclusion, or the Hurewicz map) vanishes on that image. -/
theorem map_eq_zero_of_generated_by_image {P : Type*} (f : M →ₗ[R] N) (g : P → M)
    (hgen : Submodule.span R (Set.range g) = ⊤) (h0 : ∀ p, f (g p) = 0) (x : M) : f x = 0 :=
  map_eq_zero_of_span_eq_top f (Set.range g) hgen (by rintro _ ⟨p, rfl⟩; exact h0 p) x

/-- The composite version used for the inclusions of the chain: if `f ∘ g = 0` and the image
of `g` generates, then `f = 0`. -/
theorem linearMap_eq_zero_of_generated_by_image {P : Type*} [AddCommGroup P] [Module R P]
    (f : M →ₗ[R] N) (g : P →ₗ[R] M) (hgen : Submodule.span R (Set.range g) = ⊤)
    (h0 : f.comp g = 0) : f = 0 := by
  ext x
  refine map_eq_zero_of_generated_by_image f g hgen (fun p => ?_) x
  have := congrArg (fun h : P →ₗ[R] N => h p) h0
  simpa using this

end Generation

section Wedge

variable {ι : Type*} {P : Type*} {A : ι → Type*} [∀ i, AddCommGroup (A i)]

/-- **A wedge of Cockcroft complexes is Cockcroft.**  If the second homology of the wedge is
the direct sum of the second homologies of the factors and every factor retraction kills the
Hurewicz image, then the Hurewicz map of the wedge is zero. -/
theorem eq_zero_of_component_eq_zero (h : P → DirectSum ι A)
    (hproj : ∀ (i : ι) (x : P), (h x) i = 0) (x : P) : h x = 0 := by
  ext i
  simpa using hproj i x

end Wedge

section Cockcroft

variable {P Q A B : Type*} [AddCommGroup P] [AddCommGroup Q] [AddCommGroup A] [AddCommGroup B]

/-- **A map from a Cockcroft complex that kills its fundamental group is zero on `π₂`**
(Lemma 3.10).  The map lifts to the simply connected cover of the target, where Hurewicz is
an isomorphism; so in the commuting square formed by the two Hurewicz maps, the right-hand
vertical map `hQ` is injective, while the left-hand one `hP` is zero by Cockcroftness.  Hence
the induced map on `π₂` is zero. -/
theorem map_eq_zero_of_cockcroft_of_injective_hurewicz (f₂ : P →+ Q) (hP : P →+ A) (hQ : Q →+ B)
    (g : A →+ B) (hsq : ∀ x, hQ (f₂ x) = g (hP x)) (hcock : ∀ x, hP x = 0)
    (hinj : Function.Injective hQ) (x : P) : f₂ x = 0 := by
  refine hinj ?_
  rw [hsq x, hcock x, map_zero, map_zero]

end Cockcroft

end FiniteChains
