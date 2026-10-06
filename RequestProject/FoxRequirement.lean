module

public import RequestProject.SubgroupCompactness

@[expose] public section

/-!
# The requirements of Section 2 are finitely determined

Section 2 uses that each requirement (2.2)

  `∂_{2,M}(v_M) = 0  ⟹  v_M = 0`

"depends on finitely many decisions `g ∈ M`: reduction merely adds coefficients
within cosets, whose equalities are membership tests".  This file makes that
statement precise and proves it, so that the compactness step
`exists_normal_subgroup_forall` may be applied to the Fox requirements.

A coefficient vector is an element of the group ring `ℤ[G]`, and the reduction
of `x ∈ ℤ[G]` to `ℤ[G/N]` vanishes exactly when, for every `g`, the
coefficients of `x` inside the coset `Ng` add up to zero; this is
`VanishesMod`.  The requirement attached to a finitely supported vector `v` and
a boundary matrix `b` is `FoxSat`.
-/

namespace FiniteChains

open Finset

variable {G : Type*} [Group G]

open scoped Classical in
/-- The reduction of `x ∈ ℤ[G]` to `ℤ[G/N]` is zero: inside every coset of `N` the
coefficients of `x` add up to zero. -/
def VanishesMod (N : Subgroup G) (x : G →₀ ℤ) : Prop :=
  ∀ g : G, ∑ h ∈ x.support.filter (fun h => h * g⁻¹ ∈ N), x h = 0

@[simp] theorem vanishesMod_zero (N : Subgroup G) : VanishesMod N (0 : G →₀ ℤ) := by
  intro g; simp

/-- Whether the reduction of `x` vanishes only depends on the membership in `N` of the
finitely many quotients `h h'⁻¹` of elements of the support of `x`. -/
theorem vanishesMod_congr {x : G →₀ ℤ} {N N' : Subgroup G}
    (h : ∀ g ∈ x.support, ∀ g' ∈ x.support, (g * g'⁻¹ ∈ N ↔ g * g'⁻¹ ∈ N')) :
    VanishesMod N x ↔ VanishesMod N' x := by
  classical
  have main : ∀ M M' : Subgroup G,
      (∀ g ∈ x.support, ∀ g' ∈ x.support, (g * g'⁻¹ ∈ M ↔ g * g'⁻¹ ∈ M')) →
      VanishesMod M x → VanishesMod M' x := by
    intro M M' hMM' hM g
    by_cases hempty : (x.support.filter (fun h => h * g⁻¹ ∈ M')).Nonempty
    · obtain ⟨h₀, hh₀⟩ := hempty
      rw [mem_filter] at hh₀
      obtain ⟨hh₀supp, hh₀mem⟩ := hh₀
      have hfilter : x.support.filter (fun h => h * g⁻¹ ∈ M')
          = x.support.filter (fun h => h * h₀⁻¹ ∈ M) := by
        refine filter_congr fun h hh => ?_
        constructor
        · intro hmem
          have : h * h₀⁻¹ ∈ M' := by
            have : h * h₀⁻¹ = (h * g⁻¹) * (h₀ * g⁻¹)⁻¹ := by group
            rw [this]
            exact M'.mul_mem hmem (M'.inv_mem hh₀mem)
          exact (hMM' h hh h₀ hh₀supp).mpr this
        · intro hmem
          have hM' : h * h₀⁻¹ ∈ M' := (hMM' h hh h₀ hh₀supp).mp hmem
          have : h * g⁻¹ = (h * h₀⁻¹) * (h₀ * g⁻¹) := by group
          rw [this]
          exact M'.mul_mem hM' hh₀mem
      rw [hfilter]
      exact hM h₀
    · rw [Finset.not_nonempty_iff_eq_empty] at hempty
      rw [hempty, Finset.sum_empty]
  exact ⟨main N N' h, main N' N fun g hg g' hg' => (h g hg g' hg').symm⟩

variable {I J : Type*}

/-- The `i`-th coordinate of the Fox boundary of the coefficient vector `v`, with respect
to the boundary data `b i j = ∂r_j/∂x_i` read in the group ring. -/
noncomputable def foxBoundary (b : I → J → MonoidAlgebra ℤ G)
    (v : J →₀ MonoidAlgebra ℤ G) (i : I) : MonoidAlgebra ℤ G :=
  ∑ j ∈ v.support, v j * b i j

/-- The requirement (2.2) attached to the coefficient vector `v`: if the reduced boundary
of `v` vanishes, then the reduced `v` vanishes. -/
def FoxSat (b : I → J → MonoidAlgebra ℤ G) (v : J →₀ MonoidAlgebra ℤ G)
    (N : Subgroup G) : Prop :=
  (∀ i : I, VanishesMod N (foxBoundary b v i).coeff) → ∀ j : J, VanishesMod N (v j).coeff

/-- **Each requirement depends on finitely many membership decisions.**  If the boundary of
`v` has only finitely many nonzero coordinates — as happens for a presentation, every
relator being a finite word — then the requirement attached to `v` is determined by the
membership in `N` of the elements of one finite subset of `G`. -/
theorem foxSat_finitelyDetermined (b : I → J → MonoidAlgebra ℤ G)
    (v : J →₀ MonoidAlgebra ℤ G) (hfin : {i : I | foxBoundary b v i ≠ 0}.Finite) :
    ∃ F : Finset G, ∀ N N' : Subgroup G,
      (∀ g ∈ F, (g ∈ N ↔ g ∈ N')) → (FoxSat b v N ↔ FoxSat b v N') := by
  classical
  -- all group elements occurring in `v` or in its boundary
  set S : Finset G :=
    (v.support.biUnion fun j => (v j).coeff.support) ∪
      (hfin.toFinset.biUnion fun i => (foxBoundary b v i).coeff.support) with hS
  refine ⟨(S ×ˢ S).image (fun p => p.1 * p.2⁻¹), ?_⟩
  intro N N' hagree
  have hpair : ∀ g ∈ S, ∀ g' ∈ S, (g * g'⁻¹ ∈ N ↔ g * g'⁻¹ ∈ N') := by
    intro g hg g' hg'
    exact hagree _ (Finset.mem_image.mpr ⟨(g, g'), Finset.mem_product.mpr ⟨hg, hg'⟩, rfl⟩)
  -- the coordinates of `v` and of its boundary have support inside `S`
  have hvsupp : ∀ j : J, (v j).coeff.support ⊆ S := by
    intro j g hg
    by_cases hj : j ∈ v.support
    · exact Finset.mem_union_left _ (Finset.mem_biUnion.mpr ⟨j, hj, hg⟩)
    · rw [Finsupp.notMem_support_iff.mp hj] at hg
      simp at hg
  have hbsupp : ∀ i : I, (foxBoundary b v i).coeff.support ⊆ S := by
    intro i g hg
    by_cases hi : foxBoundary b v i = 0
    · rw [hi] at hg; simp at hg
    · refine Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨i, ?_, hg⟩)
      simpa [Set.Finite.mem_toFinset] using hi
  have hv : ∀ j : J, (VanishesMod N (v j).coeff ↔ VanishesMod N' (v j).coeff) := fun j =>
    vanishesMod_congr fun g hg g' hg' => hpair g (hvsupp j hg) g' (hvsupp j hg')
  have hb : ∀ i : I, (VanishesMod N (foxBoundary b v i).coeff ↔ VanishesMod N' (foxBoundary b v i).coeff) :=
    fun i => vanishesMod_congr fun g hg g' hg' => hpair g (hbsupp i hg) g' (hbsupp i hg')
  constructor
  · intro hSat hbdry j
    exact (hv j).mp (hSat (fun i => (hb i).mpr (hbdry i)) j)
  · intro hSat hbdry j
    exact (hv j).mpr (hSat (fun i => (hb i).mp (hbdry i)) j)

end FiniteChains
