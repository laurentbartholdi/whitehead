module

public import RequestProject.Cockcroft
public import RequestProject.FoxNaturality

@[expose] public section

/-!
# Adding one generator and one relator: no new elements of `π₂`

Rule 1 of the structural operation `T` of Section 3.3 replaces an extra generator `z` by a
commutator `[a_z,b_z]`.  The paper performs this in three steps: freely adjoin `b_z`, adjoin
`a_z` together with the relator `a_z b_z a_z^{-1} = z b_z` (an HNN extension along infinite
cyclic subgroups), and finally eliminate `z` by the defining relation.  What the paper needs
of these steps is the generation statement (3.3): the second homotopy group of the enlarged
complex is generated, over the group ring of the enlarged group, by the image of the old one.

This file proves the combinatorial heart of that statement for a one-generator,
one-relator extension of a presentation.  In the model of
`RequestProject/UniversalCoverPi2.lean`, `π₂` of a presentation complex is the module of Fox
cycles, and the result is:

* `FiniteChains.extCycle_new_eq_zero` — a Fox cycle of the extended presentation has
  coefficient `0` on the new two-cell, as soon as the Fox derivative of the new relator with
  respect to the new generator is right-regular in the group ring;
* `FiniteChains.extCycle_old` — consequently its remaining coefficients form a Fox cycle of
  the *old* Fox matrix, read in the group ring of the enlarged group.

The two cases used in the paper are covered by the two regularity criteria proved here:

* `FiniteChains.foxNew_tietze` — for a defining relator `z = s` the derivative is `1`
  (elimination of the pairs `z = [a_z,b_z]`, a Tietze transformation);
* `FiniteChains.foxNew_hnn` and `FiniteChains.mul_one_sub_single_eq_zero` — for a stable
  letter relator `z u z^{-1} = v` the derivative is `1 - v`, which is right-regular exactly
  by the argument that `v` has infinite order (the hypothesis of the HNN step).

Thus, in the combinatorial model, the two extension steps of rule 1 create no new elements
of `π₂` at all: every Fox cycle of the enlarged presentation is a Fox cycle of the old
presentation with coefficients in the bigger group ring.
-/

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains

open MonoidAlgebra

section Regular

variable {k G : Type*} [Ring k] [Group G]

/-- **`1 - t` is right-regular when `t` has infinite order.**  If `x (1 - t) = 0` then `x` is
invariant under right translation by `t`, so its support is a union of infinite `t`-orbits,
hence empty.  This is the algebraic form of the paper's remark that the associated elements
of the HNN extension have infinite order. -/
theorem mul_one_sub_single_eq_zero {t : G} (ht : ¬ IsOfFinOrder t)
    (x : MonoidAlgebra k G) (hx : x * (1 - single t 1) = 0) : x = 0 := by
  have hstep : ∀ h : G, x.coeff h = x.coeff (h * t⁻¹) := by
    intro h
    have hxt : x * single t (1 : k) = x := (sub_eq_zero.mp (by simpa [mul_sub] using hx)).symm
    have h2 := DFunLike.congr_fun (congrArg (fun f : MonoidAlgebra k G => f.coeff) hxt) h
    simpa [MonoidAlgebra.mul_single_apply] using h2.symm
  by_contra hne
  obtain ⟨g, hg⟩ : ∃ g, x.coeff g ≠ 0 := by
    by_contra hall
    push_neg at hall
    exact hne (MonoidAlgebra.coeff_injective (Finsupp.ext hall))
  have key : ∀ n : ℕ, x.coeff (g * (t ^ n)⁻¹) ≠ 0 := by
    intro n
    induction n with
    | zero => simpa using hg
    | succ m ih =>
        have hrw : g * (t ^ (m + 1))⁻¹ = g * (t ^ m)⁻¹ * t⁻¹ := by group
        rw [hrw, ← hstep (g * (t ^ m)⁻¹)]
        exact ih
  have hsub : Set.range (fun n : ℕ => g * (t ^ n)⁻¹) ⊆ (x.coeff.support : Set G) := by
    rintro _ ⟨n, rfl⟩
    exact Finsupp.mem_support_iff.mpr (key n)
  have hinj : Function.Injective (fun n : ℕ => g * (t ^ n)⁻¹) := by
    intro a b hab
    simp only [mul_right_inj, inv_inj] at hab
    exact injective_pow_iff_not_isOfFinOrder.mpr ht hab
  exact (Set.infinite_range_of_injective hinj) (Set.Finite.subset x.coeff.support.finite_toSet hsub)

/-- The trivial regularity criterion: multiplication by `1` is injective. -/
theorem mul_one_eq_zero {R : Type*} [Ring R] (x : R) (hx : x * 1 = 0) : x = 0 := by
  simpa using hx

end Regular

universe u

variable {α : Type u} [Fintype α] [DecidableEq α] {J : Type u} [Fintype J] [DecidableEq J]
variable (ρ : J → FreeGroup α) (w₀ : FreeGroup (Option α))

/-- The presentation obtained from `⟨x_i | r_j⟩` by adjoining one new generator (the element
`none`) and one new relator `w₀`. -/
def extRel : Option J → FreeGroup (Option α)
  | none => w₀
  | some j => FreeGroup.map Option.some (ρ j)

omit [Fintype α] [DecidableEq α] [Fintype J] [DecidableEq J] in
@[simp] theorem extRel_none : extRel ρ w₀ none = w₀ := rfl

omit [Fintype α] [DecidableEq α] [Fintype J] [DecidableEq J] in
@[simp] theorem extRel_some (j : J) :
    extRel ρ w₀ (some j) = FreeGroup.map Option.some (ρ j) := rfl

omit [Fintype α] [Fintype J] [DecidableEq J] in
/-- The old relators do not involve the new generator. -/
theorem foxMatrix_ext_none_some (j : J) : foxMatrixPres (extRel ρ w₀) none (some j) = 0 := by
  have h : @fox (Option α) _ none (extRel ρ w₀ (some j)) = 0 := by
    rw [extRel_some]
    exact fox_map_of_not_mem_range Option.some (by simp) (ρ j)
  show quotRingHom ℤ (relSub (extRel ρ w₀)) (fox none (extRel ρ w₀ (some j))) = 0
  rw [h, map_zero]

omit [Fintype α] [DecidableEq J] in
/-- **A Fox cycle of the extended presentation is zero on the new two-cell**, provided the
Fox derivative of the new relator with respect to the new generator is right-regular. -/
theorem extCycle_new_eq_zero
    (hreg : ∀ x : MonoidAlgebra ℤ (PresGroup (extRel ρ w₀)),
      x * foxMatrixPres (extRel ρ w₀) none none = 0 → x = 0)
    {v : Option J → MonoidAlgebra ℤ (PresGroup (extRel ρ w₀))}
    (hv : IsFoxCycle (extRel ρ w₀) v) : v none = 0 := by
  have h := hv none
  rw [Fintype.sum_option] at h
  have hzero : ∑ j : J, v (some j) * foxMatrixPres (extRel ρ w₀) none (some j) = 0 := by
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [foxMatrix_ext_none_some, mul_zero]
  rw [hzero, add_zero] at h
  exact hreg _ h

/-- The map `π₁(K) → π₁(K')` induced by the extension. -/
def extHom : PresGroup ρ →* PresGroup (extRel ρ w₀) :=
  QuotientGroup.map _ _ (FreeGroup.map Option.some) (by
    refine Subgroup.normalClosure_le_normal ?_
    rintro _ ⟨j, rfl⟩
    refine Subgroup.mem_comap.2 ?_
    have : FreeGroup.map Option.some (ρ j) = extRel ρ w₀ (some j) := rfl
    rw [this]
    exact Subgroup.subset_normalClosure (Set.mem_range_self _))

omit [Fintype α] [DecidableEq α] [Fintype J] [DecidableEq J] in
@[simp] theorem extHom_mk (w : FreeGroup α) :
    extHom ρ w₀ (QuotientGroup.mk w) = QuotientGroup.mk (FreeGroup.map Option.some w) := rfl

/-- The ring map of group rings induced by `extHom`. -/
noncomputable def extRingHom :
    MonoidAlgebra ℤ (PresGroup ρ) →+* MonoidAlgebra ℤ (PresGroup (extRel ρ w₀)) :=
  MonoidAlgebra.mapDomainRingHom ℤ (extHom ρ w₀)

omit [Fintype α] [DecidableEq α] [Fintype J] [DecidableEq J] in
/-- Reading a group-ring element of `ℤ[F]` in the group ring of the enlarged group agrees
with pushing it to `ℤ[π₁(K)]` and then along the extension. -/
theorem quot_freeRingMap_ext (x : FreeGroupRing α) :
    quotRingHom ℤ (relSub (extRel ρ w₀)) (freeRingMap Option.some x)
      = extRingHom ρ w₀ (quotRingHom ℤ (relSub ρ) x) := by
  induction x using MonoidAlgebra.induction_linear with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | single w m =>
      show quotRingHom ℤ (relSub (extRel ρ w₀))
          (MonoidAlgebra.mapDomain (FreeGroup.map Option.some) (MonoidAlgebra.single w m)) = _
      rw [MonoidAlgebra.mapDomain_single, quotRingHom_single]
      show _ = MonoidAlgebra.mapDomain (extHom ρ w₀) (quotRingHom ℤ (relSub ρ) (MonoidAlgebra.single w m))
      rw [quotRingHom_single, MonoidAlgebra.mapDomain_single, extHom_mk]

omit [Fintype α] [Fintype J] [DecidableEq J] in
/-- On the old cells and the old generators the Fox matrix of the extension is the image of
the old Fox matrix. -/
theorem foxMatrix_ext_some_some (i : α) (j : J) :
    foxMatrixPres (extRel ρ w₀) (some i) (some j) = extRingHom ρ w₀ (foxMatrixPres ρ i j) := by
  have hfox : @fox (Option α) _ (some i) (extRel ρ w₀ (some j))
      = freeRingMap Option.some (fox i (ρ j)) := by
    rw [extRel_some]
    exact fox_map Option.some (Option.some_injective α) i (ρ j)
  show quotRingHom ℤ (relSub (extRel ρ w₀)) (fox (some i) (extRel ρ w₀ (some j))) = _
  rw [hfox, quot_freeRingMap_ext]
  rfl

omit [Fintype α] [DecidableEq J] in
/-- **The extension creates no new identities.**  A Fox cycle of the extended presentation
vanishes on the new two-cell, and its old coefficients form a Fox cycle of the old Fox
matrix, read in the group ring of the enlarged group.  This is the combinatorial content of
the generation statement (3.3) of Lemma 3.9 for a one-generator, one-relator extension. -/
theorem extCycle_old
    (hreg : ∀ x : MonoidAlgebra ℤ (PresGroup (extRel ρ w₀)),
      x * foxMatrixPres (extRel ρ w₀) none none = 0 → x = 0)
    {v : Option J → MonoidAlgebra ℤ (PresGroup (extRel ρ w₀))}
    (hv : IsFoxCycle (extRel ρ w₀) v) :
    v none = 0 ∧ ∀ i : α, ∑ j : J, v (some j) * extRingHom ρ w₀ (foxMatrixPres ρ i j) = 0 := by
  refine ⟨extCycle_new_eq_zero ρ w₀ hreg hv, fun i => ?_⟩
  have h := hv (some i)
  rw [Fintype.sum_option, extCycle_new_eq_zero ρ w₀ hreg hv, zero_mul, zero_add] at h
  rw [← h]
  exact Finset.sum_congr rfl fun j _ => by rw [foxMatrix_ext_some_some]

/-! ### The two relators used in rule 1 -/

/-- The defining relator `z = s` of a Tietze transformation. -/
def tietzeWord (s : FreeGroup α) : FreeGroup (Option α) :=
  FreeGroup.of none * (FreeGroup.map Option.some s)⁻¹

/-- The stable-letter relator `z u z^{-1} = v` of an HNN extension. -/
def hnnWord (u v : FreeGroup α) : FreeGroup (Option α) :=
  FreeGroup.of none * FreeGroup.map Option.some u * (FreeGroup.of none)⁻¹ *
    (FreeGroup.map Option.some v)⁻¹

omit [Fintype α] [Fintype J] [DecidableEq J] in
/-- `∂(z s^{-1})/∂z = 1`. -/
theorem fox_tietzeWord (s : FreeGroup α) :
    @fox (Option α) _ none (tietzeWord s) = 1 := by
  have hs : @fox (Option α) _ none (FreeGroup.map Option.some s) = 0 :=
    fox_map_of_not_mem_range Option.some (by simp) s
  rw [tietzeWord, fox_mul, fox_inv, hs, mul_zero, neg_zero, mul_zero, add_zero, fox_of]
  simp

omit [Fintype α] [Fintype J] [DecidableEq J] in
/-- `∂(z u z^{-1} v^{-1})/∂z = 1 - z u z^{-1}`. -/
theorem fox_hnnWord (u v : FreeGroup α) :
    @fox (Option α) _ none (hnnWord u v)
      = 1 - grp (FreeGroup.of none * FreeGroup.map Option.some u * (FreeGroup.of none)⁻¹) := by
  have hu : @fox (Option α) _ none (FreeGroup.map Option.some u) = 0 :=
    fox_map_of_not_mem_range Option.some (by simp) u
  have hv : @fox (Option α) _ none (FreeGroup.map Option.some v) = 0 :=
    fox_map_of_not_mem_range Option.some (by simp) v
  have hz : @fox (Option α) _ none (FreeGroup.of none) = 1 := by simp
  rw [hnnWord, fox_mul, fox_inv, hv, mul_zero, neg_zero, mul_zero, add_zero, fox_mul, fox_inv,
    fox_mul, hu, hz, mul_zero, add_zero]
  rw [mul_one, mul_neg, ← grp_mul, sub_eq_add_neg]

omit [Fintype α] [Fintype J] [DecidableEq J] in
/-- The Fox derivative of the Tietze relator with respect to the new generator is `1`, so it
is right-regular: a Tietze transformation creates no new identities. -/
theorem foxNew_tietze (s : FreeGroup α) :
    foxMatrixPres (extRel ρ (tietzeWord s)) none none = 1 := by
  show quotRingHom ℤ (relSub (extRel ρ (tietzeWord s))) (fox none (tietzeWord s)) = 1
  rw [fox_tietzeWord s, map_one]

omit [Fintype α] [Fintype J] [DecidableEq J] in
/-- The Fox derivative of the stable-letter relator with respect to the new generator is
`1 - v`, computed in the group ring of the enlarged group. -/
theorem foxNew_hnn (u v : FreeGroup α) :
    foxMatrixPres (extRel ρ (hnnWord u v)) none none
      = 1 - single (QuotientGroup.mk (FreeGroup.map Option.some v) :
          PresGroup (extRel ρ (hnnWord u v))) 1 := by
  have hrel : (QuotientGroup.mk (FreeGroup.of none * FreeGroup.map Option.some u *
        (FreeGroup.of none)⁻¹) : PresGroup (extRel ρ (hnnWord u v)))
      = QuotientGroup.mk (FreeGroup.map Option.some v) := by
    have hmem : hnnWord u v ∈ relSub (extRel ρ (hnnWord u v)) := by
      have : hnnWord u v = extRel ρ (hnnWord u v) none := rfl
      rw [this]
      exact Subgroup.subset_normalClosure (Set.mem_range_self _)
    have hconj : (FreeGroup.map Option.some v)⁻¹ * (hnnWord u v)⁻¹ *
        ((FreeGroup.map Option.some v)⁻¹)⁻¹ ∈ relSub (extRel ρ (hnnWord u v)) :=
      (inferInstance : (relSub (extRel ρ (hnnWord u v))).Normal).conj_mem _
        (Subgroup.inv_mem _ hmem) _
    rw [QuotientGroup.eq]
    have hx : (FreeGroup.of none * FreeGroup.map Option.some u * (FreeGroup.of none)⁻¹)⁻¹ *
        FreeGroup.map Option.some v
        = (FreeGroup.map Option.some v)⁻¹ * (hnnWord u v)⁻¹ *
          ((FreeGroup.map Option.some v)⁻¹)⁻¹ := by
      rw [hnnWord]; group
    rw [hx]
    exact hconj
  show quotRingHom ℤ (relSub (extRel ρ (hnnWord u v))) (fox none (hnnWord u v)) = _
  rw [fox_hnnWord u v, map_sub, map_one]
  congr 1
  show quotRingHom ℤ (relSub (extRel ρ (hnnWord u v)))
      (MonoidAlgebra.single (FreeGroup.of none * FreeGroup.map Option.some u *
        (FreeGroup.of none)⁻¹) 1) = _
  rw [quotRingHom_single, hrel]

omit [Fintype α] [DecidableEq J] in
/-- **The Tietze step of rule 1 creates no new elements of `π₂`.** -/
theorem extCycle_tietze (s : FreeGroup α)
    {v : Option J → MonoidAlgebra ℤ (PresGroup (extRel ρ (tietzeWord s)))}
    (hv : IsFoxCycle (extRel ρ (tietzeWord s)) v) :
    v none = 0 ∧ ∀ i : α,
      ∑ j : J, v (some j) * extRingHom ρ (tietzeWord s) (foxMatrixPres ρ i j) = 0 :=
  extCycle_old ρ _ (fun x hx => by rwa [foxNew_tietze ρ s, mul_one] at hx) hv

omit [Fintype α] [DecidableEq J] in
/-- **The HNN step of rule 1 creates no new elements of `π₂`**, under the hypothesis used in
the paper: the element `v` along which the stable letter conjugates has infinite order in the
enlarged group. -/
theorem extCycle_hnn (u v : FreeGroup α)
    (hord : ¬ IsOfFinOrder (QuotientGroup.mk (FreeGroup.map Option.some v) :
      PresGroup (extRel ρ (hnnWord u v))))
    {c : Option J → MonoidAlgebra ℤ (PresGroup (extRel ρ (hnnWord u v)))}
    (hc : IsFoxCycle (extRel ρ (hnnWord u v)) c) :
    c none = 0 ∧ ∀ i : α,
      ∑ j : J, c (some j) * extRingHom ρ (hnnWord u v) (foxMatrixPres ρ i j) = 0 :=
  extCycle_old ρ _
    (fun x hx => mul_one_sub_single_eq_zero hord x (by rwa [foxNew_hnn ρ u v] at hx)) hc

end FiniteChains
