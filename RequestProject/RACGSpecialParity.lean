import RequestProject.ChamberDescent
import RequestProject.RACGCovering

/-!
# The parity map on a special subgroup of a simplex

For a simplex `T` of `L` the special subgroup `W_T` is the elementary abelian group `(ℤ/2)^T`:
its elements are the products of duplicate-free words over `T`
(`FiniteChains.RACG.exists_nodup_cword`).  This file records what the quotient construction of
`RequestProject/ChamberQuotient.lean` needs about the parity homomorphism
`phi : W → (ℤ/2)^{L⁰}` on such a subgroup:

* `FiniteChains.RACG.phi_eq_zero_of_mem_specialSub` — an element of `W_T` has trivial parity
  outside `T`;
* `FiniteChains.RACG.phi_injOn_specialSub` — **`phi` is injective on `W_T`**;
* `FiniteChains.RACG.exists_mem_specialSub_phi_eq` — **`phi` maps `W_T` onto the sign vectors
  supported in `T`**.

Together these say that `phi` identifies `W_T` with `(ℤ/2)^T`, which is exactly what makes the
faces of a cube of `C(L)` lift uniquely to faces of a chamber of the Davis complex.
-/

namespace FiniteChains
namespace RACG

universe u

variable {V : Type u} [DecidableEq V] (A : CommRel V)

/-- An element of the special subgroup `W_T` has trivial parity outside `T`. -/
theorem phi_eq_zero_of_mem_specialSub {T : Set V} {u : CayGroup A} (hu : u ∈ specialSub A T)
    {v : V} (hv : v ∉ T) : phi A u v = 0 := by
  obtain ⟨l, hl, rfl⟩ := exists_cword_of_mem_specialSub A hu
  rw [phi_cword]
  have : l.count v = 0 := List.count_eq_zero_of_not_mem (fun hmem => hv (hl v hmem))
  simp [parList, this]

/-- An element of `W_T` with trivial parity is trivial. -/
theorem eq_one_of_mem_specialSub_of_phi_eq_zero {T : Set V} (hT : Commuting A T)
    {u : CayGroup A} (hu : u ∈ specialSub A T) (hphi : phi A u = 0) : u = 1 := by
  obtain ⟨l, hl, hnd, rfl⟩ := exists_nodup_cword A hT hu
  have hnil : l = [] := by
    cases l with
    | nil => rfl
    | cons a t =>
        exfalso
        have hcount : (a :: t).count a = 1 := List.count_eq_one_of_mem hnd (by simp)
        have h0 : phi A (cword A (a :: t)) a = 0 := congrFun hphi a
        rw [phi_cword] at h0
        simp only [parList, hcount, Nat.cast_one] at h0
        exact absurd h0 (by decide)
  rw [hnil, cword_nil]

/-- **`phi` is injective on the special subgroup of a simplex.** -/
theorem phi_injOn_specialSub {T : Set V} (hT : Commuting A T) {u u' : CayGroup A}
    (hu : u ∈ specialSub A T) (hu' : u' ∈ specialSub A T) (h : phi A u = phi A u') : u = u' := by
  have hmem : u⁻¹ * u' ∈ specialSub A T := Subgroup.mul_mem _ (Subgroup.inv_mem _ hu) hu'
  have hzero : phi A (u⁻¹ * u') = 0 := by
    rw [phi_mul, phi_inv, h]
    funext v
    exact zmod2_add_self _
  have := eq_one_of_mem_specialSub_of_phi_eq_zero A hT hmem hzero
  have h2 : u * (u⁻¹ * u') = u * 1 := by rw [this]
  simpa using h2.symm

/-- **`phi` maps `W_T` onto the sign vectors supported in `T`.** -/
theorem exists_mem_specialSub_phi_eq (T : Finset V) (t : V → ZMod 2)
    (ht : ∀ v : V, v ∉ T → t v = 0) :
    ∃ u : CayGroup A, u ∈ specialSub A (T : Set V) ∧ phi A u = t := by
  classical
  set l : List V := (T.filter (fun v : V => t v = 1)).toList with hldef
  have hlmem : ∀ a ∈ l, a ∈ (T : Set V) := by
    intro a ha
    rw [hldef, Finset.mem_toList, Finset.mem_filter] at ha
    exact ha.1
  refine ⟨cword A l, cword_mem_specialSub A hlmem, ?_⟩
  rw [phi_cword]
  funext v
  have hcount : l.count v = if v ∈ T ∧ t v = 1 then 1 else 0 := by
    by_cases h : v ∈ T ∧ t v = 1
    · rw [if_pos h]
      refine List.count_eq_one_of_mem (Finset.nodup_toList _) ?_
      rw [hldef, Finset.mem_toList, Finset.mem_filter]
      exact h
    · rw [if_neg h]
      refine List.count_eq_zero_of_not_mem ?_
      rw [hldef, Finset.mem_toList, Finset.mem_filter]
      exact h
  rw [parList, hcount]
  by_cases h : v ∈ T ∧ t v = 1
  · rw [if_pos h, h.2, Nat.cast_one]
  · have h0 : t v = 0 := by
      by_cases hv : v ∈ T
      · by_contra hne
        refine h ⟨hv, ?_⟩
        revert hne
        generalize t v = a
        revert a
        decide
      · exact ht v hv
    rw [if_neg h, h0, Nat.cast_zero]

end RACG
end FiniteChains
