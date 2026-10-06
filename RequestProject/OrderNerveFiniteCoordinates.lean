module

public import RequestProject.OrderNerveRealizationMapCoordinates

@[expose] public section

/-! Exact barycentric-coordinate reconstruction for a finite poset. This is
used to split an actual cone point into its radial coordinate and base point. -/

noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains.Comb
open CategoryTheory Simplicial
open scoped Classical

theorem orderNerveRealizationCoordinates_simplex {P : Type} [PartialOrder P]
    {n : SimplexCategory} (s : (nerve P).obj (Opposite.op n))
    (z : SimplexCategory.toTop.obj n) (p : P) :
    orderNerveRealizationCoordinates P (orderNerveRealizationSimplex P s z) p =
      orderNerveAffineSimplex (fun q => if q = p then 1 else 0) s z :=
  congrArg (fun k => k z)
    (orderNerveAffineRealization_simplex (fun q => if q = p then 1 else 0) s)

theorem orderNerveRealizationCoordinates_nonneg {P : Type} [PartialOrder P]
    (x : orderNerveRealization P) (p : P) :
    0 ≤ orderNerveRealizationCoordinates P x p := by
  obtain ⟨n, s, z, rfl⟩ := orderNerveRealizationSimplex_jointly_surjective P x
  rw [orderNerveRealizationCoordinates_simplex]
  change 0 ≤ ∑ i, z.down.weights i * (if s.obj i = p then 1 else 0)
  apply Finset.sum_nonneg
  intro i _
  exact mul_nonneg (z.down.weights_nonneg i) (by split_ifs <;> norm_num)

theorem orderNerveRealizationCoordinates_sum {P : Type} [PartialOrder P] [Fintype P]
    (x : orderNerveRealization P) : ∑ p, orderNerveRealizationCoordinates P x p = 1 := by
  obtain ⟨n, s, z, rfl⟩ := orderNerveRealizationSimplex_jointly_surjective P x
  simp only [orderNerveRealizationCoordinates_simplex, orderNerveAffineSimplex,
    ContinuousMap.coe_mk]
  rw [Finset.sum_comm]
  simpa [mul_ite] using z.down.total_of_fintype

theorem orderNerveRealizationCoordinates_support_chain {P : Type} [PartialOrder P]
    (x : orderNerveRealization P) :
    IsChain (· ≤ ·) {p | 0 < orderNerveRealizationCoordinates P x p} := by
  obtain ⟨n, s, z, hz, rfl⟩ := orderNerveRealization_interior_cover P x
  intro p hp q hq _
  rw [Set.mem_setOf_eq, orderNerveRealizationCoordinates_simplex] at hp hq
  obtain ⟨i, rfl⟩ := (orderNerveAffineSimplex_indicator_pos_iff s.val z hz p).mp hp
  obtain ⟨j, rfl⟩ := (orderNerveAffineSimplex_indicator_pos_iff s.val z hz q).mp hq
  rcases le_total i j with hij | hij
  · exact Or.inl (leOfHom (s.val.map (homOfLE hij)))
  · exact Or.inr (leOfHom (s.val.map (homOfLE hij)))

/-- Every probability vector whose positive support is a chain represents
an actual point of the geometric realization, with precisely those coordinates. -/
theorem orderNerveRealizationCoordinates_exists {P : Type} [PartialOrder P] [Fintype P]
    (c : P → ℝ) (hc : ∀ p, 0 ≤ c p) (hsum : ∑ p, c p = 1)
    (hchain : IsChain (· ≤ ·) {p | 0 < c p}) :
    ∃ x : orderNerveRealization P, ∀ p, orderNerveRealizationCoordinates P x p = c p := by
  let A := {p : P // 0 < c p}
  have hzero : ∀ p, ¬ 0 < c p → c p = 0 :=
    fun p hp => le_antisymm (le_of_not_gt hp) (hc p)
  have hA : ∑ p : A, c p.val = 1 := by
    have h := Fintype.sum_subtype_add_sum_subtype (fun p => 0 < c p) c
    have hz : (∑ p : {p : P // ¬ 0 < c p}, c p.val) = 0 :=
      Finset.sum_eq_zero (fun p _ => hzero p.val p.property)
    rw [hz, add_zero, hsum] at h
    exact h
  have hne : Nonempty A := by
    by_contra hn
    haveI : IsEmpty A := not_nonempty_iff.mp hn
    simp at hA
  letI : Nonempty A := hne
  letI : LinearOrder A :=
    { Subtype.partialOrder _ with
      le_total := fun x y => hchain.total x.property y.property
      toDecidableLE := Subtype.decidableLE
      toDecidableLT := Subtype.decidableLT
      toDecidableEq := Subtype.instDecidableEq }
  obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero (ne_of_gt (Fintype.card_pos (α := A)))
  let e : A ≃o Fin (n + 1) := (Fintype.orderIsoFinOfCardEq A hn).symm
  let s : (nerve P).obj (Opposite.op ⦋n⦌) :=
    (show Monotone (fun i : Fin (n + 1) => (e.symm i).val) from
      fun _ _ hij => e.symm.monotone hij).functor
  have hs : Function.Injective s.obj := Subtype.val_injective.comp e.symm.injective
  let zold : stdSimplex ℝ (Fin (n + 1)) := ⟨fun i => c (s.obj i),
    ⟨fun i => hc (s.obj i), by
      change (∑ i : Fin (n + 1), c (e.symm i).val) = 1
      exact (e.symm.toEquiv.sum_comp (fun a : A => c a.val)).trans hA⟩⟩
  let z : SimplexCategory.toTop.obj ⦋n⦌ :=
    ULift.up ((TopologicalSingular.simplexCoordinates n).symm zold)
  refine ⟨orderNerveRealizationSimplex P s z, ?_⟩
  intro p
  by_cases hp : 0 < c p
  · let i := e ⟨p, hp⟩
    have hi : s.obj i = p := congrArg Subtype.val (e.symm_apply_apply ⟨p, hp⟩)
    calc
      orderNerveRealizationCoordinates P (orderNerveRealizationSimplex P s z) p =
          orderNerveRealizationCoordinates P (orderNerveRealizationSimplex P s z) (s.obj i) :=
        congrArg (orderNerveRealizationCoordinates P (orderNerveRealizationSimplex P s z)) hi.symm
      _ = z.down.weights i := (orderNerveRealizationCoordinates_simplex s z (s.obj i)).trans
        (orderNerveAffineSimplex_indicator s hs i z)
      _ = c p := by
        simpa only [z, TopologicalSingular.simplexCoordinates_symm_weights_apply] using congrArg c hi
  · have hn : ∀ i, s.obj i ≠ p := by
      intro i hi
      exact hp (hi ▸ (e.symm i).property)
    rw [orderNerveRealizationCoordinates_simplex]
    simp only [orderNerveAffineSimplex, ContinuousMap.coe_mk, hn, ite_false, mul_zero,
      Finset.sum_const_zero, hzero p hp]

end FiniteChains.Comb
