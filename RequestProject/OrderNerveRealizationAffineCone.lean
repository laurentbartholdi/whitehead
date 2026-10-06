import RequestProject.OrderNerveRealizationContraction

namespace FiniteChains.Comb
open CategoryTheory Simplicial
open scoped unitInterval Classical

/-- Two simplices with mutually comparable vertices sit in a common simplex. -/
theorem orderNerveSimplex_merge {P : Type} [PartialOrder P]
    {n k : SimplexCategory} (s : (nerve P).obj (Opposite.op n))
    (r : (nerve P).obj (Opposite.op k))
    (h : ∀ i j, s.obj i ≤ r.obj j ∨ r.obj j ≤ s.obj i) :
    ∃ (m : SimplexCategory) (u : (nerve P).obj (Opposite.op m))
      (a : n ⟶ m) (b : k ⟶ m),
      (nerve P).map a.op u = s ∧ (nerve P).map b.op u = r := by
  classical
  let A : Set P := Set.range s.obj ∪ Set.range r.obj
  have hA : IsChain (· ≤ ·) A := by
    intro x hx y hy _
    rcases hx with ⟨i, rfl⟩ | ⟨i, rfl⟩
    · rcases hy with ⟨j, rfl⟩ | ⟨j, rfl⟩
      · rcases le_total i j with hij | hij
        · exact Or.inl (leOfHom (s.map (homOfLE hij)))
        · exact Or.inr (leOfHom (s.map (homOfLE hij)))
      · exact h i j
    · rcases hy with ⟨j, rfl⟩ | ⟨j, rfl⟩
      · exact (h j i).symm
      · rcases le_total i j with hij | hij
        · exact Or.inl (leOfHom (r.map (homOfLE hij)))
        · exact Or.inr (leOfHom (r.map (homOfLE hij)))
  letI : Fintype A := ((Set.finite_range s.obj).union (Set.finite_range r.obj)).fintype
  letI : LinearOrder A :=
    { Subtype.partialOrder _ with
      le_total := fun x y => hA.total x.property y.property
      toDecidableLE := Subtype.decidableLE
      toDecidableLT := Subtype.decidableLT
      toDecidableEq := Subtype.instDecidableEq }
  letI : Nonempty A := ⟨⟨s.obj 0, Or.inl ⟨0, rfl⟩⟩⟩
  obtain ⟨l, hl⟩ := Nat.exists_eq_succ_of_ne_zero (ne_of_gt (Fintype.card_pos (α := A)))
  let e : A ≃o Fin (l + 1) := (Fintype.orderIsoFinOfCardEq A hl).symm
  let u : (nerve P).obj (Opposite.op ⦋l⦌) :=
    (show Monotone (fun i : Fin (l + 1) => (e.symm i).val) from
      fun _ _ hij => e.symm.monotone hij).functor
  let a : n ⟶ ⦋l⦌ := SimplexCategory.mkHom
    ⟨fun i => e ⟨s.obj i, Or.inl ⟨i, rfl⟩⟩,
      fun _ _ hij => e.monotone (leOfHom (s.map (homOfLE hij)))⟩
  let b : k ⟶ ⦋l⦌ := SimplexCategory.mkHom
    ⟨fun i => e ⟨r.obj i, Or.inr ⟨i, rfl⟩⟩,
      fun _ _ hij => e.monotone (leOfHom (r.map (homOfLE hij)))⟩
  refine ⟨⦋l⦌, u, a, b, ?_, ?_⟩
  · exact CategoryTheory.Functor.ext (fun i =>
      congrArg Subtype.val (e.symm_apply_apply ⟨s.obj i, Or.inl ⟨i, rfl⟩⟩))
  · exact CategoryTheory.Functor.ext (fun i =>
      congrArg Subtype.val (e.symm_apply_apply ⟨r.obj i, Or.inr ⟨i, rfl⟩⟩))

/-- Affine interpolation towards a fixed simplex with universally comparable
vertices exists in the actual realization. -/
theorem orderNerveRealization_affineCone_exists {P : Type} [PartialOrder P]
    {k : SimplexCategory} (r : (nerve P).obj (Opposite.op k))
    (hr : ∀ p j, p ≤ r.obj j ∨ r.obj j ≤ p) (w : SimplexCategory.toTop.obj k)
    (t : I) (x : orderNerveRealization P) :
    ∃ y : orderNerveRealization P, ∀ p,
      orderNerveRealizationCoordinates P y p =
        (1 - (t : ℝ)) * orderNerveRealizationCoordinates P x p +
        (t : ℝ) * orderNerveRealizationCoordinates P (orderNerveRealizationSimplex P r w) p := by
  obtain ⟨n, s, z, rfl⟩ := orderNerveRealizationSimplex_jointly_surjective P x
  obtain ⟨m, u, a, b, hs, hr'⟩ := orderNerveSimplex_merge s r (fun i j => hr (s.obj i) j)
  have hz := congrArg (fun f => f z) (orderNerveRealizationSimplex_operator P a u)
  have hw := congrArg (fun f => f w) (orderNerveRealizationSimplex_operator P b u)
  change orderNerveRealizationSimplex P u (SimplexCategory.toTop.map a z) =
    orderNerveRealizationSimplex P ((nerve P).map a.op u) z at hz
  change orderNerveRealizationSimplex P u (SimplexCategory.toTop.map b w) =
    orderNerveRealizationSimplex P ((nerve P).map b.op u) w at hw
  rw [hs] at hz
  rw [hr'] at hw
  refine ⟨orderNerveRealizationSimplex P u
    (topologicalSimplexBlend t (SimplexCategory.toTop.map a z) (SimplexCategory.toTop.map b w)),
    fun p => ?_⟩
  rw [orderNerveRealizationCoordinates_blend, hz, hw]

noncomputable def orderNerveRealizationAffineCone {P : Type} [PartialOrder P]
    {k : SimplexCategory} (r : (nerve P).obj (Opposite.op k))
    (hr : ∀ p j, p ≤ r.obj j ∨ r.obj j ≤ p) (w : SimplexCategory.toTop.obj k)
    (t : I) (x : orderNerveRealization P) : orderNerveRealization P :=
  (orderNerveRealization_affineCone_exists r hr w t x).choose

theorem orderNerveRealizationAffineCone_coordinates {P : Type} [PartialOrder P]
    {k : SimplexCategory} (r : (nerve P).obj (Opposite.op k))
    (hr : ∀ p j, p ≤ r.obj j ∨ r.obj j ≤ p) (w : SimplexCategory.toTop.obj k)
    (t : I) (x : orderNerveRealization P) (p : P) :
    orderNerveRealizationCoordinates P (orderNerveRealizationAffineCone r hr w t x) p =
      (1 - (t : ℝ)) * orderNerveRealizationCoordinates P x p +
      (t : ℝ) * orderNerveRealizationCoordinates P (orderNerveRealizationSimplex P r w) p :=
  (orderNerveRealization_affineCone_exists r hr w t x).choose_spec p

/-- Joint continuity uses the weak realization topology, not coordinatewise
continuity as a substitute for that topology. -/
theorem orderNerveRealizationAffineCone_continuous {P : Type} [PartialOrder P]
    {k : SimplexCategory} (r : (nerve P).obj (Opposite.op k))
    (hr : ∀ p j, p ≤ r.obj j ∨ r.obj j ≤ p) (w : SimplexCategory.toTop.obj k) :
    Continuous (fun tx : I × orderNerveRealization P =>
      orderNerveRealizationAffineCone r hr w tx.1 tx.2) := by
  apply (orderNerveRealization_continuous_prod_iff P _).mpr
  intro n s
  obtain ⟨m, u, a, b, hs, hr'⟩ := orderNerveSimplex_merge s r (fun i j => hr (s.obj i) j)
  have hz (z : SimplexCategory.toTop.obj n) := congrArg (fun f => f z)
    (orderNerveRealizationSimplex_operator P a u)
  have hw := congrArg (fun f => f w) (orderNerveRealizationSimplex_operator P b u)
  change orderNerveRealizationSimplex P u (SimplexCategory.toTop.map b w) =
    orderNerveRealizationSimplex P ((nerve P).map b.op u) w at hw
  rw [hr'] at hw
  have he : (fun tx : I × SimplexCategory.toTop.obj n =>
      orderNerveRealizationAffineCone r hr w tx.1 (orderNerveRealizationSimplex P s tx.2)) =
      (fun tx => orderNerveRealizationSimplex P u
        (topologicalSimplexBlend tx.1 (SimplexCategory.toTop.map a tx.2)
          (SimplexCategory.toTop.map b w))) := by
    funext tx
    apply orderNerveRealizationCoordinates_injective P
    funext p
    rw [orderNerveRealizationAffineCone_coordinates, orderNerveRealizationCoordinates_blend, hw]
    have hz' := hz tx.2
    change orderNerveRealizationSimplex P u (SimplexCategory.toTop.map a tx.2) =
      orderNerveRealizationSimplex P ((nerve P).map a.op u) tx.2 at hz'
    rw [hs] at hz'
    rw [hz']
  rw [he]
  exact (orderNerveRealizationSimplex P u).hom.continuous.comp
    (topologicalSimplexBlend_continuous.comp
      (continuous_fst.prodMk (((SimplexCategory.toTop.map a).hom.continuous.comp
        continuous_snd).prodMk continuous_const)))

@[simp] theorem orderNerveRealizationAffineCone_zero {P : Type} [PartialOrder P]
    {k : SimplexCategory} (r : (nerve P).obj (Opposite.op k))
    (hr : ∀ p j, p ≤ r.obj j ∨ r.obj j ≤ p) (w : SimplexCategory.toTop.obj k)
    (x : orderNerveRealization P) : orderNerveRealizationAffineCone r hr w 0 x = x := by
  apply orderNerveRealizationCoordinates_injective P
  funext p
  simp [orderNerveRealizationAffineCone_coordinates]

@[simp] theorem orderNerveRealizationAffineCone_one {P : Type} [PartialOrder P]
    {k : SimplexCategory} (r : (nerve P).obj (Opposite.op k))
    (hr : ∀ p j, p ≤ r.obj j ∨ r.obj j ≤ p) (w : SimplexCategory.toTop.obj k)
    (x : orderNerveRealization P) :
    orderNerveRealizationAffineCone r hr w 1 x = orderNerveRealizationSimplex P r w := by
  apply orderNerveRealizationCoordinates_injective P
  funext p
  simp [orderNerveRealizationAffineCone_coordinates]

/-- Affine interpolation preserves simultaneous positivity of any specified
coordinates when both endpoints have those positive coordinates. -/
theorem orderNerveRealizationAffineCone_positive {P : Type} [PartialOrder P]
    {k : SimplexCategory} (r : (nerve P).obj (Opposite.op k))
    (hr : ∀ p j, p ≤ r.obj j ∨ r.obj j ≤ p) (w : SimplexCategory.toTop.obj k)
    (t : I) (x : orderNerveRealization P) (p : P)
    (hx : 0 < orderNerveRealizationCoordinates P x p)
    (hw : 0 < orderNerveRealizationCoordinates P (orderNerveRealizationSimplex P r w) p) :
    0 < orderNerveRealizationCoordinates P (orderNerveRealizationAffineCone r hr w t x) p := by
  rw [orderNerveRealizationAffineCone_coordinates]
  rcases lt_or_eq_of_le t.property.2 with ht | ht
  · exact add_pos_of_pos_of_nonneg (mul_pos (sub_pos.mpr ht) hx)
      (mul_nonneg t.property.1 (le_of_lt hw))
  · simpa [ht] using hw

end FiniteChains.Comb
