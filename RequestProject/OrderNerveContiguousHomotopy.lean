import RequestProject.OrderNerveCommonSimplex

namespace FiniteChains.Comb
open CategoryTheory Simplicial
open scoped unitInterval Classical
variable {P Q : Type} [PartialOrder P] [PartialOrder Q]
variable (f : P → Q) (hf : Monotone f) (g : P → Q) (hg : Monotone g)
variable (hc : ∀ p q, p ≤ q ∨ q ≤ p → f p ≤ g q ∨ g q ≤ f p)
include hc

/-- Cross-comparability gives a common target simplex for both actual maps
on each source simplex. This is stronger than pointwise comparison. -/
theorem orderNerveSimplex_common_maps {n : SimplexCategory}
    (s : (nerve P).obj (Opposite.op n)) :
    ∃ (m : SimplexCategory) (u : (nerve Q).obj (Opposite.op m))
      (a b : n ⟶ m),
      (∀ z, orderNerveRealizationSimplex Q u (SimplexCategory.toTop.map a z) =
        orderNerveRealizationMap f hf (orderNerveRealizationSimplex P s z)) ∧
      (∀ z, orderNerveRealizationSimplex Q u (SimplexCategory.toTop.map b z) =
        orderNerveRealizationMap g hg (orderNerveRealizationSimplex P s z)) := by
  have hcross : ∀ i j, f (s.obj i) ≤ g (s.obj j) ∨ g (s.obj j) ≤ f (s.obj i) := by
    intro i j
    apply hc
    rcases le_total i j with h | h
    · exact Or.inl (leOfHom (s.map (homOfLE h)))
    · exact Or.inr (leOfHom (s.map (homOfLE h)))
  obtain ⟨m, u, a, b, ha, hb⟩ := orderNerveSimplex_common
    ((nerveMap hf.functor).app _ s) ((nerveMap hg.functor).app _ s) hcross
  refine ⟨m, u, a, b, ?_, ?_⟩
  · intro z
    have h := congrArg (fun k => k z) (orderNerveRealizationSimplex_operator Q a u)
    change orderNerveRealizationSimplex Q u (SimplexCategory.toTop.map a z) =
      orderNerveRealizationSimplex Q ((nerve Q).map a.op u) z at h
    rw [ha] at h
    have hn := congrArg (fun k => k z) (orderNerveRealizationSimplex_natural f hf s)
    exact h.trans hn.symm
  · intro z
    have h := congrArg (fun k => k z) (orderNerveRealizationSimplex_operator Q b u)
    change orderNerveRealizationSimplex Q u (SimplexCategory.toTop.map b z) =
      orderNerveRealizationSimplex Q ((nerve Q).map b.op u) z at h
    rw [hb] at h
    have hn := congrArg (fun k => k z) (orderNerveRealizationSimplex_natural g hg s)
    exact h.trans hn.symm

theorem orderNerveRealization_blend_exists (t : I) (x : orderNerveRealization P) :
    ∃ y : orderNerveRealization Q, ∀ q,
      orderNerveRealizationCoordinates Q y q =
        (1 - (t : ℝ)) * orderNerveRealizationCoordinates Q (orderNerveRealizationMap f hf x) q +
        (t : ℝ) * orderNerveRealizationCoordinates Q (orderNerveRealizationMap g hg x) q := by
  obtain ⟨n, s, z, rfl⟩ := orderNerveRealizationSimplex_jointly_surjective P x
  obtain ⟨m, u, a, b, ha, hb⟩ := orderNerveSimplex_common_maps f hf g hg hc s
  refine ⟨orderNerveRealizationSimplex Q u
    (topologicalSimplexBlend t (SimplexCategory.toTop.map a z) (SimplexCategory.toTop.map b z)),
    fun q => ?_⟩
  rw [orderNerveRealizationCoordinates_blend, ha, hb]

/-- The unique affine interpolation, defined in global barycentric coordinates. -/
noncomputable def orderNerveRealizationBlend (t : I) (x : orderNerveRealization P) :
    orderNerveRealization Q := (orderNerveRealization_blend_exists f hf g hg hc t x).choose

theorem orderNerveRealizationBlend_coordinates (t : I) (x : orderNerveRealization P) (q : Q) :
    orderNerveRealizationCoordinates Q (orderNerveRealizationBlend f hf g hg hc t x) q =
      (1 - (t : ℝ)) * orderNerveRealizationCoordinates Q (orderNerveRealizationMap f hf x) q +
      (t : ℝ) * orderNerveRealizationCoordinates Q (orderNerveRealizationMap g hg x) q :=
  (orderNerveRealization_blend_exists f hf g hg hc t x).choose_spec q

/-- Joint continuity holds in the actual weak CW topology, including infinite posets. -/
theorem orderNerveRealizationBlend_continuous :
    Continuous (fun tx : I × orderNerveRealization P =>
      orderNerveRealizationBlend f hf g hg hc tx.1 tx.2) := by
  apply (orderNerveRealization_continuous_prod_iff P _).mpr
  intro n s
  obtain ⟨m, u, a, b, ha, hb⟩ := orderNerveSimplex_common_maps f hf g hg hc s
  have he : (fun tx : I × SimplexCategory.toTop.obj n =>
      orderNerveRealizationBlend f hf g hg hc tx.1 (orderNerveRealizationSimplex P s tx.2)) =
      (fun tx => orderNerveRealizationSimplex Q u
        (topologicalSimplexBlend tx.1 (SimplexCategory.toTop.map a tx.2)
          (SimplexCategory.toTop.map b tx.2))) := by
    funext tx
    apply orderNerveRealizationCoordinates_injective Q
    funext q
    rw [orderNerveRealizationBlend_coordinates, orderNerveRealizationCoordinates_blend, ha, hb]
  rw [he]
  exact (orderNerveRealizationSimplex Q u).hom.continuous.comp
    (topologicalSimplexBlend_continuous.comp
      (continuous_fst.prodMk
        (((SimplexCategory.toTop.map a).hom.continuous.comp continuous_snd).prodMk
          ((SimplexCategory.toTop.map b).hom.continuous.comp continuous_snd))))

@[simp] theorem orderNerveRealizationBlend_zero (x : orderNerveRealization P) :
    orderNerveRealizationBlend f hf g hg hc 0 x = orderNerveRealizationMap f hf x := by
  apply orderNerveRealizationCoordinates_injective Q
  funext q
  simp [orderNerveRealizationBlend_coordinates]

@[simp] theorem orderNerveRealizationBlend_one (x : orderNerveRealization P) :
    orderNerveRealizationBlend f hf g hg hc 1 x = orderNerveRealizationMap g hg x := by
  apply orderNerveRealizationCoordinates_injective Q
  funext q
  simp [orderNerveRealizationBlend_coordinates]

/-- The interpolation is stationary at every point where the two actual maps agree. -/
theorem orderNerveRealizationBlend_stationary (t : I) (x : orderNerveRealization P)
    (hx : orderNerveRealizationMap f hf x = orderNerveRealizationMap g hg x) :
    orderNerveRealizationBlend f hf g hg hc t x = orderNerveRealizationMap f hf x := by
  apply orderNerveRealizationCoordinates_injective Q
  funext q
  rw [orderNerveRealizationBlend_coordinates, ← hx]
  ring

/-- A concrete topological homotopy between maps with cross-comparable images. -/
noncomputable def orderNerveRealizationContiguousHomotopy :
    ContinuousMap.Homotopy
      (⟨orderNerveRealizationMap f hf, (orderNerveRealizationMap f hf).hom.continuous⟩ :
        C(orderNerveRealization P, orderNerveRealization Q))
      ⟨orderNerveRealizationMap g hg, (orderNerveRealizationMap g hg).hom.continuous⟩ where
  toFun tx := orderNerveRealizationBlend f hf g hg hc tx.1 tx.2
  continuous_toFun := orderNerveRealizationBlend_continuous f hf g hg hc
  map_zero_left := orderNerveRealizationBlend_zero f hf g hg hc
  map_one_left := orderNerveRealizationBlend_one f hf g hg hc

end FiniteChains.Comb
