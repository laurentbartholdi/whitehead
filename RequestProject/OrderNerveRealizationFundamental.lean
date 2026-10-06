import RequestProject.OrderNerveRealizationStarContractible

namespace FiniteChains.Comb
open CategoryTheory Simplicial

/-- Paths lying in a simply connected subspace are homotopic in the ambient
space, with their endpoints fixed. -/
theorem paths_homotopic_of_range_subset {X : Type} [TopologicalSpace X]
    {A : Set X} (hA : IsSimplyConnected A) {a b : X} (p q : Path a b)
    (hp : Set.range p ⊆ A) (hq : Set.range q ⊆ A) : p.Homotopic q := by
  letI : SimplyConnectedSpace A := hA
  have ha : a ∈ A := hp p.source_mem_range
  have hb : b ∈ A := hp p.target_mem_range
  let p' : Path (⟨a, ha⟩ : A) ⟨b, hb⟩ :=
    { toFun := fun t => ⟨p t, hp ⟨t, rfl⟩⟩
      continuous_toFun := p.continuous.subtype_mk _
      source' := Subtype.ext p.source
      target' := Subtype.ext p.target }
  let q' : Path (⟨a, ha⟩ : A) ⟨b, hb⟩ :=
    { toFun := fun t => ⟨q t, hq ⟨t, rfl⟩⟩
      continuous_toFun := q.continuous.subtype_mk _
      source' := Subtype.ext q.source
      target' := Subtype.ext q.target }
  exact (SimplyConnectedSpace.paths_homotopic p' q').map
    ⟨Subtype.val, continuous_subtype_val⟩

/-- Two vertices of a canonical simplex can be joined inside that simplex. -/
theorem orderNerveRealizationSimplex_exists_path {P : Type} [PartialOrder P]
    {n : SimplexCategory} (s : (nerve P).obj (Opposite.op n))
    (i j : Fin (n.len + 1)) :
    ∃ p : Path (orderNerveRealizationVertex (s.obj i))
        (orderNerveRealizationVertex (s.obj j)),
      Set.range p ⊆ Set.range (orderNerveRealizationSimplex P s) := by
  obtain ⟨z, hz⟩ := orderNerveRealizationVertex_mem_simplex s i
  obtain ⟨w, hw⟩ := orderNerveRealizationVertex_mem_simplex s j
  let p := (PathConnectedSpace.joined z w).somePath.map
    (orderNerveRealizationSimplex P s).hom.continuous
  refine ⟨p.cast hz.symm hw.symm, ?_⟩
  rintro x ⟨t, rfl⟩
  exact ⟨(PathConnectedSpace.joined z w).somePath t, rfl⟩

/-- A realized comparable edge, chosen inside its canonical one-simplex. -/
noncomputable def orderNerveRealizationEdgePath {P : Type} [PartialOrder P]
    {a b : P} (h : a ≤ b) : Path (orderNerveRealizationVertex a)
      (orderNerveRealizationVertex b) :=
  (orderNerveRealizationSimplex_exists_path (n := ⦋1⦌) (ComposableArrows.mk₁ (homOfLE h))
    (0 : Fin 2) (1 : Fin 2)).choose

theorem orderNerveRealizationEdgePath_range {P : Type} [PartialOrder P]
    {a b : P} (h : a ≤ b) :
    Set.range (orderNerveRealizationEdgePath h) ⊆
      Set.range (orderNerveRealizationSimplex P (n := ⦋1⦌) (ComposableArrows.mk₁ (homOfLE h))) :=
  (orderNerveRealizationSimplex_exists_path (n := ⦋1⦌) (ComposableArrows.mk₁ (homOfLE h))
    (0 : Fin 2) (1 : Fin 2)).choose_spec

/-- A comparable edge stays in any closed vertex star containing its endpoints. -/
theorem orderNerveRealizationEdgePath_supported {P : Type} [PartialOrder P]
    {a b : P} (h : a ≤ b) (v : P) (ha : a ≤ v ∨ v ≤ a) (hb : b ≤ v ∨ v ≤ b) :
    Set.range (orderNerveRealizationEdgePath h) ⊆
      (orderNerveRealizationSubcomplex P (orderNerveVertexStar P v) :
        Set (orderNerveRealization P)) := by
  apply (orderNerveRealizationEdgePath_range h).trans
  apply orderNerveRealizationSimplex_supported (orderNerveVertexStar P v)
  intro i
  fin_cases i
  · exact ha
  · exact hb

theorem orderNerveRealizationVertex_mem_closedStar {P : Type} [PartialOrder P]
    {p v : P} (hp : p ≤ v ∨ v ≤ p) :
    orderNerveRealizationVertex p ∈
      (orderNerveRealizationSubcomplex P (orderNerveVertexStar P v) :
        Set (orderNerveRealization P)) := by
  classical
  intro q hq
  by_cases he : p = q
  · subst q
    exact (hq hp).elim
  · simp only [orderNerveRealizationCoordinates_vertex, if_neg he]

/-- The degenerate edge represents the identity path class. -/
theorem orderNerveRealizationEdgePath_refl {P : Type} [PartialOrder P] (a : P) :
    (orderNerveRealizationEdgePath (le_refl a)).Homotopic
      (Path.refl (orderNerveRealizationVertex a)) := by
  letI := orderNerveRealization_closedStar_contractible a
  apply paths_homotopic_of_range_subset
    (A := (orderNerveRealizationSubcomplex P (orderNerveVertexStar P a) :
      Set (orderNerveRealization P))) (by
        change SimplyConnectedSpace _
        infer_instance)
  · exact orderNerveRealizationEdgePath_supported le_rfl a (Or.inl le_rfl) (Or.inl le_rfl)
  · rintro x ⟨t, rfl⟩
    exact orderNerveRealizationVertex_mem_closedStar (Or.inl le_rfl)

/-- A chain of three vertices gives the actual topological triangle relation. -/
theorem orderNerveRealizationEdgePath_trans {P : Type} [PartialOrder P]
    {a b c : P} (hab : a ≤ b) (hbc : b ≤ c) :
    (orderNerveRealizationEdgePath (hab.trans hbc)).Homotopic
      ((orderNerveRealizationEdgePath hab).trans (orderNerveRealizationEdgePath hbc)) := by
  letI := orderNerveRealization_closedStar_contractible b
  apply paths_homotopic_of_range_subset
    (A := (orderNerveRealizationSubcomplex P (orderNerveVertexStar P b) :
      Set (orderNerveRealization P))) (by
        change SimplyConnectedSpace _
        infer_instance)
  · exact orderNerveRealizationEdgePath_supported _ b (Or.inl hab) (Or.inr hbc)
  · rw [Path.trans_range]
    exact Set.union_subset
      (orderNerveRealizationEdgePath_supported hab b (Or.inl hab) (Or.inl le_rfl))
      (orderNerveRealizationEdgePath_supported hbc b (Or.inl le_rfl) (Or.inr hbc))

/-- Comparable vertices and their canonical edge paths form a functor to the
actual topological fundamental groupoid of the realization. -/
noncomputable def orderNerveRealizationFundamentalFunctor (P : Type) [PartialOrder P] :
    P ⥤ FundamentalGroupoid (orderNerveRealization P) where
  obj p := FundamentalGroupoid.mk (orderNerveRealizationVertex p)
  map h := Path.Homotopic.Quotient.mk (orderNerveRealizationEdgePath (leOfHom h))
  map_id a := Quotient.sound (orderNerveRealizationEdgePath_refl a)
  map_comp f g := Quotient.sound (orderNerveRealizationEdgePath_trans (leOfHom f) (leOfHom g))

end FiniteChains.Comb
