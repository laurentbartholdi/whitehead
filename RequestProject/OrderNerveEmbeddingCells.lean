import RequestProject.OrderNerveRealizationSubtypeCells
import RequestProject.OrderNervePosetCoverVertexStars

namespace FiniteChains.Comb
open CategoryTheory Topology
variable {P Q : Type} [PartialOrder P] [PartialOrder Q]

/-- An order embedding maps every actual nondegenerate cell to a nondegenerate cell. -/
def orderNerveEmbeddingCell (f : P ↪o Q) {n : ℕ}
    (s : (nerve P).nonDegenerate n) : (nerve Q).nonDegenerate n :=
  ⟨(nerveMap f.monotone.functor).app _ s.val, by
    apply (PartialOrder.mem_nerve_nonDegenerate_iff_strictMono _).mpr
    exact f.strictMono.comp
      ((PartialOrder.mem_nerve_nonDegenerate_iff_strictMono s.val).mp s.property)⟩

/-- Order isomorphisms preserve the actual CW cell indexing in every dimension. -/
def orderNerveIsoCellEquiv (e : P ≃o Q) (n : ℕ) :
    (nerve P).nonDegenerate n ≃ (nerve Q).nonDegenerate n where
  toFun := orderNerveEmbeddingCell e.toOrderEmbedding
  invFun := orderNerveEmbeddingCell e.symm.toOrderEmbedding
  left_inv s := by
    apply Subtype.ext
    exact CategoryTheory.Functor.ext (fun i => e.symm_apply_apply (s.val.obj i))
  right_inv s := by
    apply Subtype.ext
    exact CategoryTheory.Functor.ext (fun i => e.apply_symm_apply (s.val.obj i))

/-- The range factorization retains the given embedding on points. -/
noncomputable def orderEmbeddingRangeIso (f : P ↪o Q) : P ≃o Set.range f where
  toEquiv := Equiv.ofInjective f f.injective
  map_rel_iff' := f.le_iff_le

/-- The source cells are exactly the ambient cells supported on the embedding range. -/
noncomputable def orderNerveEmbeddingCellEquiv (f : P ↪o Q) (n : ℕ) :
    (nerve P).nonDegenerate n ≃
      {s : (nerve Q).nonDegenerate n // ∀ i, s.val.obj i ∈ Set.range f} :=
  (orderNerveIsoCellEquiv (orderEmbeddingRangeIso f) n).trans
    (orderNerveSubtypeCellEquiv (Set.range f) n)

theorem orderNerveEmbeddingCellEquiv_val (f : P ↪o Q) (n : ℕ)
    (s : (nerve P).nonDegenerate n) :
    (orderNerveEmbeddingCellEquiv f n s).val = orderNerveEmbeddingCell f s := by
  apply Subtype.ext
  exact CategoryTheory.Functor.ext (fun _ => rfl)

/-- Every realized order embedding identifies its source with a genuine ambient
CW subcomplex, using the actual realization of the original map. -/
noncomputable def orderNerveRealizationEmbeddingHomeomorph (f : P ↪o Q) :
    orderNerveRealization P ≃ₜ
      (orderNerveRealizationSubcomplex Q (Set.range f) : Set (orderNerveRealization Q)) :=
  (orderNerveRealizationOrderIso (orderEmbeddingRangeIso f)).trans
    (orderNerveRealizationSubtypeHomeomorph (Set.range f))

theorem orderNerveRealizationEmbeddingHomeomorph_coe (f : P ↪o Q)
    (x : orderNerveRealization P) :
    (orderNerveRealizationEmbeddingHomeomorph f x).val =
      orderNerveRealizationMap f f.monotone x := by
  change orderNerveRealizationMap (Subtype.val : Set.range f → Q) (fun _ _ h => h)
      (orderNerveRealizationMap (orderEmbeddingRangeIso f)
        (orderEmbeddingRangeIso f).monotone x) = _
  exact orderNerveRealizationMap_comp (orderEmbeddingRangeIso f)
    (orderEmbeddingRangeIso f).monotone (Subtype.val : Set.range f → Q) (fun _ _ h => h) x

theorem orderNerveRealizationEmbeddingHomeomorph_openCell (f : P ↪o Q) (n : ℕ)
    (s : (nerve P).nonDegenerate n) :
    (fun x => (orderNerveRealizationEmbeddingHomeomorph f x).val) ''
        CWComplex.openCell (C := (Set.univ : Set (orderNerveRealization P))) n s =
      CWComplex.openCell (C := (Set.univ : Set (orderNerveRealization Q))) n
        (orderNerveEmbeddingCellEquiv f n s).val := by
  simp only [orderNerveRealizationEmbeddingHomeomorph_coe,
    orderNerveEmbeddingCellEquiv_val]
  exact orderNerveRealizationMap_openCell f f.monotone s (orderNerveEmbeddingCell f s) rfl

/-- Dimension bounds descend through order embeddings. -/
theorem orderNerveEmbedding_hasDimensionLE (f : P ↪o Q) (d : ℕ)
    [(nerve Q).HasDimensionLE d] : (nerve P).HasDimensionLE d := by
  constructor
  intro n hn
  apply Set.eq_univ_of_forall
  intro s
  rw [SSet.mem_degenerate_iff_notMem_nonDegenerate]
  intro hs
  have hd := (nerve Q).dim_le_of_nonDegenerate (orderNerveEmbeddingCell f ⟨s, hs⟩) d
  omega

/-- The precise initial-identification requirement is preserved for arbitrary
order embeddings, with a proved bijection on the original open cells. -/
theorem orderNerveRealizationEmbedding_initialIdentification (f : P ↪o Q)
    [Nonempty P] [Nonempty Q] [(nerve P).HasDimensionLE 2] [(nerve Q).HasDimensionLE 2]
    (hP : IsConnected (orderCx P)) (hQ : IsConnected (orderCx Q)) :
    @Whitehead.InitialIdentification (orderNerveTwoComplex P hP)
      (orderNerveTwoComplex Q hQ) (orderNerveRealizationSubcomplex Q (Set.range f))
      (orderNerveRealizationEmbeddingHomeomorph f) := by
  intro n
  exact ⟨orderNerveEmbeddingCellEquiv f n,
    orderNerveRealizationEmbeddingHomeomorph_openCell f n⟩

end FiniteChains.Comb
