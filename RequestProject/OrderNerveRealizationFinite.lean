import RequestProject.OrderNerveTwoComplex

namespace FiniteChains.Comb
open CategoryTheory Topology

/-- Each dimension has finitely many actual nondegenerate simplices when the poset is finite. -/
instance orderNerve_nonDegenerate_finite (P : Type) [PartialOrder P] [Finite P] (n : ℕ) :
    Finite ((nerve P).nonDegenerate n) := by
  apply Finite.of_injective (fun s : (nerve P).nonDegenerate n => s.val.obj)
  intro s t h
  apply Subtype.ext
  exact CategoryTheory.Functor.ext (fun i => congrFun h i)

/-- No nondegenerate simplex of a finite poset has dimension as large as the vertex count. -/
theorem orderNerve_nonDegenerate_dimension_lt_card (P : Type) [PartialOrder P] [Fintype P]
    {n : ℕ} (s : (nerve P).nonDegenerate n) : n < Fintype.card P := by
  have h := Fintype.card_le_of_injective s.val.obj
    ((PartialOrder.mem_nerve_nonDegenerate_iff_injective s.val).mp s.property)
  simp only [Fintype.card_fin, SimplexCategory.len_mk] at h
  omega

/-- The actual CW realization of a finite poset has finitely many cells in total. -/
instance orderNerveRealization_cells_finite (P : Type) [PartialOrder P] [Finite P] :
    Finite (Σ n, RelCWComplex.cell (Set.univ : Set (orderNerveRealization P)) n) := by
  letI := Fintype.ofFinite P
  let f : (Σ n, (nerve P).nonDegenerate n) →
      (Σ n : Fin (Fintype.card P), (nerve P).nonDegenerate n.val) := fun s =>
    ⟨⟨s.1, orderNerve_nonDegenerate_dimension_lt_card P s.2⟩, s.2⟩
  let g : (Σ n : Fin (Fintype.card P), (nerve P).nonDegenerate n.val) →
      (Σ n, (nerve P).nonDegenerate n) := fun s => ⟨s.1.val, s.2⟩
  have hf : Function.Injective f := (show Function.LeftInverse g f from fun _ => rfl).injective
  exact Finite.of_injective f hf

/-- The genuine two-complex constructed from a finite poset satisfies the submission's
actual finite-cell condition. -/
theorem orderNerveTwoComplex_finiteCells (P : Type) [PartialOrder P] [Nonempty P] [Finite P]
    [(nerve P).HasDimensionLE 2] (hP : IsConnected (orderCx P)) :
    Whitehead.FiniteCells (orderNerveTwoComplex P hP) :=
  orderNerveRealization_cells_finite P

end FiniteChains.Comb
