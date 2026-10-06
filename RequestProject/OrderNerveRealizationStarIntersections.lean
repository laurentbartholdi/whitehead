import RequestProject.TopologicalSingular.SimplexCoordinates
import RequestProject.OrderNerveRealizationAffineCone
import RequestProject.OrderNerveRealizationStarAcyclic

namespace FiniteChains.Comb
open CategoryTheory Simplicial
open scoped unitInterval Classical

/-- The intersection of the open vertex stars indexed by a simplex. -/
def orderNerveRealizationSimplexOpenStar {P : Type} [PartialOrder P]
    {n : SimplexCategory} (s : (nerve P).obj (Opposite.op n)) :
    Set (orderNerveRealization P) :=
  {x | ∀ i, x ∈ orderNerveRealizationOpenStar P (s.obj i)}

theorem orderNerveRealizationSimplexOpenStar_isOpen {P : Type} [PartialOrder P]
    {n : SimplexCategory} (s : (nerve P).obj (Opposite.op n)) :
    IsOpen (orderNerveRealizationSimplexOpenStar s) := by
  convert isOpen_iInter_of_finite (fun i => orderNerveRealizationOpenStar_isOpen P (s.obj i)) using 1
  ext x
  simp [orderNerveRealizationSimplexOpenStar]

/-- All simplex-star intersections are nonempty, including degenerate simplices. -/
theorem orderNerveRealizationSimplexOpenStar_nonempty {P : Type} [PartialOrder P]
    {n : SimplexCategory} (s : (nerve P).obj (Opposite.op n)) :
    (orderNerveRealizationSimplexOpenStar s).Nonempty := by
  let w : SimplexCategory.toTop.obj n := ULift.up ((TopologicalSingular.simplexCoordinates n.len).symm stdSimplex.barycenter)
  have hw : ∀ i, 0 < w.down.weights i := by
    intro i
    change 0 < (TopologicalSingular.simplexCoordinates n.len
      ((TopologicalSingular.simplexCoordinates n.len).symm stdSimplex.barycenter)).val i
    rw [Homeomorph.apply_symm_apply]
    simp only [stdSimplex.barycenter]
    positivity
  refine ⟨orderNerveRealizationSimplex P s w, fun i => ?_⟩
  exact (orderNerveRealizationSimplex_mem_openStar_iff s w hw _).mpr ⟨i, rfl⟩

/-- When the vertices are universally comparable, affine contraction to their
barycenter preserves the entire open-star intersection. -/
theorem orderNerveRealizationSimplexOpenStar_contractible_of_comparable
    {P : Type} [PartialOrder P] {n : SimplexCategory}
    (s : (nerve P).obj (Opposite.op n))
    (hs : ∀ p i, p ≤ s.obj i ∨ s.obj i ≤ p) :
    ContractibleSpace (orderNerveRealizationSimplexOpenStar s) := by
  let w : SimplexCategory.toTop.obj n := ULift.up ((TopologicalSingular.simplexCoordinates n.len).symm stdSimplex.barycenter)
  have hw : ∀ i, 0 < w.down.weights i := by
    intro i
    change 0 < (TopologicalSingular.simplexCoordinates n.len
      ((TopologicalSingular.simplexCoordinates n.len).symm stdSimplex.barycenter)).val i
    rw [Homeomorph.apply_symm_apply]
    simp only [stdSimplex.barycenter]
    positivity
  let center : orderNerveRealizationSimplexOpenStar s :=
    ⟨orderNerveRealizationSimplex P s w, fun i =>
      (orderNerveRealizationSimplex_mem_openStar_iff s w hw _).mpr ⟨i, rfl⟩⟩
  apply (contractible_iff_id_nullhomotopic _).mpr
  refine ⟨center, ⟨?_⟩⟩
  exact
    { toFun := fun tx => ⟨orderNerveRealizationAffineCone s hs w tx.1 tx.2.val,
        fun i => orderNerveRealizationAffineCone_positive s hs w tx.1 tx.2.val
          (s.obj i) (tx.2.property i) (center.property i)⟩
      continuous_toFun := ((orderNerveRealizationAffineCone_continuous s hs w).comp
        (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))).subtype_mk _
      map_zero_left := fun x => Subtype.ext (orderNerveRealizationAffineCone_zero s hs w x.val)
      map_one_left := fun x => Subtype.ext (orderNerveRealizationAffineCone_one s hs w x.val) }

/-- Vertices simultaneously comparable to all vertices of a simplex. -/
def orderNerveSimplexStar {P : Type} [PartialOrder P]
    {n : SimplexCategory} (s : (nerve P).obj (Opposite.op n)) : Set P :=
  {p | ∀ i, p ≤ s.obj i ∨ s.obj i ≤ p}

def orderNerveSimplexStar_lift {P : Type} [PartialOrder P]
    {n : SimplexCategory} (s : (nerve P).obj (Opposite.op n)) :
    (nerve (orderNerveSimplexStar s)).obj (Opposite.op n) :=
  (show Monotone (fun i => (⟨s.obj i, fun j => by
      rcases le_total i j with h | h
      · exact Or.inl (leOfHom (s.map (homOfLE h)))
      · exact Or.inr (leOfHom (s.map (homOfLE h)))⟩ : orderNerveSimplexStar s)) from
    fun _ _ h => leOfHom (s.map (homOfLE h))).functor

theorem orderNerveRealizationSimplexOpenStar_subset_subcomplex {P : Type}
    [PartialOrder P] {n : SimplexCategory} (s : (nerve P).obj (Opposite.op n)) :
    orderNerveRealizationSimplexOpenStar s ⊆
      (orderNerveRealizationSubcomplex P (orderNerveSimplexStar s) :
        Set (orderNerveRealization P)) := by
  intro x hx p hp
  by_contra he
  apply hp
  intro i
  by_contra hi
  exact he (orderNerveRealizationOpenStar_subset_subcomplex (s.obj i) (hx i) p hi)

/-- Restricting to the common closed-star subposet preserves the actual
topology and every open-star membership condition. -/
noncomputable def orderNerveRealizationSimplexOpenStar_subtypeHomeomorph {P : Type}
    [PartialOrder P] {n : SimplexCategory} (s : (nerve P).obj (Opposite.op n)) :
    orderNerveRealizationSimplexOpenStar (orderNerveSimplexStar_lift s) ≃ₜ
      orderNerveRealizationSimplexOpenStar s :=
  ((orderNerveRealizationSubtypeHomeomorph (orderNerveSimplexStar s)).subtype
    (p := fun x => x ∈ orderNerveRealizationSimplexOpenStar (orderNerveSimplexStar_lift s))
    (q := fun x => x.val ∈ orderNerveRealizationSimplexOpenStar s) (by
      intro x
      change (∀ i, 0 < orderNerveRealizationCoordinates (orderNerveSimplexStar s) x
          ((orderNerveSimplexStar_lift s).obj i)) ↔
        (∀ i, 0 < orderNerveRealizationCoordinates P
          (orderNerveRealizationSubtypeHomeomorph (orderNerveSimplexStar s) x).val (s.obj i))
      rw [orderNerveRealizationSubtypeHomeomorph_coe]
      apply forall_congr'
      intro i
      exact (congrArg (fun r : ℝ => 0 < r)
        (orderNerveRealizationCoordinates_map_injective
          (Subtype.val : orderNerveSimplexStar s → P) (fun _ _ h => h)
          Subtype.val_injective x ((orderNerveSimplexStar_lift s).obj i))).symm.to_iff)).trans
    (orderNerveNestedCarrierHomeomorph _ _
      (orderNerveRealizationSimplexOpenStar_subset_subcomplex s)).symm

/-- Every simplex-indexed intersection of the actual open vertex stars is
contractible, with no finiteness condition on the ambient poset. -/
theorem orderNerveRealizationSimplexOpenStar_contractible {P : Type} [PartialOrder P]
    {n : SimplexCategory} (s : (nerve P).obj (Opposite.op n)) :
    ContractibleSpace (orderNerveRealizationSimplexOpenStar s) := by
  letI := orderNerveRealizationSimplexOpenStar_contractible_of_comparable
    (orderNerveSimplexStar_lift s) (fun p i => p.property i)
  exact (orderNerveRealizationSimplexOpenStar_subtypeHomeomorph s).symm.contractibleSpace

/-- The intersections are acyclic in the precise integral singular-homology
sense appearing in the original statement. -/
theorem orderNerveRealizationSimplexOpenStar_acyclic {P : Type} [PartialOrder P]
    {n : SimplexCategory} (s : (nerve P).obj (Opposite.op n)) :
    Whitehead.Acyclic (orderNerveRealizationSimplexOpenStar s) := by
  letI := orderNerveRealizationSimplexOpenStar_contractible s
  exact Whitehead.acyclic_of_contractible _

end FiniteChains.Comb
