module

public import RequestProject.OrderNerveRealizationSubtypeHomeomorph
public import RequestProject.OrderNerveTwoComplex

@[expose] public section

namespace FiniteChains.Comb
open CategoryTheory Simplicial Topology
open scoped Classical

/-- Lift a selected nondegenerate ambient simplex to a nondegenerate subtype simplex. -/
def orderNerveSelectedSubtypeCell {P : Type} [PartialOrder P] (A : Set P) {n : ℕ}
    (s : {s : (nerve P).nonDegenerate n // ∀ i, s.val.obj i ∈ A}) :
    (nerve A).nonDegenerate n :=
  ⟨orderNerveSimplexSubtype A s.val.val s.property, by
    apply (PartialOrder.mem_nerve_nonDegenerate_iff_strictMono _).mpr
    intro i j hij
    exact ((PartialOrder.mem_nerve_nonDegenerate_iff_strictMono s.val.val).mp
      s.val.property) hij⟩

/-- Actual cells of an induced-subposet realization correspond to the selected ambient cells. -/
def orderNerveSubtypeCellEquiv {P : Type} [PartialOrder P] (A : Set P) (n : ℕ) :
    (nerve A).nonDegenerate n ≃
      {s : (nerve P).nonDegenerate n // ∀ i, s.val.obj i ∈ A} where
  toFun s := ⟨orderNerveSubtypeCell A s, fun i => (s.val.obj i).property⟩
  invFun s := orderNerveSelectedSubtypeCell A s
  left_inv s := by
    apply Subtype.ext
    exact CategoryTheory.Functor.ext (fun _ => Subtype.ext rfl)
  right_inv s := by
    apply Subtype.ext
    apply Subtype.ext
    exact CategoryTheory.Functor.ext (fun _ => rfl)

/-- The carrier homeomorphism preserves every open cell with the actual cell bijection. -/
theorem orderNerveRealizationSubtypeHomeomorph_openCell {P : Type} [PartialOrder P]
    (A : Set P) (n : ℕ) (s : (nerve A).nonDegenerate n) :
    (fun x => (orderNerveRealizationSubtypeHomeomorph A x).val) ''
        CWComplex.openCell (C := (Set.univ : Set (orderNerveRealization A))) n s =
      CWComplex.openCell (C := (Set.univ : Set (orderNerveRealization P))) n
        (orderNerveSubtypeCellEquiv A n s).val := by
  exact orderNerveRealizationSubtype_openCell A s

/-- The exact initial-identification condition of the submission holds for induced subposets. -/
theorem orderNerveRealizationSubtype_initialIdentification {P : Type} [PartialOrder P]
    (A : Set P) [Nonempty P] [Nonempty A] [(nerve P).HasDimensionLE 2]
    [(nerve A).HasDimensionLE 2] (hP : IsConnected (orderCx P))
    (hA : IsConnected (orderCx A)) :
    @Whitehead.InitialIdentification (orderNerveTwoComplex A hA)
      (orderNerveTwoComplex P hP) (orderNerveRealizationSubcomplex P A)
      (orderNerveRealizationSubtypeHomeomorph A) := by
  intro n
  exact ⟨orderNerveSubtypeCellEquiv A n,
    orderNerveRealizationSubtypeHomeomorph_openCell A n⟩

/-- Induced subposets inherit the actual nerve dimension bound. -/
theorem orderNerveSubtype_hasDimensionLE {P : Type} [PartialOrder P] (A : Set P)
    (d : ℕ) [(nerve P).HasDimensionLE d] : (nerve A).HasDimensionLE d := by
  constructor
  intro n hn
  apply Set.eq_univ_of_forall
  intro s
  rw [SSet.mem_degenerate_iff_notMem_nonDegenerate]
  intro hs
  have hd := (nerve P).dim_le_of_nonDegenerate (orderNerveSubtypeCell A ⟨s, hs⟩) d
  omega

/-- A combinatorially connected induced subposet gives a connected supported CW carrier. -/
theorem orderNerveRealizationSubcomplex_connectedSpace {P : Type} [PartialOrder P]
    (A : Set P) [Nonempty A] (hA : IsConnected (orderCx A)) :
    ConnectedSpace (orderNerveRealizationSubcomplex P A : Set (orderNerveRealization P)) := by
  letI := orderNerveRealization_pathConnectedSpace A hA
  exact (orderNerveRealizationSubtypeHomeomorph A).surjective.connectedSpace
    (orderNerveRealizationSubtypeHomeomorph A).continuous

end FiniteChains.Comb
