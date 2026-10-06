module

public import RequestProject.FreshLoopTreeStrictness
public import RequestProject.StrictOrderComplex
public import RequestProject.OriginalCoverCellChains
public import RequestProject.PresIdentityCoverChains

@[expose] public section

/-! A triangle forces a non-tree edge, independently of the chosen
spanning tree. The canonical model always has such a triangle from its
dummy relator. This supplies a marked generator without another
stabilization of the descended chain. Awaiting final Lean verification. -/

noncomputable section
open scoped Classical
namespace FiniteChains.Comb.SpanningTree
universe u
variable {P : Type u} [PartialOrder P]

theorem nonempty_nonTree_of_strictTriangle (T : SpanningTree (strictOrderCx P))
    (t : StrictOrdTri P) : Nonempty (NonTree T) := by
  let e₀₁ : StrictOrdEdge P := ⟨(t.val.1, t.val.2.1), t.property.1⟩
  let e₁₂ : StrictOrdEdge P := ⟨(t.val.2.1, t.val.2.2), t.property.2⟩
  let e₀₂ : StrictOrdEdge P := ⟨(t.val.1, t.val.2.2), t.property.1.trans t.property.2⟩
  by_cases h₀₁ : T.isTree e₀₁
  · by_cases h₁₂ : T.isTree e₁₂
    · by_cases h₀₂ : T.isTree e₀₂
      · have h₁ := T.height_step_of_isTree h₀₁
        have h₂ := T.height_step_of_isTree h₁₂
        have h₃ := T.height_step_of_isTree h₀₂
        change (T.ht t.val.1 + 1 = T.ht t.val.2.1 ∨
          T.ht t.val.2.1 + 1 = T.ht t.val.1) at h₁
        change (T.ht t.val.2.1 + 1 = T.ht t.val.2.2 ∨
          T.ht t.val.2.2 + 1 = T.ht t.val.2.1) at h₂
        change (T.ht t.val.1 + 1 = T.ht t.val.2.2 ∨
          T.ht t.val.2.2 + 1 = T.ht t.val.1) at h₃
        omega
      · exact ⟨⟨e₀₂, h₀₂⟩⟩
    · exact ⟨⟨e₁₂, h₁₂⟩⟩
  · exact ⟨⟨e₀₁, h₀₁⟩⟩

end FiniteChains.Comb.SpanningTree

namespace FiniteChains.ClassicalCW
open Comb PresModel

def canonicalStrictTriangle (K : Whitehead.TwoComplex) : StrictOrdTri (CanonicalPos K) :=
  presCoverRelatorTriangle (canonicalWords K) id (IdentityChains.cover (canonicalWords K))
    (presCanonicalWords_positive (canonicalRelators K) (canonicalDummy K))
    ⟨(apexOf (canonicalWords K) (Sum.inr PUnit.unit), Sum.inr PUnit.unit), rfl⟩

def canonicalTreeGenerator (K : Whitehead.TwoComplex)
    (T : SpanningTree (strictOrderCx (CanonicalPos K))) : SpanningTree.NonTree T :=
  Classical.choice (T.nonempty_nonTree_of_strictTriangle (canonicalStrictTriangle K))

end FiniteChains.ClassicalCW
