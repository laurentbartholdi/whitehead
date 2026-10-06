import RequestProject.ClassicalCWCanonicalPresentation
import RequestProject.AcyclicPresentationOriginalChains

/-! Original-cell-preserving chains for every acyclic connected CW
two-complex. The finite theorem is precisely the finite acyclic clause
of Whitehead.MainClaim. The original CW model, matrix condition, and
initial comparison are all supplied by constructions. This source has
not yet undergone the final Lean verification. -/

noncomputable section
open scoped Classical

namespace Whitehead
open FiniteChains FiniteChains.ClassicalCW FiniteChains.RelativeNormalForm

theorem canonical_expMatrix_bijective_of_acyclic
    (K : TwoComplex) (hK : Acyclic K) :
    Function.Bijective (expMatrix.{0, 0} (canonicalRelators K)) :=
  actual_expMatrix_bijective_of_acyclic (canonicalRelators K) K hK (canonicalDummy K)
    (originalClassicalPresWordDiskEquiv K).symm

theorem hasChain_of_acyclic (K : TwoComplex) (hK : Acyclic K)
    (n : ℕ) (hn : 1 ≤ n) : HasChain K n false := by
  cases n with
  | zero => omega
  | succ n =>
      exact actual_hasOriginalChain_of_acyclic (canonicalRelators K) K hK
        (canonicalDummy K) (originalClassicalPresWordDiskEquiv K).symm n

theorem hasFiniteChain_of_acyclic (K : TwoComplex) (hfinite : FiniteCells K)
    (hK : Acyclic K) (n : ℕ) (hn : 1 ≤ n) : HasChain K n true := by
  letI := canonicalGen_finite K hfinite
  letI := canonicalRel_finite K hfinite
  cases n with
  | zero => omega
  | succ n =>
      exact actual_hasOriginalFiniteChain_of_acyclic (canonicalRelators K) K hfinite hK
        (canonicalDummy K) (originalClassicalPresWordDiskEquiv K).symm n

/-- The full finite acyclic clause with the exact quantifiers from the
original challenge. This does not assert the regular-cover equivalence. -/
theorem original_finite_acyclic_clause :
    ∀ K : TwoComplex, FiniteCells K → Acyclic K →
      ∀ n : ℕ, 1 ≤ n → HasChain K n true :=
  hasFiniteChain_of_acyclic

end Whitehead
