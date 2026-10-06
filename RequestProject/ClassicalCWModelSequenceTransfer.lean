module

public import RequestProject.ClassicalCWOneTwoDiskTransfer
public import RequestProject.ClassicalCWSequentialChains

@[expose] public section

/-! Transfer a whole sequence of relative one/two-cell models to the
literal original CW complex. Each stage is constructed from the preceding
one; the initial open cells are consequently retained in the final common
ambient complex. -/

noncomputable section
namespace Whitehead
open FiniteChains.RelativeAttachment
open scoped Topology Classical

structure DiskExtensionModel (P Q : Type) [TopologicalSpace P] [TopologicalSpace Q] where
  oneCells : Type
  twoCells : Type
  oneAttaching : C(BoundaryFamily oneCells (Fin 1 → ℝ), P)
  twoAttaching : C(BoundaryFamily twoCells (Fin 2 → ℝ), DiskAttachment oneAttaching)
  comparison : ContinuousMap.HomotopyEquiv (DiskAttachment twoAttaching) Q

namespace DiskExtensionModel

variable {P Q : Type} [TopologicalSpace P] [TopologicalSpace Q] (M : DiskExtensionModel P Q)

def map : C(P, Q) := M.comparison.toFun.comp (oneTwoAttachmentMap M.oneAttaching M.twoAttaching)

theorem killsPi2_iff : KillsPi2 M.map ↔ KillsPi2 (oneTwoAttachmentMap M.oneAttaching M.twoAttaching) :=
  killsPi2_homotopyEquiv_postcomp_iff M.comparison _

end DiskExtensionModel

structure TransferredModelStage (P : Type) [TopologicalSpace P] where
  complex : TwoComplex
  comparison : ContinuousMap.HomotopyEquiv P complex

variable {P : ℕ → Type} [∀ i, TopologicalSpace (P i)]
  (M : ∀ i, DiskExtensionModel (P i) (P (i + 1)))
  (K : TwoComplex) (e₀ : ContinuousMap.HomotopyEquiv (P 0) K)

def transferredModelStage : (i : ℕ) → TransferredModelStage (P i)
  | 0 => ⟨K, e₀⟩
  | i + 1 =>
    let R := transferredModelStage i
    let T := oneTwoDiskTransfer R.complex R.comparison (M i).oneAttaching (M i).twoAttaching
    ⟨T.target, (M i).comparison.symm.trans T.comparison⟩

def transferredModelStep (i : ℕ) :
    CWCellEmbedding (transferredModelStage M K e₀ i).complex
      (transferredModelStage M K e₀ (i + 1)).complex :=
  (oneTwoDiskTransfer (transferredModelStage M K e₀ i).complex
    (transferredModelStage M K e₀ i).comparison (M i).oneAttaching (M i).twoAttaching).oldEmbedding

theorem transferredModelStep_killsPi2 (i : ℕ) (h : KillsPi2 (M i).map) :
    KillsPi2 (transferredModelStep M K e₀ i).map := by
  apply (OneTwoDiskTransfer.killsPi2_iff _ _ _ _
    (oneTwoDiskTransfer (transferredModelStage M K e₀ i).complex
      (transferredModelStage M K e₀ i).comparison (M i).oneAttaching (M i).twoAttaching)).mpr
  exact ((M i).killsPi2_iff).mp h

theorem transferredModelStep_proper (i : ℕ)
    (h : Nonempty (M i).oneCells ∨ Nonempty (M i).twoCells) :
    ∃ z : (transferredModelStage M K e₀ (i + 1)).complex,
      z ∉ Set.range (transferredModelStep M K e₀ i).map :=
  (oneTwoDiskTransfer (transferredModelStage M K e₀ i).complex
    (transferredModelStage M K e₀ i).comparison
    (M i).oneAttaching (M i).twoAttaching).proper h

theorem transferredModelStage_finite (n : ℕ) (hK : FiniteCells K)
    (hfin : ∀ i, i < n → Finite (M i).oneCells ∧ Finite (M i).twoCells) :
    FiniteCells (transferredModelStage M K e₀ n).complex := by
  have h : ∀ m, m ≤ n → FiniteCells (transferredModelStage M K e₀ m).complex := by
    intro m
    induction m with
    | zero => exact fun _ => hK
    | succ m ih =>
        intro hm
        have hc := hfin m (by omega)
        exact (oneTwoDiskTransfer (transferredModelStage M K e₀ m).complex
          (transferredModelStage M K e₀ m).comparison
          (M m).oneAttaching (M m).twoAttaching).finite
            (ih (by omega)) hc.1 hc.2
  exact h n le_rfl

include e₀ in
/-- All topological transfer and common-ambient construction steps are
discharged here. Applications supply the concrete relative models and
their already-derived zero-on-pi2 and strictness conclusions. -/
theorem hasChain_of_diskExtensionModels (n : ℕ)
    (hp : ∀ i, i < n → Nonempty (M i).oneCells ∨ Nonempty (M i).twoCells)
    (hz : ∀ i, i < n → KillsPi2 (M i).map)
    (finite : Bool)
    (hfin : finite = true → FiniteCells K ∧
      ∀ i, i < n → Finite (M i).oneCells ∧ Finite (M i).twoCells) :
    HasChain K n finite := by
  change HasChain (transferredModelStage M K e₀ 0).complex n finite
  apply hasChain_of_successive_cellEmbeddings (transferredModelStep M K e₀) n
    (fun i hi => transferredModelStep_proper M K e₀ i (hp i hi))
    (fun i hi => transferredModelStep_killsPi2 M K e₀ i (hz i hi)) finite
  intro hf
  exact transferredModelStage_finite M K e₀ n (hfin hf).1 (hfin hf).2

end Whitehead
