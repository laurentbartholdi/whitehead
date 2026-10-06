import RequestProject.ClassicalCWChainFixedBase
import RequestProject.ClassicalCWWordDiskModel
import Mathlib.Order.Fin.Basic

/-! A fixed initial presentation for every ambient CW chain of the given
original complex. The original cellwise homeomorphism is upgraded by
recharacterization, and all stage-zero choices are transported from K.
There is no remaining fixed-C0 or characteristic-map premise. Unverified. -/

noncomputable section
namespace FiniteChains.ClassicalCW.ChainWords
open ClassicalSkeletonAttachment ClassicalGraphModel RelativeAttachment PresModel Comb
open Set Topology
open scoped Classical
variable (D K : Whitehead.TwoComplex) {n : ℕ}
  (C : Fin (n + 1) → CWComplex.Subcomplex (Set.univ : Set K))
  (hC : Monotone C) (hconn : ∀ i, ConnectedSpace (C i : Set K))
  (T : SpanningTree (originalGraph D))
  (e : Whitehead.CWCellEmbedding D K)
  (hchart : ∀ m (j : RelCWComplex.cell (Set.univ : Set D) m) (x : Fin m → ℝ),
    RelCWComplex.map (C := (Set.univ : Set K)) m (e.cellIndex m j) x =
      e.map (RelCWComplex.map (C := (Set.univ : Set D)) m j x))
  (h₀ : C 0 = e.imageSubcomplex)

private def chartedGraphAt (S : CWComplex.Subcomplex (Set.univ : Set K))
    (hS : S = e.imageSubcomplex) : Hom (originalGraph D) (subcomplexGraph S) :=
  hS.symm ▸ e.graphHom hchart

private def chartedCellsAt (S : CWComplex.Subcomplex (Set.univ : Set K))
    (hS : S = e.imageSubcomplex) (m : ℕ) :
    RelCWComplex.cell (Set.univ : Set D) m ≃ RelCWComplex.cell (S : Set K) m :=
  hS.symm ▸ e.imageCellEquiv m

private theorem chartedGraphAt_injective_V (S : CWComplex.Subcomplex (Set.univ : Set K))
    (hS : S = e.imageSubcomplex) : Function.Injective (chartedGraphAt D K e hchart S hS).onV := by
  subst S
  exact e.graphHom_injective_V hchart

private theorem chartedGraphAt_injective_E (S : CWComplex.Subcomplex (Set.univ : Set K))
    (hS : S = e.imageSubcomplex) : Function.Injective (chartedGraphAt D K e hchart S hS).onE := by
  subst S
  exact e.graphHom_injective_E hchart

private theorem chartedWordAt_spec (S : CWComplex.Subcomplex (Set.univ : Set K))
    (hS : S = e.imageSubcomplex) (j : RelCWComplex.cell (Set.univ : Set D) 2) :
    (subcomplexCellBoundary S (chartedCellsAt D K e S hS 2 j)).Homotopic
      ((fixedGraphWord D j).map (chartedGraphAt D K e hchart S hS)).boundaryMap := by
  subst S
  exact e.fixedGraphWord_transport hchart j

def chartedInitialGraph : Hom (originalGraph D) (subcomplexGraph (C 0)) :=
  chartedGraphAt D K e hchart (C 0) h₀

def chartedInitialCells (m : ℕ) :
    RelCWComplex.cell (Set.univ : Set D) m ≃ RelCWComplex.cell (C 0 : Set K) m :=
  chartedCellsAt D K e (C 0) h₀ m

theorem chartedInitialGraph_injective_V : Function.Injective (chartedInitialGraph D K C e hchart h₀).onV :=
  chartedGraphAt_injective_V D K e hchart (C 0) h₀

theorem chartedInitialGraph_injective_E : Function.Injective (chartedInitialGraph D K C e hchart h₀).onE :=
  chartedGraphAt_injective_E D K e hchart (C 0) h₀

theorem chartedInitialWord_spec (j : RelCWComplex.cell (Set.univ : Set D) 2) :
    (subcomplexCellBoundary (C 0) (chartedInitialCells D K C e h₀ 2 j)).Homotopic
      ((fixedGraphWord D j).map (chartedInitialGraph D K C e hchart h₀)).boundaryMap :=
  chartedWordAt_spec D K e hchart (C 0) h₀ j

def chartedInitialChoices : Choices C :=
  seededChoices K C
    (fun j => (fixedGraphWord D ((chartedInitialCells D K C e h₀ 2).symm j)).map
      (chartedInitialGraph D K C e hchart h₀))
    (fun j => by simpa only [Equiv.apply_symm_apply] using
      chartedInitialWord_spec D K C e hchart h₀ ((chartedInitialCells D K C e h₀ 2).symm j))

theorem chartedInitialChoices_old (j : RelCWComplex.cell (Set.univ : Set D) 2) :
    (chartedInitialChoices D K C e hchart h₀).cellWord 0 (chartedInitialCells D K C e h₀ 2 j) =
      (fixedGraphWord D j).map (chartedInitialGraph D K C e hchart h₀) := by
  rw [chartedInitialChoices, seededChoices_zero, Equiv.symm_apply_apply]

def chartedFixedPresChainFS
    (hkill : ∀ i : Fin n, Whitehead.KillsPi2
      (⟨Set.inclusion (hC (show i.castSucc ≤ i.succ from Nat.le_succ i.val)),
        continuous_inclusion _⟩ : C((C i.castSucc : Set K), (C i.succ : Set K)))) :
    PresChainFS (fixedRelators D T) n := by
  letI : Choices C := chartedInitialChoices D K C e hchart h₀
  let g := chartedInitialGraph D K C e hchart h₀
  let htree := SpanningTree.exists_extension g
    (graph_connected K C hC hconn 0) T.root T
    (chartedInitialGraph_injective_V D K C e hchart h₀)
    (chartedInitialGraph_injective_E D K C e hchart h₀)
  let U := Classical.choose htree
  have hU := (Classical.choose_spec htree).2
  letI : TreeChoice K C := seededTreeChoice K C U
  have ht : ∀ a, (chainTree K C hC hconn 0).isTree (g.onE a) ↔ T.isTree a := by
    rw [chainTree_zero K C hC hconn U rfl]
    exact hU
  exact fixedPresChainFS D K C hC hconn T g
    (chartedInitialGraph_injective_E D K C e hchart h₀)
    (chartedInitialCells D K C e h₀ 2).toEmbedding
    (chartedInitialChoices_old D K C e hchart h₀) ht hkill

end FiniteChains.ClassicalCW.ChainWords

namespace Whitehead
open FiniteChains FiniteChains.ClassicalCW FiniteChains.ClassicalCW.ChainWords
open Set Topology
open scoped Classical
variable (K : TwoComplex) (T : Comb.SpanningTree (originalGraph K))

theorem fixedPresChainFS_of_hasChain {n : ℕ} {finite : Bool} (h : HasChain K n finite) :
    Nonempty (PresChainFS (fixedRelators K T) n) := by
  obtain ⟨L, C, e, he, _hfin, hconn, hstep⟩ := h
  have hC : Monotone C := Fin.monotone_iff_le_succ.mpr (fun i => (hstep i).choose)
  let f := initialCellEmbedding (C 0) e he
  let L' := f.recharacterizedComplex
  let C' (i : Fin (n + 1)) : CWComplex.Subcomplex (Set.univ : Set L') := f.recharacterizedSubcomplex (C i)
  have hC' : Monotone C' := hC
  have hconn' : ∀ i, ConnectedSpace (C' i : Set L') := hconn
  let f' : CWCellEmbedding K L' := f.recharacterizedEmbedding
  have h₀ : C' 0 = f'.imageSubcomplex := by
    apply SetLike.coe_injective
    exact (initialCellEmbedding_range (C 0) e he).symm
  have hchart : ∀ m (j : RelCWComplex.cell (Set.univ : Set K) m) (x : Fin m → ℝ),
      RelCWComplex.map (C := (Set.univ : Set L')) m (f'.cellIndex m j) x =
        f'.map (RelCWComplex.map (C := (Set.univ : Set K)) m j x) :=
    f.recharacterizedEmbedding_characteristic
  have hz : ∀ i : Fin n, KillsPi2
      (⟨Set.inclusion (hC' (show i.castSucc ≤ i.succ from Nat.le_succ i.val)),
        continuous_inclusion _⟩ : C((C' i.castSucc : Set L'), (C' i.succ : Set L'))) := by
    intro i
    exact (hstep i).choose_spec.2
  exact ⟨chartedFixedPresChainFS K L' C' hC' hconn' T f' hchart h₀ hz⟩

/-- The base is fixed before any ambient chain is chosen. -/
theorem fixedPresChainsFS_of_original_chains
    (h : ∀ n : ℕ, 1 ≤ n → HasChain K n false) :
    ∀ n : ℕ, Nonempty (PresChainFS (fixedRelators K T) n) := by
  intro n
  cases n with
  | zero =>
      obtain ⟨L, C, e, he, hf, hc, _hs⟩ := h 1 le_rfl
      apply fixedPresChainFS_of_hasChain K T (finite := false)
      refine ⟨L, (fun _ : Fin 1 => C 0), e, he, hf, (fun _ => hc 0), ?_⟩
      intro i
      exact Fin.elim0 i
  | succ n => exact fixedPresChainFS_of_hasChain K T (h (n + 1) (Nat.succ_pos n))

theorem fixedPresentation_hasAcyclicRegularCover_of_original_chains
    (h : ∀ n : ℕ, 1 ≤ n → HasChain K n false) :
    Comb.HasAcyclicRegularCover (Comb.presComplex (fixedRelators K T)) :=
  presComplex_hasAcyclicRegularCover_of_presChainsFS (fixedRelators K T)
    (fixedPresChainsFS_of_original_chains K T h)

end Whitehead
