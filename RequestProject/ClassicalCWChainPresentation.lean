import RequestProject.ClassicalCWChainCanonicalHomotopies
import RequestProject.PresWordEmbeddingCombPi2
import RequestProject.PresChainTopologicalFinsupp

/-! The actual topological pi2 hypotheses of an original CW filtration
give a finite-support presentation chain. The initial presentation here
is the simultaneous model of this filtration's C0. Identifying it with
one fixed model across different ambient filtrations is a separate step.
Unverified source. -/

noncomputable section
namespace FiniteChains.ClassicalCW.ChainWords
open ClassicalSkeletonAttachment ClassicalGraphModel RelativeAttachment PresModel
open Set Topology
open scoped Classical
variable (K : Whitehead.TwoComplex) {n : ℕ}
  (C : Fin (n + 1) → CWComplex.Subcomplex (Set.univ : Set K))
  (hC : Monotone C) (hconn : ∀ i, ConnectedSpace (C i : Set K))
  [Choices C]
  [TreeChoice K C]

theorem canonicalInclusion_zeroPi2_iff {i k : Fin (n + 1)} (hik : i ≤ k) :
    Comb.ZeroPi2 (Comb.presInclHom (canonicalGenInclusion K C hC hconn hik)
      (canonicalGenInclusion K C hC hconn hik).injective
      (canonicalRelators K C hC hconn i) (canonicalRelators K C hC hconn k)
      (canonicalCellInclusion K C hC hik) (canonicalRelators_natural K C hC hconn hik)) ↔
      Whitehead.KillsPi2 (⟨Set.inclusion (hC hik), continuous_inclusion (hC hik)⟩ :
        C((C i : Set K), (C k : Set K))) := by
  let e := canonicalWordEmbedding K C hC hconn hik
  have h₁ := e.killsPi2_iff_combPi2
    (fun j => List.length_pos_of_ne_nil (canonicalWords_ne_nil K C hC hconn i j))
    (fun j => List.length_pos_of_ne_nil (canonicalWords_ne_nil K C hC hconn k j))
    (canonicalRelators K C hC hconn i) (canonicalRelators K C hC hconn k)
    (canonicalWords_mk K C hC hconn i) (canonicalWords_mk K C hC hconn k)
  have h₂ := e.classicalWordDiskMap_killsPi2_iff
    (canonicalWords_ne_nil K C hC hconn i) (canonicalWords_ne_nil K C hC hconn k)
  exact h₁.symm.trans (h₂.symm.trans (canonicalDiskInclusion_killsPi2_iff K C hC hconn hik))

def canonicalPresChainTopFS
    (hkill : ∀ i : Fin n, Whitehead.KillsPi2
      (⟨Set.inclusion (hC (show i.castSucc ≤ i.succ from Nat.le_succ i.val)),
        continuous_inclusion _⟩ : C((C i.castSucc : Set K), (C i.succ : Set K)))) :
    PresChainTopFS (canonicalRelators K C hC hconn 0) n where
  gen r := CanonicalGen K C hC hconn (boundedStage n r)
  cell r := CanonicalRel K C (boundedStage n r)
  decGen _ := inferInstance
  rel r := canonicalRelators K C hC hconn (boundedStage n r)
  genIncl r := canonicalGenInclusion K C hC hconn (boundedStage_monotone n (Nat.le_succ r))
  genIncl_injective r := (canonicalGenInclusion K C hC hconn
    (boundedStage_monotone n (Nat.le_succ r))).injective
  cellIncl r := canonicalCellInclusion K C hC (boundedStage_monotone n (Nat.le_succ r))
  cellIncl_injective r := (canonicalCellInclusion K C hC
    (boundedStage_monotone n (Nat.le_succ r))).injective
  rel_incl r := canonicalRelators_natural K C hC hconn (boundedStage_monotone n (Nat.le_succ r))
  baseGen := id
  baseGen_injective := Function.injective_id
  baseCell := id
  baseCell_injective := Function.injective_id
  rel_base j := (FreeGroup.map.id _).symm
  zero_pi2 := by
    intro r hr
    let i : Fin n := ⟨r, hr⟩
    have H := (canonicalInclusion_zeroPi2_iff K C hC hconn
      (show i.castSucc ≤ i.succ from Nat.le_succ r)).mpr (hkill i)
    have hleft : boundedStage n r = i.castSucc := Fin.ext (Nat.min_eq_left (Nat.le_of_lt hr))
    have hright : boundedStage n (r + 1) = i.succ := Fin.ext (Nat.min_eq_left (Nat.succ_le_of_lt hr))
    change Comb.ZeroPi2 (Comb.presInclHom
      (canonicalGenInclusion K C hC hconn (boundedStage_monotone n (Nat.le_succ r))) _
      (canonicalRelators K C hC hconn (boundedStage n r))
      (canonicalRelators K C hC hconn (boundedStage n (r + 1)))
      (canonicalCellInclusion K C hC (boundedStage_monotone n (Nat.le_succ r))) _)
    have hh (a b : Fin (n + 1)) (hab : a ≤ b)
        (ha : a = i.castSucc) (hb : b = i.succ) :
        Comb.ZeroPi2 (Comb.presInclHom (canonicalGenInclusion K C hC hconn hab)
          (canonicalGenInclusion K C hC hconn hab).injective
          (canonicalRelators K C hC hconn a) (canonicalRelators K C hC hconn b)
          (canonicalCellInclusion K C hC hab) (canonicalRelators_natural K C hC hconn hab)) := by
      subst a
      subst b
      exact H
    exact hh _ _ _ hleft hright

def canonicalPresChainFS
    (hkill : ∀ i : Fin n, Whitehead.KillsPi2
      (⟨Set.inclusion (hC (show i.castSucc ≤ i.succ from Nat.le_succ i.val)),
        continuous_inclusion _⟩ : C((C i.castSucc : Set K), (C i.succ : Set K)))) :
    PresChainFS (canonicalRelators K C hC hconn 0) n :=
  (canonicalPresChainTopFS K C hC hconn hkill).toPresChainFS

end FiniteChains.ClassicalCW.ChainWords
