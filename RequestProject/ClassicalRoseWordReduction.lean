module

public import RequestProject.HomeomorphContinuousMap
public import RequestProject.PresRoseAffineWordReading
public import RequestProject.SquareBoundaryLoopQuotient
public import Mathlib.GroupTheory.FreeGroup.Reduce

@[expose] public section

/-! Free reduction and insertion of a cancelling pair give actual based
path homotopies in the literal disk rose, and hence actual homotopies of
disk attaching maps. Pending Lean verification. -/

noncomputable section
open scoped Classical unitInterval Topology
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains.PresModel
open ClassicalGraphModel RelativeAttachment

variable {A : Type}

theorem classicalRoseRead_append (l m : List (A × Bool)) :
    ((classicalRoseRead l).trans (classicalRoseRead m)).Homotopic (classicalRoseRead (l ++ m)) := by
  induction l with
  | nil => exact Path.Homotopic.refl_trans _
  | cons p l ih =>
    rcases p with ⟨a, b⟩
    exact (Path.Homotopic.trans_assoc _ _ _).trans ((Path.Homotopic.refl _).hcomp ih)

theorem classicalRoseRead_cancelHead (a : A) (b : Bool) (l : List (A × Bool)) :
    (classicalRoseRead ((a, b) :: (a, !b) :: l)).Homotopic (classicalRoseRead l) := by
  cases b
  · change (((graphEdgePath (roseAttaching A) a).symm).trans
      ((graphEdgePath (roseAttaching A) a).trans (classicalRoseRead l))).Homotopic _
    exact (Path.Homotopic.trans_assoc _ _ _).symm.trans
      (((Path.Homotopic.symm_trans _).hcomp (Path.Homotopic.refl _)).trans
        (Path.Homotopic.refl_trans _))
  · change ((graphEdgePath (roseAttaching A) a).trans
      (((graphEdgePath (roseAttaching A) a).symm).trans (classicalRoseRead l))).Homotopic _
    exact (Path.Homotopic.trans_assoc _ _ _).symm.trans
      (((Path.Homotopic.trans_symm _).hcomp (Path.Homotopic.refl _)).trans
        (Path.Homotopic.refl_trans _))

theorem classicalRoseRead_cancelPair (l r : List (A × Bool)) (a : A) (b : Bool) :
    (classicalRoseRead (l ++ (a, b) :: (a, !b) :: r)).Homotopic (classicalRoseRead (l ++ r)) :=
  (classicalRoseRead_append l _).symm.trans
    (((Path.Homotopic.refl _).hcomp (classicalRoseRead_cancelHead a b r)).trans
      (classicalRoseRead_append l r))

theorem classicalRoseRead_homotopic_of_step {l m : List (A × Bool)} (h : FreeGroup.Red.Step l m) :
    (classicalRoseRead l).Homotopic (classicalRoseRead m) := by
  cases h with
  | not => exact classicalRoseRead_cancelPair _ _ _ _

theorem classicalRoseRead_homotopic_of_red {l m : List (A × Bool)} (h : FreeGroup.Red l m) :
    (classicalRoseRead l).Homotopic (classicalRoseRead m) := by
  induction h with
  | refl => exact Path.Homotopic.refl _
  | tail _ hstep ih => exact ih.trans (classicalRoseRead_homotopic_of_step hstep)

/-- Equality in the free group is realized by an actual fixed-endpoint
homotopy of the continuous word paths. -/
theorem classicalRoseRead_homotopic_of_mk_eq {l m : List (A × Bool)}
    (h : FreeGroup.mk l = FreeGroup.mk m) :
    (classicalRoseRead l).Homotopic (classicalRoseRead m) := by
  obtain ⟨r, hl, hm⟩ := FreeGroup.Red.exact.mp h
  exact (classicalRoseRead_homotopic_of_red hl).trans (classicalRoseRead_homotopic_of_red hm).symm

theorem classicalRoseRead_homotopic_toWord (l : List (A × Bool)) :
    (classicalRoseRead l).Homotopic (classicalRoseRead (FreeGroup.mk l).toWord) := by
  classical
  exact classicalRoseRead_homotopic_of_mk_eq FreeGroup.mk_toWord.symm

theorem classicalRoseRead_homotopic_padded_toWord (l : List (A × Bool)) (a : A) :
    (classicalRoseRead l).Homotopic
      (classicalRoseRead ((FreeGroup.mk l).toWord ++ [(a, true), (a, false)])) := by
  classical
  exact (classicalRoseRead_homotopic_toWord l).trans
    (by simpa only [List.append_nil, Bool.not_true] using
      (classicalRoseRead_cancelPair (FreeGroup.mk l).toWord [] a true).symm)

def classicalRoseWordBoundary (l : List (A × Bool)) :
    C(UnitBoundary (Fin 2 → ℝ), ClassicalGraphModel.Rose A) :=
  (squareLoopDesc (classicalRoseRead l)).comp unitBoundarySquareHomeomorph.toContinuousMap

theorem classicalRoseWordBoundary_homotopic_of_read {l m : List (A × Bool)}
    (h : (classicalRoseRead l).Homotopic (classicalRoseRead m)) :
    (classicalRoseWordBoundary l).Homotopic (classicalRoseWordBoundary m) :=
  (squareLoopDesc_homotopic h).comp
    (ContinuousMap.Homotopic.refl unitBoundarySquareHomeomorph.toContinuousMap)

theorem classicalRoseWordBoundary_homotopic_of_mk_eq {l m : List (A × Bool)}
    (h : FreeGroup.mk l = FreeGroup.mk m) :
    (classicalRoseWordBoundary l).Homotopic (classicalRoseWordBoundary m) :=
  classicalRoseWordBoundary_homotopic_of_read (classicalRoseRead_homotopic_of_mk_eq h)

theorem classicalRoseWordBoundary_homotopic_toWord (l : List (A × Bool)) :
    (classicalRoseWordBoundary l).Homotopic (classicalRoseWordBoundary (FreeGroup.mk l).toWord) :=
  classicalRoseWordBoundary_homotopic_of_read (classicalRoseRead_homotopic_toWord l)

theorem classicalRoseWordBoundary_homotopic_padded_toWord (l : List (A × Bool)) (a : A) :
    (classicalRoseWordBoundary l).Homotopic
      (classicalRoseWordBoundary ((FreeGroup.mk l).toWord ++ [(a, true), (a, false)])) :=
  classicalRoseWordBoundary_homotopic_of_read (classicalRoseRead_homotopic_padded_toWord l a)

end FiniteChains.PresModel
