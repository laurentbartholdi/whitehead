import RequestProject.ChamberQuotientOldStar
import RequestProject.ChamberQuotientEquivariantGeneration
import RequestProject.ChamberZConnected
import RequestProject.BlockSpinePres

/-! The actual intersection cover is a cover of the original attaching simplex poset. -/
namespace FiniteChains.Davis
open RACG Mirror Comb
universe u
variable {V : Type u} [DecidableEq V] {A : CommRel V}
  {X : Type u} [PartialOrder X] {att : NeSpx A →o X}

abbrev QPositiveOld := {p : Qpos A X att // InQOld p ∧ InQBaseStar p}

def qPositiveOldSimplex (p : QPositiveOld (att := att)) : NeSpx A := by
  rcases p with ⟨p, hp⟩
  cases p with
  | inl c =>
    exact ⟨c.1.spx, Finset.nonempty_iff_ne_empty.mpr (fun h => c.2 ⟨h, hp.2⟩), c.1.isSimplex⟩
  | inr x => exact False.elim hp.1

def qPositiveOldPoint (s : NeSpx A) : QPositiveOld (att := att) :=
  ⟨Sum.inl (posQCube s), trivial, rfl⟩

def qPositiveOldOrderIso : QPositiveOld (att := att) ≃o NeSpx A where
  toFun := qPositiveOldSimplex
  invFun := qPositiveOldPoint
  left_inv p := by
    rcases p with ⟨p, hp⟩
    cases p with
    | inl c =>
      apply Subtype.ext
      apply congrArg Sum.inl
      apply Subtype.ext
      apply QCube.ext'
      · rfl
      · intro v _
        exact (congrFun hp.2 v).symm
    | inr x => exact False.elim hp.1
  right_inv s := rfl
  map_rel_iff' := by
    rintro ⟨p, hp⟩ ⟨r, hr⟩
    cases p with
    | inr x => exact False.elim hp.1
    | inl c =>
      cases r with
      | inr x => exact False.elim hr.1
      | inl d =>
        constructor
        · intro h
          refine ⟨h, ?_⟩
          intro v _
          exact (congrFun hp.2 v).trans (congrFun hr.2 v).symm
        · exact fun h => h.1

abbrev QLiftedAttaching (a : Qpos A X att) :=
  {p : UOrder (Qpos A X att) a // InQOld (uOrderEnd p) ∧ InQBaseStar (uOrderEnd p)}

def qAttachingCoverEnd (a : Qpos A X att) (p : QLiftedAttaching a) : NeSpx A :=
  qPositiveOldSimplex ⟨uOrderEnd p.1, p.2⟩

variable [Fintype V]

/-- The cycles extracted by the old/star gluing lie on an actual covering of
the original attaching locus; no abstract surface identification is assumed. -/
theorem qAttachingCoverEnd_isPosetCover (x : X) (hx : IsConnected (orderCx X)) :
    IsPosetCover (qAttachingCoverEnd (qNew (A := A) (att := att) x)) := by
  letI : Nonempty X := ⟨x⟩
  have hc : IsConnected (orderCx (Qpos A X att)) := qpos_isConnected_of_zpos (zpos_isConnected hx)
  have hf := (uOrderEnd_isPosetCover hc).restriction
    (f := uOrderEnd (P := Qpos A X att) (a := qNew x))
    {p | InQOld p ∧ InQBaseStar p}
  exact hf.postcompose_orderIso qPositiveOldOrderIso

end FiniteChains.Davis
