import RequestProject.CombPi2
import RequestProject.CombPi1Conj

/-!
# Universal-cover transport along an actual path

A path `a : x ⟶ y` gives a cellular map from the universal cover based at `y`
to the universal cover based at `x`, by prefixing `a` to every represented
path.  Its projection is the identity on every underlying cell.  The map
intertwines deck transformations by the actual conjugation `pi1Conj ha`.
No equality of base points or connectedness hypothesis is used.


-/

namespace FiniteChains.Comb

universe u

variable {K : Complex2.{u}} {x y : K.V} {a : List (K.E × Bool)}
  (ha : IsPath K.src K.tgt a x y)

/-- Prefix the actual path from `x` to `y` to a path starting at `y`. -/
def pathTransportP (p : PathFrom K y) : PathFrom K x :=
  ⟨a ++ p.1, by
    rw [endpt_append, endpt_eq_of_isPath ha]
    exact ha.append p.2⟩

theorem endpt_pathTransportP (p : PathFrom K y) :
    endpt K x (pathTransportP ha p).1 = endpt K y p.1 := by
  change endpt K x (a ++ p.1) = endpt K y p.1
  rw [endpt_append, endpt_eq_of_isPath ha]

/-- Prefixing descends to homotopy classes of paths. -/
def pathTransportV (c : UV K y) : UV K x :=
  Quotient.map (pathTransportP ha) (by
    intro p q hpq
    change Htpy K x (endpt K x (pathTransportP ha p).1)
      (pathTransportP ha p).1 (pathTransportP ha q).1
    rw [endpt_pathTransportP]
    exact Htpy.append_congr ha p.2 (Htpy.refl _) hpq) c

@[simp] theorem pathTransportV_mk (p : PathFrom K y) :
    pathTransportV ha (UV.mk p) = UV.mk (pathTransportP ha p) := rfl

@[simp] theorem endV_pathTransportV (c : UV K y) :
    endV (pathTransportV ha c) = endV c := by
  induction c using UV.ind with
  | h p => exact endpt_pathTransportP ha p

/-- Prefixing commutes with extending a path by an edge, including the
convention that an edge with the wrong source leaves a path unchanged. -/
theorem extend_pathTransportV (eb : K.E × Bool) (c : UV K y) :
    extend eb (pathTransportV ha c) = pathTransportV ha (extend eb c) := by
  induction c using UV.ind with
  | h p =>
      have hl : (extendP eb (pathTransportP ha p)).1 =
          (pathTransportP ha (extendP eb p)).1 := by
        by_cases h : endpt K y p.1 = germSrc K.src K.tgt eb
        · have h' : endpt K x (pathTransportP ha p).1 = germSrc K.src K.tgt eb := by
            rw [endpt_pathTransportP]
            exact h
          rw [extendP_pos h']
          change (a ++ p.1) ++ [eb] = a ++ (extendP eb p).1
          rw [extendP_pos h]
          exact List.append_assoc _ _ _
        · have h' : ¬ endpt K x (pathTransportP ha p).1 = germSrc K.src K.tgt eb := by
            rw [endpt_pathTransportP]
            exact h
          rw [extendP_neg h']
          change a ++ p.1 = a ++ (extendP eb p).1
          rw [extendP_neg h]
      apply UV.sound
      change Htpy K x (endpt K x (extendP eb (pathTransportP ha p)).1)
        (extendP eb (pathTransportP ha p)).1 (pathTransportP ha (extendP eb p)).1
      rw [hl]
      exact Htpy.refl _

/-- Transport an edge by prefixing the path attached to its initial vertex. -/
def pathTransportE (e : UE K y) : UE K x :=
  ⟨(pathTransportV ha e.1.1, e.1.2), by rw [endV_pathTransportV]; exact e.2⟩

/-- Transport a face by prefixing the path attached to its base vertex. -/
def pathTransportF (t : UF K y) : UF K x :=
  ⟨(pathTransportV ha t.1.1, t.1.2), by rw [endV_pathTransportV]; exact t.2⟩

theorem liftGerm_pathTransportV {c : UV K y} {eb : K.E × Bool}
    (h : endV c = germSrc K.src K.tgt eb)
    (h' : endV (pathTransportV ha c) = germSrc K.src K.tgt eb) :
    liftGerm (pathTransportV ha c) eb h' =
      (pathTransportE ha (liftGerm c eb h).1, (liftGerm c eb h).2) := by
  obtain ⟨e, b⟩ := eb
  cases b with
  | true => rfl
  | false =>
      refine Prod.ext ?_ rfl
      apply Subtype.ext
      exact Prod.ext (extend_pathTransportV ha (e, false) c) rfl

theorem uLiftPath_pathTransportV :
    ∀ (p : List (K.E × Bool)) (c : UV K y) (z : K.V),
      IsPath K.src K.tgt p (endV c) z →
        uLiftPath p (pathTransportV ha c) =
          (uLiftPath p c).map (fun eb => (pathTransportE ha eb.1, eb.2)) := by
  intro p
  induction p with
  | nil => intro c z _; rfl
  | cons eb p ih =>
      intro c z hp
      have h : endV c = germSrc K.src K.tgt eb := hp.1
      have h' : endV (pathTransportV ha c) = germSrc K.src K.tgt eb := by
        rw [endV_pathTransportV]
        exact h
      rw [uLiftPath_cons h', uLiftPath_cons h, List.map_cons,
        liftGerm_pathTransportV ha h h', extend_pathTransportV ha eb c,
        ih (extend eb c) z (by rw [endV_extend h]; exact hp.2)]

/-- The actual cellular change of universal-cover base along `a : x ⟶ y`. -/
noncomputable def uCoverPathTransport : Hom (uCover K y) (uCover K x) where
  onV := pathTransportV ha
  onE := pathTransportE ha
  onF := pathTransportF ha
  src_onE := fun _ => rfl
  tgt_onE := fun e => extend_pathTransportV ha (e.1.2, true) e.1.1
  base_onF := fun _ => rfl
  att_onF := by
    intro t
    change uLiftPath (K.att t.1.2) (pathTransportV ha t.1.1) = _
    apply uLiftPath_pathTransportV
    rw [t.2]
    exact K.att_isLoop t.1.2

theorem uCoverPathTransport_base :
    (uCoverPathTransport ha).onV (UV.base K y) =
      UV.mk ⟨a, by rw [endpt_eq_of_isPath ha]; exact ha⟩ := by
  change UV.mk (pathTransportP ha ⟨[], rfl⟩) = _
  apply congrArg UV.mk
  exact Subtype.ext (List.append_nil a)

theorem uCoverPathTransport_vertex (c : UV K y) :
    endV ((uCoverPathTransport ha).onV c) = endV c :=
  endV_pathTransportV ha c

theorem uCoverPathTransport_edge (e : UE K y) :
    ((uCoverPathTransport ha).onE e).1.2 = e.1.2 := rfl

theorem uCoverPathTransport_face (t : UF K y) :
    ((uCoverPathTransport ha).onF t).1.2 = t.1.2 := rfl

/-- Prefix transport intertwines the deck actions by conjugation along the same path. -/
theorem uCoverPathTransport_deckV (γ : Pi1 K y) (c : UV K y) :
    (uCoverPathTransport ha).onV (deckV γ c) =
      deckV (pi1Conj ha γ) ((uCoverPathTransport ha).onV c) := by
  induction γ using Quotient.ind with
  | _ g =>
      induction c using UV.ind with
      | h p =>
          apply UV.sound
          change Htpy K x (endpt K x (a ++ (g.1 ++ p.1)))
            (a ++ (g.1 ++ p.1)) ((a ++ g.1 ++ revPath a) ++ (a ++ p.1))
          rw [endpt_append, endpt_eq_of_isPath ha,
            endpt_append, endpt_eq_of_isPath g.2]
          have h := (htpy_revPath_append ha).congr_append (ha.append g.2) p.2
          simpa only [List.append_assoc, List.nil_append] using h.symm

theorem uCoverPathTransport_deckE (γ : Pi1 K y) (e : UE K y) :
    (uCoverPathTransport ha).onE (deckE γ e) =
      deckE (pi1Conj ha γ) ((uCoverPathTransport ha).onE e) := by
  apply Subtype.ext
  exact Prod.ext (uCoverPathTransport_deckV ha γ e.1.1) rfl

theorem uCoverPathTransport_deckF (γ : Pi1 K y) (t : UF K y) :
    (uCoverPathTransport ha).onF (deckF γ t) =
      deckF (pi1Conj ha γ) ((uCoverPathTransport ha).onF t) := by
  apply Subtype.ext
  exact Prod.ext (uCoverPathTransport_deckV ha γ t.1.1) rfl

/-- Transport by the reverse path undoes the original prefix on vertices. -/
theorem pathTransportV_reverse (c : UV K y) :
    pathTransportV (isPath_revPath ha) (pathTransportV ha c) = c := by
  induction c using UV.ind with
  | h p =>
      apply UV.sound
      change Htpy K y (endpt K y (revPath a ++ (a ++ p.1)))
        (revPath a ++ (a ++ p.1)) p.1
      rw [endpt_append, endpt_eq_of_isPath (isPath_revPath ha),
        endpt_append, endpt_eq_of_isPath ha]
      have h := (htpy_revPath_append ha).congr_append
        (show IsPath K.src K.tgt [] y y from rfl) p.2
      simpa only [List.nil_append, List.append_assoc] using h

/-- Reversing the order gives the other inverse identity. -/
theorem pathTransportV_reverse' (c : UV K x) :
    pathTransportV ha (pathTransportV (isPath_revPath ha) c) = c := by
  induction c using UV.ind with
  | h p =>
      apply UV.sound
      change Htpy K x (endpt K x (a ++ (revPath a ++ p.1)))
        (a ++ (revPath a ++ p.1)) p.1
      rw [endpt_append, endpt_eq_of_isPath ha,
        endpt_append, endpt_eq_of_isPath (isPath_revPath ha)]
      have h := (htpy_append_revPath ha).congr_append
        (show IsPath K.src K.tgt [] x x from rfl) p.2
      simpa only [List.nil_append, List.append_assoc] using h

theorem uCoverPathTransport_onV_bijective : Function.Bijective (uCoverPathTransport ha).onV :=
  ⟨(show Function.LeftInverse (pathTransportV (isPath_revPath ha)) (pathTransportV ha)
      from pathTransportV_reverse ha).injective,
    (show Function.RightInverse (pathTransportV (isPath_revPath ha)) (pathTransportV ha)
      from pathTransportV_reverse' ha).surjective⟩

theorem uCoverPathTransport_onE_bijective : Function.Bijective (uCoverPathTransport ha).onE := by
  constructor
  · intro e f hef
    apply Subtype.ext
    apply Prod.ext
    · exact (uCoverPathTransport_onV_bijective ha).1
        (congrArg (fun e : UE K x => e.1.1) hef)
    · exact congrArg (fun e : UE K x => e.1.2) hef
  · intro e
    refine ⟨pathTransportE (isPath_revPath ha) e, ?_⟩
    apply Subtype.ext
    exact Prod.ext (pathTransportV_reverse' ha e.1.1) rfl

theorem uCoverPathTransport_onF_bijective : Function.Bijective (uCoverPathTransport ha).onF := by
  constructor
  · intro t s hts
    apply Subtype.ext
    apply Prod.ext
    · exact (uCoverPathTransport_onV_bijective ha).1
        (congrArg (fun t : UF K x => t.1.1) hts)
    · exact congrArg (fun t : UF K x => t.1.2) hts
  · intro t
    refine ⟨pathTransportF (isPath_revPath ha) t, ?_⟩
    apply Subtype.ext
    exact Prod.ext (pathTransportV_reverse' ha t.1.1) rfl

end FiniteChains.Comb
