module

public import RequestProject.QCubeCoordinateEquiv
public import RequestProject.NerveDegree

@[expose] public section

/-! Face incidences of the truncated complex, including its new cut cells. -/

namespace FiniteChains.Davis
open RACG Mirror
variable {V : Type} [DecidableEq V] {A : CommRel V}

/-- A new cut cell has dimension `σ.card - 1` and requires a nonempty simplex. -/
def CutCell (A : CommRel V) := {σ : Finset V // σ.Nonempty ∧ IsSimplex A σ}

/-- Retained (possibly truncated) cubes and the new simplicial cut cells. -/
abbrev TruncatedCell (A : CommRel V) := QOld A ⊕ CutCell A

def TruncatedFace : TruncatedCell A → TruncatedCell A → Prop
  | .inl c, .inl d => c.1 ≤ d.1
  | .inr σ, .inr τ => σ.1 ⊆ τ.1
  | .inr σ, .inl c => σ.1 ⊆ c.1.spx ∧ c.1.sgn = 0
  | .inl _, .inr _ => False

theorem qCube_sgn_zero_of_face {c d : QCube A} (h : c ≤ d) (hc : c.sgn = 0) :
    d.sgn = 0 := by
  funext v
  by_cases hv : v ∈ d.spx
  · exact d.sgn_eq_zero v hv
  · exact (h.2 v hv).symm.trans (congrFun hc v)

instance : PartialOrder (TruncatedCell A) where
  le := TruncatedFace
  le_refl c := by
    cases c with
    | inl c => exact le_refl c.1
    | inr c => exact Finset.Subset.refl c.1
  le_trans c d e hcd hde := by
    cases c with
    | inl c =>
      cases d with
      | inl d =>
        cases e with
        | inl e => exact le_trans hcd hde
        | inr e => exact False.elim hde
      | inr d => exact False.elim hcd
    | inr c =>
      cases d with
      | inl d =>
        cases e with
        | inl e => exact ⟨hcd.1.trans hde.1, qCube_sgn_zero_of_face hde hcd.2⟩
        | inr e => exact False.elim hde
      | inr d =>
        cases e with
        | inl e => exact ⟨hcd.trans hde.1, hde.2⟩
        | inr e => exact hcd.trans hde
  le_antisymm c d hcd hdc := by
    cases c with
    | inl c =>
      cases d with
      | inl d => exact congrArg Sum.inl (Subtype.ext (le_antisymm hcd hdc))
      | inr d => exact False.elim hcd
    | inr c =>
      cases d with
      | inl d => exact False.elim hdc
      | inr d => exact congrArg Sum.inr (Subtype.ext (Finset.Subset.antisymm hcd hdc))

/-- The cut surface is an actual subposet with the simplex face order. -/
def cutCellEmbedding : CutCell A ↪ TruncatedCell A :=
  ⟨Sum.inr, Sum.inr_injective⟩

/-- A cut cell meets precisely the positive cubes whose directions contain its simplex. -/
theorem cut_le_old_iff (σ : CutCell A) (c : QOld A) :
    (Sum.inr σ : TruncatedCell A) ≤ Sum.inl c ↔
      σ.1 ⊆ c.1.spx ∧ c.1.sgn = 0 := Iff.rfl

/-- Retained cubes embed as their actual truncated cells. -/
def oldCellIncl : QOld A → TruncatedCell A := Sum.inl

theorem oldCellIncl_monotone : Monotone (oldCellIncl (A := A)) := fun _ _ h => h

/-- Project a cut simplex to the positive cube containing it; retained cubes are fixed.
This supplies the comparison with the older cube-poset block model. -/
def truncatedCellRetraction : TruncatedCell A → QOld A
  | .inl c => c
  | .inr σ => posQCube ⟨σ.1, σ.2⟩

theorem truncatedCellRetraction_monotone : Monotone (truncatedCellRetraction (A := A)) := by
  intro c d h
  cases c with
  | inl c =>
    cases d with
    | inl d => exact h
    | inr d => exact False.elim h
  | inr σ =>
    cases d with
    | inl d =>
      refine ⟨h.1, ?_⟩
      intro v _
      change (0 : ZMod 2) = d.1.sgn v
      rw [h.2]
      rfl
    | inr τ => exact posQCube_monotone h

omit [DecidableEq V] in
@[simp] theorem truncatedCellRetraction_old (c : QOld A) :
    truncatedCellRetraction (oldCellIncl c) = c := rfl

/-- Every cell is a face of its retained-cube image. Thus the section and retraction
have a pointwise order homotopy, including the cut cells. -/
theorem truncatedCell_le_retraction (c : TruncatedCell A) :
    c ≤ oldCellIncl (truncatedCellRetraction c) := by
  cases c with
  | inl c => exact le_refl _
  | inr σ => exact ⟨Finset.Subset.refl _, rfl⟩

/-- A degree-preserving full-nerve boundary witnesses the comparison with the retained
cube model. The witness retains the three-cells when applied to two-cycles. -/
theorem truncated_cycle_retraction_boundary (n : ℕ) (c : Nerve.Ch (TruncatedCell A))
    (hc : c ∈ Nerve.Inc (TruncatedCell A)) (hd : Nerve.bdry c = 0)
    (hn : Nerve.lengthProjection n c = c) :
    ∃ b : Nerve.Ch (TruncatedCell A), b ∈ Nerve.Inc (TruncatedCell A) ∧
      Nerve.lengthProjection (n + 1) b = b ∧
      Nerve.bdry b = Nerve.lengthProjection n
        (Nerve.cmap (oldCellIncl ∘ truncatedCellRetraction) c) - c := by
  let g : TruncatedCell A → TruncatedCell A := oldCellIncl ∘ truncatedCellRetraction
  have hg : Monotone g := oldCellIncl_monotone.comp truncatedCellRetraction_monotone
  let p := Nerve.prism id g c
  have hp : p ∈ Nerve.Inc (TruncatedCell A) :=
    Nerve.prism_mem_inc monotone_id hg truncatedCell_le_retraction hc
  have hb : Nerve.bdry p = Nerve.cmap g c - c := by
    simpa [p, hd] using Nerve.bdry_prism_add_prism_bdry id g c
  refine ⟨Nerve.lengthProjection (n + 1) p, Nerve.lengthProjection_mem_inc _ hp,
    Nerve.lengthProjection_idempotent _ _, ?_⟩
  rw [← Nerve.lengthProjection_bdry, hb, map_sub, hn]


variable [Fintype V]

/-- The cut incidence can also be read directly from the coordinates used by the collapse. -/
theorem cut_le_old_coordinate_iff (σ : CutCell A) (c : QOld A) :
    (Sum.inr σ : TruncatedCell A) ≤ Sum.inl c ↔
      σ.1 ⊆ freeSet (qCubeToCoordinate c.1) ∧
        qCubeToCoordinate c.1 = posCube c.1.spx := by
  rw [cut_le_old_iff, freeSet_qCubeToCoordinate]
  constructor
  · rintro ⟨hs, hz⟩
    exact ⟨hs, qCubeToCoordinate_sgn_zero c.1 hz⟩
  · rintro ⟨hs, hz⟩
    refine ⟨hs, ?_⟩
    funext v
    by_cases hv : v ∈ c.1.spx
    · exact c.1.sgn_eq_zero v hv
    · rw [← qCubeToCoordinate_parity c.1 v, hz]
      simp [posCube, hv]

end FiniteChains.Davis
