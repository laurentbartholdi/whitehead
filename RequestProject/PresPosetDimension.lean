import RequestProject.PresPosetPartialOrder
import RequestProject.OrderThreeNormalization

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains.PresModel
open Comb
universe u
variable {α J : Type u}

def roseDimension : Rose α → ℕ
  | Rose.base => 1
  | Rose.mid _ => 1
  | Rose.edg _ _ => 2

theorem roseDimension_monotone : Monotone (roseDimension (α := α)) := by
  intro x y h
  change Rose.le x y at h
  cases x <;> cases y <;> simp_all [Rose.le, roseDimension]

theorem roseDimension_strictMono : StrictMono (roseDimension (α := α)) := by
  intro x y h
  have hn := ne_of_lt h
  have hl := le_of_lt h
  change Rose.le x y at hl
  cases x <;> cases y <;> simp_all [Rose.le, roseDimension]

noncomputable def circleDimension (w : J → List (α × Bool)) (x : TCirc w) : ℕ := by
  classical
  exact if x.2.1 < (w x.1).length ∧
    (x.2.2 = CPos.cedgL ∨ x.2.2 = CPos.cedgR) then 1 else 0

theorem circleDimension_le_one (w : J → List (α × Bool)) (x : TCirc w) :
    circleDimension w x ≤ 1 := by
  classical
  unfold circleDimension
  split <;> omega

theorem circleDimension_strictMono (w : J → List (α × Bool)) :
    StrictMono (circleDimension w) := by
  classical
  intro x y h
  have hn := ne_of_lt h
  have hl := le_of_lt h
  change x = y ∨ TCirc.lt w x y at hl
  rcases hl with he | hl
  · exact (hn he).elim
  obtain ⟨j, k, t⟩ := x
  obtain ⟨j', k', t'⟩ := y
  obtain ⟨hj, hk, htags⟩ := hl
  subst j'
  rcases htags with ⟨ht, ht', _⟩ | ⟨ht, ht', _⟩ | ⟨ht, ht', _⟩ | ⟨ht, ht', _⟩ <;>
    subst t <;> subst t' <;> simp [circleDimension, hk]

theorem circleDimension_lt_aFun (w : J → List (α × Bool)) (x : TCirc w) :
    circleDimension w x < roseDimension (aFun w x) := by
  classical
  obtain ⟨j, k, t⟩ := x
  by_cases hk : k < (w j).length
  · obtain ⟨p, hp⟩ := exists_get_of_lt w hk
    cases t <;> simp_all [circleDimension, aFun, roseDimension]
  · have hp : (w j)[k]? = none := List.getElem?_eq_none (by omega)
    cases t <;> simp_all [circleDimension, aFun, roseDimension]

noncomputable def cylinderDimension (w : J → List (α × Bool)) : CylBase w → ℕ :=
  Sum.elim roseDimension (circleDimension w)

theorem cylinderDimension_strictMono (w : J → List (α × Bool)) :
    StrictMono (cylinderDimension w) := by
  intro p q h
  have hn := ne_of_lt h
  have hl := le_of_lt h
  cases p with
  | inl p =>
    cases q with
    | inl q =>
      exact roseDimension_strictMono (lt_of_le_of_ne hl (by
        intro he; exact hn (congrArg Sum.inl he)))
    | inr q => exact hl.elim
  | inr p =>
    cases q with
    | inl q =>
      exact (circleDimension_lt_aFun w p).trans_le (roseDimension_monotone hl)
    | inr q =>
      exact circleDimension_strictMono w (lt_of_le_of_ne hl (by
        intro he; exact hn (congrArg Sum.inr he)))

noncomputable def presPosDimension (w : J → List (α × Bool)) : PresPos w → ℕ :=
  Sum.elim (cylinderDimension w) (fun _ => 2)

theorem presPosDimension_le_two (w : J → List (α × Bool)) (p : PresPos w) :
    presPosDimension w p ≤ 2 := by
  cases p with
  | inl p =>
    cases p with
    | inl r => cases r <;> simp [presPosDimension, cylinderDimension, roseDimension]
    | inr c => exact (circleDimension_le_one w c).trans (by decide)
  | inr j => exact le_refl _

theorem presPosDimension_strictMono (w : J → List (α × Bool)) :
    StrictMono (presPosDimension w) := by
  intro p q h
  have hn := ne_of_lt h
  have hl := le_of_lt h
  cases p with
  | inl p =>
    cases q with
    | inl q =>
      exact cylinderDimension_strictMono w (lt_of_le_of_ne hl (by
        intro he; exact hn (congrArg Sum.inl he)))
    | inr j =>
      obtain ⟨r, hr, hpr⟩ := hl
      obtain ⟨k, t, _, he⟩ := hr
      subst r
      have hm := (cylinderDimension_strictMono w).monotone hpr
      have hb := circleDimension_le_one w (TCirc.pt w j k t)
      change cylinderDimension w p < 2
      change cylinderDimension w p ≤ circleDimension w (TCirc.pt w j k t) at hm
      omega
  | inr j =>
    cases q with
    | inl q => exact hl.elim
    | inr k => exact (hn (congrArg Sum.inr hl)).elim

/-- The genuine presentation-poset model has no strict tetrahedra. -/
theorem presPos_strict_three_flags_empty (w : J → List (α × Bool)) :
    IsEmpty (StrictOrdTet (PresPos w)) := by
  refine ⟨fun t => ?_⟩
  have h01 := presPosDimension_strictMono w t.2.1
  have h12 := presPosDimension_strictMono w t.2.2.1
  have h23 := presPosDimension_strictMono w t.2.2.2
  have hb := presPosDimension_le_two w t.1.2.2.2
  omega

theorem presPos_normalized_three_boundary_zero (w : J → List (α × Bool))
    (y : OrdTet (PresPos w) →₀ ℤ) : normalizeOrdChain2 (ordBoundary3 y) = 0 := by
  haveI := presPos_strict_three_flags_empty w
  have hy : normalizeOrdChain3 y = 0 := by
    ext t
    exact isEmptyElim t
  rw [normalizeOrdChain2_ordBoundary3, hy, map_zero]

end FiniteChains.PresModel
