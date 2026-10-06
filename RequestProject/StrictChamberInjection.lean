import RequestProject.StrictOrderComplex
import RequestProject.ChamberQuotientCover

/-! The chamber group injection in the genuine, nondegenerate simplicial model. -/

namespace FiniteChains.Davis
open RACG Comb
universe u
variable {V X : Type u} [DecidableEq V] [Fintype V] {A : CommRel V}
  [PartialOrder X] {att : NeSpx A →o X}

instance qposPartialOrder : PartialOrder (Qpos A X att) where
  toPreorder := qposPreorder
  le_antisymm s t hst hts := by
    cases s with
    | inl c =>
      cases t with
      | inl d => exact congrArg Sum.inl (Subtype.ext (le_antisymm hst hts))
      | inr y => exact hst.elim
    | inr x =>
      cases t with
      | inl d => exact hts.elim
      | inr y => exact congrArg Sum.inr (le_antisymm hst hts)

omit [Fintype V] in
theorem qNew_strictMono : StrictMono (qNew (A := A) (X := X) (att := att)) := by
  intro x y hxy
  change x ≤ y ∧ ¬ y ≤ x
  exact ⟨hxy.le, hxy.not_ge⟩

/-- The actual inclusion into the quotient is injective on fundamental groups after
normalization of all degenerate edges and triangles. -/
theorem pi1Map_strict_qNew_injective (x : X) : Function.Injective
    (pi1Map (strictOrderCxMap (qNew (A := A) (X := X) (att := att)) qNew_strictMono) x) :=
  strictOrderCxMap_pi1_injective _ qNew_strictMono x (pi1Map_qNew_injective x)

end FiniteChains.Davis
