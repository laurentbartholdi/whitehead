module

public import RequestProject.CombPi2
public import RequestProject.Framework

@[expose] public section

/-!
# Theorem A over honest combinatorial two-complexes

`RequestProject/Framework.lean` proves Theorem A relative to the interface `TwoComplexData`,
whose notions (subcomplex, `π₂`, Cockcroft, acyclic regular cover) were left abstract.  With
the combinatorial two-complexes of `RequestProject/CellComplex.lean`, their fundamental group
(`RequestProject/CombPi1.lean`), their universal cover (`RequestProject/CombUniversalCover.lean`)
and their second homotopy module (`RequestProject/CombPi2.lean`) all constructed, the interface
can now be instantiated by honest definitions:

* `FiniteChains.Comb.Sub` — `X` is a subcomplex of `Y`: there is a cellular map injective on
  vertices, edges and two-cells;
* `FiniteChains.combData` — the instance of `TwoComplexData` carried by combinatorial
  two-complexes, in which
  * `Cockcroft` is `FiniteChains.Comb.IsCockcroft` (the Hurewicz map `π₂ → H₂` vanishes),
  * `ZeroPi2 X Y` says that every subcomplex inclusion `X ⊆ Y` is zero on
    `π₂ = ker ∂₂` of the universal covers,
  * `Pi1Trivial X Y` says that every such inclusion kills the fundamental group,
  * `Acyclic` is `FiniteChains.Comb.IsAcyclic` and `IsAcyclicCover` is the combinatorial
    notion of a connected acyclic regular covering;
* `FiniteChains.hasAcyclicRegularCover_combData_iff` — condition (2) of Theorem A in this
  instance is exactly `FiniteChains.Comb.HasAcyclicRegularCover`, the statement of
  `RequestProject/CellComplex.lean`.

Non-vacuity is checked on the one-point complex.
-/

namespace FiniteChains
namespace Comb

universe u

/-! ### Identity and composition of cellular maps -/

/-- The identity cellular map. -/
def Hom.id (X : Complex2.{u}) : Hom X X where
  onV := _root_.id
  onE := _root_.id
  onF := _root_.id
  src_onE := fun _ => rfl
  tgt_onE := fun _ => rfl
  base_onF := fun _ => rfl
  att_onF := fun f => by simp

/-- The composition of cellular maps. -/
def Hom.comp {X Y Z : Complex2.{u}} (g : Hom Y Z) (h : Hom X Y) : Hom X Z where
  onV := g.onV ∘ h.onV
  onE := g.onE ∘ h.onE
  onF := g.onF ∘ h.onF
  src_onE := fun e => by
    show Z.src (g.onE (h.onE e)) = g.onV (h.onV (X.src e))
    rw [g.src_onE, h.src_onE]
  tgt_onE := fun e => by
    show Z.tgt (g.onE (h.onE e)) = g.onV (h.onV (X.tgt e))
    rw [g.tgt_onE, h.tgt_onE]
  base_onF := fun f => by
    show Z.base (g.onF (h.onF f)) = g.onV (h.onV (X.base f))
    rw [g.base_onF, h.base_onF]
  att_onF := fun f => by
    show Z.att (g.onF (h.onF f)) = (X.att f).map (fun eb => (g.onE (h.onE eb.1), eb.2))
    rw [g.att_onF, h.att_onF]
    simp

/-- **Subcomplex**: a cellular map injective on vertices, edges and two-cells. -/
def Sub (X Y : Complex2.{u}) : Prop :=
  ∃ h : Hom X Y, Function.Injective h.onV ∧ Function.Injective h.onE ∧ Function.Injective h.onF

theorem Sub.refl (X : Complex2.{u}) : Sub X X :=
  ⟨Hom.id X, fun _ _ h => h, fun _ _ h => h, fun _ _ h => h⟩

theorem Sub.trans {X Y Z : Complex2.{u}} (h : Sub X Y) (h' : Sub Y Z) : Sub X Z := by
  obtain ⟨f, hfV, hfE, hfF⟩ := h
  obtain ⟨g, hgV, hgE, hgF⟩ := h'
  exact ⟨g.comp f, hgV.comp hfV, hgE.comp hfE, hgF.comp hfF⟩

/-- A connected acyclic regular covering of `Y` with total space `D`. -/
def IsAcyclicCover (D Y : Complex2.{u}) : Prop :=
  ∃ (Q : Type u) (_ : Group Q) (p : Hom D Y) (A : DeckAction D Q),
    IsCovering p ∧ IsRegular p A ∧ IsConnected D ∧ IsAcyclic D

theorem hasAcyclicRegularCover_iff (Y : Complex2.{u}) :
    (∃ D, IsAcyclicCover D Y) ↔ HasAcyclicRegularCover Y := by
  constructor
  · rintro ⟨D, Q, hQ, p, A, h⟩
    exact ⟨D, Q, hQ, p, A, h⟩
  · rintro ⟨D, Q, hQ, p, A, h⟩
    exact ⟨D, Q, hQ, p, A, h⟩

end Comb

/-- **Theorem A's interface, carried by combinatorial two-complexes.**  Every notion is the
honest combinatorial one; nothing is abstract any more. -/
def combData : TwoComplexData.{u + 1} where
  Cx := Comb.Complex2.{u}
  Sub := Comb.Sub
  sub_refl := Comb.Sub.refl
  sub_trans := Comb.Sub.trans
  Cockcroft := Comb.IsCockcroft
  ZeroPi2 := fun X Y => ∀ h : Comb.Hom X Y,
    Function.Injective h.onV → Function.Injective h.onE → Function.Injective h.onF →
      Comb.ZeroPi2 h
  Pi1Trivial := fun X Y => ∀ h : Comb.Hom X Y,
    Function.Injective h.onV → Function.Injective h.onE → Function.Injective h.onF →
      Comb.Pi1Trivial h
  Acyclic := Comb.IsAcyclic
  IsAcyclicCover := Comb.IsAcyclicCover

/-- **Condition (2) of Theorem A in the combinatorial instance** is exactly the statement of
`RequestProject/CellComplex.lean`: the complex has a connected acyclic regular cover. -/
theorem hasAcyclicRegularCover_combData_iff (K : Comb.Complex2.{u}) :
    HasAcyclicRegularCover combData K ↔ Comb.HasAcyclicRegularCover K :=
  Comb.hasAcyclicRegularCover_iff K

namespace Comb

/-! ### Non-vacuity: the one-point complex -/

/-- The complex with one vertex and no cells. -/
abbrev pointComplex : Complex2.{u} where
  V := PUnit.{u + 1}
  E := PEmpty.{u + 1}
  F := PEmpty.{u + 1}
  src := PEmpty.elim
  tgt := PEmpty.elim
  base := PEmpty.elim
  att := PEmpty.elim
  att_isLoop := fun f => f.elim

theorem pointComplex_isConnected : IsConnected pointComplex.{u} := by
  intro a b
  exact ⟨[], by cases a; cases b; rfl⟩

theorem pointComplex_isAcyclic : IsAcyclic pointComplex.{u} := by
  classical
  refine ⟨?_, ?_, ?_⟩
  · intro u v _
    exact Subsingleton.elim u v
  · intro c _
    refine ⟨0, ?_⟩
    have : c = 0 := Subsingleton.elim c 0
    rw [this, map_zero]
  · intro c hc
    refine ⟨0, ?_⟩
    rw [map_zero]
    have hsingle : c = Finsupp.single PUnit.unit (c PUnit.unit) := by
      refine Finsupp.ext ?_
      intro a
      obtain ⟨⟩ := a
      simp
    have hzero : c PUnit.unit = 0 := by
      rw [hsingle, augC_single] at hc
      exact hc
    rw [hsingle, hzero, Finsupp.single_zero]

/-- The one-point complex is Cockcroft: its universal cover has no two-cells at all. -/
theorem pointComplex_isCockcroft : IsCockcroft pointComplex.{u} := by
  intro x₀ c _
  have : c = 0 := by
    ext F
    exact F.1.2.elim
  rw [this, map_zero]

end Comb
end FiniteChains
