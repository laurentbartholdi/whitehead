module

public import RequestProject.PosetCoverRoofCycles
public import RequestProject.ChamberZCoverOrdinaryCycles

@[expose] public section

/-! Actual finite fillings in lifted attaching intersections. -/
namespace FiniteChains.Davis
open RACG Mirror Comb
universe u
variable {V : Type u} [DecidableEq V] [Fintype V] {A : CommRel V}
  {X : Type u} [PartialOrder X] {M : CayGroup A → Prop} {att : NeSpx A →o X}
  {P : Type u} [PartialOrder P] {f : P → Zpos A X M att}

theorem strict_twoCycle_cover_attaching_intersection (hf : IsPosetCover f)
    (w : CayGroup A) (hw : w ≠ 1)
    (c : StrictOrdTri {p : P // ZJSet w (f p)} →₀ ℤ)
    (hc : Comb.bdry2 (strictOrderCx {p : P // ZJSet w (f p)}) c = 0) :
    ∃ y : StrictOrdTet {p : P // ZJSet w (f p)} →₀ ℤ,
      strictOrdBoundary3 y = c := by
  let S : Set (Zpos A X M att) := {z | ZJSet w z}
  let e := zJSetOrderIso (A := A) (X := X) (M := M) (att := att) w
  let g : S → S := fun q => e.symm (interRho (e q))
  let b : S := e.symm (interTop hw)
  have hmono : Monotone g := fun _ _ h =>
    e.symm.monotone (interRho_mono (e.monotone h))
  have hg : ∀ q, g q ≤ q := by
    intro q
    have h := e.symm.monotone (interRho_le (e q))
    simpa only [OrderIso.symm_apply_apply] using h
  have hb : ∀ q, g q ≤ b := fun q =>
    e.symm.monotone (interRho_le_top hw (e q))
  exact strict_twoCycle_cover_roof (IsPosetCover.restriction f S hf)
    g hmono hg b hb c hc

theorem strict_twoCycle_uOrder_attaching_intersection
    (a : Zpos A X M att) (hconn : IsConnected (orderCx (Zpos A X M att)))
    (w : CayGroup A) (hw : w ≠ 1)
    (c : StrictOrdTri {p : UOrder (Zpos A X M att) a // ZJSet w (uOrderEnd p)} →₀ ℤ)
    (hc : Comb.bdry2 (strictOrderCx
      {p : UOrder (Zpos A X M att) a // ZJSet w (uOrderEnd p)}) c = 0) :
    ∃ y : StrictOrdTet
      {p : UOrder (Zpos A X M att) a // ZJSet w (uOrderEnd p)} →₀ ℤ,
      strictOrdBoundary3 y = c :=
  strict_twoCycle_cover_attaching_intersection (uOrderEnd_isPosetCover hconn) w hw c hc

theorem strict_oneCycle_cover_attaching_intersection (hf : IsPosetCover f)
    (w : CayGroup A) (hw : w ≠ 1)
    (c : StrictOrdEdge {p : P // ZJSet w (f p)} →₀ ℤ)
    (hc : Comb.bdry1 (strictOrderCx {p : P // ZJSet w (f p)}) c = 0) :
    ∃ y : StrictOrdTri {p : P // ZJSet w (f p)} →₀ ℤ,
      Comb.bdry2 (strictOrderCx {p : P // ZJSet w (f p)}) y = c := by
  let S : Set (Zpos A X M att) := {z | ZJSet w z}
  let e := zJSetOrderIso (A := A) (X := X) (M := M) (att := att) w
  let g : S → S := fun q => e.symm (interRho (e q))
  let b : S := e.symm (interTop hw)
  have hmono : Monotone g := fun _ _ h =>
    e.symm.monotone (interRho_mono (e.monotone h))
  have hg : ∀ q, g q ≤ q := by
    intro q
    have h := e.symm.monotone (interRho_le (e q))
    simpa only [OrderIso.symm_apply_apply] using h
  have hb : ∀ q, g q ≤ b := fun q =>
    e.symm.monotone (interRho_le_top hw (e q))
  exact strict_oneCycle_cover_roof (IsPosetCover.restriction f S hf)
    g hmono hg b hb c hc

theorem strict_oneCycle_uOrder_attaching_intersection
    (a : Zpos A X M att) (hconn : IsConnected (orderCx (Zpos A X M att)))
    (w : CayGroup A) (hw : w ≠ 1)
    (c : StrictOrdEdge {p : UOrder (Zpos A X M att) a // ZJSet w (uOrderEnd p)} →₀ ℤ)
    (hc : Comb.bdry1 (strictOrderCx
      {p : UOrder (Zpos A X M att) a // ZJSet w (uOrderEnd p)}) c = 0) :
    ∃ y : StrictOrdTri
      {p : UOrder (Zpos A X M att) a // ZJSet w (uOrderEnd p)} →₀ ℤ,
      Comb.bdry2 (strictOrderCx
        {p : UOrder (Zpos A X M att) a // ZJSet w (uOrderEnd p)}) y = c :=
  strict_oneCycle_cover_attaching_intersection (uOrderEnd_isPosetCover hconn) w hw c hc

end FiniteChains.Davis
