import RequestProject.QCubeSquareRadialIndex

/-! The actual internal radial boundary matrix of the eight square flags. -/
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains.Davis
open RACG Mirror Comb
variable {V : Type} [DecidableEq V] {A : CommRel V}

def squareFlagCornerIndex (i : Bool × ZMod 2 × Bool) : ZMod 2 × ZMod 2 :=
  if i.1 then (i.2.1, if i.2.2 then 0 else 1) else
    (if i.2.2 then 0 else 1, i.2.1)

theorem squareFlag_middle (c : QCube A) (a b : V) (hne : a ≠ b)
    (hs : c.spx = {a, b}) (i : Bool × ZMod 2 × Bool) :
    (squareFlag c a b hne hs i).1.2.1 = squareFacetIndex c a b (i.1, i.2.1) := by
  obtain ⟨e, s, f⟩ := i
  cases e <;> cases f <;> rfl

theorem squareFlag_top (c : QCube A) (a b : V) (hne : a ≠ b)
    (hs : c.spx = {a, b}) (i : Bool × ZMod 2 × Bool) :
    (squareFlag c a b hne hs i).1.2.2 = c := by
  obtain ⟨e, s, f⟩ := i
  cases e <;> cases f <;> rfl

theorem squareFlag_vertex (c : QCube A) (a b : V) (hne : a ≠ b)
    (hs : c.spx = {a, b}) (i : Bool × ZMod 2 × Bool) :
    (squareFlag c a b hne hs i).1.1 =
      squareCorner c a b (squareFlagCornerIndex i).1 (squareFlagCornerIndex i).2 := by
  obtain ⟨e, s, f⟩ := i
  cases e <;> cases f
  · exact (squareCorner_negative c b a (Ne.symm hne)
      (by simpa [Finset.pair_comm] using hs) s).symm.trans
      (squareCorner_swap c b a (Ne.symm hne) s 1)
  · exact (squareCorner_positive c b a (Ne.symm hne)
      (by simpa [Finset.pair_comm] using hs) s).symm.trans
      (squareCorner_swap c b a (Ne.symm hne) s 0)
  · exact (squareCorner_negative c a b hne hs s).symm
  · exact (squareCorner_positive c a b hne hs s).symm

noncomputable def squareRadialCoordinates (c : QCube A) (a b : V) (hne : a ≠ b)
    (hs : c.spx = {a, b}) : ((strictOrderCx (QCube A)).E →₀ ℤ) →ₗ[ℤ]
      (SquareRadialIndex →₀ ℤ) :=
  Finsupp.lcomapDomain (squareRadialEdge c a b hne hs)
    (squareRadialEdge_injective c a b hne hs)

theorem squareRadialCoordinates_single (c : QCube A) (a b : V) (hne : a ≠ b)
    (hs : c.spx = {a, b}) (i : SquareRadialIndex) (n : ℤ) :
    squareRadialCoordinates c a b hne hs (Finsupp.single (squareRadialEdge c a b hne hs i) n) =
      Finsupp.single i n :=
  Finsupp.comapDomain_single _ _ _ (squareRadialEdge_injective c a b hne hs).injOn

theorem squareRadialCoordinates_off_top (c : QCube A) (a b : V) (hne : a ≠ b)
    (hs : c.spx = {a, b}) (e : (strictOrderCx (QCube A)).E) (he : e.1.2 ≠ c) (n : ℤ) :
    squareRadialCoordinates c a b hne hs (Finsupp.single e n) = 0 := by
  classical
  ext i
  change Finsupp.single e n (squareRadialEdge c a b hne hs i) = 0
  have hne : e ≠ squareRadialEdge c a b hne hs i := by
    intro h
    exact he (congrArg (fun e : (strictOrderCx (QCube A)).E => e.1.2) h)
  simp [hne]

noncomputable def squareInternalBoundary : ((Bool × ZMod 2 × Bool) →₀ ℤ) →ₗ[ℤ]
    (SquareRadialIndex →₀ ℤ) :=
  Finsupp.linearCombination ℤ (fun i => Finsupp.single (.inl (i.1, i.2.1)) 1 -
    Finsupp.single (.inr (squareFlagCornerIndex i)) 1)

/-- Each actual flag contributes its facet radial edge minus its corner radial edge. -/
theorem squareFlag_internal_boundary (c : QCube A) (a b : V) (hne : a ≠ b)
    (hs : c.spx = {a, b}) (i : Bool × ZMod 2 × Bool) :
    squareRadialCoordinates c a b hne hs
      (Comb.bdry2 (strictOrderCx (QCube A))
        (Finsupp.single (squareFlag c a b hne hs i) 1)) =
      Finsupp.single (.inl (i.1, i.2.1)) 1 -
        Finsupp.single (.inr (squareFlagCornerIndex i)) 1 := by
  let t := squareFlag c a b hne hs i
  let e01 : (strictOrderCx (QCube A)).E := ⟨(t.1.1, t.1.2.1), t.2.1⟩
  let e12 : (strictOrderCx (QCube A)).E := ⟨(t.1.2.1, t.1.2.2), t.2.2⟩
  let e02 : (strictOrderCx (QCube A)).E := ⟨(t.1.1, t.1.2.2), t.2.1.trans t.2.2⟩
  have h12 : e12 = squareRadialEdge c a b hne hs (.inl (i.1, i.2.1)) := by
    apply Subtype.ext
    change (t.1.2.1, t.1.2.2) = (squareFacetIndex c a b (i.1, i.2.1), c)
    exact Prod.ext (squareFlag_middle c a b hne hs i) (squareFlag_top c a b hne hs i)
  have h02 : e02 = squareRadialEdge c a b hne hs (.inr (squareFlagCornerIndex i)) := by
    apply Subtype.ext
    change (t.1.1, t.1.2.2) =
      (squareCorner c a b (squareFlagCornerIndex i).1 (squareFlagCornerIndex i).2, c)
    exact Prod.ext (squareFlag_vertex c a b hne hs i) (squareFlag_top c a b hne hs i)
  have h01 : e01.1.2 ≠ c := by
    change t.1.2.1 ≠ c
    rw [squareFlag_middle]
    exact (squareFacetIndex_lt c a b hs (i.1, i.2.1)).ne
  have hb : Comb.bdry2 (strictOrderCx (QCube A)) (Finsupp.single t 1) =
      Finsupp.single e01 1 + Finsupp.single e12 1 - Finsupp.single e02 1 := by
    rw [Comb.bdry2_single (X := strictOrderCx (QCube A)), one_smul]
    simp [strictOrderCx, pathChain, e01, e12, e02]
    abel
  rw [hb, map_sub, map_add, squareRadialCoordinates_off_top c a b hne hs e01 h01 1,
    h12, h02, squareRadialCoordinates_single, squareRadialCoordinates_single, zero_add]

/-- The finite radial matrix is obtained by the actual strict cellular boundary. -/
theorem squareInternalBoundary_naturality (c : QCube A) (a b : V) (hne : a ≠ b)
    (hs : c.spx = {a, b}) (z : (Bool × ZMod 2 × Bool) →₀ ℤ) :
    squareRadialCoordinates c a b hne hs
      (Comb.bdry2 (strictOrderCx (QCube A))
        (Finsupp.mapDomain (squareFlag c a b hne hs) z)) = squareInternalBoundary z := by
  induction z using Finsupp.induction_linear with
  | zero => simp
  | add z w hz hw => rw [Finsupp.mapDomain_add, map_add, map_add, hz, hw, map_add]
  | single i n =>
      rw [Finsupp.mapDomain_single]
      have hn : Finsupp.single (squareFlag c a b hne hs i) n =
          n • Finsupp.single (squareFlag c a b hne hs i) 1 := by simp
      rw [hn, map_smul, map_smul, squareFlag_internal_boundary, squareInternalBoundary,
        Finsupp.linearCombination_single]

end FiniteChains.Davis
