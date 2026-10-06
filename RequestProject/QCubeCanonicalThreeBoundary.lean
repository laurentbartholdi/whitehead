module

public import RequestProject.QCubeThreeOrderedFrame

@[expose] public section

/-! Actual three-cube cells and their canonical decreasing boundary frames. -/
namespace FiniteChains.Davis
open RACG Mirror Comb
open scoped Classical
variable {V : Type} [DecidableEq V] [LinearOrder V] {A : CommRel V}

abbrev QThreeCube (A : CommRel V) := {c : QCube A // c.spx.card = 3}

noncomputable def qThreeFrame (c : QThreeCube A) :
    {p : V × V × V // p.2.1 < p.1 ∧ p.2.2 < p.2.1 ∧ c.1.spx = {p.1, p.2.1, p.2.2}} := by
  apply Classical.choice
  obtain ⟨u, v, w, huv, hvw, hs⟩ := qCube_three_ordered_frame c.1 c.2
  exact ⟨⟨(u, v, w), huv, hvw, hs⟩⟩

noncomputable def qThreeUpper (c : QThreeCube A) : V := (qThreeFrame c).1.1
noncomputable def qThreeMiddle (c : QThreeCube A) : V := (qThreeFrame c).1.2.1
noncomputable def qThreeLower (c : QThreeCube A) : V := (qThreeFrame c).1.2.2

theorem qThree_middle_lt_upper (c : QThreeCube A) : qThreeMiddle c < qThreeUpper c :=
  (qThreeFrame c).2.1

theorem qThree_lower_lt_middle (c : QThreeCube A) : qThreeLower c < qThreeMiddle c :=
  (qThreeFrame c).2.2.1

theorem qThree_free_directions (c : QThreeCube A) :
    c.1.spx = {qThreeUpper c, qThreeMiddle c, qThreeLower c} := (qThreeFrame c).2.2.2

noncomputable def qThreeCubeBoundary (c : QThreeCube A) :
    (strictOrderCx (QCube A)).F →₀ ℤ :=
  cubeThreeSquareBoundary c.1 (qThreeUpper c) (qThreeMiddle c) (qThreeLower c)
    (Ne.symm (qThree_middle_lt_upper c).ne)
    (Ne.symm ((qThree_lower_lt_middle c).trans (qThree_middle_lt_upper c)).ne)
    (Ne.symm (qThree_lower_lt_middle c).ne) (qThree_free_directions c)

noncomputable def qThreeChainBoundary : (QThreeCube A →₀ ℤ) →ₗ[ℤ]
    ((strictOrderCx (QCube A)).F →₀ ℤ) :=
  Finsupp.linearCombination ℤ qThreeCubeBoundary

theorem qThreeCubeBoundary_cycle (c : QThreeCube A) :
    Comb.bdry2 (strictOrderCx (QCube A)) (qThreeCubeBoundary c) = 0 :=
  cubeThreeSquareBoundary_cycle _ _ _ _ _ _ _ _

theorem qThreeChainBoundary_cycle (r : QThreeCube A →₀ ℤ) :
    Comb.bdry2 (strictOrderCx (QCube A)) (qThreeChainBoundary r) = 0 := by
  induction r using Finsupp.induction_linear with
  | zero => simp
  | add r s hr hs => rw [map_add, map_add, hr, hs, add_zero]
  | single c n =>
      rw [qThreeChainBoundary, Finsupp.linearCombination_single, map_smul,
        qThreeCubeBoundary_cycle, smul_zero]

theorem qThreeCube_component_boundary (c : QThreeCube A)
    (y : StrictOrdTet (QCube A) →₀ ℤ)
    (hy : ∀ t ∈ y.support, t.1.2.2.2.spx.card ≤ 3)
    (hb : ∀ s ∈ (strictOrdBoundary3 y).support, s.1.2.2.spx.card ≤ 2) :
    ∃ k : ℤ, strictOrdBoundary3 (y.filter (fun t => t.1.2.2.2 = c.1)) =
      k • qThreeCubeBoundary c :=
  qCube_three_component_boundary_scalar c.1 _ _ _ (qThree_middle_lt_upper c)
    (qThree_lower_lt_middle c) (qThree_free_directions c) y hy hb

end FiniteChains.Davis
