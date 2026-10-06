import RequestProject.QCubeDoubleFacetIndex
import RequestProject.QCubeCubicalTwoBoundary
import RequestProject.QCubeThreeFacetCoordinates

/-! The six actual square faces in the ordered three-cube coefficient index. -/
namespace FiniteChains.Davis
open RACG Mirror Comb
variable {V : Type} [DecidableEq V] {A : CommRel V}

def qThreeDirection (u v w : V) (e : Fin 3) : V :=
  if e = 0 then u else if e = 1 then v else w

omit [DecidableEq V] in
theorem qThreeDirection_injective (u v w : V) (huv : u ≠ v) (huw : u ≠ w) (hvw : v ≠ w) :
    Function.Injective (qThreeDirection u v w) := by
  intro i j h
  fin_cases i <;> fin_cases j <;> simp_all [qThreeDirection, Fin.ext_iff]

theorem qThreeDirection_mem (c : QCube A) (u v w : V) (hs : c.spx = {u, v, w})
    (e : Fin 3) : qThreeDirection u v w e ∈ c.spx := by
  fin_cases e <;> simp [qThreeDirection, hs, Fin.ext_iff]

theorem qCube_three_card (c : QCube A) (u v w : V)
    (huv : u ≠ v) (huw : u ≠ w) (hvw : v ≠ w) (hs : c.spx = {u, v, w}) :
    c.spx.card = 3 := by simp [hs, huv, huw, hvw]

def qThreeFaceSquare (c : QCube A) (u v w : V)
    (huv : u ≠ v) (huw : u ≠ w) (hvw : v ≠ w) (hs : c.spx = {u, v, w})
    (i : Fin 3 × ZMod 2) : QSquare A :=
  qThreeFacetSquare c (qCube_three_card c u v w huv huw hvw hs)
    (⟨qThreeDirection u v w i.1, qThreeDirection_mem c u v w hs i.1⟩, i.2)

theorem qThreeFaceSquare_injective (c : QCube A) (u v w : V)
    (huv : u ≠ v) (huw : u ≠ w) (hvw : v ≠ w) (hs : c.spx = {u, v, w}) :
    Function.Injective (qThreeFaceSquare c u v w huv huw hvw hs) := by
  intro ⟨e, s⟩ ⟨f, t⟩ h
  have hp := qThreeFacetSquare_injective c (qCube_three_card c u v w huv huw hvw hs) h
  have hd := congrArg (fun i : {v : V // v ∈ c.spx} × ZMod 2 => i.1.1) hp
  have hsign := congrArg (fun i : {v : V // v ∈ c.spx} × ZMod 2 => i.2) hp
  exact Prod.ext (qThreeDirection_injective u v w huv huw hvw hd) hsign

/-- Every actual square facet occurs in the six-entry coordinate index. -/
theorem qThreeFaceSquare_exhaustive (c : QCube A) (u v w : V)
    (huv : u ≠ v) (huw : u ≠ w) (hvw : v ≠ w) (hs : c.spx = {u, v, w})
    (s : QSquare A) (hslt : s.1 < c) :
    ∃ i : Fin 3 × ZMod 2, qThreeFaceSquare c u v w huv huw hvw hs i = s := by
  obtain ⟨a, ha, he⟩ := exists_qCube_facet_of_card s.1 c hslt.le
    (by rw [qCube_three_card c u v w huv huw hvw hs, s.2])
  rw [hs, Finset.mem_insert, Finset.mem_insert, Finset.mem_singleton] at ha
  rcases ha with ha | ha | ha
  · subst a
    exact ⟨(0, s.1.sgn u), Subtype.ext he.symm⟩
  · subst a
    exact ⟨(1, s.1.sgn v), Subtype.ext he.symm⟩
  · subst a
    refine ⟨(2, s.1.sgn w), Subtype.ext ?_⟩
    have h21 : (2 : Fin 3) ≠ 1 := by decide
    simpa [qThreeFaceSquare, qThreeFacetSquare, qCubeFacetIndex, qThreeDirection, h21] using he.symm

end FiniteChains.Davis
