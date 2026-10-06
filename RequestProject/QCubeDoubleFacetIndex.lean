import RequestProject.QCubeFacetIndex
import RequestProject.QCubeEdgeChainEmbedding
import RequestProject.QCubeThreeSubdivision

/-! Actual codimension-two faces and their coordinate signs. -/
namespace FiniteChains.Davis
open RACG Mirror Comb
variable {V : Type} [DecidableEq V] {A : CommRel V}

def qCubeDoubleFacet (c : QCube A) (a b : V) (s t : ZMod 2) : QCube A :=
  qCubeFacet (qCubeFacet c a s) b t

@[simp] theorem qCubeDoubleFacet_sgn_first (c : QCube A) (a b : V) (hne : a ≠ b)
    (s t : ZMod 2) : (qCubeDoubleFacet c a b s t).sgn a = s := by
  simp [qCubeDoubleFacet, qCubeFacet, hne]

@[simp] theorem qCubeDoubleFacet_sgn_second (c : QCube A) (a b : V)
    (s t : ZMod 2) : (qCubeDoubleFacet c a b s t).sgn b = t := by
  simp [qCubeDoubleFacet]

theorem qCubeDoubleFacet_signs_injective (c : QCube A) (a b : V) (hne : a ≠ b) :
    Function.Injective (fun i : ZMod 2 × ZMod 2 => qCubeDoubleFacet c a b i.1 i.2) := by
  intro ⟨s, t⟩ ⟨u, v⟩ h
  have hs := congrArg (fun d : QCube A => d.sgn a) h
  have ht := congrArg (fun d : QCube A => d.sgn b) h
  simp only [qCubeDoubleFacet_sgn_first _ _ _ hne] at hs
  simp only [qCubeDoubleFacet_sgn_second] at ht
  exact Prod.ext hs ht

theorem qCubeDoubleFacet_spx (c : QCube A) (a b : V) (s t : ZMod 2) :
    (qCubeDoubleFacet c a b s t).spx = (c.spx.erase a).erase b := rfl

def qThreeEdgeCell (c : QCube A) (u v w : V) (i : Fin 3 × ZMod 2 × ZMod 2) : QCube A :=
  if i.1 = 0 then qCubeDoubleFacet c u v i.2.1 i.2.2
  else if i.1 = 1 then qCubeDoubleFacet c u w i.2.1 i.2.2
  else qCubeDoubleFacet c v w i.2.1 i.2.2

theorem qThreeEdgeCell_spx (c : QCube A) (u v w : V)
    (huv : u ≠ v) (huw : u ≠ w) (hvw : v ≠ w) (hs : c.spx = {u, v, w})
    (i : Fin 3 × ZMod 2 × ZMod 2) :
    (qThreeEdgeCell c u v w i).spx = if i.1 = 0 then {w} else if i.1 = 1 then {v} else {u} := by
  have h0 : (c.spx.erase u).erase v = {w} := by
    ext x
    simp only [hs, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton]
    aesop
  have h1 : (c.spx.erase u).erase w = {v} := by
    ext x
    simp only [hs, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton]
    aesop
  have h2 : (c.spx.erase v).erase w = {u} := by
    ext x
    simp only [hs, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton]
    aesop
  obtain ⟨e, s, t⟩ := i
  fin_cases e
  · simpa [qThreeEdgeCell, qCubeDoubleFacet_spx] using h0
  · simpa [qThreeEdgeCell, qCubeDoubleFacet_spx] using h1
  · have h21 : (2 : Fin 3) ≠ 1 := by decide
    simpa [qThreeEdgeCell, qCubeDoubleFacet_spx, h21] using h2

theorem qThreeEdgeCell_injective (c : QCube A) (u v w : V)
    (huv : u ≠ v) (huw : u ≠ w) (hvw : v ≠ w) (hs : c.spx = {u, v, w}) :
    Function.Injective (qThreeEdgeCell c u v w) := by
  intro ⟨e, s, t⟩ ⟨f, a, b⟩ h
  have he := congrArg QCube.spx h
  rw [qThreeEdgeCell_spx c u v w huv huw hvw hs,
    qThreeEdgeCell_spx c u v w huv huw hvw hs] at he
  have h21 : (2 : Fin 3) ≠ 1 := by decide
  fin_cases e <;> fin_cases f
  · have hp := qCubeDoubleFacet_signs_injective c u v huv h
    exact Prod.ext rfl hp
  · have hwv : w = v := by simpa using he
    exact False.elim (hvw hwv.symm)
  · have hwu : w = u := by simpa [h21] using he
    exact False.elim (huw hwu.symm)
  · have hvw' : v = w := by simpa using he
    exact False.elim (hvw hvw')
  · have hp := qCubeDoubleFacet_signs_injective c u w huw h
    exact Prod.ext rfl hp
  · have hvu : v = u := by simpa [h21] using he
    exact False.elim (huv hvu.symm)
  · have huw' : u = w := by simpa [h21] using he
    exact False.elim (huw huw')
  · have huv' : u = v := by simpa [h21] using he
    exact False.elim (huv huv')
  · have hp : (s, t) = (a, b) := qCubeDoubleFacet_signs_injective c v w hvw
      (by simpa [qThreeEdgeCell, h21] using h)
    exact Prod.ext rfl hp

/-- Each indexed codimension-two face is an actual edge cube. -/
def qThreeEdge (c : QCube A) (u v w : V)
    (huv : u ≠ v) (huw : u ≠ w) (hvw : v ≠ w) (hs : c.spx = {u, v, w})
    (i : Fin 3 × ZMod 2 × ZMod 2) : QEdge A :=
  ⟨qThreeEdgeCell c u v w i, by
    rw [qThreeEdgeCell_spx c u v w huv huw hvw hs i]
    split_ifs <;> simp⟩

theorem qThreeEdge_injective (c : QCube A) (u v w : V)
    (huv : u ≠ v) (huw : u ≠ w) (hvw : v ≠ w) (hs : c.spx = {u, v, w}) :
    Function.Injective (qThreeEdge c u v w huv huw hvw hs) := by
  intro i j h
  exact qThreeEdgeCell_injective c u v w huv huw hvw hs (congrArg Subtype.val h)

end FiniteChains.Davis
