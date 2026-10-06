import Mathlib.Topology.Homotopy.HomotopyGroup
import Mathlib.Topology.Connected.Basic

/-! Connectedness of the boundary used in Mathlib's two-dimensional based-loop model. -/

open scoped unitInterval Topology
namespace Whitehead

/-- A side of the unit square. -/
def squareEdge (i : Fin 2) (v : I) (s : I) : Fin 2 → I :=
  fun j => if j = i then v else s

theorem squareEdge_continuous (i : Fin 2) (v : I) : Continuous (squareEdge i v) := by
  apply continuous_pi
  intro j
  by_cases h : j = i
  · simpa [squareEdge, h] using (continuous_const : Continuous (fun _ : I => v))
  · exact continuous_id.congr fun s => by simp [squareEdge, h]

theorem square_boundary_eq : Cube.boundary (Fin 2) =
    ((Set.range (squareEdge 0 0) ∪ Set.range (squareEdge 1 0)) ∪
      Set.range (squareEdge 0 1)) ∪ Set.range (squareEdge 1 1) := by
  ext t
  constructor
  · rintro ⟨i, hi⟩
    fin_cases i
    · rcases hi with hi | hi
      · exact Or.inl (Or.inl (Or.inl ⟨t 1, by apply funext; intro j; fin_cases j; exact hi.symm; rfl⟩))
      · exact Or.inl (Or.inr ⟨t 1, by apply funext; intro j; fin_cases j; exact hi.symm; rfl⟩)
    · rcases hi with hi | hi
      · exact Or.inl (Or.inl (Or.inr ⟨t 0, by apply funext; intro j; fin_cases j; rfl; exact hi.symm⟩))
      · exact Or.inr ⟨t 0, by apply funext; intro j; fin_cases j; rfl; exact hi.symm⟩
  · rintro (((⟨s, rfl⟩ | ⟨s, rfl⟩) | ⟨s, rfl⟩) | ⟨s, rfl⟩)
    · exact ⟨0, Or.inl (by simp [squareEdge])⟩
    · exact ⟨1, Or.inl (by simp [squareEdge])⟩
    · exact ⟨0, Or.inr (by simp [squareEdge])⟩
    · exact ⟨1, Or.inr (by simp [squareEdge])⟩

/-- The boundary of the two-dimensional cube is preconnected. -/
theorem square_boundary_isPreconnected : IsPreconnected (Cube.boundary (Fin 2)) := by
  rw [square_boundary_eq]
  have he (i : Fin 2) (v : I) : IsPreconnected (Set.range (squareEdge i v)) :=
    isPreconnected_range (squareEdge_continuous i v)
  have h00 : squareEdge 0 0 0 = squareEdge 1 0 0 := by
    ext j; fin_cases j <;> simp [squareEdge]
  have h10 : squareEdge 0 1 0 = squareEdge 1 0 1 := by
    ext j; fin_cases j <;> simp [squareEdge]
  have h01 : squareEdge 1 1 0 = squareEdge 0 0 1 := by
    ext j; fin_cases j <;> simp [squareEdge]
  have hleft : IsPreconnected (Set.range (squareEdge 0 0) ∪ Set.range (squareEdge 1 0)) := (he 0 0).union' ⟨squareEdge 0 0 0, ⟨0, rfl⟩, ⟨0, h00.symm⟩⟩ (he 1 0)
  have hthree : IsPreconnected ((Set.range (squareEdge 0 0) ∪ Set.range (squareEdge 1 0)) ∪ Set.range (squareEdge 0 1)) := hleft.union'
    ⟨squareEdge 0 1 0, Or.inr ⟨1, h10.symm⟩, ⟨0, rfl⟩⟩ (he 0 1)
  exact hthree.union'
    ⟨squareEdge 1 1 0, Or.inl (Or.inl ⟨1, h01.symm⟩), ⟨0, rfl⟩⟩ (he 1 1)

end Whitehead
