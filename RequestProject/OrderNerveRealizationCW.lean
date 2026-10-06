import RequestProject.OrderNerveCharacteristicCells
import Mathlib.Topology.CWComplex.Classical.Basic

namespace FiniteChains.Comb
open CategoryTheory Simplicial Topology
open scoped Classical

/-- The actual Mathlib realization of a poset nerve has the genuine CW structure
whose cells are its actual nondegenerate simplices. -/
noncomputable instance orderNerveRealization_cwComplex (P : Type) [PartialOrder P] :
    CWComplex (Set.univ : Set (orderNerveRealization P)) where
  cell n := (nerve P).nonDegenerate n
  map _ s := orderNerveCharacteristicMap s
  source_eq _ s := orderNerveCharacteristicMap_source s
  continuousOn _ s := orderNerveCharacteristicMap_continuousOn s
  continuousOn_symm _ s := orderNerveCharacteristicMap_continuousOn_symm s
  pairwiseDisjoint' := orderNerveCharacteristicMap_pairwiseDisjoint P
  mapsTo' := by
    intro n s
    cases n with
    | zero =>
      refine ⟨fun _ => ∅, ?_⟩
      intro x hx
      have hx0 : x = 0 := Subsingleton.elim _ _
      have he := Metric.mem_sphere.mp hx
      rw [hx0, dist_self] at he
      norm_num at he
    | succ n =>
      obtain ⟨I, hI⟩ := orderNerveCharacteristicMap_boundary s
      let J : ∀ m, Finset ((nerve P).nonDegenerate m) := fun m =>
        if h : m = n then h.symm ▸ I else ∅
      refine ⟨J, ?_⟩
      intro x hx
      obtain ⟨t, ht, hcell⟩ := hI x hx
      simp only [Set.mem_iUnion]
      refine ⟨n, Nat.lt_succ_self n, t, ?_, hcell⟩
      simpa only [J, dif_pos rfl] using ht
  closed' A _ h := orderNerveCharacteristicMap_isClosed P A h
  union' := orderNerveCharacteristicMap_union P

/-- The actual CW realization has no cells above the proved simplicial dimension. -/
theorem orderNerveRealization_cell_isEmpty (P : Type) [PartialOrder P]
    (d : ℕ) [(nerve P).HasDimensionLE d] (n : ℕ) (hn : d < n) :
    IsEmpty (RelCWComplex.cell (Set.univ : Set (orderNerveRealization P)) n) := by
  constructor
  intro s
  exact (not_le_of_gt hn) ((nerve P).dim_le_of_nonDegenerate s d)

end FiniteChains.Comb
