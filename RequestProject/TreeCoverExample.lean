import RequestProject.TreeCoverTheoremA

/-!
# Non-vacuity of the tree-collapse form of Theorem A

The statement `FiniteChains.Comb.SpanningTree.hasAcyclicRegularCover_of_topChains` is applied
here to a complex whose spanning tree is not trivial: the *interval*, two vertices joined by an
edge.  Its spanning tree consists of that edge, so the collapse is the empty presentation, the
chains of condition (1) exist in every length (take all of them empty), and the theorem yields
a connected acyclic regular cover of the interval.
-/

namespace FiniteChains
namespace Comb
namespace SpanningTree

universe u

/-- The interval: two vertices, one edge, no two-cells. -/
def intervalComplex : Complex2.{u} where
  V := ULift.{u} Bool
  E := PUnit.{u + 1}
  F := PEmpty.{u + 1}
  src _ := ULift.up false
  tgt _ := ULift.up true
  base := PEmpty.elim
  att := PEmpty.elim
  att_isLoop := fun f => f.elim

/-- The spanning tree of the interval: its only edge. -/
def intervalTree : SpanningTree intervalComplex.{u} where
  root := ULift.up false
  ht a := if a.down then 1 else 0
  isTree _ := True
  up a _ := (PUnit.unit, false)
  ht_root := rfl
  ht_eq_zero := by
    rintro ⟨a⟩ ha
    cases a
    · rfl
    · simp at ha
  up_src := by
    rintro ⟨a⟩ ha
    cases a
    · exact absurd rfl ha
    · rfl
  up_ht := by
    rintro ⟨a⟩ ha
    cases a
    · exact absurd rfl ha
    · rfl
  isTree_iff := fun _ =>
    ⟨fun _ => ⟨ULift.up true, by intro h; exact Bool.noConfusion (congrArg ULift.down h), rfl⟩,
      fun _ => trivial⟩

instance : IsEmpty (NonTree intervalTree.{u}) := ⟨fun x => x.2 trivial⟩

instance : Fintype intervalComplex.{u}.F := inferInstanceAs (Fintype PEmpty.{u + 1})

instance : DecidableEq intervalComplex.{u}.F := inferInstanceAs (DecidableEq PEmpty.{u + 1})

noncomputable instance : Fintype (NonTree intervalTree.{u}) := Fintype.ofIsEmpty

instance : DecidableEq (NonTree intervalTree.{u}) := fun x => isEmptyElim x

/-- The chains of condition (1) over the collapse of the interval: all stages are empty. -/
noncomputable def intervalChain (n : ℕ) : PresChainTop (treeRel intervalTree.{u}) n where
  gen _ := NonTree intervalTree
  cell _ := intervalComplex.F
  decGen _ := inferInstance
  finGen _ := inferInstance
  finCell _ := inferInstance
  rel _ := treeRel intervalTree
  genIncl _ := id
  genIncl_injective _ := fun _ _ h => h
  cellIncl _ := id
  cellIncl_injective _ := fun _ _ h => h
  rel_incl := fun _ c => c.elim
  baseGen := id
  baseGen_injective := fun _ _ h => h
  baseCell := id
  baseCell_injective := fun _ _ h => h
  rel_base := fun j => j.elim
  zero_pi2 := by
    intro r _ x₀ c _
    have hc : c = 0 := by
      ext F
      exact F.1.2.elim
    rw [hc, map_zero]

/-- **The theorem is not vacuous**: the interval satisfies its hypotheses, and therefore has a
connected acyclic regular cover. -/
theorem intervalComplex_hasAcyclicRegularCover :
    HasAcyclicRegularCover intervalComplex.{u} :=
  hasAcyclicRegularCover_of_topChains intervalTree (fun n => ⟨intervalChain n⟩)

end SpanningTree
end Comb
end FiniteChains
