import RequestProject.CellularAcyclicBijection
import RequestProject.TreeCoverAcyclicReflection
import RequestProject.InitialRelChainW

/-! Acyclicity of an arbitrary combinatorial two-complex gives the
bijective exponent boundary of its actual spanning-tree presentation.
The one-sheeted covers identify both original cell complexes exactly.
Pending final Lean verification. -/

noncomputable section
open scoped Classical
namespace FiniteChains.Comb
universe u

theorem bdry2_presComplex_eq_expMatrix {A J : Type u} [DecidableEq A]
    (ρ : J → FreeGroup A) : bdry2 (presComplex ρ) = FiniteChains.expMatrix ρ := by
  rw [bdry2_presComplex_eq_expCol]
  apply congrArg (Finsupp.linearCombination ℤ)
  exact funext (expCol_eq_expVec ρ)

private theorem oneSheetProjection_bijective {Q B : Type u} [One Q] [Subsingleton Q] :
    Function.Bijective (Prod.snd : Q × B → B) := by
  constructor
  · intro a b h
    exact Prod.ext (Subsingleton.elim _ _) h
  · intro b
    exact ⟨(1, b), rfl⟩

namespace SpanningTree
variable {D : Complex2.{u}} (T : SpanningTree D)

theorem expMatrix_bijective_of_acyclic (hD : IsAcyclic D) :
    Function.Bijective (FiniteChains.expMatrix (treeRel T)) := by
  let N : Subgroup (FreeGroup (NonTree T)) := ⊤
  let hN : ∀ f, treeRel T f ∈ N := fun _ => Subgroup.mem_top _
  letI : Subsingleton (CovQ T N) := QuotientGroup.subsingleton_quotient_top
  have htree : IsAcyclic (treeCover T N hN) :=
    (isAcyclic_iff_of_cell_bijections (treeCoverProj T N hN)
      oneSheetProjection_bijective oneSheetProjection_bijective oneSheetProjection_bijective).mpr hD
  have hcover : IsAcyclic (coverComplex N (treeRel T) hN) :=
    coverComplex_isAcyclic_of_treeCover T N hN htree
  have hpres : IsAcyclic (presComplex (treeRel T)) :=
    (isAcyclic_iff_of_cell_bijections (coverProj hN)
      ⟨fun _ _ _ => Subsingleton.elim _ _, fun x => ⟨1, Subsingleton.elim _ _⟩⟩
      oneSheetProjection_bijective oneSheetProjection_bijective).mp hcover
  have hb : Function.Bijective (bdry2 (presComplex (treeRel T))) :=
    ⟨hpres.h2, fun z => hpres.h1 z (bdry1_presComplex (treeRel T) z)⟩
  rwa [bdry2_presComplex_eq_expMatrix] at hb

end SpanningTree
end FiniteChains.Comb
