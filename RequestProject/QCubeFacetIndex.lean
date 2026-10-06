import RequestProject.QCubeCanonicalTwoCycles
import RequestProject.QCubeImmediateFaces

/-! Faithful indexing of the actual facets of a quotient cube. -/
namespace FiniteChains.Davis
open RACG Mirror Comb
variable {V : Type} [DecidableEq V] {A : CommRel V}

def qCubeFacetIndex (c : QCube A) (i : {v : V // v ∈ c.spx} × ZMod 2) : QCube A :=
  qCubeFacet c i.1.1 i.2

theorem qCubeFacetIndex_injective (c : QCube A) : Function.Injective (qCubeFacetIndex c) := by
  intro ⟨⟨v, hv⟩, s⟩ ⟨⟨w, hw⟩, t⟩ h
  have he : c.spx.erase v = c.spx.erase w := congrArg QCube.spx h
  have hvw : v = w := by
    by_contra hvw
    have hm : v ∈ c.spx.erase w := Finset.mem_erase.mpr ⟨hvw, hv⟩
    rw [← he] at hm
    exact (Finset.notMem_erase v c.spx) hm
  subst w
  have hst := congrArg (fun d : QCube A => d.sgn v) h
  simp only [qCubeFacetIndex, qCubeFacet_sgn_self] at hst
  exact Prod.ext (Subtype.ext rfl) hst

def qThreeFacetSquare (c : QCube A) (hc : c.spx.card = 3)
    (i : {v : V // v ∈ c.spx} × ZMod 2) : QSquare A :=
  ⟨qCubeFacetIndex c i, by
    change (c.spx.erase i.1.1).card = 2
    rw [Finset.card_erase_of_mem i.1.2, hc]⟩

theorem qThreeFacetSquare_injective (c : QCube A) (hc : c.spx.card = 3) :
    Function.Injective (qThreeFacetSquare c hc) := by
  intro i j h
  exact qCubeFacetIndex_injective c (congrArg Subtype.val h)

/-- Every actual square below a three-cube belongs to its six-facet index. -/
theorem qThreeFacetSquare_exhaustive (c : QCube A) (hc : c.spx.card = 3)
    (s : QSquare A) (hs : s.1 < c) :
    ∃ i : {v : V // v ∈ c.spx} × ZMod 2, qThreeFacetSquare c hc i = s := by
  obtain ⟨v, hv, he⟩ := exists_qCube_facet_of_card s.1 c hs.le (by rw [hc, s.2])
  exact ⟨(⟨v, hv⟩, s.1.sgn v), Subtype.ext he.symm⟩

end FiniteChains.Davis
