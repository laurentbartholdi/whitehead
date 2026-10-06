module

public import RequestProject.DavisUniversalThree
public import RequestProject.UniversalThreeAugmentation

@[expose] public section

/-! Independence of actual universal-cover fillings modulo three-boundaries. -/
namespace FiniteChains.Davis
open RACG Mirror Comb
universe u
variable {V : Type u} [DecidableEq V] [Fintype V]

/-- Two fillings of the same cover chain differ by an actual lifted three-boundary. -/
theorem fillings_difference_boundary3 (A : CommRel V) (b : QCube A)
    (c d : (uCover (orderCx (QCube A)) b).F →₀ ℤ)
    (h : Comb.bdry2 (uCover (orderCx (QCube A)) b) c =
      Comb.bdry2 (uCover (orderCx (QCube A)) b) d) :
    ∃ y : UOrdTet (QCube A) b →₀ ℤ, uOrdBoundary3 y = c - d := by
  apply exists_universal_bdry3_of_cycle_qCube A b
  rw [map_sub, h, sub_self]

/-- Projected fillings of the same lifted boundary differ by an ordinary three-boundary. -/
theorem projected_fillings_difference_boundary3 (A : CommRel V) (b : QCube A)
    (c d : (uCover (orderCx (QCube A)) b).F →₀ ℤ)
    (h : Comb.bdry2 (uCover (orderCx (QCube A)) b) c =
      Comb.bdry2 (uCover (orderCx (QCube A)) b) d) :
    ∃ y : OrdTet (QCube A) →₀ ℤ,
      ordBoundary3 y = hurewicz (orderCx (QCube A)) b c -
        hurewicz (orderCx (QCube A)) b d := by
  obtain ⟨y, hy⟩ := fillings_difference_boundary3 A b c d h
  refine ⟨Finsupp.mapDomain (fun t : UOrdTet (QCube A) b => t.1.2) y, ?_⟩
  rw [← hurewicz_uOrdBoundary3, hy, map_sub]

end FiniteChains.Davis
