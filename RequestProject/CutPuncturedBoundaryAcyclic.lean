import RequestProject.VertexPunctureAcyclic
import RequestProject.PositiveBoundaryCoordinates

/-! Actual augmented fillings on the boundary after its cut facet is removed. -/
namespace FiniteChains.Davis
open RACG Mirror Comb Nerve
variable {V : Type} [Fintype V] [DecidableEq V] {A : CommRel V}

theorem positiveRetainedBoundary_acyclic (t : QOld A)
    (ht : t.1.sgn = 0) (hcard : t.1.spx.card = 3) :
    ∀ c ∈ Inc (RetainedProperBoundary t), Nerve.bdry c = 0 →
      ∃ y ∈ Inc (RetainedProperBoundary t), Nerve.bdry y = c :=
  exists_bdry_eq_of_cycle_of_orderIso
    (positiveBoundaryOrderIso t ht (positiveThreeCubeCoordinates t hcard))
    vertexPuncturedCube_acyclic

/-- The order homotopy to the retained proper faces supplies the missing prism. -/
theorem positiveCutPuncturedBoundary_acyclic (t : QOld A)
    (hne : t.1.spx.Nonempty) (ht : t.1.sgn = 0) (hcard : t.1.spx.card = 3) :
    ∀ c ∈ Inc (CutPuncturedBoundary t hne), Nerve.bdry c = 0 →
      ∃ y ∈ Inc (CutPuncturedBoundary t hne), Nerve.bdry y = c := by
  let r := cutBoundaryRetraction t hne
  let s := cutBoundarySection t hne
  have hr := cutBoundaryRetraction_monotone t hne
  have hs := cutBoundarySection_monotone t hne
  intro c hc hcyc
  obtain ⟨y, hy, hdy⟩ := positiveRetainedBoundary_acyclic t ht hcard
    (cmap r c) (cmap_mem_inc_of_monotone hr hc)
    (by rw [← cmap_bdry, hcyc, map_zero])
  have hp := bdry_prism_add_prism_bdry id (s ∘ r) c
  rw [hcyc, map_zero, add_zero, cmap_id] at hp
  refine ⟨cmap s y - prism id (s ∘ r) c,
    AddSubgroup.sub_mem _ (cmap_mem_inc_of_monotone hs hy)
      (prism_mem_inc monotone_id (hs.comp hr)
        (cutBoundary_le_section_retraction t hne) hc), ?_⟩
  rw [map_sub, ← cmap_bdry, hdy, cmap_comp, hp]
  abel

end FiniteChains.Davis
