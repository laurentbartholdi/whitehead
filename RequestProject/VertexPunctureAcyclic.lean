import RequestProject.VertexIntersectionContraction
import RequestProject.NerveRelativeGluing

/-! Augmented acyclicity of the actual punctured three-cube boundary. -/
namespace FiniteChains.Davis
open Comb Nerve

theorem vertexPuncture_left_acyclic : AcyclicIn vertexPunctureLeft := by
  apply acyclicIn_of_subtype _ ⟨vertexPunctureLeftPole.1, vertexPunctureLeftPole.2⟩
  intro c hc hcyc
  exact exists_bdry_eq_of_cycle vertexPunctureLeftProjection vertexPunctureLeftPole
    vertexPunctureLeftProjection_monotone vertexPunctureLeftProjection_le
    vertexPunctureLeftProjection_le_pole hc hcyc

theorem vertexPuncture_right_acyclic : AcyclicIn vertexPunctureRight := by
  apply acyclicIn_of_subtype _ ⟨vertexPunctureRightPole.1, vertexPunctureRightPole.2⟩
  intro c hc hcyc
  exact exists_bdry_eq_of_cycle vertexPunctureRightProjection vertexPunctureRightPole
    vertexPunctureRightProjection_monotone vertexPunctureRightProjection_le
    vertexPunctureRightProjection_le_pole hc hcyc

/-- The two actual coordinate pieces glue along the seven-cell path. -/
theorem vertexPuncturedCube_acyclic :
    ∀ c ∈ Inc VertexPuncturedCube, Nerve.bdry c = 0 →
      ∃ y ∈ Inc VertexPuncturedCube, Nerve.bdry y = c := by
  have h : AcyclicIn (fun _ : VertexPuncturedCube => True) :=
    acyclicIn_union_of_unmixed (fun c => ⟨fun _ => vertexPuncture_cover c, fun _ => trivial⟩)
      (fun c d h _ _ => vertexPuncture_unmixed c d h)
      vertexPuncture_left_acyclic vertexPuncture_right_acyclic
      vertexPuncture_intersection_acyclic
  intro c hc hcyc
  have hc' : c ∈ IncOn (fun _ : VertexPuncturedCube => True) := by
    simpa only [cmap_id] using
      cmap_mem_incOn_of_maps (f := id) monotone_id (fun _ => True.intro) hc
  obtain ⟨y, hy, hdy⟩ := h c hc' hcyc
  exact ⟨y, incOn_le_inc _ hy, hdy⟩

end FiniteChains.Davis
