module

/- Adapted from the local 2026-09-11 Lean audit; see PROVENANCE.json. -/

public import RequestProject.TopologicalSingular.SingularPathHomotopy

@[expose] public section

/-! # Path concatenation is addition modulo actual singular boundaries -/


namespace FiniteChains.TopologicalSingular

open Set Topology

universe u
variable {X : Type u} [TopologicalSpace X] {a b c : X}

noncomputable def compositionTriangle (p : Path a b) (q : Path b c) : Simplex X 2 :=
  ⟨fun z => (p.trans q).extend (z.val 1 / 2 + z.val 2),
    (p.trans q).continuous_extend.comp
      ((((continuous_apply 1).comp continuous_subtype_val).div_const 2).add
        ((continuous_apply 2).comp continuous_subtype_val))⟩

theorem compositionTriangle_face0 (p : Path a b) (q : Path b c) :
    face 0 (compositionTriangle p q) = pathSimplex q := by
  apply ContinuousMap.ext
  intro z
  change (p.trans q).extend ((stdSimplex.map (SimplexCategory.δ (0 : Fin 3)) z).val 1 / 2 +
    (stdSimplex.map (SimplexCategory.δ (0 : Fin 3)) z).val 2) = q (stdSimplexHomeomorphUnitInterval z)
  rw [triangle_face_zero]
  change (p.trans q).extend (z.val 0 / 2 + z.val 1) = q (stdSimplexHomeomorphUnitInterval z)
  have hz := z.property.2
  rw [Fin.sum_univ_two] at hz
  have hz1 := z.property.1 1
  rw [Path.extend_trans_of_half_le p q (by linarith)]
  rw [show 2 * (z.val 0 / 2 + z.val 1) - 1 = z.val 1 by linarith]
  exact Path.extend_apply q (mem_Icc_of_mem_stdSimplex z.property 1)

theorem compositionTriangle_face1 (p : Path a b) (q : Path b c) :
    face 1 (compositionTriangle p q) = pathSimplex (p.trans q) := by
  apply ContinuousMap.ext
  intro z
  change (p.trans q).extend ((stdSimplex.map (SimplexCategory.δ (1 : Fin 3)) z).val 1 / 2 +
    (stdSimplex.map (SimplexCategory.δ (1 : Fin 3)) z).val 2) = (p.trans q) (stdSimplexHomeomorphUnitInterval z)
  rw [triangle_face_one]
  change (p.trans q).extend (0 / 2 + z.val 1) = _
  rw [zero_div, zero_add]
  exact Path.extend_apply (p.trans q) (mem_Icc_of_mem_stdSimplex z.property 1)

theorem compositionTriangle_face2 (p : Path a b) (q : Path b c) :
    face 2 (compositionTriangle p q) = pathSimplex p := by
  apply ContinuousMap.ext
  intro z
  change (p.trans q).extend ((stdSimplex.map (SimplexCategory.δ (2 : Fin 3)) z).val 1 / 2 +
    (stdSimplex.map (SimplexCategory.δ (2 : Fin 3)) z).val 2) = p (stdSimplexHomeomorphUnitInterval z)
  rw [triangle_face_two]
  change (p.trans q).extend (z.val 1 / 2 + 0) = p (stdSimplexHomeomorphUnitInterval z)
  rw [add_zero]
  have hz1 := (mem_Icc_of_mem_stdSimplex z.property 1).2
  rw [Path.extend_trans_of_le_half p q (by linarith)]
  rw [show 2 * (z.val 1 / 2) = z.val 1 by ring]
  exact Path.extend_apply p (mem_Icc_of_mem_stdSimplex z.property 1)

theorem boundary_compositionTriangle (p : Path a b) (q : Path b c) (r : ℤ) :
    boundary 1 (Finsupp.single (compositionTriangle p q) r) =
      Finsupp.single (pathSimplex q) r - Finsupp.single (pathSimplex (p.trans q)) r +
        Finsupp.single (pathSimplex p) r := by
  rw [boundary_two_single, compositionTriangle_face0, compositionTriangle_face1,
    compositionTriangle_face2]

theorem path_trans_relation_mem_range (p : Path a b) (q : Path b c) (r : ℤ) :
    Finsupp.single (pathSimplex q) r - Finsupp.single (pathSimplex (p.trans q)) r +
      Finsupp.single (pathSimplex p) r ∈ LinearMap.range (boundary 1) :=
  ⟨Finsupp.single (compositionTriangle p q) r, boundary_compositionTriangle p q r⟩

end FiniteChains.TopologicalSingular
