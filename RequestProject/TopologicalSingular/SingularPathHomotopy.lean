/- Adapted from the local 2026-09-11 Lean audit; see PROVENANCE.json. -/

import RequestProject.TopologicalSingular.SingularTriangleGeometry

/-! # A path homotopy gives an explicit bounding singular two-chain -/


namespace FiniteChains.TopologicalSingular

open Set Topology

universe u
variable {X : Type u} [TopologicalSpace X]

theorem boundary_two_single (σ : Simplex X 2) (r : ℤ) :
    boundary 1 (Finsupp.single σ r) =
      Finsupp.single (face 0 σ) r - Finsupp.single (face 1 σ) r + Finsupp.single (face 2 σ) r := by
  rw [boundary_single, Fin.sum_univ_three]
  change (1 : ℤ) • _ + (-1 : ℤ) • _ + (1 : ℤ) • _ = _
  rw [one_smul, neg_smul, one_smul, one_smul, sub_eq_add_neg]

theorem boundary_constant_two (x : X) (r : ℤ) :
    boundary 1 (Finsupp.single (ContinuousMap.const (Domain 2) x) r) =
      Finsupp.single (ContinuousMap.const (Domain 1) x) r := by
  rw [boundary_two_single]
  change Finsupp.single (ContinuousMap.const (Domain 1) x) r -
    Finsupp.single (ContinuousMap.const (Domain 1) x) r +
    Finsupp.single (ContinuousMap.const (Domain 1) x) r = _
  exact sub_add_cancel _ _

variable {a b : X} {p q : Path a b}

noncomputable def homotopyTriangle0 (F : Path.Homotopy p q) : Simplex X 2 :=
  F.toHomotopy.toContinuousMap.comp squareTriangle0

noncomputable def homotopyTriangle1 (F : Path.Homotopy p q) : Simplex X 2 :=
  F.toHomotopy.toContinuousMap.comp squareTriangle1

theorem homotopyTriangle0_face0 (F : Path.Homotopy p q) :
    face 0 (homotopyTriangle0 F) = ContinuousMap.const _ b := by
  apply ContinuousMap.ext
  intro z
  change F (squareTriangle0 (stdSimplex.map (SimplexCategory.δ (0 : Fin 3)) z)) = b
  rw [(squareTriangle0_faces z).1]
  exact F.target _

theorem homotopyTriangle0_face2 (F : Path.Homotopy p q) :
    face 2 (homotopyTriangle0 F) = pathSimplex p := by
  apply ContinuousMap.ext
  intro z
  change F (squareTriangle0 (stdSimplex.map (SimplexCategory.δ (2 : Fin 3)) z)) = _
  rw [(squareTriangle0_faces z).2.2]
  exact F.apply_zero _

theorem homotopyTriangle1_face0 (F : Path.Homotopy p q) :
    face 0 (homotopyTriangle1 F) = pathSimplex q := by
  apply ContinuousMap.ext
  intro z
  change F (squareTriangle1 (stdSimplex.map (SimplexCategory.δ (0 : Fin 3)) z)) = _
  rw [(squareTriangle1_faces z).1]
  exact F.apply_one _

theorem homotopyTriangle1_face2 (F : Path.Homotopy p q) :
    face 2 (homotopyTriangle1 F) = ContinuousMap.const _ a := by
  apply ContinuousMap.ext
  intro z
  change F (squareTriangle1 (stdSimplex.map (SimplexCategory.δ (2 : Fin 3)) z)) = a
  rw [(squareTriangle1_faces z).2.2]
  exact F.source _

theorem homotopyTriangle_diagonal (F : Path.Homotopy p q) :
    face 1 (homotopyTriangle0 F) = face 1 (homotopyTriangle1 F) := by
  apply ContinuousMap.ext
  intro z
  change F (squareTriangle0 (stdSimplex.map (SimplexCategory.δ (1 : Fin 3)) z)) =
    F (squareTriangle1 (stdSimplex.map (SimplexCategory.δ (1 : Fin 3)) z))
  rw [(squareTriangle0_faces z).2.1, (squareTriangle1_faces z).2.1]

noncomputable def homotopyPrism1 (F : Path.Homotopy p q) (r : ℤ) : Chain X 2 :=
  Finsupp.single (homotopyTriangle1 F) r - Finsupp.single (homotopyTriangle0 F) r +
    Finsupp.single (ContinuousMap.const (Domain 2) b) r -
    Finsupp.single (ContinuousMap.const (Domain 2) a) r

theorem boundary_homotopyPrism1 (F : Path.Homotopy p q) (r : ℤ) :
    boundary 1 (homotopyPrism1 F r) = Finsupp.single (pathSimplex q) r - Finsupp.single (pathSimplex p) r := by
  simp only [homotopyPrism1, map_sub, map_add, boundary_two_single,
    homotopyTriangle1_face0, homotopyTriangle1_face2, homotopyTriangle0_face0,
    homotopyTriangle0_face2, homotopyTriangle_diagonal]
  have hc (x : X) (i : Fin 3) : face i (ContinuousMap.const (Domain 2) x) =
      ContinuousMap.const (Domain 1) x := rfl
  simp only [hc]
  abel

theorem pathHomotopic_difference_mem_range (h : p.Homotopic q) (r : ℤ) :
    Finsupp.single (pathSimplex q) r - Finsupp.single (pathSimplex p) r ∈ LinearMap.range (boundary 1) := by
  obtain ⟨F⟩ := h
  exact ⟨homotopyPrism1 F r, boundary_homotopyPrism1 F r⟩

end FiniteChains.TopologicalSingular
