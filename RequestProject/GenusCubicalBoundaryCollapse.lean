import RequestProject.QCubeTruncatedBoundaryCollapse
import RequestProject.GenusSpineCells

/-! Actual genus cube boundaries vanish under the chosen geometric collapse. -/
namespace FiniteChains.Davis.Genus
open RACG Mirror Comb ASC
variable (q : ℕ) [NeZero q]

theorem genus_threeCube_occurs_in_collapse
    (c : QThreeCube (cmpRel (GenusVertex q))) :
    ∃ f, (qCubeToCoordinate c.1, f) ∈ genusChainCollapse q := by
  apply (genusChainCollapse_isPairCollapse q).covers
  apply mem_topCubes.mpr
  rw [freeSet_qCubeToCoordinate]
  exact ⟨genus_simplex_mem_faces q c.1.isSimplex, c.2⟩

theorem genus_truncated_three_boundary_collapse_zero
    (r : QThreeCube (cmpRel (GenusVertex q)) →₀ ℤ) :
    CollapseChain.cmap (cubeBdry (V := GenusVertex q)) (genusChainCollapse q)
      (qThreeTruncatedCoordinateBoundary r) = 0 := by
  apply qThreeTruncatedBoundary_collapse_zero _ (genusChainCollapse_isChainCollapse q)
  intro c _
  exact genus_threeCube_occurs_in_collapse q c

/-- Every cut cell surviving the actual genus collapse has at most two vertices. -/
theorem genusSpine_cut_card_le_two (σ : CutCell (cmpRel (GenusVertex q)))
    (hσ : (Sum.inr σ : GenusTruncatedCell q) ∈ genusSpineCellSet q) : σ.1.card ≤ 2 := by
  have hmax := genus_chain_card_le_three q (genus_simplex_mem_faces q σ.2.2)
  by_contra hnot
  have hthree : σ.1.card = 3 := by omega
  have hremoved := genusChainCollapse_removes_cut_triangle q σ.1
    ⟨genus_simplex_mem_faces q σ.2.2, hthree⟩
  exact hσ.2 hremoved

/-- The actual surviving-spine comparison lands entirely in quotient cube dimension
at most two, including its retained cut cells. -/
theorem genusSpineCellToOld_dimension_le_two (c : GenusSpineCell q) :
    (genusSpineCellToOld q c).1.spx.card ≤ 2 := by
  cases hc : c.1 with
  | inl d =>
      have hd := c.2.1
      rw [hc] at hd
      simpa [genusSpineCellToOld, truncatedCellRetraction, hc, truncatedCellDimension] using hd
  | inr σ =>
      have hσ := c.2
      rw [hc] at hσ
      have hcard := genusSpine_cut_card_le_two q σ hσ
      simpa [genusSpineCellToOld, truncatedCellRetraction, hc, posQCube] using hcard

end FiniteChains.Davis.Genus
