import RequestProject.GenusChainCollapse
import RequestProject.TruncatedCellDimension
import RequestProject.ChamberQuotientFinite
import RequestProject.StrictOrderComplex
import RequestProject.CombData

/-! Surviving cells of the actual chosen truncated genus-block collapse. -/

namespace FiniteChains.Davis.Genus
open RACG Mirror ASC
variable (q : ℕ) [NeZero q]

abbrev GenusTruncatedCell := TruncatedCell (cmpRel (GenusVertex q))

def genusSpineCellSet : Set (GenusTruncatedCell q) :=
  {c | truncatedCellDimension c ≤ 2 ∧
    truncatedFaceIndex c ∉ (genusChainCollapse q).map Prod.snd}

/-- The cells of the actual spine, retaining their face order. -/
def GenusSpineCell := {c : GenusTruncatedCell q // c ∈ genusSpineCellSet q}

instance : PartialOrder (GenusSpineCell q) := Subtype.partialOrder _

instance : Finite (GenusSpineCell q) :=
  Finite.of_injective (fun c : GenusSpineCell q => truncatedFaceIndex c.1)
    (fun _ _ h => Subtype.ext (truncatedFaceIndex_injective h))

theorem genus_removedFace_dimension (c : GenusTruncatedCell q)
    (hc : truncatedFaceIndex c ∈ (genusChainCollapse q).map Prod.snd) :
    truncatedCellDimension c = 2 := by
  obtain ⟨p, hp, he⟩ := List.mem_map.mp hc
  have hi := (genusChainCollapse_isPairCollapse q).pair_inc hp
  rw [he] at hi
  cases c with
  | inl c =>
    have hd : (freeSet (qCubeToCoordinate c.1)).card = 2 := by
      by_contra hn
      rw [freeSet_qCubeToCoordinate] at hn
      simp [truncatedFaceIndex, spineInc, hn] at hi
    simpa [truncatedCellDimension] using hd
  | inr σ =>
    have hs : IsTri (orderComplex (GenusVertex q)) σ.1 := by
      by_contra hn
      simp [truncatedFaceIndex, spineInc, hn] at hi
    change σ.1.card - 1 = 2
    rw [hs.2]

/-- Removing the chosen two-faces after the top cubes leaves a genuine subcomplex
incidence set: every face of a surviving cell also survives. -/
theorem genusSpineCellSet_down_closed {c d : GenusTruncatedCell q}
    (hc : c ∈ genusSpineCellSet q) (hdc : d ≤ c) : d ∈ genusSpineCellSet q := by
  refine ⟨le_trans (truncatedCellDimension_monotone hdc) hc.1, ?_⟩
  intro hd
  have hdim := genus_removedFace_dimension q d hd
  have hdimc : truncatedCellDimension c = 2 := by
    have hm := truncatedCellDimension_monotone hdc
    have hc2 := hc.1
    omega
  have he := truncatedCell_eq_of_le_of_dimension_eq hdc (hdim.trans hdimc.symm)
  exact hc.2 (he ▸ hd)

/-- Every vertex and edge survives, since all chosen faces have dimension two. -/
theorem genusSpineCellSet_of_dimension_lt_two (c : GenusTruncatedCell q)
    (hc : truncatedCellDimension c < 2) : c ∈ genusSpineCellSet q := by
  refine ⟨Nat.le_of_lt hc, ?_⟩
  intro hm
  have hd := genus_removedFace_dimension q c hm
  omega

theorem genusSpineCell_dimension_le_two (c : GenusSpineCell q) :
    truncatedCellDimension c.1 ≤ 2 := c.2.1

theorem genus_simplex_mem_faces {σ : Finset (GenusVertex q)}
    (hσ : IsSimplex (cmpRel (GenusVertex q)) σ) :
    σ ∈ (orderComplex (GenusVertex q)).faces := by
  intro a ha b hb _
  exact (isSimplex_cmpRel_iff.mp hσ) a ha b hb

theorem genus_oldCell_removed_iff_dimension_three
    (c : QOld (cmpRel (GenusVertex q))) :
    qCubeToCoordinate c.1 ∈ (genusChainCollapse q).map Prod.fst ↔
      truncatedCellDimension (Sum.inl c : GenusTruncatedCell q) = 3 := by
  constructor
  · intro hm
    obtain ⟨p, hp, he⟩ := List.mem_map.mp hm
    have ht := (genusChainCollapse_isPairCollapse q).top_mem hp
    rw [he] at ht
    simpa [truncatedCellDimension] using (mem_topCubes.mp ht).2
  · intro hd
    have ht : qCubeToCoordinate c.1 ∈ topCubes (orderComplex (GenusVertex q)) := by
      apply mem_topCubes.mpr
      rw [freeSet_qCubeToCoordinate]
      exact ⟨genus_simplex_mem_faces q c.1.isSimplex, hd⟩
    obtain ⟨f, hf⟩ := (genusChainCollapse_isPairCollapse q).covers ht
    exact List.mem_map.mpr ⟨(qCubeToCoordinate c.1, f), hf, rfl⟩

theorem genusTruncatedCell_dimension_le_three (c : GenusTruncatedCell q) :
    truncatedCellDimension c ≤ 3 := by
  cases c with
  | inl c => exact genus_chain_card_le_three q (genus_simplex_mem_faces q c.1.isSimplex)
  | inr σ =>
    have hs := genus_chain_card_le_three q (genus_simplex_mem_faces q σ.2.2)
    change σ.1.card - 1 ≤ 3
    omega

theorem genus_cutCell_dimension_le_two (σ : CutCell (cmpRel (GenusVertex q))) :
    truncatedCellDimension (Sum.inr σ : GenusTruncatedCell q) ≤ 2 := by
  have hs := genus_chain_card_le_three q (genus_simplex_mem_faces q σ.2.2)
  change σ.1.card - 1 ≤ 2
  omega

/-- Exact survival criterion: remove precisely the chosen top cells and their chosen faces. -/
theorem genusSpineCellSet_iff_survives (c : GenusTruncatedCell q) :
    c ∈ genusSpineCellSet q ↔
      truncatedFaceIndex c ∉ (genusChainCollapse q).map Prod.snd ∧
      (match c with
        | .inl d => qCubeToCoordinate d.1 ∉ (genusChainCollapse q).map Prod.fst
        | .inr _ => True) := by
  cases c with
  | inl c =>
    have hmax := genusTruncatedCell_dimension_le_three q (Sum.inl c)
    dsimp only
    rw [genus_oldCell_removed_iff_dimension_three]
    constructor
    · intro h
      exact ⟨h.2, by have := h.1; omega⟩
    · rintro ⟨hf, ht⟩
      exact ⟨by omega, hf⟩
  | inr σ =>
    constructor
    · intro h
      exact ⟨h.2, trivial⟩
    · rintro ⟨hf, _⟩
      exact ⟨genus_cutCell_dimension_le_two q σ, hf⟩

theorem genusSpineCellDimension_strictMono :
    StrictMono (fun c : GenusSpineCell q => truncatedCellDimension c.1) := by
  intro c d hcd
  apply truncatedCellDimension_strictMono
  exact hcd

/-- The genuine order nerve of the spine has no simplices above dimension two. -/
theorem genusSpine_chain_card_le_three {s : Finset (GenusSpineCell q)}
    (hs : s ∈ (orderComplex (GenusSpineCell q)).faces) : s.card ≤ 3 := by
  classical
  let dim : GenusSpineCell q → ℕ := fun c => truncatedCellDimension c.1
  have hinj : Set.InjOn dim (s : Set (GenusSpineCell q)) := by
    intro a ha b hb he
    by_cases hab : a = b
    · exact hab
    · rcases hs ha hb hab with h | h
      · exact Subtype.ext (truncatedCell_eq_of_le_of_dimension_eq h he)
      · exact Subtype.ext (truncatedCell_eq_of_le_of_dimension_eq h he.symm).symm
  have hsub : s.image dim ⊆ Finset.range 3 := by
    intro n hn
    obtain ⟨c, _, rfl⟩ := Finset.mem_image.mp hn
    exact Finset.mem_range.mpr (Nat.lt_succ_of_le c.2.1)
  calc
    s.card = (s.image dim).card := (Finset.card_image_of_injOn hinj).symm
    _ ≤ (Finset.range 3).card := Finset.card_le_card hsub
    _ = 3 := Finset.card_range _

/-- The genuine finite simplicial two-complex associated with the surviving cells. -/
def genusSpineCx : Comb.Complex2 := Comb.strictOrderCx (GenusSpineCell q)

instance : Finite (genusSpineCx q).V := inferInstanceAs (Finite (GenusSpineCell q))
instance : Finite (genusSpineCx q).E :=
  inferInstanceAs (Finite (Comb.strictOrderCx (GenusSpineCell q)).E)
instance : Finite (genusSpineCx q).F :=
  inferInstanceAs (Finite (Comb.strictOrderCx (GenusSpineCell q)).F)

def genusSpineCellToOld (c : GenusSpineCell q) : QOld (cmpRel (GenusVertex q)) :=
  truncatedCellRetraction c.1

theorem genusSpineCellToOld_monotone : Monotone (genusSpineCellToOld q) :=
  fun _ _ h => truncatedCellRetraction_monotone h

/-- The comparison to the older cube-poset block is constructed from the actual cells. -/
def genusSpineToOld : Comb.Hom (genusSpineCx q) (Comb.orderCx (QOld (cmpRel (GenusVertex q)))) :=
  Comb.Hom.comp (Comb.orderCxMap (genusSpineCellToOld q) (genusSpineCellToOld_monotone q))
    (Comb.strictOrderIncl (GenusSpineCell q))

/-- The full cut one-skeleton survives. This supplies the cells of the canonical markings. -/
def genusSpineCutCell (σ : NeSpx (cmpRel (GenusVertex q))) (hσ : σ.1.card ≤ 2) :
    GenusSpineCell q :=
  ⟨Sum.inr ⟨σ.1, σ.2⟩, genusSpineCellSet_of_dimension_lt_two q _ (by
    change σ.1.card - 1 < 2
    omega)⟩

theorem genusSpineCutCell_le {σ τ : NeSpx (cmpRel (GenusVertex q))}
    (hσ : σ.1.card ≤ 2) (hτ : τ.1.card ≤ 2) (h : σ ≤ τ) :
    genusSpineCutCell q σ hσ ≤ genusSpineCutCell q τ hτ := h

@[simp] theorem genusSpineCellToOld_cutCell (σ : NeSpx (cmpRel (GenusVertex q)))
    (hσ : σ.1.card ≤ 2) :
    genusSpineCellToOld q (genusSpineCutCell q σ hσ) = posQCube σ := rfl

instance : Nonempty (GenusSpineCell q) :=
  ⟨genusSpineCutCell q (spx1 (cC (gc q))) (by simp [spx1_val])⟩

end FiniteChains.Davis.Genus
