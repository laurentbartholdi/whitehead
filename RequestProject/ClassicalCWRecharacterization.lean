import RequestProject.ClassicalCWCellEmbedding

/-! Replace the characteristic maps on an embedded subcomplex by the
literal transported maps of its given CW structure. All ambient open and
closed cells, and hence all subcomplexes, remain the same. This removes
the chart-compatibility ambiguity in InitialIdentification. Unverified. -/

noncomputable section
open scoped Classical
open Set Topology Metric
namespace Whitehead.CWCellEmbedding
open FiniteChains
variable {K L : TwoComplex} (e : CWCellEmbedding K L)

def recharacterizationMap (n : ℕ) (j : RelCWComplex.cell (Set.univ : Set L) n) :
    PartialEquiv (Fin n → ℝ) L :=
  if hj : j ∈ Set.range (e.cellIndex n) then
    ClosedEmbeddingCW.imageCharacteristic e.map e.closedEmbedding n (Classical.choose hj)
  else RelCWComplex.map (C := (Set.univ : Set L)) n j

theorem recharacterizationMap_old (n : ℕ) (j : RelCWComplex.cell (Set.univ : Set K) n) :
    recharacterizationMap e n (e.cellIndex n j) =
      ClosedEmbeddingCW.imageCharacteristic e.map e.closedEmbedding n j := by
  have hj : e.cellIndex n j ∈ Set.range (e.cellIndex n) := ⟨j, rfl⟩
  have he : Classical.choose hj = j := (e.cellIndex n).injective (Classical.choose_spec hj)
  simp only [recharacterizationMap, dif_pos hj, he]

theorem recharacterizationMap_open (n : ℕ) (j : RelCWComplex.cell (Set.univ : Set L) n) :
    recharacterizationMap e n j '' ball 0 1 = CWComplex.openCell (C := (Set.univ : Set L)) n j := by
  by_cases hj : j ∈ Set.range (e.cellIndex n)
  · rw [recharacterizationMap, dif_pos hj, ClosedEmbeddingCW.imageCharacteristic_image]
    change e.map '' CWComplex.openCell (C := (Set.univ : Set K)) n (Classical.choose hj) = _
    rw [e.openCell_image, Classical.choose_spec hj]
  · rw [recharacterizationMap, dif_neg hj]
    rfl

theorem image_closedCell (n : ℕ) (j : RelCWComplex.cell (Set.univ : Set K) n) :
    e.map '' CWComplex.closedCell (C := (Set.univ : Set K)) n j =
      CWComplex.closedCell (C := (Set.univ : Set L)) n (e.cellIndex n j) := by
  rw [← CWComplex.closure_openCell_eq_closedCell,
    ← CWComplex.closure_openCell_eq_closedCell, ← e.openCell_image,
    e.closedEmbedding.closure_image_eq]

theorem recharacterizationMap_closed (n : ℕ) (j : RelCWComplex.cell (Set.univ : Set L) n) :
    recharacterizationMap e n j '' closedBall 0 1 =
      CWComplex.closedCell (C := (Set.univ : Set L)) n j := by
  by_cases hj : j ∈ Set.range (e.cellIndex n)
  · rw [recharacterizationMap, dif_pos hj, ClosedEmbeddingCW.imageCharacteristic_image]
    change e.map '' CWComplex.closedCell (C := (Set.univ : Set K)) n (Classical.choose hj) = _
    rw [image_closedCell, Classical.choose_spec hj]
  · rw [recharacterizationMap, dif_neg hj]
    rfl

def recharacterizedCW : CWComplex (Set.univ : Set L) where
  cell n := RelCWComplex.cell (Set.univ : Set L) n
  map := recharacterizationMap e
  source_eq := by
    intro n j
    by_cases hj : j ∈ Set.range (e.cellIndex n)
    · rw [recharacterizationMap, dif_pos hj]
      exact ClosedEmbeddingCW.imageCharacteristic_source _ _ _ _
    · rw [recharacterizationMap, dif_neg hj]
      exact RelCWComplex.source_eq n j
  continuousOn := by
    intro n j
    by_cases hj : j ∈ Set.range (e.cellIndex n)
    · rw [recharacterizationMap, dif_pos hj]
      exact ClosedEmbeddingCW.imageCharacteristic_continuousOn _ _ _ _
    · rw [recharacterizationMap, dif_neg hj]
      exact RelCWComplex.continuousOn n j
  continuousOn_symm := by
    intro n j
    by_cases hj : j ∈ Set.range (e.cellIndex n)
    · rw [recharacterizationMap, dif_pos hj]
      exact ClosedEmbeddingCW.imageCharacteristic_continuousOn_symm _ _ _ _
    · rw [recharacterizationMap, dif_neg hj]
      exact RelCWComplex.continuousOn_symm n j
  pairwiseDisjoint' := by
    intro a _ b _ hab
    change Disjoint (recharacterizationMap e a.1 a.2 '' ball 0 1)
      (recharacterizationMap e b.1 b.2 '' ball 0 1)
    rw [recharacterizationMap_open, recharacterizationMap_open]
    exact RelCWComplex.disjoint_openCell_of_ne (C := (Set.univ : Set L)) hab
  mapsTo' := by
    intro n j
    by_cases hj : j ∈ Set.range (e.cellIndex n)
    · let k := Classical.choose hj
      obtain ⟨I, hI⟩ := CWComplex.mapsTo' (C := (Set.univ : Set K)) n k
      refine ⟨fun m => (I m).map (e.cellIndex m), ?_⟩
      intro x hx
      obtain ⟨m, hm, a, ha, hy⟩ := by simpa only [Set.mem_iUnion] using hI hx
      simp only [Set.mem_iUnion]
      refine ⟨m, hm, e.cellIndex m a, Finset.mem_map.mpr ⟨a, ha, rfl⟩, ?_⟩
      rw [recharacterizationMap_closed, ← image_closedCell]
      refine ⟨RelCWComplex.map (C := (Set.univ : Set K)) n k x, hy, ?_⟩
      rw [recharacterizationMap, dif_pos hj]
      rfl
    · obtain ⟨I, hI⟩ := CWComplex.mapsTo' (C := (Set.univ : Set L)) n j
      refine ⟨I, ?_⟩
      intro x hx
      change recharacterizationMap e n j x ∈
        ⋃ m, ⋃ (_ : m < n), ⋃ k ∈ I m, recharacterizationMap e m k '' closedBall 0 1
      simp only [recharacterizationMap_closed]
      rw [recharacterizationMap, dif_neg hj]
      exact hI hx
  closed' := by
    intro A hA hclosed
    apply (CWComplex.closed (Set.univ : Set L) A hA).mpr
    intro n j
    simpa only [recharacterizationMap_closed] using hclosed n j
  union' := by
    simp only [recharacterizationMap_closed]
    exact CWComplex.union

def recharacterizedComplex : TwoComplex where
  space := L
  topology := L.topology
  hausdorff := L.hausdorff
  cw := recharacterizedCW e
  connected := L.connected
  dimension := L.dimension

theorem recharacterized_openCell (n : ℕ) (j : RelCWComplex.cell (Set.univ : Set L) n) :
    @RelCWComplex.openCell L L.topology Set.univ ∅
      (@CWComplex.instRelCWComplex L L.topology Set.univ (recharacterizedCW e)) n j =
      CWComplex.openCell (C := (Set.univ : Set L)) n j :=
  recharacterizationMap_open e n j

def recharacterizedSubcomplex (D : CWComplex.Subcomplex (Set.univ : Set L)) :
    CWComplex.Subcomplex (Set.univ : Set (recharacterizedComplex e)) where
  carrier := D.carrier
  I := D.I
  closed' := D.closed
  union' := by
    change ∅ ∪ (⋃ m, ⋃ j : {j // j ∈ D.I m},
      recharacterizationMap e m j.val '' ball 0 1) = D.carrier
    simp only [recharacterizationMap_open]
    exact D.union

def recharacterizedEmbedding : CWCellEmbedding K (recharacterizedComplex e) where
  map := e.map
  closedEmbedding := e.closedEmbedding
  cellIndex := e.cellIndex
  openCell_image n j := (e.openCell_image n j).trans (recharacterized_openCell e n _).symm

theorem recharacterizedEmbedding_characteristic (n : ℕ)
    (j : RelCWComplex.cell (Set.univ : Set K) n) (x : Fin n → ℝ) :
    @CWComplex.map L L.topology Set.univ (recharacterizedCW e) n (e.cellIndex n j) x =
      e.map (RelCWComplex.map (C := (Set.univ : Set K)) n j x) := by
  change recharacterizationMap e n (e.cellIndex n j) x = _
  rw [recharacterizationMap_old]
  rfl

theorem recharacterizedComplex_finite (hL : FiniteCells L) :
    FiniteCells (recharacterizedComplex e) := hL

end Whitehead.CWCellEmbedding

namespace Whitehead
variable {K L : TwoComplex} (C : CWComplex.Subcomplex (Set.univ : Set L))
  (e : K ≃ₜ (C : Set L)) (he : InitialIdentification C e)

def initialCellEmbedding : CWCellEmbedding K L where
  map := ⟨fun x => (e x).val, continuous_subtype_val.comp e.continuous⟩
  closedEmbedding := C.closed.isClosedEmbedding_subtypeVal.comp e.isClosedEmbedding
  cellIndex n := {
    toFun := fun j => (Classical.choose (he n) j).val
    inj' := fun _ _ hjk => (Classical.choose (he n)).injective (Subtype.ext hjk) }
  openCell_image n j := Classical.choose_spec (he n) j

theorem initialCellEmbedding_range : Set.range (initialCellEmbedding C e he).map = C := by
  ext y
  constructor
  · rintro ⟨x, rfl⟩
    exact (e x).property
  · intro hy
    obtain ⟨x, hx⟩ := e.surjective ⟨y, hy⟩
    exact ⟨x, congrArg Subtype.val hx⟩

theorem initialCellEmbedding_cellRange (n : ℕ) :
    Set.range ((initialCellEmbedding C e he).cellIndex n) = C.I n := by
  ext j
  constructor
  · rintro ⟨i, rfl⟩
    exact (Classical.choose (he n) i).property
  · intro hj
    obtain ⟨i, hi⟩ := (Classical.choose (he n)).surjective ⟨j, hj⟩
    exact ⟨i, congrArg Subtype.val hi⟩

end Whitehead
