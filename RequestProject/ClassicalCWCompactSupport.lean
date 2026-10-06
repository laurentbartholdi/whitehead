import Mathlib.Topology.CWComplex.Classical.Basic
import Mathlib.Topology.Compactness.Compact
import Mathlib.Data.Set.Finite.Lattice

/-! Compact subsets of an original classical Hausdorff CW complex meet only
finitely many original open cells. The proof uses the actual weak topology
and closure-finiteness axioms. Pending Lean verification. -/

noncomputable section
open scoped Classical
open Set Topology

namespace FiniteChains.ClassicalCW

variable {X : Type} [TopologicalSpace X] [T2Space X]
  [CWComplex (Set.univ : Set X)]

/-- At most one selected point lies in each original open cell. -/
def CellSeparated (S : Set X) : Prop :=
  ∀ n (j : RelCWComplex.cell (Set.univ : Set X) n),
    (S ∩ RelCWComplex.openCell n j).Subsingleton

omit [T2Space X] in
theorem CellSeparated.mono {S T : Set X} (hS : CellSeparated S) (hTS : T ⊆ S) :
    CellSeparated T := by
  intro n j x hx y hy
  exact hS n j ⟨hTS hx.1, hx.2⟩ ⟨hTS hy.1, hy.2⟩

omit [T2Space X] in
theorem CellSeparated.finite_inter_closedCell {S : Set X} (hS : CellSeparated S)
    (n : ℕ) (j : RelCWComplex.cell (Set.univ : Set X) n) :
    (S ∩ RelCWComplex.closedCell n j).Finite := by
  obtain ⟨I, hI⟩ := CWComplex.cellFrontier_subset_finite_openCell (C := (Set.univ : Set X)) n j
  have hf : (⋃ m : Fin n, ⋃ k ∈ I m.val, S ∩ RelCWComplex.openCell m.val k).Finite := by
    apply Set.finite_iUnion
    intro m
    exact (I m.val).finite_toSet.biUnion (fun k _ => (hS m.val k).finite)
  have hfront : (S ∩ RelCWComplex.cellFrontier n j).Finite := by
    apply hf.subset
    intro x hx
    obtain ⟨m, hm, k, hk, hcell⟩ := by
      simpa only [Set.mem_iUnion] using hI hx.2
    exact Set.mem_iUnion.mpr ⟨⟨m, hm⟩,
      Set.mem_iUnion.mpr ⟨k, Set.mem_iUnion.mpr ⟨hk, hx.1, hcell⟩⟩⟩
  rw [← RelCWComplex.cellFrontier_union_openCell_eq_closedCell, Set.inter_union_distrib_left]
  exact hfront.union (hS n j).finite

theorem CellSeparated.isClosed {S : Set X} (hS : CellSeparated S) : IsClosed S := by
  apply (CWComplex.closed (Set.univ : Set X) S (Set.subset_univ _)).mpr
  intro n j
  exact (hS.finite_inter_closedCell n j).isClosed

theorem CellSeparated.isDiscrete {S : Set X} (hS : CellSeparated S) : IsDiscrete S := by
  constructor
  apply discreteTopology_iff_forall_isClosed.mpr
  intro T
  have hT : CellSeparated (Subtype.val '' T) := hS.mono (by
    rintro _ ⟨x, _, rfl⟩
    exact x.property)
  have hc := hT.isClosed.preimage (continuous_subtype_val : Continuous (Subtype.val : S → X))
  simpa only [Set.preimage_image_eq _ Subtype.val_injective] using hc

theorem CellSeparated.finite_of_subset_compact {S K : Set X} (hS : CellSeparated S)
    (hK : IsCompact K) (hSK : S ⊆ K) : S.Finite :=
  (hK.of_isClosed_subset hS.isClosed hSK).finite hS.isDiscrete

def touchedCells (K : Set X) : Set (Σ n, RelCWComplex.cell (Set.univ : Set X) n) :=
  {c | (K ∩ RelCWComplex.openCell c.1 c.2).Nonempty}

/-- Compactness plus the actual CW weak topology rules out meeting
infinitely many different open cells. -/
theorem IsCompact.finite_touchedCells {K : Set X} (hK : IsCompact K) :
    (touchedCells K).Finite := by
  let p : touchedCells K → X := fun c => Classical.choose c.property
  have hp (c : touchedCells K) : p c ∈ K ∧ p c ∈ RelCWComplex.openCell c.val.1 c.val.2 :=
    Classical.choose_spec c.property
  have heq {n m : ℕ} {i : RelCWComplex.cell (Set.univ : Set X) n}
      {j : RelCWComplex.cell (Set.univ : Set X) m} {x : X}
      (hi : x ∈ RelCWComplex.openCell n i) (hj : x ∈ RelCWComplex.openCell m j) :
      (⟨n, i⟩ : Σ n, RelCWComplex.cell (Set.univ : Set X) n) = ⟨m, j⟩ := by
    apply RelCWComplex.eq_of_not_disjoint_openCell
    intro hd
    exact Set.disjoint_left.mp hd hi hj
  have hinj : Function.Injective p := by
    intro c d h
    apply Subtype.ext
    exact heq (hp c).2 (by simpa only [h] using (hp d).2)
  have hs : CellSeparated (Set.range p) := by
    intro n j x hx y hy
    obtain ⟨c, rfl⟩ := hx.1
    obtain ⟨d, rfl⟩ := hy.1
    have hc := heq (hp c).2 hx.2
    have hd := heq (hp d).2 hy.2
    have hcd : c = d := Subtype.ext (hc.trans hd.symm)
    exact congrArg p hcd
  have hpK : Set.range p ⊆ K := by
    rintro _ ⟨c, rfl⟩
    exact (hp c).1
  have hf := hs.finite_of_subset_compact hK hpK
  letI : Finite (touchedCells K) := (Set.finite_range_iff hinj).mp hf
  exact Set.toFinite _

/-- In particular every continuous loop, path, or sphere image has finite
support in the original cells as soon as its domain is compact. -/
theorem continuous_finite_touchedCells {A : Type} [TopologicalSpace A] [CompactSpace A]
    (f : C(A, X)) : (touchedCells (Set.range f)).Finite :=
  IsCompact.finite_touchedCells (isCompact_range f.continuous)

/-- A compact subset of a lower skeleton has genuine finite support by
cells of strictly lower dimension. -/
theorem IsCompact.finite_lower_support {K : Set X} (hK : IsCompact K) (d : ℕ)
    (hKd : K ⊆ CWComplex.skeletonLT (Set.univ : Set X) (d : ℕ∞)) :
    ∃ I : ∀ m, Finset (RelCWComplex.cell (Set.univ : Set X) m),
      K ⊆ ⋃ (m < d) (j ∈ I m), RelCWComplex.closedCell m j := by
  have hT := IsCompact.finite_touchedCells hK
  have hI (m : ℕ) : ((Sigma.mk m) ⁻¹' touchedCells K).Finite :=
    Set.Finite.preimage (by intro i _ j _ h; cases h; rfl) hT
  let I := fun m => (hI m).toFinset
  refine ⟨I, ?_⟩
  intro x hx
  have hxall : x ∈ ⋃ m, ⋃ j : RelCWComplex.cell (Set.univ : Set X) m,
      RelCWComplex.openCell m j := by rw [CWComplex.iUnion_openCell_eq_complex]; trivial
  obtain ⟨m, j, hj⟩ := by simpa only [Set.mem_iUnion] using hxall
  have hmd : m < d := by
    by_contra h
    have hdm : (d : ℕ∞) ≤ m := by exact_mod_cast Nat.le_of_not_gt h
    exact Set.disjoint_left.mp (CWComplex.disjoint_skeletonLT_openCell (C := (Set.univ : Set X))
      (j := j) hdm) (hKd hx) hj
  simp only [Set.mem_iUnion]
  refine ⟨m, hmd, j, ?_, RelCWComplex.openCell_subset_closedCell m j hj⟩
  exact (Set.Finite.mem_toFinset (hI m)).mpr ⟨x, hx, hj⟩

end FiniteChains.ClassicalCW
