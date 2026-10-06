/- Adapted from the local 2026-09-11 Lean audit; see PROVENANCE.json. -/

import Mathlib
import Mathlib.Topology.UnitInterval

/-! # Finite path subdivisions subordinate to open covers

The cut paths are actual restrictions with affine reparametrization. Their
finite concatenation is proved homotopic to the original cut. The same
cover argument gives finite rectangular subdivisions of path homotopies.
These are inputs for the still-open fundamental-group generation and
reverse-kernel proofs.
-/


namespace FiniteChains.PathSubdivision

open Set Topology
open scoped unitInterval

universe u v

noncomputable def intervalPath (a b : unitInterval) : Path a b where
  toFun s := ⟨(1 - (s : ℝ)) * a + s * b,by
    have hs : 0 ≤ 1 - (s : ℝ) := sub_nonneg.mpr s.property.2
    constructor
    · exact add_nonneg (mul_nonneg hs a.property.1) (mul_nonneg s.property.1 b.property.1)
    · have h1 := mul_le_mul_of_nonneg_left a.property.2 hs
      have h2 := mul_le_mul_of_nonneg_left b.property.2 s.property.1
      nlinarith⟩
  continuous_toFun := by fun_prop
  source' := by apply Subtype.ext; simp
  target' := by apply Subtype.ext; simp

theorem intervalPath_range {a b : unitInterval} (hab : a ≤ b) (s : unitInterval) :
    intervalPath a b s ∈ Set.Icc a b := by
  change a ≤ (intervalPath a b s) ∧ (intervalPath a b s) ≤ b
  change (a : ℝ) ≤ (1 - (s : ℝ)) * a + s * b ∧
    (1 - (s : ℝ)) * a + s * b ≤ b
  have h1 := mul_nonneg s.property.1 (sub_nonneg.mpr (show (a : ℝ) ≤ b from hab))
  have h2 := mul_nonneg (sub_nonneg.mpr s.property.2) (sub_nonneg.mpr (show (a : ℝ) ≤ b from hab))
  constructor <;> nlinarith

theorem interval_simplyConnected : SimplyConnectedSpace unitInterval := by
  letI : ContractibleSpace unitInterval := (convex_Icc (0 : ℝ) 1).contractibleSpace
    ⟨0,by simp⟩
  infer_instance

variable {X : Type u} [TopologicalSpace X] {x y : X}

noncomputable def cut (p : Path x y) (a b : unitInterval) : Path (p a) (p b) :=
  (intervalPath a b).map p.continuous

theorem cut_range (p : Path x y) {a b : unitInterval} (hab : a ≤ b) :
    Set.range (cut p a b) ⊆ p '' Set.Icc a b := by
  rintro z ⟨s,rfl⟩
  exact ⟨intervalPath a b s,intervalPath_range hab s,rfl⟩

theorem cut_trans_homotopic (p : Path x y) (a b c : unitInterval) :
    ((cut p a b).trans (cut p b c)).Homotopic (cut p a c) := by
  letI := interval_simplyConnected
  have h := (SimplyConnectedSpace.paths_homotopic
    ((intervalPath a b).trans (intervalPath b c)) (intervalPath a c)).map p.toContinuousMap
  simpa only [Path.map_trans, Path.coe_toContinuousMap, cut] using h

theorem cut_self_homotopic (p : Path x y) (a : unitInterval) :
    (Path.refl (p a)).Homotopic (cut p a a) := by
  letI := interval_simplyConnected
  have h := (SimplyConnectedSpace.paths_homotopic (Path.refl a) (intervalPath a a)).map p.toContinuousMap
  have he : (Path.refl a).map p.continuous = Path.refl (p a) := by ext t; rfl
  rw [he] at h
  exact h

theorem cut_zero_one_homotopic (p : Path x y) :
    (cut p 0 1).Homotopic (p.cast p.source p.target) := by
  letI := interval_simplyConnected
  have h := (SimplyConnectedSpace.paths_homotopic (intervalPath 0 1) Path.id).map p.toContinuousMap
  have he : Path.id.map p.continuous = p.cast p.source p.target := by ext t; rfl
  rw [he] at h
  exact h

noncomputable def concatenateCuts (p : Path x y) (t : ℕ → unitInterval) :
    (N : ℕ) → Path (p (t 0)) (p (t N))
  | 0 => Path.refl _
  | N+1 => (concatenateCuts p t N).trans (cut p (t N) (t (N+1)))

theorem concatenateCuts_homotopic (p : Path x y) (t : ℕ → unitInterval) (N : ℕ) :
    (concatenateCuts p t N).Homotopic (cut p (t 0) (t N)) := by
  induction N with
  | zero => exact cut_self_homotopic p _
  | succ N ih =>
    exact (ih.hcomp (Path.Homotopic.refl _)).trans (cut_trans_homotopic p _ _ _)

theorem exists_subdivision (p : Path x y) {ι : Type v} (U : ι → Set X)
    (hU : ∀ i, IsOpen (U i)) (hp : ∀ s, ∃ i, p s ∈ U i) :
    ∃ (t : ℕ → unitInterval) (N : ℕ), t 0 = 0 ∧ t N = 1 ∧ Monotone t ∧
      ∀ j < N, ∃ i, Set.range (cut p (t j) (t (j+1))) ⊆ U i := by
  obtain ⟨t,ht0,htm,⟨N,hN⟩,htU⟩ :=
    exists_monotone_Icc_subset_open_cover_unitInterval
      (fun i => (hU i).preimage p.continuous)
      (fun s _ => Set.mem_iUnion.mpr (hp s))
  refine ⟨t,N,ht0,hN N le_rfl,htm,?_⟩
  intro j _
  obtain ⟨i,hi⟩ := htU j
  refine ⟨i,?_⟩
  intro z hz
  obtain ⟨s,hs,rfl⟩ := cut_range p (htm (Nat.le_succ j)) hz
  exact hi hs

theorem exists_homotopy_grid {p q : Path x y} (H : p.Homotopy q)
    {ι : Type v} (U : ι → Set X) (hU : ∀ i, IsOpen (U i)) (hH : ∀ st, ∃ i, H st ∈ U i) :
    ∃ (t : ℕ → unitInterval) (N : ℕ), t 0 = 0 ∧ t N = 1 ∧ Monotone t ∧
      ∀ j < N, ∀ k < N, ∃ i,
        MapsTo H (Set.Icc (t j) (t (j+1)) ×ˢ Set.Icc (t k) (t (k+1))) (U i) := by
  obtain ⟨t,ht0,htm,⟨N,hN⟩,htU⟩ :=
    exists_monotone_Icc_subset_open_cover_unitInterval_prod_self
      (fun i => (hU i).preimage H.continuous)
      (fun st _ => Set.mem_iUnion.mpr (hH st))
  exact ⟨t,N,ht0,hN N le_rfl,htm,fun j _ k _ => htU j k⟩

end FiniteChains.PathSubdivision
