module

public import RequestProject.HomeomorphContinuousMap
public import RequestProject.IntervalEndpointHomotopyExtension
public import RequestProject.ClassicalCWLoopCellularization

@[expose] public section

/-! Cellular representatives for actual attaching circle maps, including
maps whose chosen starting point is not in the one-skeleton. Four endpoint
motions are extended over the sides, then genuine path cellularization
and corner-compatible homotopy pasting finish the construction. -/

noncomputable section
open scoped Topology unitInterval Classical
open Topology
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains.ClassicalCW
open RelativeAttachment

def pointVertexInOneSkeleton (K : Whitehead.TwoComplex) (x : K) : OneSkeleton K :=
  ⟨vertexPoint (pointVertex x), by
    apply CWComplex.skeletonLT_mono (C := (Set.univ : Set K))
      (show (0 : ℕ∞) + 1 ≤ 2 by norm_num)
    apply CWComplex.closedCell_subset_skeletonLT 0 (pointVertex x)
    rw [RelCWComplex.closedCell_zero_eq_singleton]
    rfl⟩

/-- Any continuous square-boundary map can be moved into the original
one-skeleton, without any initial condition on its corner values. -/
theorem squareBoundary_into_oneSkeleton (K : Whitehead.TwoComplex)
    (r : C(SquareBoundary, K)) :
    ∃ q : C(SquareBoundary, OneSkeleton K),
      r.Homotopic ((⟨Subtype.val, continuous_subtype_val⟩ : C(OneSkeleton K, K)).comp q) := by
  let v : SquareBoundary → OneSkeleton K := fun z => pointVertexInOneSkeleton K (r z)
  let p (z : SquareBoundary) : Path (r z) (v z).val := pointVertexPath (r z)
  let E (s : SquareSide) := intervalEndpointExtension (r.comp (squareSideMap s))
    (p (squareSideMap s 0)) (p (squareSideMap s 1))
  have hE : ∀ s τ t, t = 0 ∨ t = 1 →
      (E s).map (τ, t) = p (squareSideMap s t) τ := by
    intro s τ t ht
    rcases ht with rfl | rfl
    · exact (E s).side_zero τ
    · exact (E s).side_one τ
  let G := squareBoundaryHomotopyPasting (fun s => (E s).map) (fun τ z => p z τ) hE
  let r₁ : C(SquareBoundary, K) := G.comp ⟨fun z => (1, z), continuous_const.prodMk continuous_id⟩
  have hG₀ : ∀ z, G (0, z) = r z := by
    intro z
    obtain ⟨⟨s, t⟩, rfl⟩ := squareSideQuotient_surjective z
    change squareBoundaryHomotopyPasting _ _ hE (0, squareSideMap s t) = r (squareSideMap s t)
    rw [squareBoundaryHomotopyPasting_side]
    exact (E s).zero t
  let H₀ : r.Homotopy r₁ := {
    toContinuousMap := G
    map_zero_left := hG₀
    map_one_left := fun _ => rfl }
  let l (s : SquareSide) : Path (v (squareSideMap s 0)).val (v (squareSideMap s 1)).val := {
    toFun := fun t => (E s).map (1, t)
    continuous_toFun := (E s).map.continuous.comp (continuous_const.prodMk continuous_id)
    source' := ((E s).side_zero 1).trans (p (squareSideMap s 0)).target
    target' := ((E s).side_one 1).trans (p (squareSideMap s 1)).target }
  have hl : ∀ s, ∃ q : Path (v (squareSideMap s 0)) (v (squareSideMap s 1)),
      (l s).Homotopic (q.map continuous_subtype_val) := by
    intro s
    exact path_into_oneSkeleton K _ _ (l s)
  choose q hq using hl
  have hqV : ∀ s t, t = 0 ∨ t = 1 → q s t = v (squareSideMap s t) := by
    intro s t ht
    rcases ht with rfl | rfl
    · exact (q s).source
    · exact (q s).target
  let Q := squareBoundaryPasting (fun s => (q s).toContinuousMap) v hqV
  let H (s : SquareSide) := Classical.choice (hq s)
  have hHV : ∀ s τ t, t = 0 ∨ t = 1 →
      H s (τ, t) = (v (squareSideMap s t)).val := by
    intro s τ t ht
    rcases ht with rfl | rfl
    · exact (H s).source τ
    · exact (H s).target τ
  let G₁ := squareBoundaryHomotopyPasting (fun s => (H s).toHomotopy.toContinuousMap)
    (fun _ z => (v z).val) hHV
  let ι : C(OneSkeleton K, K) := ⟨Subtype.val, continuous_subtype_val⟩
  let H₁ : r₁.Homotopy (ι.comp Q) := {
    toContinuousMap := G₁
    map_zero_left := by
      intro z
      obtain ⟨⟨s, t⟩, rfl⟩ := squareSideQuotient_surjective z
      change G₁ (0, squareSideMap s t) = G (1, squareSideMap s t)
      rw [squareBoundaryHomotopyPasting_side, squareBoundaryHomotopyPasting_side]
      exact (H s).apply_zero t
    map_one_left := by
      intro z
      obtain ⟨⟨s, t⟩, rfl⟩ := squareSideQuotient_surjective z
      change G₁ (1, squareSideMap s t) = (Q (squareSideMap s t)).val
      rw [squareBoundaryHomotopyPasting_side, squareBoundaryPasting_side]
      exact (H s).apply_one t }
  exact ⟨Q, ⟨H₀.trans H₁⟩⟩

/-- This is the actual normed circle used by classical CW attachments,
not a replacement of the attaching domain by a combinatorial loop. -/
theorem boundary_into_oneSkeleton (K : Whitehead.TwoComplex)
    (r : C(UnitBoundary (Fin 2 → ℝ), K)) :
    ∃ q : C(UnitBoundary (Fin 2 → ℝ), OneSkeleton K),
      r.Homotopic ((⟨Subtype.val, continuous_subtype_val⟩ : C(OneSkeleton K, K)).comp q) := by
  let e := unitBoundarySquareHomeomorph
  obtain ⟨q, hq⟩ := squareBoundary_into_oneSkeleton K (r.comp e.symm.toContinuousMap)
  refine ⟨q.comp e.toContinuousMap, ?_⟩
  have h := hq.comp (ContinuousMap.Homotopic.refl e.toContinuousMap)
  have he : (r.comp e.symm.toContinuousMap).comp e.toContinuousMap = r := by
    apply ContinuousMap.ext
    intro a
    exact congrArg r (e.symm_apply_apply a)
  rw [he] at h
  exact h

/-- Arbitrary families are cellularized simultaneously. Each new boundary
has finite support in the original lower-dimensional cells; the whole
family and the old CW complex may both be infinite. -/
theorem boundaryFamily_into_oneSkeleton (K : Whitehead.TwoComplex) {J : Type}
    (r : C(BoundaryFamily J (Fin 2 → ℝ), K)) :
    ∃ q : C(BoundaryFamily J (Fin 2 → ℝ), K),
      r.Homotopic q ∧ FiniteLowerBoundary 2 q := by
  let rj (j : J) : C(UnitBoundary (Fin 2 → ℝ), K) :=
    r.comp (⟨fun a : UnitBoundary (Fin 2 → ℝ) => ⟨j, a⟩, by
      exact continuous_sigmaMk («σ» := fun _ : J => UnitBoundary (Fin 2 → ℝ)) (i := j)⟩ :
        C(UnitBoundary (Fin 2 → ℝ), BoundaryFamily J (Fin 2 → ℝ)))
  have hj := fun j => boundary_into_oneSkeleton K (rj j)
  choose q hq using hj
  let ι : C(OneSkeleton K, K) := ⟨Subtype.val, continuous_subtype_val⟩
  let Q : C(BoundaryFamily J (Fin 2 → ℝ), K) :=
    ⟨fun a => (q a.1 a.2).val,
      continuous_sigma (fun j => continuous_subtype_val.comp (q j).continuous)⟩
  let H (j : J) := Classical.choice (hq j)
  let F : C(BoundaryFamily J (Fin 2 → ℝ), C(I, K)) :=
    ⟨fun a => ((H a.1).toContinuousMap.comp ⟨Prod.swap, continuous_swap⟩).curry a.2,
      continuous_sigma (fun j =>
        ((H j).toContinuousMap.comp ⟨Prod.swap, continuous_swap⟩).curry.continuous)⟩
  refine ⟨Q, ⟨{
    toContinuousMap := F.uncurry.comp ⟨Prod.swap, continuous_swap⟩
    map_zero_left := fun a => (H a.1).apply_zero a.2
    map_one_left := fun a => (H a.1).apply_one a.2 }⟩, ?_⟩
  letI : CompactSpace (UnitBoundary (Fin 2 → ℝ)) := isCompact_iff_compactSpace.mp (by
    convert isCompact_sphere (0 : Fin 2 → ℝ) 1 using 1
    ext x
    simp only [Metric.mem_sphere, dist_zero_right]
    rfl)
  intro j
  obtain ⟨support, hsupport⟩ := IsCompact.finite_lower_support (isCompact_range (ι.comp (q j)).continuous) 2
    (by rintro _ ⟨a, rfl⟩; exact (q j a).property)
  exact ⟨support, fun a => hsupport ⟨a, rfl⟩⟩

end FiniteChains.ClassicalCW
