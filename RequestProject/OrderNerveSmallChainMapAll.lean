module

public import RequestProject.OrderNerveSmallChainMapLow

@[expose] public section

namespace FiniteChains.Comb
open TopologicalSingular SingularSubdivision
variable {P : Type} [PartialOrder P]

/-- The data needed to extend a carried approximation by one degree. -/
structure OrderSmallNerveStage (P : Type) [PartialOrder P] (n : ℕ) where
  map : smallChains (orderNerveRealizationOpenStar P) n →ₗ[ℤ] Nerve.Ch P
  carrier : ∀ σ : OrderSmallSimplex P n,
    map (orderSmallSingle σ 1) ∈ Nerve.IncOn (orderNerveSingularCarrier σ.val)
  homogeneous : ∀ c, Nerve.lengthProjection (n + 1) (map c) = map c
  closed_boundary : ∀ c : smallChains (orderNerveRealizationOpenStar P) (n + 1),
    Nerve.bdry (map (smallBoundary (orderNerveRealizationOpenStar P) n c)) = 0

noncomputable def orderSmallNerveStageZero : OrderSmallNerveStage P 0 where
  map := orderSmallToNerve0
  carrier := orderSmallToNerve0_single_carrier
  homogeneous := orderSmallToNerve0_length
  closed_boundary c := by
    rw [orderSmallToNerve0_boundary]
    change augmentation (boundary 0 c.val) • _ = 0
    rw [augmentation_boundary, zero_smul]

theorem orderSmallNerveBoundary_carrier {n : ℕ}
    (f : smallChains (orderNerveRealizationOpenStar P) n →ₗ[ℤ] Nerve.Ch P)
    (hf : ∀ τ : OrderSmallSimplex P n,
      f (orderSmallSingle τ 1) ∈ Nerve.IncOn (orderNerveSingularCarrier τ.val))
    (σ : OrderSmallSimplex P (n + 1)) :
    f (smallBoundary (orderNerveRealizationOpenStar P) n (orderSmallSingle σ 1)) ∈
      Nerve.IncOn (orderNerveSingularCarrier σ.val) := by
  rw [orderSmallSingle_boundary, map_sum]
  apply AddSubgroup.sum_mem
  intro i _
  rw [map_smul]
  apply AddSubgroup.zsmul_mem
  exact Nerve.incOn_mono (fun _ hp => orderSmallSimplexFace_carrier i σ hp)
    (hf (orderSmallSimplexFace i σ))

/-- Every new simplex can be filled in its own acyclic order carrier. -/
theorem orderSmallNerveStage_fill {n : ℕ} (s : OrderSmallNerveStage P n)
    (σ : OrderSmallSimplex P (n + 1)) :
    ∃ b : Nerve.Ch P, b ∈ Nerve.IncOn (orderNerveSingularCarrier σ.val) ∧
      Nerve.lengthProjection (n + 2) b = b ∧ Nerve.bdry b =
        s.map (smallBoundary (orderNerveRealizationOpenStar P) n (orderSmallSingle σ 1)) := by
  obtain ⟨b, hb, he⟩ := orderNerveSingularCarrier_nerve_acyclic σ.val σ.property _
    (orderSmallNerveBoundary_carrier s.map s.carrier σ) (s.closed_boundary _)
  refine ⟨Nerve.lengthProjection (n + 2) b, Nerve.lengthProjection_mem_incOn _ hb,
    Nerve.lengthProjection_idempotent _ _, ?_⟩
  rw [← Nerve.lengthProjection_bdry, he]
  exact s.homogeneous _

noncomputable def orderSmallNerveStageNextMap {n : ℕ} (s : OrderSmallNerveStage P n) :
    smallChains (orderNerveRealizationOpenStar P) (n + 1) →ₗ[ℤ] Nerve.Ch P :=
  (Finsupp.linearCombination ℤ (fun σ => (orderSmallNerveStage_fill s σ).choose)).comp
    (orderSmallChainEquiv P (n + 1)).toLinearMap

theorem orderSmallNerveStageNextMap_single {n : ℕ} (s : OrderSmallNerveStage P n)
    (σ : OrderSmallSimplex P (n + 1)) :
    orderSmallNerveStageNextMap s (orderSmallSingle σ 1) =
      (orderSmallNerveStage_fill s σ).choose := by
  have he := (orderSmallChainEquiv P (n + 1)).apply_symm_apply (Finsupp.single σ 1)
  rw [orderSmallChainEquiv_symm_single] at he
  change (Finsupp.linearCombination ℤ (fun τ : OrderSmallSimplex P (n + 1) =>
    (orderSmallNerveStage_fill s τ).choose))
      ((orderSmallChainEquiv P (n + 1)) (orderSmallSingle σ 1)) = _
  rw [he, Finsupp.linearCombination_single, one_smul]

theorem orderSmallNerveStageNextMap_boundary {n : ℕ} (s : OrderSmallNerveStage P n)
    (c : smallChains (orderNerveRealizationOpenStar P) (n + 1)) :
    Nerve.bdry (orderSmallNerveStageNextMap s c) =
      s.map (smallBoundary (orderNerveRealizationOpenStar P) n c) := by
  have he : Nerve.bdry.toIntLinearMap.comp (orderSmallNerveStageNextMap s) =
      s.map.comp (smallBoundary (orderNerveRealizationOpenStar P) n) := by
    apply orderSmallSingle_spans
    intro σ
    change Nerve.bdry (orderSmallNerveStageNextMap s (orderSmallSingle σ 1)) = _
    rw [orderSmallNerveStageNextMap_single]
    exact (orderSmallNerveStage_fill s σ).choose_spec.2.2
  exact DFunLike.congr_fun he c

noncomputable def orderSmallNerveStageNext {n : ℕ} (s : OrderSmallNerveStage P n) :
    OrderSmallNerveStage P (n + 1) where
  map := orderSmallNerveStageNextMap s
  carrier σ := by
    rw [orderSmallNerveStageNextMap_single]
    exact (orderSmallNerveStage_fill s σ).choose_spec.1
  homogeneous c := by
    have he : (Nerve.lengthProjection (n + 2)).toIntLinearMap.comp
        (orderSmallNerveStageNextMap s) = orderSmallNerveStageNextMap s := by
      apply orderSmallSingle_spans
      intro σ
      change Nerve.lengthProjection (n + 2)
        (orderSmallNerveStageNextMap s (orderSmallSingle σ 1)) = _
      rw [orderSmallNerveStageNextMap_single]
      exact (orderSmallNerveStage_fill s σ).choose_spec.2.1
    exact DFunLike.congr_fun he c
  closed_boundary c := by
    rw [orderSmallNerveStageNextMap_boundary]
    have hd := DFunLike.congr_fun (smallBoundary_squared (orderNerveRealizationOpenStar P) n) c
    change smallBoundary (orderNerveRealizationOpenStar P) n
      (smallBoundary (orderNerveRealizationOpenStar P) (n + 1) c) = 0 at hd
    rw [hd, map_zero]

/-- A carried approximation exists simultaneously in all dimensions. -/
noncomputable def orderSmallNerveStage (P : Type) [PartialOrder P] :
    (n : ℕ) → OrderSmallNerveStage P n
  | 0 => orderSmallNerveStageZero
  | n + 1 => orderSmallNerveStageNext (orderSmallNerveStage P n)

noncomputable def orderSmallToNerve (P : Type) [PartialOrder P] (n : ℕ) :
    smallChains (orderNerveRealizationOpenStar P) n →ₗ[ℤ] Nerve.Ch P :=
  (orderSmallNerveStage P n).map

theorem orderSmallToNerve_carrier (n : ℕ) (σ : OrderSmallSimplex P n) :
    orderSmallToNerve P n (orderSmallSingle σ 1) ∈
      Nerve.IncOn (orderNerveSingularCarrier σ.val) :=
  (orderSmallNerveStage P n).carrier σ

theorem orderSmallToNerve_length (n : ℕ)
    (c : smallChains (orderNerveRealizationOpenStar P) n) :
    Nerve.lengthProjection (n + 1) (orderSmallToNerve P n c) = orderSmallToNerve P n c :=
  (orderSmallNerveStage P n).homogeneous c

theorem orderSmallToNerve_boundary (n : ℕ)
    (c : smallChains (orderNerveRealizationOpenStar P) (n + 1)) :
    Nerve.bdry (orderSmallToNerve P (n + 1) c) =
      orderSmallToNerve P n (smallBoundary (orderNerveRealizationOpenStar P) n c) :=
  orderSmallNerveStageNextMap_boundary (orderSmallNerveStage P n) c

theorem orderSmallToNerve_mem_inc (n : ℕ)
    (c : smallChains (orderNerveRealizationOpenStar P) n) :
    orderSmallToNerve P n c ∈ Nerve.Inc P := by
  obtain ⟨d, rfl⟩ := (orderSmallChainEquiv P n).symm.surjective c
  induction d using Finsupp.induction_linear with
  | zero => simp
  | add d e hd he => simpa only [map_add] using (Nerve.Inc P).add_mem hd he
  | single σ r =>
    have hr : Finsupp.single σ r = r • Finsupp.single σ 1 := by simp
    rw [hr, map_smul, map_smul, orderSmallChainEquiv_symm_single]
    exact (Nerve.Inc P).zsmul_mem
      (Nerve.incOn_le_inc _ (orderSmallToNerve_carrier n σ)) r

end FiniteChains.Comb
