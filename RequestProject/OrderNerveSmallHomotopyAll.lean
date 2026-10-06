import RequestProject.OrderNerveSmallSingularApproximationAll

namespace FiniteChains.Comb
open TopologicalSingular SingularSubdivision
variable {P : Type} [PartialOrder P]

/-- Carried homotopy data, with the identity on boundaries needed for extension. -/
structure OrderSmallHomotopyStage (P : Type) [PartialOrder P] (n : ℕ) where
  map : smallChains (orderNerveRealizationOpenStar P) n →ₗ[ℤ]
    Chain (orderNerveRealization P) (n + 1)
  carrier : ∀ σ : OrderSmallSimplex P n,
    map (orderSmallSingle σ 1) ∈ orderSingularCarrierChains σ.val (n + 1)
  on_boundary : ∀ c : smallChains (orderNerveRealizationOpenStar P) (n + 1),
    boundary n (map (smallBoundary (orderNerveRealizationOpenStar P) n c)) =
      boundary n c.val - orderSmallSingularApproximation P n
        (smallBoundary (orderNerveRealizationOpenStar P) n c)

noncomputable def orderSmallHomotopyStageZero : OrderSmallHomotopyStage P 0 where
  map := orderSmallHomotopy0
  carrier := orderSmallHomotopy0_carrier
  on_boundary c := by
    rw [orderSmallHomotopy0_boundary, orderSmallSingularApproximation_zero]
    rfl

theorem orderSmallHomotopyStage_fill {n : ℕ} (s : OrderSmallHomotopyStage P n)
    (σ : OrderSmallSimplex P (n + 1)) :
    ∃ b : Chain (orderNerveRealization P) (n + 2),
      b ∈ orderSingularCarrierChains σ.val (n + 2) ∧
      boundary (n + 1) b = Finsupp.single σ.val 1 -
        orderSmallSingularApproximation P (n + 1) (orderSmallSingle σ 1) -
        s.map (smallBoundary (orderNerveRealizationOpenStar P) n (orderSmallSingle σ 1)) := by
  apply orderSingularCarrierChains_cycle_bounds σ.val σ.property n
  · exact Submodule.sub_mem _
      (Submodule.sub_mem _ (orderSingularCarrierChains_single σ.val 1)
        (orderSmallSingularApproximation_carrier (n + 1) σ))
      (orderSmallBoundary_map_carrier s.map s.carrier σ)
  · rw [map_sub, map_sub, orderSmallSingularApproximation_boundary, s.on_boundary]
    exact sub_self _

noncomputable def orderSmallHomotopyStageNextMap {n : ℕ} (s : OrderSmallHomotopyStage P n) :
    smallChains (orderNerveRealizationOpenStar P) (n + 1) →ₗ[ℤ]
      Chain (orderNerveRealization P) (n + 2) :=
  (Finsupp.linearCombination ℤ (fun σ => (orderSmallHomotopyStage_fill s σ).choose)).comp
    (orderSmallChainEquiv P (n + 1)).toLinearMap

theorem orderSmallHomotopyStageNextMap_single {n : ℕ} (s : OrderSmallHomotopyStage P n)
    (σ : OrderSmallSimplex P (n + 1)) :
    orderSmallHomotopyStageNextMap s (orderSmallSingle σ 1) =
      (orderSmallHomotopyStage_fill s σ).choose := by
  have he := (orderSmallChainEquiv P (n + 1)).apply_symm_apply (Finsupp.single σ 1)
  rw [orderSmallChainEquiv_symm_single] at he
  change (Finsupp.linearCombination ℤ (fun τ : OrderSmallSimplex P (n + 1) =>
    (orderSmallHomotopyStage_fill s τ).choose))
      ((orderSmallChainEquiv P (n + 1)) (orderSmallSingle σ 1)) = _
  rw [he, Finsupp.linearCombination_single, one_smul]

theorem orderSmallHomotopyStageNextMap_boundary {n : ℕ} (s : OrderSmallHomotopyStage P n)
    (c : smallChains (orderNerveRealizationOpenStar P) (n + 1)) :
    boundary (n + 1) (orderSmallHomotopyStageNextMap s c) =
      c.val - orderSmallSingularApproximation P (n + 1) c -
        s.map (smallBoundary (orderNerveRealizationOpenStar P) n c) := by
  have he : (boundary (n + 1)).comp (orderSmallHomotopyStageNextMap s) =
      (smallChains (orderNerveRealizationOpenStar P) (n + 1)).subtype -
        orderSmallSingularApproximation P (n + 1) -
        s.map.comp (smallBoundary (orderNerveRealizationOpenStar P) n) := by
    apply orderSmallSingle_spans
    intro σ
    simp only [LinearMap.comp_apply, LinearMap.sub_apply, orderSmallHomotopyStageNextMap_single]
    exact (orderSmallHomotopyStage_fill s σ).choose_spec.2
  exact DFunLike.congr_fun he c

noncomputable def orderSmallHomotopyStageNext {n : ℕ} (s : OrderSmallHomotopyStage P n) :
    OrderSmallHomotopyStage P (n + 1) where
  map := orderSmallHomotopyStageNextMap s
  carrier σ := by
    rw [orderSmallHomotopyStageNextMap_single]
    exact (orderSmallHomotopyStage_fill s σ).choose_spec.1
  on_boundary c := by
    rw [orderSmallHomotopyStageNextMap_boundary]
    have hd := DFunLike.congr_fun (smallBoundary_squared (orderNerveRealizationOpenStar P) n) c
    change smallBoundary (orderNerveRealizationOpenStar P) n
      (smallBoundary (orderNerveRealizationOpenStar P) (n + 1) c) = 0 at hd
    rw [hd, map_zero, sub_zero]
    rfl

noncomputable def orderSmallHomotopyStage (P : Type) [PartialOrder P] :
    (n : ℕ) → OrderSmallHomotopyStage P n
  | 0 => orderSmallHomotopyStageZero
  | n + 1 => orderSmallHomotopyStageNext (orderSmallHomotopyStage P n)

noncomputable def orderSmallHomotopy (P : Type) [PartialOrder P] (n : ℕ) :
    smallChains (orderNerveRealizationOpenStar P) n →ₗ[ℤ]
      Chain (orderNerveRealization P) (n + 1) :=
  (orderSmallHomotopyStage P n).map

/-- A carried chain homotopy from the realized approximation to inclusion, in every degree. -/
theorem orderSmallHomotopy_boundary (n : ℕ)
    (c : smallChains (orderNerveRealizationOpenStar P) (n + 1)) :
    boundary (n + 1) (orderSmallHomotopy P (n + 1) c) =
      c.val - orderSmallSingularApproximation P (n + 1) c -
        orderSmallHomotopy P n (smallBoundary (orderNerveRealizationOpenStar P) n c) :=
  orderSmallHomotopyStageNextMap_boundary (orderSmallHomotopyStage P n) c

theorem orderSmallHomotopy_carrier (n : ℕ) (σ : OrderSmallSimplex P n) :
    orderSmallHomotopy P n (orderSmallSingle σ 1) ∈ orderSingularCarrierChains σ.val (n + 1) :=
  (orderSmallHomotopyStage P n).carrier σ

theorem orderSmallSingularApproximation_homologous (n : ℕ)
    (c : smallChains (orderNerveRealizationOpenStar P) (n + 1))
    (hc : smallBoundary (orderNerveRealizationOpenStar P) n c = 0) :
    ∃ b : Chain (orderNerveRealization P) (n + 2),
      boundary (n + 1) b = c.val - orderSmallSingularApproximation P (n + 1) c := by
  refine ⟨orderSmallHomotopy P (n + 1) c, ?_⟩
  rw [orderSmallHomotopy_boundary, hc, map_zero, sub_zero]

end FiniteChains.Comb
