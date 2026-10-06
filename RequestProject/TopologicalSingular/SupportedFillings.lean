import RequestProject.TopologicalSingular.RelativeSingularMaps
import RequestProject.TopologicalSingular.SingularChainH0
import RequestProject.TopologicalSingular.ContractibleSingularChains

namespace FiniteChains.TopologicalSingular
universe u
variable {X : Type u} [TopologicalSpace X]

/-- Exactness in a contractible subspace gives a filling that stays in it. -/
theorem contractible_supported_cycle_bounds (A : Set X) [ContractibleSpace A]
    (n : ℕ) (c : Chain X (n + 1)) (hc : c ∈ subChains A (n + 1))
    (hz : boundary n c = 0) :
    ∃ b : Chain X (n + 2), b ∈ subChains A (n + 2) ∧ boundary (n + 1) b = c := by
  obtain ⟨a, rfl⟩ := hc
  have ha : boundary n a = 0 := by
    apply map_inclusion_injective A n
    rw [map_boundary, hz, map_zero]
  obtain ⟨b, hb⟩ := contractible_cycle_bounds n a ha
  refine ⟨map (inclusion A) (n + 2) b, ⟨b, rfl⟩, ?_⟩
  rw [← map_boundary, hb]

/-- The same support control holds in augmented degree zero. -/
theorem connected_supported_zero_bounds (A : Set X) [PathConnectedSpace A]
    (c : Chain X 0) (hc : c ∈ subChains A 0) (hz : augmentation c = 0) :
    ∃ b : Chain X 1, b ∈ subChains A 1 ∧ boundary 0 b = c := by
  obtain ⟨a, rfl⟩ := hc
  have ha : a ∈ LinearMap.ker augmentation := by
    change augmentation a = 0
    simpa only [augmentation_map] using hz
  rw [ker_augmentation_eq_range_boundary] at ha
  obtain ⟨b, hb⟩ := ha
  refine ⟨map (inclusion A) 1 b, ⟨b, rfl⟩, ?_⟩
  rw [← map_boundary, hb]

end FiniteChains.TopologicalSingular
