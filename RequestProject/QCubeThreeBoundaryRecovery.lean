module

public import RequestProject.QCubeCanonicalThreeBoundary
public import RequestProject.StrictThreeTopPartition

@[expose] public section

/-! Finite cubical recovery of actual strict three-boundaries in dimension three. -/
open scoped Classical
namespace FiniteChains.Davis
open RACG Mirror Comb
variable {V : Type} [DecidableEq V] [LinearOrder V] {A : CommRel V}

theorem qCube_three_boundary_reconstruction (y : StrictOrdTet (QCube A) →₀ ℤ)
    (hy : ∀ t ∈ y.support, t.1.2.2.2.spx.card ≤ 3)
    (hb : ∀ s ∈ (strictOrdBoundary3 y).support, s.1.2.2.spx.card ≤ 2) :
    ∃ r : QThreeCube A →₀ ℤ, qThreeChainBoundary r = strictOrdBoundary3 y := by
  classical
  let S := y.support.image (fun t => t.1.2.2.2)
  have hc (c : QCube A) (hmem : c ∈ S) : c.spx.card = 3 := by
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hmem
    exact (qCube_tetrahedron_dimensions t (hy t ht)).2.2.2
  let C : {c : QCube A // c ∈ S} → QThreeCube A := fun c => ⟨c.1, hc c.1 c.2⟩
  have hex (a : {c : QCube A // c ∈ S}) : ∃ k : ℤ,
      strictOrdBoundary3 (y.filter (fun t => t.1.2.2.2 = a.1)) =
        k • qThreeCubeBoundary (C a) := qThreeCube_component_boundary (C a) y hy hb
  choose k hk using hex
  refine ⟨∑ a ∈ S.attach, Finsupp.single (C a) (k a), ?_⟩
  rw [map_sum]
  simp only [qThreeChainBoundary, Finsupp.linearCombination_single]
  have hp : strictOrdBoundary3 y = ∑ c ∈ S,
      strictOrdBoundary3 (y.filter (fun t => t.1.2.2.2 = c)) := by
    conv_lhs => rw [strictThreeChain_top_partition y]
    rw [map_sum]
  rw [hp, ← Finset.sum_attach S (fun c =>
    strictOrdBoundary3 (y.filter (fun t => t.1.2.2.2 = c)))]
  apply Finset.sum_congr rfl
  intro a _
  exact (hk a).symm

end FiniteChains.Davis
