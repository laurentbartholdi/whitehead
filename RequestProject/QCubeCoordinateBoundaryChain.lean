module

public import RequestProject.QCubeCoordinateFacetRecovery
public import RequestProject.QCubeFacetIndex

@[expose] public section

/-! Finite coordinate facet chains realize the collapse's ordinary cubical boundary. -/
namespace FiniteChains.Davis
open RACG Mirror Comb
variable {V : Type} [DecidableEq V] [Fintype V] [LinearOrder V] {A : CommRel V}

noncomputable def qCubeCoordinateFacetChain (c : QCube A) : Cube V →₀ ℤ :=
  ∑ i : {v : V // v ∈ c.spx} × ZMod 2,
    Finsupp.single (qCubeToCoordinate (qCubeFacetIndex c i))
      (incid (qCubeToCoordinate (qCubeFacetIndex c i)) i.1.1)

/-- Every coefficient of the genuine finite coordinate facet chain is the ordinary
cubical boundary coefficient used by the truncated collapse. -/
theorem qCubeCoordinateFacetChain_apply (c : QCube A) (g : Cube V) :
    qCubeCoordinateFacetChain c g = cubeBdry (qCubeToCoordinate c) (Sum.inl g) := by
  classical
  have hinj : Function.Injective (fun i : {v : V // v ∈ c.spx} × ZMod 2 =>
      qCubeToCoordinate (qCubeFacetIndex c i)) :=
    qCubeToCoordinate_injective.comp (qCubeFacetIndex_injective c)
  simp only [qCubeCoordinateFacetChain, Finsupp.finset_sum_apply]
  by_cases hg : ∃ i : {v : V // v ∈ c.spx} × ZMod 2,
      qCubeToCoordinate (qCubeFacetIndex c i) = g
  · obtain ⟨i, rfl⟩ := hg
    rw [Finset.sum_eq_single i]
    · simp only [Finsupp.single_eq_same]
      exact (cubeBdry_actual_facet c i.1.1 i.1.2 i.2).symm
    · intro j _ hji
      have hne : qCubeToCoordinate (qCubeFacetIndex c j) ≠
          qCubeToCoordinate (qCubeFacetIndex c i) := fun h => hji (hinj h)
      simp [hne]
    · simp
  · have hzero : cubeBdry (qCubeToCoordinate c) (Sum.inl g) = 0 := by
      apply cubeBdry_zero_off_actual_facets
      intro v hv s he
      exact hg ⟨(⟨v, hv⟩, s), he.symm⟩
    rw [hzero]
    apply Finset.sum_eq_zero
    intro i _
    have hne : qCubeToCoordinate (qCubeFacetIndex c i) ≠ g := fun h => hg ⟨i, h⟩
    simp [hne]

end FiniteChains.Davis
