import RequestProject.OrderNerveSmallChainMapAll

namespace FiniteChains.Comb
open TopologicalSingular SingularSubdivision
variable {P : Type} [PartialOrder P]

/-- Restrict the comparable-vertex carrier to vertices that actually occur
at some point of the singular simplex. This restriction preserves acyclicity
and makes the carrier respect every vertex subcomplex. -/
def orderNerveTightCarrier {n : ℕ} (σ : Simplex (orderNerveRealization P) n) : Set P :=
  {p | (∃ z, σ z ∈ orderNerveRealizationOpenStar P p) ∧ p ∈ orderNerveSingularCarrier σ}

theorem orderNerveTightCarrier_face {n : ℕ} (σ : Simplex (orderNerveRealization P) (n + 1))
    (i : Fin (n + 2)) : orderNerveTightCarrier (face i σ) ⊆ orderNerveTightCarrier σ := by
  rintro p ⟨⟨z, hz⟩, hp⟩
  exact ⟨⟨_, hz⟩, orderNerveSingularCarrier_face σ i hp⟩

theorem orderNerveStarIndices_subset_tight {n : ℕ} (σ : Simplex (orderNerveRealization P) n) :
    orderNerveSingularStarIndices σ ⊆ orderNerveTightCarrier σ := by
  intro p hp
  exact ⟨⟨stdSimplex.vertex 0, hp _⟩, orderNerveSingularStarIndices_subset_carrier σ hp⟩

theorem orderNerveTightCarrier_acyclic {n : ℕ} (σ : OrderSmallSimplex P n) :
    Nerve.AcyclicIn (orderNerveTightCarrier σ.val) := by
  obtain ⟨v, hv⟩ := σ.property
  have hv' := orderNerveStarIndices_subset_tight σ.val hv
  apply Nerve.acyclicIn_of_subtype _ ⟨v, hv'⟩
  intro c hc hz
  exact orderNerve_cycle_bounds_of_comparable
    (⟨v, hv'⟩ : orderNerveTightCarrier σ.val) (fun p => p.property.2 v hv) hc hz

theorem orderNerveTightCarrier_subset {n : ℕ} (σ : Simplex (orderNerveRealization P) n)
    (A : Set P) (hσ : ∀ z, σ z ∈ orderNerveRealizationSubcomplex P A) :
    orderNerveTightCarrier σ ⊆ A := by
  rintro p ⟨⟨z, hz⟩, _⟩
  by_contra hp
  have he := hσ z p hp
  change 0 < orderNerveRealizationCoordinates P (σ z) p at hz
  rw [he] at hz
  exact lt_irrefl _ hz

theorem orderSmallToNerve0_tight (σ : OrderSmallSimplex P 0) :
    orderSmallToNerve0 (orderSmallSingle σ 1) ∈ Nerve.IncOn (orderNerveTightCarrier σ.val) := by
  rw [orderSmallToNerve0_single, one_smul]
  apply Nerve.of_mem_incOn (by simp)
  intro p hp
  have hp' : p = orderSmallChosenVertex σ := by simpa using hp
  rw [hp']
  exact orderNerveStarIndices_subset_tight σ.val σ.property.choose_spec

end FiniteChains.Comb
