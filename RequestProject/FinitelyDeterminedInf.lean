import RequestProject.SubgroupCompactness

/-!
# Finitely determined requirements pass to intersections of chains

The minimality step of Section 2 needs that, at the intersection of a decreasing chain of
normal subgroups all of which satisfy the requirements, no requirement can fail: "any
finite list of membership answers agrees with some member".

This file proves that for an arbitrary finitely determined family of requirements
(`FinitelyDetermined`, see `RequestProject/SubgroupCompactness.lean`), so that the
hypothesis `sat_sInf_chain` of `FiniteChains.NecessityInputs` is a theorem for the Fox
requirements of Section 2.
-/

namespace FiniteChains

variable {G : Type*} [Group G]

/-- A finite subset of a nonempty chain has a lower bound inside the chain. -/
theorem exists_lower_bound_of_chain {C : Set (Subgroup G)} (hC : IsChain (· ≤ ·) C)
    (hne : C.Nonempty) (T : Finset (Subgroup G)) (hT : ↑T ⊆ C) :
    ∃ N ∈ C, ∀ x ∈ T, N ≤ x := by
  classical
  induction T using Finset.induction with
  | empty => obtain ⟨N, hN⟩ := hne; exact ⟨N, hN, by simp⟩
  | insert a T _ ih =>
      have hTsub : ↑T ⊆ C := fun x hx => hT (by simp [hx])
      have haC : a ∈ C := hT (by simp)
      obtain ⟨N, hNC, hN⟩ := ih hTsub
      rcases eq_or_ne N a with rfl | hne'
      · exact ⟨N, hNC, fun x hx => by
          rcases Finset.mem_insert.mp hx with rfl | hx'
          · exact le_rfl
          · exact hN x hx'⟩
      · rcases hC hNC haC hne' with hle | hle
        · exact ⟨N, hNC, fun x hx => by
            rcases Finset.mem_insert.mp hx with rfl | hx'
            · exact hle
            · exact hN x hx'⟩
        · exact ⟨a, haC, fun x hx => by
            rcases Finset.mem_insert.mp hx with rfl | hx'
            · exact le_rfl
            · exact hle.trans (hN x hx')⟩

/-- **The requirements pass to intersections of decreasing chains.**  If every requirement
depends on finitely many membership decisions, and if every member of a nonempty chain of
subgroups satisfies all requirements, then so does the intersection of the chain. -/
theorem sat_sInf_of_finitelyDetermined {ι : Type*} (Sat : Subgroup G → ι → Prop)
    (det : FinitelyDetermined Sat) {C : Set (Subgroup G)} (hC : IsChain (· ≤ ·) C)
    (hne : C.Nonempty) (hsat : ∀ N ∈ C, ∀ v, Sat N v) (v : ι) : Sat (sInf C) v := by
  classical
  obtain ⟨F, hF⟩ := det v
  -- for each element of `F` missing from the intersection, a member of the chain missing it
  have hchoice : ∀ g : G, ∃ N : Subgroup G, N ∈ C ∧ (g ∉ sInf C → g ∉ N) := by
    intro g
    by_cases hg : g ∈ sInf C
    · obtain ⟨N, hN⟩ := hne
      exact ⟨N, hN, fun h => absurd hg h⟩
    · have : ∃ N ∈ C, g ∉ N := by
        by_contra hcon
        push_neg at hcon
        exact hg (Subgroup.mem_sInf.mpr hcon)
      obtain ⟨N, hNC, hgN⟩ := this
      exact ⟨N, hNC, fun _ => hgN⟩
  choose wit hwitC hwit using hchoice
  obtain ⟨N, hNC, hNle⟩ :=
    exists_lower_bound_of_chain hC hne (F.image wit)
      (by
        intro x hx
        simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe] at hx
        obtain ⟨g, -, rfl⟩ := hx
        exact hwitC g)
  have hagree : ∀ g ∈ F, (g ∈ sInf C ↔ g ∈ N) := by
    intro g hg
    refine ⟨fun hmem => (sInf_le hNC) hmem, fun hmem => ?_⟩
    by_contra hcon
    exact hwit g hcon (hNle _ (Finset.mem_image.mpr ⟨g, hg, rfl⟩) hmem)
  exact (hF (sInf C) N hagree).2 (hsat N hNC v)

end FiniteChains
