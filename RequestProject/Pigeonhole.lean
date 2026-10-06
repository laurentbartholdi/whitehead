import Mathlib

/-!
# The one-violation principle of Section 2

Section 2 of the paper argues as follows.  A chain of `m` inclusions supplies
`m + 1` normal subgroups `M_0, …, M_m` of `G`, and formula (2.3) says that a
*requirement* (indexed here by an element `v` of some type `ι`) which fails at
stage `r` is automatically satisfied at every later stage.  Consequently a fixed
requirement can fail at most once along the chain, so any `m` requirements are
simultaneously satisfied at one of the `m + 1` stages.

This file isolates that combinatorial statement and proves it.  Nothing about
groups, complexes or Fox derivatives is used: the argument is pure pigeonhole.
-/

namespace FiniteChains

/-- **The one-violation principle.**

`P r v` reads "stage `r` satisfies requirement `v`".  The hypothesis `hlater`
is formula (2.3) of the paper: if requirement `v` fails at stage `r`, then it
holds at every later stage of the chain.  If at most `m` requirements are
imposed, then one of the `m + 1` stages `0, …, m` satisfies all of them. -/
theorem exists_stage_satisfying_all {ι : Type*} [DecidableEq ι] {m : ℕ}
    (S : Finset ι) (hcard : S.card ≤ m) (P : ℕ → ι → Prop)
    (hlater : ∀ r, ∀ v, ¬ P r v → ∀ s, r < s → s ≤ m → P s v) :
    ∃ r ≤ m, ∀ v ∈ S, P r v := by
  classical
  rcases S.eq_empty_or_nonempty with rfl | ⟨v₀, hv₀⟩
  · exact ⟨0, Nat.zero_le _, by simp⟩
  -- The stages at which some requirement from `S` fails.
  set bad : Finset ℕ :=
    (Finset.range (m + 1)).filter (fun r => ∃ v ∈ S, ¬ P r v) with hbad
  -- Each requirement fails at most once, so `bad` injects into `S`.
  have hbadcard : bad.card ≤ S.card := by
    have hmem : ∀ r ∈ bad, ∃ v ∈ S, ¬ P r v := by
      intro r hr
      simpa [hbad] using (Finset.mem_filter.mp hr).2
    choose w hwS hwP using hmem
    refine Finset.card_le_card_of_injOn (fun r => if h : r ∈ bad then w r h else v₀)
      ?_ ?_
    · intro r hr
      simp only [Finset.mem_coe] at hr
      simp only [Finset.mem_coe, dif_pos hr]
      exact hwS r hr
    · intro r hr s hs hrs
      simp only [Finset.mem_coe] at hr hs
      simp only [dif_pos hr, dif_pos hs] at hrs
      by_contra hne
      rcases lt_or_gt_of_ne hne with h | h
      · have hsle : s ≤ m := by
          have := (Finset.mem_filter.mp hs).1
          simpa [Nat.lt_succ_iff] using Finset.mem_range.mp this
        exact hwP s hs (hrs ▸ hlater r (w r hr) (hwP r hr) s h hsle)
      · have hrle : r ≤ m := by
          have := (Finset.mem_filter.mp hr).1
          simpa [Nat.lt_succ_iff] using Finset.mem_range.mp this
        exact hwP r hr (hrs ▸ hlater s (w s hs) (hwP s hs) r h hrle)
  -- There are `m + 1` stages but at most `m` bad ones.
  have hsub : bad ⊆ Finset.range (m + 1) := Finset.filter_subset _ _
  have : bad ≠ Finset.range (m + 1) := by
    intro h
    have : m + 1 ≤ m := by
      have := hbadcard.trans hcard
      rwa [h, Finset.card_range] at this
    omega
  obtain ⟨r, hr, hrbad⟩ := Finset.exists_of_ssubset (hsub.ssubset_of_ne this)
  refine ⟨r, by simpa [Nat.lt_succ_iff] using Finset.mem_range.mp hr, ?_⟩
  intro v hv
  by_contra hP
  exact hrbad (Finset.mem_filter.mpr ⟨hr, ⟨v, hv, hP⟩⟩)

end FiniteChains
