import RequestProject.StrictSubposetChains
import RequestProject.NormalizedStrictBoundary
import RequestProject.PresCylinderCoverCycles

namespace FiniteChains.PresModel
open Comb
universe u
variable {α J P : Type u} [PartialOrder P] (w : J → List (α × Bool))
  (f : P → CylBase w) (hf : IsPosetCover f)

def cylinderCoverRoseSet : Set P := {p | ∃ x : Rose α, f p = cylIn (aHom w) x}

theorem cylinderCoverCollapse_mem_rose (p : P) :
    cylinderCoverCollapse w hf p ∈ cylinderCoverRoseSet w f :=
  ⟨cylRetr (aHom w) (f p), cylinderCoverCollapse_projection w hf p⟩

theorem cylinderCoverCollapse_fixed_of_mem_rose (p : P)
    (hp : p ∈ cylinderCoverRoseSet w f) : cylinderCoverCollapse w hf p = p := by
  apply hf.upTransform_fixed (cylCollapse (aHom w)) (le_cylIn_cylRetr (aHom w))
  obtain ⟨x, hx⟩ := hp
  rw [hx]
  rfl

theorem cylinderCoverCollapse_idempotent : ∀ p, cylinderCoverCollapse w hf (cylinderCoverCollapse w hf p) = cylinderCoverCollapse w hf p :=
  fun p => cylinderCoverCollapse_fixed_of_mem_rose w f hf _
    (cylinderCoverCollapse_mem_rose w f hf p)

theorem cylinderCoverCollapse_range : Set.range (cylinderCoverCollapse w hf) =
    cylinderCoverRoseSet w f := by
  ext p
  constructor
  · rintro ⟨q, rfl⟩
    exact cylinderCoverCollapse_mem_rose w f hf q
  · intro hp
    exact ⟨p, cylinderCoverCollapse_fixed_of_mem_rose w f hf p hp⟩

/-- Every surviving genuine edge of a collapsed finite chain lies in the actual rose preimage. -/
theorem cylinderCoverCollapsedChain_support_rose (c : StrictOrdEdge P →₀ ℤ) :
    ∀ e ∈ (normalizedStrictChain1 (cylinderCoverCollapse w hf)
      (cylinderCoverCollapse_monotone w hf) c).support,
      e.1.1 ∈ cylinderCoverRoseSet w f ∧ e.1.2 ∈ cylinderCoverRoseSet w f := by
  classical
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd =>
    intro e he
    rw [map_add] at he
    rcases Finset.mem_union.mp (Finsupp.support_add he) with h | h
    · exact hc e h
    · exact hd e h
  | single t n =>
    intro e he
    rw [normalizedStrictChain1_single] at he
    by_cases h : cylinderCoverCollapse w hf t.1.1 = cylinderCoverCollapse w hf t.1.2
    · simp [normalizeOrdEdge, h] at he
    · simp only [normalizeOrdEdge, dif_neg h] at he
      let r : StrictOrdEdge P := ⟨(cylinderCoverCollapse w hf t.1.1,
        cylinderCoverCollapse w hf t.1.2),
        lt_of_le_of_ne (cylinderCoverCollapse_monotone w hf t.2.le) h⟩
      change e ∈ (n • Finsupp.single r (1 : ℤ)).support at he
      have hr : e = r := by
        by_contra hn
        have hz : (n • Finsupp.single r (1 : ℤ)) e = 0 := by simp [Ne.symm hn]
        exact (Finsupp.mem_support_iff.mp he) hz
      subst e
      exact ⟨cylinderCoverCollapse_mem_rose w f hf t.1.1,
        cylinderCoverCollapse_mem_rose w f hf t.1.2⟩

/-- The actual collapsed chain is a genuine finite edge chain on the actual rose preimage. -/
theorem exists_cylinderCoverCollapsedRoseChain (c : StrictOrdEdge P →₀ ℤ) :
    ∃ d : StrictOrdEdge (cylinderCoverRoseSet w f) →₀ ℤ,
      chain1 (strictSubposetIncl (cylinderCoverRoseSet w f)) d =
        normalizedStrictChain1 (cylinderCoverCollapse w hf)
          (cylinderCoverCollapse_monotone w hf) c := by
  let z := normalizedStrictChain1 (cylinderCoverCollapse w hf)
    (cylinderCoverCollapse_monotone w hf) c
  let d := Finsupp.comapDomain (strictSubposetIncl (cylinderCoverRoseSet w f)).onE z
    (strictSubposetIncl_onE_injective (cylinderCoverRoseSet w f)).injOn
  refine ⟨d, ?_⟩
  apply Finsupp.mapDomain_comapDomain _ (strictSubposetIncl_onE_injective _) z
  intro e he
  have hs := cylinderCoverCollapsedChain_support_rose w f hf c e he
  exact ⟨⟨(⟨e.1.1, hs.1⟩, ⟨e.1.2, hs.2⟩), e.2⟩, Subtype.ext rfl⟩

end FiniteChains.PresModel
