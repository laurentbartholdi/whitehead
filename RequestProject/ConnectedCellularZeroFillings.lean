module

public import RequestProject.CellComplex
public import RequestProject.StrictOrderChains

@[expose] public section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains.Comb
universe u

/-- Paths from a chosen vertex fill every augmented cellular zero-cycle. -/
theorem zeroCycle_filling_of_connected (X : Complex2.{u}) (a : X.V)
    (hX : IsConnected X) (c : X.V →₀ ℤ) (hc : augC X c = 0) :
    ∃ b : X.E →₀ ℤ, bdry1 X b = c := by
  classical
  choose p hp using hX a
  let s : (X.V →₀ ℤ) →ₗ[ℤ] (X.E →₀ ℤ) :=
    Finsupp.linearCombination ℤ (fun v => pathChain (p v))
  have hs (z : X.V →₀ ℤ) : bdry1 X (s z) = z - augC X z • Finsupp.single a 1 := by
    induction z using Finsupp.induction_linear with
    | zero => simp
    | add z t hz ht =>
      rw [map_add, map_add, hz, ht, map_add, add_smul]
      abel
    | single v n =>
      change bdry1 X (Finsupp.linearCombination ℤ (fun v => pathChain (p v))
        (Finsupp.single v n)) = _
      rw [Finsupp.linearCombination_single, map_smul, bdry1_pathChain_of_isPath (hp v),
        augC_single, smul_sub]
      simp
  exact ⟨s c, by rw [hs, hc, zero_smul, sub_zero]⟩

/-- Normalizing a weak edge filling gives the required strict cellular filling. -/
theorem strict_order_zeroCycle_filling_of_connected {P : Type u} [PartialOrder P]
    (a : P) (hP : IsConnected (orderCx P)) (c : P →₀ ℤ)
    (hc : augC (strictOrderCx P) c = 0) :
    ∃ b : StrictOrdEdge P →₀ ℤ, bdry1 (strictOrderCx P) b = c := by
  obtain ⟨b, hb⟩ := zeroCycle_filling_of_connected (orderCx P) a hP c hc
  exact ⟨normalizeOrdChain1 b, by rw [bdry1_normalizeOrdChain1, hb]⟩

end FiniteChains.Comb
