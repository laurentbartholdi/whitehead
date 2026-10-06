module

public import RequestProject.NerveDegreeTransfer

@[expose] public section

/-! Actual fillings transferred by a lower order homotopy. -/
namespace FiniteChains.Nerve
universe u
variable {P Q : Type u} [Preorder P] [Preorder Q]

theorem filling_of_lower_composite (r : P → Q) (s : Q → P)
    (hr : Monotone r) (hs : Monotone s) (hle : ∀ p, s (r p) ≤ p) (n : ℕ)
    (hfill : ∀ c ∈ Inc Q, lengthProjection n c = c → bdry c = 0 →
      ∃ y ∈ Inc Q, bdry y = c)
    (c : Ch P) (hc : c ∈ Inc P) (hd : lengthProjection n c = c)
    (hcyc : bdry c = 0) : ∃ y ∈ Inc P, bdry y = c := by
  obtain ⟨b, hb, hdb⟩ := hfill (cmap r c) (cmap_mem_inc_of_monotone hr hc)
    (by rw [lengthProjection_cmap, hd]) (by rw [← cmap_bdry, hcyc, map_zero])
  have hp := bdry_prism_add_prism_bdry (s ∘ r) id c
  rw [hcyc, map_zero, add_zero, cmap_id] at hp
  refine ⟨cmap s b + prism (s ∘ r) id c,
    AddSubgroup.add_mem _ (cmap_mem_inc_of_monotone hs hb)
      (prism_mem_inc (hs.comp hr) monotone_id hle hc), ?_⟩
  rw [map_add, ← cmap_bdry, hdb, hp, cmap_comp]
  abel

end FiniteChains.Nerve
