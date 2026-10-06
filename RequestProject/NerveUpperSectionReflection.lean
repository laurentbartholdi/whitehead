module

public import RequestProject.NerveRelativeGluing

@[expose] public section

/-! A concrete upper order homotopy reflects fillings along its projection. -/
namespace FiniteChains.Nerve
universe u
variable {P Q : Type u} [Preorder P] [Preorder Q]

/-- A filling of the projected cycle pulls back along the section; the prism
corrects it to a filling of the original cycle. -/
theorem boundary_reflection_of_upper_section (r : P → Q) (s : Q → P)
    (hr : Monotone r) (hs : Monotone s) (hle : ∀ p, p ≤ s (r p))
    (c : Ch P) (hc : c ∈ Inc P) (hcyc : bdry c = 0)
    (hbound : ∃ y ∈ Inc Q, bdry y = cmap r c) :
    ∃ y ∈ Inc P, bdry y = c := by
  obtain ⟨y, hy, hdy⟩ := hbound
  have hp := bdry_prism_add_prism_bdry id (s ∘ r) c
  rw [hcyc, map_zero, add_zero, cmap_id] at hp
  refine ⟨cmap s y - prism id (s ∘ r) c,
    AddSubgroup.sub_mem _ (cmap_mem_inc_of_monotone hs hy)
      (prism_mem_inc monotone_id (hs.comp hr) hle hc), ?_⟩
  rw [map_sub, ← cmap_bdry, hdy, cmap_comp, hp]
  abel

end FiniteChains.Nerve
