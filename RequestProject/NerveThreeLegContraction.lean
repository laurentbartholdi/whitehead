module

public import RequestProject.NervePrism

@[expose] public section

/-! A three-leg order contraction supplies actual augmented nerve fillings. -/
namespace FiniteChains.Nerve
universe u
variable {P : Type u} [Preorder P]

theorem exists_bdry_eq_of_cycle_threeLeg (r g : P → P) (d : P)
    (hr : Monotone r) (hg : Monotone g) (hri : ∀ p, r p ≤ p)
    (hrg : ∀ p, r p ≤ g p) (hdg : ∀ p, d ≤ g p)
    (c : Ch P) (hc : c ∈ Inc P) (hcyc : bdry c = 0) :
    ∃ y ∈ Inc P, bdry y = c := by
  have h₁ := bdry_prism_add_prism_bdry r id c
  have h₂ := bdry_prism_add_prism_bdry r g c
  have h₃ := bdry_prism_add_prism_bdry (fun _ => d) g c
  rw [hcyc, map_zero, add_zero, cmap_id] at h₁
  rw [hcyc, map_zero, add_zero] at h₂ h₃
  have h₄ : bdry (consMap d (cmap (fun _ => d) c)) = cmap (fun _ => d) c := by
    have he : bdry (consMap d (cmap (fun _ => d) c)) +
        consMap d (cmap (fun _ => d) (bdry c)) = cmap (fun _ => d) c := by
      rw [bdry_consMap, cmap_bdry]
      abel
    simpa only [hcyc, map_zero, add_zero] using he
  refine ⟨prism r id c - prism r g c + prism (fun _ => d) g c +
    consMap d (cmap (fun _ => d) c), ?_, ?_⟩
  · exact AddSubgroup.add_mem _
      (AddSubgroup.add_mem _
        (AddSubgroup.sub_mem _ (prism_mem_inc hr monotone_id hri hc)
          (prism_mem_inc hr hg hrg hc))
        (prism_mem_inc monotone_const hg hdg hc)) (cone_const_mem_inc d c)
  · rw [map_add, map_add, map_sub, h₁, h₂, h₃, h₄]
    abel

end FiniteChains.Nerve
