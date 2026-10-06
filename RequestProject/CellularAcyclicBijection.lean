import RequestProject.CellularChainMapZero

/-! Acyclicity is preserved and reflected by bijections on actual
cell labels. Pending final Lean verification. -/

namespace FiniteChains.Comb
universe u
variable {X Y : Complex2.{u}} (f : Hom X Y)

theorem augC_chain0 (z : X.V →₀ ℤ) : augC Y (chain0 f z) = augC X z := by
  induction z using Finsupp.induction_linear with
  | zero => simp
  | add z w hz hw => rw [map_add, map_add, map_add, hz, hw]
  | single v n => simp [chain0, augC_single]

theorem isAcyclic_iff_of_cell_bijections
    (hV : Function.Bijective f.onV) (hE : Function.Bijective f.onE)
    (hF : Function.Bijective f.onF) : IsAcyclic X ↔ IsAcyclic Y := by
  classical
  have iV : Function.Injective (chain0 f) := Finsupp.mapDomain_injective hV.1
  have iE : Function.Injective (chain1 f) := Finsupp.mapDomain_injective hE.1
  have iF : Function.Injective (chain2 f) := Finsupp.mapDomain_injective hF.1
  have sV : Function.Surjective (chain0 f) := Finsupp.mapDomain_surjective (M := ℤ) hV.2
  have sE : Function.Surjective (chain1 f) := Finsupp.mapDomain_surjective (M := ℤ) hE.2
  have sF : Function.Surjective (chain2 f) := Finsupp.mapDomain_surjective (M := ℤ) hF.2
  constructor
  · intro h
    refine ⟨?_, ?_, ?_⟩
    · intro a b hab
      obtain ⟨a', rfl⟩ := sF a
      obtain ⟨b', rfl⟩ := sF b
      rw [bdry2_chain2, bdry2_chain2] at hab
      exact congrArg (chain2 f) (h.h2 (iE hab))
    · intro a ha
      obtain ⟨a', rfl⟩ := sE a
      have hcycle : bdry1 X a' = 0 := by
        apply iV
        rw [map_zero, ← bdry1_chain1, ha]
      obtain ⟨b, hb⟩ := h.h1 a' hcycle
      exact ⟨chain2 f b, by rw [bdry2_chain2, hb]⟩
    · intro a ha
      obtain ⟨a', rfl⟩ := sV a
      rw [augC_chain0] at ha
      obtain ⟨b, hb⟩ := h.h0 a' ha
      exact ⟨chain1 f b, by rw [bdry1_chain1, hb]⟩
  · intro h
    refine ⟨?_, ?_, ?_⟩
    · intro a b hab
      apply iF
      apply h.h2
      rw [bdry2_chain2, bdry2_chain2, hab]
    · intro a ha
      have hcycle : bdry1 Y (chain1 f a) = 0 := by
        rw [bdry1_chain1, ha, map_zero]
      obtain ⟨b, hb⟩ := h.h1 (chain1 f a) hcycle
      obtain ⟨b', rfl⟩ := sF b
      exact ⟨b', iE (by rwa [← bdry2_chain2])⟩
    · intro a ha
      have hcycle : augC Y (chain0 f a) = 0 := by rw [augC_chain0, ha]
      obtain ⟨b, hb⟩ := h.h0 (chain0 f a) hcycle
      obtain ⟨b', rfl⟩ := sE b
      exact ⟨b', iV (by rwa [← bdry1_chain1])⟩

end FiniteChains.Comb
