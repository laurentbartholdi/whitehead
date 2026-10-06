module

public import RequestProject.NerveDegreeGluing

@[expose] public section

/-! Ambient generation in one piece forces generation by the intersection in the other. -/
namespace FiniteChains.Nerve
universe u
variable {P : Type u} [Preorder P]

theorem generatesDegreeIn_intersection_of_ambient {A B U : P → Prop} {n : ℕ}
    (hAU : ∀ p, A p → U p)
    (hmix : ∀ a b : P, a ≤ b → U a → U b → (A a ∧ A b) ∨ (B a ∧ B b))
    (hgen : GeneratesDegreeIn U B n) :
    GeneratesDegreeIn A (fun p => A p ∧ B p) n := by
  intro z hz hd hcyc
  obtain ⟨c, hc, y, hy, _, he⟩ := hgen z (incOn_mono hAU hz) hd hcyc
  obtain ⟨a, ha, b, hb, hab⟩ := exists_split_of_unmixed hmix hy
  let t := z - bdry a
  have htA : t ∈ IncOn A := AddSubgroup.sub_mem _ hz (bdry_mem_incOn ha)
  have htB : t ∈ IncOn B := by
    have ht : t = c + bdry b := by
      dsimp only [t]
      rw [he, hab, map_add]
      abel
    rw [ht]
    exact AddSubgroup.add_mem _ hc (bdry_mem_incOn hb)
  refine ⟨t, ?_, a, ha, ?_, ?_⟩
  · rw [← incOn_inf]
    exact ⟨htA, htB⟩
  · simp only [t, map_sub, bdry_bdry, hcyc, sub_zero]
  · dsimp only [t]
    abel

end FiniteChains.Nerve
