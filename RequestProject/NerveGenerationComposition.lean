import RequestProject.NerveDegreeGluing

/-! Compose positive-degree generation while retaining finite homogeneous fillings. -/
namespace FiniteChains.Nerve
universe u
variable {P : Type u} [Preorder P]

theorem generatesDegreeIn_trans {U B C : P → Prop} {n : ℕ}
    (hBU : ∀ p, B p → U p) (hUB : GeneratesDegreeIn U B (n + 1))
    (hBC : GeneratesDegreeIn B C (n + 1)) : GeneratesDegreeIn U C (n + 1) := by
  intro z hz hd hcyc
  obtain ⟨c, hc, y, hy, hdc, he⟩ := hUB z hz hd hcyc
  let c' := lengthProjection (n + 1) c
  let y' := lengthProjection (n + 2) y
  have hc' : c' ∈ IncOn B := lengthProjection_mem_incOn _ hc
  have hdc' : bdry c' = 0 := by
    rw [← lengthProjection_bdry, hdc, map_zero]
  have he' : z = c' + bdry y' := by
    rw [← hd, he, map_add, lengthProjection_bdry]
  obtain ⟨d, hdC, w, hw, hdd, hec⟩ :=
    hBC c' hc' (lengthProjection_idempotent _ _) hdc'
  refine ⟨d, hdC, y' + w, AddSubgroup.add_mem _ (lengthProjection_mem_incOn _ hy)
    (incOn_mono hBU hw), hdd, ?_⟩
  rw [he', hec, map_add]
  abel

end FiniteChains.Nerve
