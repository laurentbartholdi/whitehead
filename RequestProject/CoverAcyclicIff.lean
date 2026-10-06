module

public import RequestProject.HurewiczIso
public import RequestProject.CoverAcyclic

@[expose] public section

/-!
# Remark 1 of the paper, in algebraic form: acyclicity of `K_N` characterises `N`

`RequestProject/CoverAcyclic.lean` proves one direction of Remark 1: if `N = Ñ/R` is perfect
and the requirements (2.2) hold for `Ñ`, then the chain complex of the cover `K_N` is
acyclic.  With the Hurewicz dictionary of `RequestProject/HurewiczIso.lean` the converse is
available as well, so the two conditions are equivalent:

`H₁(K_N) = 0 ⟺ N is perfect` (`FiniteChains.cover_h1_trivial_iff_perfect`,
`FiniteChains.subsingleton_coverH1_iff`), and `H₂(K_N) = 0 ⟺` the requirements (2.2)
(`FiniteChains.foxSat_iff_bdry2_injective`); together they give
`FiniteChains.cover_acyclic_iff`, the algebraic statement of Remark 1.
-/

namespace FiniteChains

open MonoidAlgebra

variable {α : Type*} [Fintype α] [DecidableEq α]
variable (Nsub : Subgroup (FreeGroup α)) [Nsub.Normal]
variable {J : Type*} [Fintype J] (ρ : J → FreeGroup α)

/-- **`H₁(K_N) = 0` forces `N` to be perfect.**  If every cycle of the chain complex of the
cover is a boundary, then `Ñ ≤ R·[Ñ, Ñ]`. -/
theorem le_relComm_of_cycles_eq_bdrys (hρ : ∀ j, ρ j ∈ Nsub)
    (h1 : ∀ c : α → CoverRing Nsub, bdry1 Nsub c = 0 →
      ∃ u : J → CoverRing Nsub, bdry2 Nsub ρ u = c) :
    Nsub ≤ relComm Nsub ρ := by
  intro w hw
  obtain ⟨u, hu⟩ := h1 (foxVec Nsub w) (bdry1_foxVec Nsub hw)
  exact (foxVec_mem_range_bdry2_iff Nsub ρ hρ hw).1 ⟨u, hu⟩

/-- **`H₁(K_N) = 0` if and only if `N` is perfect.** -/
theorem cover_h1_trivial_iff_perfect (hρ : ∀ j, ρ j ∈ Nsub) :
    (∀ c : α → CoverRing Nsub, bdry1 Nsub c = 0 →
      ∃ u : J → CoverRing Nsub, bdry2 Nsub ρ u = c) ↔ Nsub ≤ relComm Nsub ρ :=
  ⟨le_relComm_of_cycles_eq_bdrys Nsub ρ hρ, fun hperf =>
    exists_bdry2_preimage Nsub ρ hρ hperf⟩

omit [Fintype α] [DecidableEq α] [Fintype J] [Nsub.Normal] in
/-- `Ñ ≤ R·[Ñ, Ñ]` says exactly that `N = Ñ/R` is perfect. -/
theorem le_relComm_iff_perfect (hR : relSub ρ ≤ Nsub) :
    Nsub ≤ relComm Nsub ρ ↔ ⁅presSub ρ Nsub, presSub ρ Nsub⁆ = presSub ρ Nsub := by
  have hcomm : ⁅presSub ρ Nsub, presSub ρ Nsub⁆
      = ⁅Nsub, Nsub⁆.map (QuotientGroup.mk' (relSub ρ)) := by
    rw [presSub, ← Subgroup.map_commutator]
  constructor
  · intro hperf
    refine le_antisymm ?_ ?_
    · exact Subgroup.commutator_le_self _
    · have hmap : (relComm Nsub ρ).map (QuotientGroup.mk' (relSub ρ))
          = ⁅presSub ρ Nsub, presSub ρ Nsub⁆ := by
        rw [relComm, Subgroup.map_sup, hcomm, ← relSub,
          (Subgroup.map_eq_bot_iff _).2 (by rw [QuotientGroup.ker_mk']), bot_sup_eq]
      calc presSub ρ Nsub = Nsub.map (QuotientGroup.mk' (relSub ρ)) := rfl
        _ ≤ (relComm Nsub ρ).map (QuotientGroup.mk' (relSub ρ)) := Subgroup.map_mono hperf
        _ = ⁅presSub ρ Nsub, presSub ρ Nsub⁆ := hmap
  · intro hperf
    have hcomap : Subgroup.comap (QuotientGroup.mk' (relSub ρ)) (presSub ρ Nsub) = Nsub :=
      Subgroup.comap_map_eq_self (by simpa using hR)
    have h := comap_le_ker_sup_commutator (QuotientGroup.mk' (relSub ρ))
      (QuotientGroup.mk'_surjective _) hperf
    rw [hcomap, QuotientGroup.ker_mk'] at h
    exact h

/-- The first homology of the cover is trivial exactly when every cycle is a boundary. -/
theorem subsingleton_coverH1_iff_cycles_eq_bdrys :
    Subsingleton (CoverH1 Nsub ρ) ↔
      ∀ c : α → CoverRing Nsub, bdry1 Nsub c = 0 →
        ∃ u : J → CoverRing Nsub, bdry2 Nsub ρ u = c := by
  constructor
  · intro hsub c hc
    have h0 : QuotientAddGroup.mk (s := (coverBdrys Nsub ρ).addSubgroupOf (coverCycles Nsub))
        (⟨c, hc⟩ : coverCycles Nsub) = 0 := Subsingleton.elim _ _
    obtain ⟨u, hu⟩ := (QuotientAddGroup.eq_zero_iff _).1 h0
    exact ⟨u, hu⟩
  · intro h1
    refine ⟨fun x y => ?_⟩
    have hzero : ∀ z : CoverH1 Nsub ρ, z = 0 := by
      intro z
      refine QuotientAddGroup.induction_on z fun c => ?_
      refine (QuotientAddGroup.eq_zero_iff _).2 ?_
      obtain ⟨u, hu⟩ := h1 (c : α → CoverRing Nsub) c.2
      exact ⟨u, hu⟩
    rw [hzero x, hzero y]

/-- **`H₁(K_N) = 0` if and only if `N = Ñ/R` is perfect**, in terms of the homology group
itself. -/
theorem subsingleton_coverH1_iff (hR : relSub ρ ≤ Nsub) :
    Subsingleton (CoverH1 Nsub ρ) ↔ ⁅presSub ρ Nsub, presSub ρ Nsub⁆ = presSub ρ Nsub := by
  have hρ : ∀ j, ρ j ∈ Nsub := fun j =>
    hR (Subgroup.subset_normalClosure (Set.mem_range_self j))
  rw [subsingleton_coverH1_iff_cycles_eq_bdrys, cover_h1_trivial_iff_perfect Nsub ρ hρ,
    le_relComm_iff_perfect Nsub ρ hR]

/-- **Remark 1 of the paper, algebraically.**  The chain complex of the cover `K_N` is
acyclic if and only if `N = Ñ/R` is perfect and the requirements (2.2) hold for `Ñ`, that
is, the Fox boundary `∂_{2,N}` is injective. -/
theorem cover_acyclic_iff (hR : relSub ρ ≤ Nsub) :
    ((∀ u : J → CoverRing Nsub, bdry2 Nsub ρ u = 0 → u = 0) ∧
        ∀ c : α → CoverRing Nsub, bdry1 Nsub c = 0 →
          ∃ u : J → CoverRing Nsub, bdry2 Nsub ρ u = c) ↔
      (⁅presSub ρ Nsub, presSub ρ Nsub⁆ = presSub ρ Nsub ∧
        ∀ v : J →₀ FreeGroupRing α, FoxSat (foxMatrix ρ) v Nsub) := by
  have hρ : ∀ j, ρ j ∈ Nsub := fun j =>
    hR (Subgroup.subset_normalClosure (Set.mem_range_self j))
  rw [and_comm (a := ⁅presSub ρ Nsub, presSub ρ Nsub⁆ = presSub ρ Nsub),
    foxSat_iff_bdry2_injective Nsub ρ, cover_h1_trivial_iff_perfect Nsub ρ hρ,
    le_relComm_iff_perfect Nsub ρ hR]

end FiniteChains
