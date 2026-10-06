import RequestProject.ChamberQuotientOldGeneration
import RequestProject.ChamberQuotientAttachingCover
import RequestProject.NerveDegreeTransfer

/-! Actual finite cycles in the covering of the attaching surface, with old-cell corrections. -/
namespace FiniteChains.Davis
open RACG Mirror Comb Nerve
universe u
variable {V : Type u} [DecidableEq V] [Fintype V] {A : CommRel V}
  {X : Type u} [PartialOrder X] {att : NeSpx A →o X}

/-- Every old-cell two-cycle is a genuine cycle of the lifted attaching poset,
modulo a finite homogeneous three-chain entirely on old cells.
The anchor simplex only supplies nonemptiness of the attaching cover. -/
theorem qUniversal_old_cycle_from_attaching (x : X) (hx : IsConnected (orderCx X))
    (σ : NeSpx A)
    (z : Ch (UOrder (Qpos A X att) (qNew x)))
    (hz : z ∈ IncOn (fun p => InQOld (uOrderEnd p)))
    (hd : lengthProjection 3 z = z) (hcyc : Nerve.bdry z = 0) :
    ∃ c : Ch (QLiftedAttaching (qNew (A := A) (att := att) x)),
      c ∈ Inc _ ∧ lengthProjection 3 c = c ∧ Nerve.bdry c = 0 ∧
      ∃ y ∈ IncOn (fun p => InQOld (uOrderEnd p)),
        lengthProjection 4 y = y ∧ z = cmap Subtype.val c + Nerve.bdry y := by
  letI : Nonempty X := ⟨x⟩
  let J := fun p : UOrder (Qpos A X att) (qNew x) =>
    InQOld (uOrderEnd p) ∧ InQBaseStar (uOrderEnd p)
  have hnonempty : ∃ p, J p := by
    have hc : IsConnected (orderCx (Qpos A X att)) :=
      qpos_isConnected_of_zpos (zpos_isConnected hx)
    obtain ⟨p, hp⟩ := (uOrderEnd_isPosetCover (a := qNew x) hc).surj
      (Sum.inl (posQCube σ))
    refine ⟨p, ?_⟩
    change InQOld (uOrderEnd p) ∧ InQBaseStar (uOrderEnd p)
    rw [hp]
    exact ⟨trivial, rfl⟩
  obtain ⟨c₀, hc₀, y₀, hy₀, hdc₀, he₀⟩ :=
    qUniversal_old_generates_positive x hx z hz hd hcyc
  let b := lengthProjection 3 c₀
  let y := lengthProjection 4 y₀
  have hb : b ∈ IncOn J := lengthProjection_mem_incOn _ hc₀
  have hbd : lengthProjection 3 b = b := lengthProjection_idempotent _ _
  have hbc : Nerve.bdry b = 0 := by
    rw [← lengthProjection_bdry, hdc₀, map_zero]
  have he : z = b + Nerve.bdry y := by
    rw [← hd, he₀, map_add, lengthProjection_bdry]
  obtain ⟨c, hc, hcb⟩ := exists_preimage_of_mem_incOn J hb
  refine ⟨c, hc, ?_, ?_, y, lengthProjection_mem_incOn _ hy₀,
    lengthProjection_idempotent _ _, ?_⟩
  · apply cmap_val_injective J hnonempty
    rw [← lengthProjection_cmap, hcb, hbd]
  · apply cmap_val_injective J hnonempty
    rw [cmap_bdry, hcb, hbc, map_zero]
  · rw [hcb]
    exact he

end FiniteChains.Davis
