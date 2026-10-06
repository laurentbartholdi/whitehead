import RequestProject.ChamberQuotientOldRelativeFillings
import RequestProject.ChamberQuotientAttachingCover

/-! Relative old-cell fillings with the prescribed boundary in the actual attaching cover. -/
namespace FiniteChains.Davis
open RACG Mirror Comb Nerve
universe u
variable {V : Type u} [DecidableEq V] [Fintype V] {A : CommRel V}
  {X : Type u} [PartialOrder X] {att : NeSpx A →o X}

/-- A relative old two-chain is replaced by a two-chain on the genuine
attaching cover, with its prescribed boundary there. No zero-boundary input
is imposed on the original chain. -/
theorem qUniversal_old_relative_chain_from_attaching (x : X)
    (hx : IsConnected (orderCx X)) (σ : NeSpx A)
    (z : Ch (UOrder (Qpos A X att) (qNew x)))
    (hz : z ∈ IncOn (fun p => InQOld (uOrderEnd p)))
    (hd : lengthProjection 3 z = z)
    (b : Ch (QLiftedAttaching (qNew (A := A) (att := att) x))) (hb : b ∈ Inc _)
    (hbz : Nerve.bdry z = cmap Subtype.val b) :
    ∃ c : Ch (QLiftedAttaching (qNew (A := A) (att := att) x)),
      c ∈ Inc _ ∧ lengthProjection 3 c = c ∧ Nerve.bdry c = b ∧
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
  have hdz : Nerve.bdry z ∈ IncOn J := by
    rw [hbz]
    exact cmap_val_mem_incOn J hb
  obtain ⟨t, ht, htd, hdt, y, hy, hyd, he⟩ :=
    qUniversal_old_relative_filling x hx z hz hd hdz
  obtain ⟨c, hc, hct⟩ := exists_preimage_of_mem_incOn J ht
  refine ⟨c, hc, ?_, ?_, y, hy, hyd, ?_⟩
  · apply cmap_val_injective J hnonempty
    rw [← lengthProjection_cmap, hct, htd]
  · apply cmap_val_injective J hnonempty
    rw [cmap_bdry, hct, hdt, hbz]
  · rw [hct]
    exact he

end FiniteChains.Davis
