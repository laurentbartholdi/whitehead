import RequestProject.PresWordEmbeddingValidPi2
import RequestProject.Pi2DictionaryFinsupp
import RequestProject.PresUnivCoverIso

namespace FiniteChains
open Comb

variable {α β J K Q : Type} [DecidableEq α] [Group Q]

/-- The Fox-kernel condition is exactly the existing algebraic-cover cycle
condition, including for infinite sets of generators and relators. -/
theorem fox_kernel_vanish_iff_univCover (ρ : J → FreeGroup α)
    (φ : PresGroup ρ →* Q) (g : J → K) :
    (∀ z : LinearMap.ker ((coverSecondBoundary (relSub ρ) ρ).restrictScalars ℤ),
      Finsupp.mapDomain (Prod.map φ g) (groupCellChainEquiv.symm z.val) = 0) ↔
    ∀ c : PresGroup ρ × J →₀ ℤ, Comb.bdry2 (univCover ρ) c = 0 →
      Finsupp.mapDomain (Prod.map φ g) c = 0 := by
  have hb (c : PresGroup ρ × J →₀ ℤ) :
      Comb.bdry2 (univCover ρ) c = 0 ↔
        coverSecondBoundary (relSub ρ) ρ (groupCellChainEquiv c) = 0 := by
    change Comb.bdry2 (univCover ρ) c = 0 ↔
      coverSecondBoundary (relSub ρ) ρ (fsCoords (relSub ρ) J c) = 0
    rw [fs_coverComplex_bdry2]
    exact (map_eq_zero_iff _ (fsCoords (relSub ρ) α).injective).symm
  constructor
  · intro hz c hc
    have he := hz ⟨groupCellChainEquiv c, (hb c).mp hc⟩
    simpa only [LinearEquiv.symm_apply_apply] using he
  · intro hz z
    apply hz
    apply (hb _).mpr
    rw [LinearEquiv.apply_symm_apply]
    exact z.property

namespace PresModel.PresWordEmbedding
variable {w : J → List (α × Bool)} {v : K → List (β × Bool)}
  (h : PresWordEmbedding w v)
  (hw : ∀ j, 0 < (w j).length) (hv : ∀ k, 0 < (v k).length)
  (ρ : J → FreeGroup α) (σ : K → FreeGroup β)
  (hwm : ∀ j, FreeGroup.mk (w j) = ρ j) (hvm : ∀ k, FreeGroup.mk (v k) = σ k)

include hw hv in
/-- Actual topological pi2 vanishing agrees with the algebraic universal-cover
condition used in the presentation-chain arguments. -/
theorem killsPi2_iff_univCover :
    Whitehead.KillsPi2 h.realizationMap ↔
      ∀ c : PresGroup ρ × J →₀ ℤ, Comb.bdry2 (univCover ρ) c = 0 →
        Finsupp.mapDomain (Prod.map (h.groupHom ρ σ hwm hvm) h.cell) c = 0 :=
  (h.killsPi2_iff_fox hw hv ρ σ hwm hvm).trans
    (fox_kernel_vanish_iff_univCover ρ (h.groupHom ρ σ hwm hvm) h.cell)

variable [DecidableEq β]

include hw hv in
/-- The previously combinatorial pi2 hypothesis now has a proved comparison
with the actual topological pi2 of these presentation realizations. -/
theorem killsPi2_iff_combPi2 :
    Whitehead.KillsPi2 h.realizationMap ↔
      Comb.ZeroPi2 (presInclHom h.gen h.gen.injective ρ σ h.cell
        (h.relator_compat ρ σ hwm hvm)) :=
  (h.killsPi2_iff_univCover hw hv ρ σ hwm hvm).trans
    (zeroPi2_presInclHom_iff ρ h.gen h.gen.injective h.cell
      (h.relator_compat ρ σ hwm hvm)).symm

include hw hv in
/-- A combinatorial pi2 calculation proves actual pi2 vanishing for the
cell-preserving inclusion of the retained valid-position models. -/
theorem valid_killsPi2_of_combPi2
    (hz : Comb.ZeroPi2 (presInclHom h.gen h.gen.injective ρ σ h.cell
      (h.relator_compat ρ σ hwm hvm))) :
    Whitehead.KillsPi2 h.validRealizationMap :=
  h.valid_killsPi2_of_full ((h.killsPi2_iff_combPi2 hw hv ρ σ hwm hvm).mpr hz)

end PresModel.PresWordEmbedding
end FiniteChains
