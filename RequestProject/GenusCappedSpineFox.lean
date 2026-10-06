import RequestProject.GenusCappedSpineHurewicz
import RequestProject.PresCockcroftDictionary

/-! The actual capped spine and the Fox complex of its genuine presentation agree. -/
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains.Comb
open scoped Classical

 theorem coverCycles_cockcroft_iff {α J : Type} [Fintype α] [DecidableEq α] [Fintype J]
    (ρ : J → FreeGroup α) :
    (∀ c : (univCover ρ).F →₀ ℤ, bdry2 (univCover ρ) c = 0 →
      Finsupp.mapDomain Prod.snd c = 0) ↔ _root_.FiniteChains.IsCockcroft ρ := by
  constructor
  · intro h v hv j
    let c := (coords (relSub ρ) J).symm v
    have hcoords : coords (relSub ρ) J c = v := LinearEquiv.apply_symm_apply _ v
    have hcycle : bdry2 (univCover ρ) c = 0 := by
      apply (univCover_bdry2_eq_zero_iff ρ c).mpr
      intro i
      rw [hcoords]
      exact hv i
    have hz := h c hcycle
    have ha := augQ_coords ρ c j
    rw [hcoords, hz] at ha
    exact ha
  · intro h c hc
    have hv := (univCover_bdry2_eq_zero_iff ρ c).mp hc
    apply Finsupp.ext
    intro j
    rw [← augQ_coords ρ c j]
    exact h _ hv j
end FiniteChains.Comb

namespace FiniteChains.Davis.Genus
open RACG Mirror Comb
open scoped Classical
variable (q : ℕ) [NeZero q]

noncomputable instance : Fintype (SpinePresentationGen q) := Fintype.ofFinite _
noncomputable instance : Fintype (SpinePresentationRel q) := Fintype.ofFinite _
noncomputable instance : Fintype (SpinePresentationRel q ⊕ (Fin q × Bool)) := Fintype.ofFinite _

theorem cappedSpine_cockcroft_iff_fox :
    Comb.IsCockcroft (cappedSpineCx q) ↔
      _root_.FiniteChains.IsCockcroft (cappedSpinePresentation q) := by
  letI : Fintype (SpanningTree.NonTree (cappedSpineTree q)) := Fintype.ofFinite _
  letI : Fintype (cappedSpineCx q).F := Fintype.ofFinite _
  have h := (cappedSpine_cockcroft_iff q).trans
    (coverCycles_cockcroft_iff (SpanningTree.treeRel (cappedSpineTree q)))
  simpa only [cappedSpineTree_rel] using h

end FiniteChains.Davis.Genus
