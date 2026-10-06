import RequestProject.SurfaceCocycleFan
import RequestProject.BarycentricCocycleDescent

/-! Boundary flat sections extend across the actual closed polygon surface. -/
namespace FiniteChains.Davis.SurfaceSection
open RACG Mirror Comb Cell
universe u v w
variable {κ ι : Type u} {M : ℕ} [NeZero M]
  {vc : Fin M → κ} {ec : Fin M → ι} (hc : Compat vc ec)
  {G : Type v} [Group G] {Ω : Type w} [MulAction G Ω]
  (c : OrdCocycle (SCell vc ec hc) G) (rv : κ → Ω) (re : ι → Ω)
  (hb : ∀ p : Fin M,
    c.val (cV hc p) (cE hc p) • re (ec p) = rv (vc p) ∧
    c.val (cV hc (p + 1)) (cE hc p) • re (ec p) = rv (vc (p + 1)))

include hb in
theorem section_flat : c.IsFlatSection (surfaceSection hc c rv re (centreValue hc c rv)) := by
  intro a b hab
  rcases hab with heq | h
  · subst b
    rw [c.val_refl, one_smul]
  change plt vc ec a b at h
  cases a <;> cases b <;> simp only [plt] at h
  case vtx.bed v e =>
    obtain ⟨p, hp, hv⟩ := h
    subst e
    rcases hv with hv | hv
    · subst v; exact (hb p).1
    · subst v; exact (hb p).2
  case vtx.dia v p =>
    subst v
    exact v_d hc c rv re (centreValue hc c rv) p
  case vtx.gdi v p =>
    subst v
    exact v_g hc c rv re (centreValue hc c rv) p
  case cvx.ced x p =>
    rcases h with h | h
    · subst x; exact w_f hc c rv re (centreValue hc c rv) p
    · subst x; exact w1_f hc c rv re (centreValue hc c rv) hb p
  case cvx.dia x p =>
    subst x
    exact w_d hc c rv re (centreValue hc c rv) p
  case cvx.gdi x p =>
    subst x
    exact w1_g hc c rv re (centreValue hc c rv) hb p
  case cvx.rad x p =>
    subst x
    exact w_r hc c rv re hb p
  case ctr.rad p => exact c_r hc c rv re p
  case bed.tr1 e p =>
    subst e
    exact e_t1 hc c rv re (centreValue hc c rv) p
  case ced.tr2 x p =>
    subst x
    exact f_t2 hc c rv re (centreValue hc c rv) p
  case ced.inn x p =>
    subst x
    exact f_i hc c rv re hb p
  case dia.tr1 x p =>
    subst x
    exact d1_t1 hc c rv re (centreValue hc c rv) hb p
  case dia.tr2 x p =>
    subst x
    exact d_t2 hc c rv re (centreValue hc c rv) p
  case gdi.tr1 x p =>
    subst x
    exact g_t1 hc c rv re (centreValue hc c rv) hb p
  case gdi.tr2 x p =>
    subst x
    exact g_t2 hc c rv re (centreValue hc c rv) p
  case rad.inn x p =>
    rcases h with h | h
    · subst x; exact r_i hc c rv re p
    · subst x; exact r1_i hc c rv re p
  case vtx.tr1 v p =>
    rcases h with h | h
    · subst v; exact v_t1 hc c rv re (centreValue hc c rv) hb p
    · subst v; exact v1_t1 hc c rv re (centreValue hc c rv) hb p
  case vtx.tr2 v p =>
    subst v
    exact v_t2 hc c rv re (centreValue hc c rv) p
  case cvx.tr1 x p =>
    subst x
    exact w1_t1 hc c rv re (centreValue hc c rv) hb p
  case cvx.tr2 x p =>
    rcases h with h | h
    · subst x; exact w_t2 hc c rv re (centreValue hc c rv) p
    · subst x; exact w1_t2 hc c rv re (centreValue hc c rv) hb p
  case cvx.inn x p =>
    rcases h with h | h
    · subst x; exact w_i hc c rv re hb p
    · subst x; exact w1_i hc c rv re hb p
  case ctr.inn p => exact c_i hc c rv re p

include hb in
/-- No new monodromy is introduced by the collar and the interior fan. All
flat boundary data extend for an arbitrary group action. -/
theorem exists_flat_section : ∃ s : SCell vc ec hc → Ω,
    c.IsFlatSection s ∧
    (∀ v, s (toS vc ec hc (.vtx v)) = rv v) ∧
    (∀ e, s (toS vc ec hc (.bed e)) = re e) :=
  ⟨surfaceSection hc c rv re (centreValue hc c rv), section_flat hc c rv re hb,
    fun _ => rfl, fun _ => rfl⟩

end FiniteChains.Davis.SurfaceSection

namespace FiniteChains.Davis
open RACG Mirror Comb Cell
universe u v w
variable {κ ι : Type u} {M : ℕ} [NeZero M] [DecidableEq κ] [DecidableEq ι]
  {vc : Fin M → κ} {ec : Fin M → ι} (hc : Compat vc ec)
  {G : Type v} [Group G] {Ω : Type w} [MulAction G Ω]
  (c : OrdCocycle (NeSpx (cmpRel (SCell vc ec hc))) G)
  (rv : κ → Ω) (re : ι → Ω)

/-- The extension is on the actual subdivided surface used by the chamber
construction, and preserves each original boundary cell value. -/
theorem surface_exists_flat_section
    (hb : ∀ p : Fin M,
      c.readPath (edgeHop (cV_le_cE hc p)) • re (ec p) = rv (vc p) ∧
      c.readPath (edgeHop (cV1_le_cE hc p)) • re (ec p) = rv (vc (p + 1))) :
    ∃ s : NeSpx (cmpRel (SCell vc ec hc)) → Ω, c.IsFlatSection s ∧
      (∀ v, s (spx1 (toS vc ec hc (.vtx v))) = rv v) ∧
      (∀ e, s (spx1 (toS vc ec hc (.bed e))) = re e) := by
  have hd : ∀ p : Fin M,
      (barycentricCocycle c).val (cV hc p) (cE hc p) • re (ec p) = rv (vc p) ∧
      (barycentricCocycle c).val (cV hc (p + 1)) (cE hc p) • re (ec p) = rv (vc (p + 1)) := by
    intro p
    simpa only [barycentricCocycle_val c (cV_le_cE hc p),
      barycentricCocycle_val c (cV1_le_cE hc p)] using hb p
  obtain ⟨s, hs, hv, he⟩ := SurfaceSection.exists_flat_section hc (barycentricCocycle c) rv re hd
  refine ⟨barycentricSection c s, barycentricSection_flat c s hs, ?_, ?_⟩
  · intro v
    rw [barycentricSection_spx1, hv]
  · intro e
    rw [barycentricSection_spx1, he]

end FiniteChains.Davis
