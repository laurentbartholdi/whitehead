import RequestProject.SurfaceCells
import RequestProject.AttCycle

/-!
# The marking of the polygon: the cellular map into the model of the presentation complex

The polygon of `RequestProject/SurfacePoset.lean` is *marked*: its boundary is subdivided into
the letters of a chosen relator word `w j₀`, and the marking is a **monotone map of the face
poset of the surface into the poset model of the presentation complex**.  Monotonicity is what
makes it a cellular map, and it is the only thing the chamber construction asks of an attaching
map.

The marking is forced by the geometry:

* a boundary vertex and a boundary edge go to the cell of the subdivided rose carrying the same
  letter of the word (this is what makes the boundary of the polygon read the word);
* the collar is the attaching circle of the two-cell of the relator `j₀`: the collar vertex and
  the collar edge at the position `p` go to the corresponding point of that circle;
* the triangles of the collar are degenerate: they go to the one-cell of the rose carrying the
  letter, and so do the two diagonals;
* the centre, the radii and the triangles of the fan go to the two-cell of the relator `j₀`.

`FiniteChains.Davis.surfAtt` is the resulting attaching map `NeSpx (cmpRel …) →o PresPos w`.
-/

namespace FiniteChains
namespace Davis

open RACG Mirror Comb PresModel Cell

universe u

section Label

variable {α J : Type u} {w : J → List (α × Bool)} {j₀ : J}
  {κ ι : Type u} {M : ℕ} [NeZero M] [DecidableEq κ] [DecidableEq ι]
  {vc : Fin M → κ} {ec : Fin M → ι}
  {vlab : κ → Rose α} {elb : ι → Rose α}

/-! ### The position arithmetic -/

theorem fin_succ_val (p : Fin M) : (p + 1).val = (p.val + 1) % M := by
  show (p.val + (1 : Fin M).val) % M = (p.val + 1) % M
  have h1 : (1 : Fin M).val = 1 % M := rfl
  rw [h1, Nat.add_mod_mod]

/-! ### The circle of the relator -/

variable (w j₀) in
/-- The point of the attaching circle of the relator `j₀` carried by the collar vertex at the
position `p`. -/
def cVtx (p : Fin M) : TCirc w :=
  TCirc.pt w j₀ (p.val / 2) (if p.val % 2 = 0 then CPos.cor else CPos.cmid)

variable (w j₀) in
/-- The point of the attaching circle of the relator `j₀` carried by the collar edge at the
position `p`. -/
def cEdg (p : Fin M) : TCirc w :=
  TCirc.pt w j₀ (p.val / 2) (if p.val % 2 = 0 then CPos.cedgL else CPos.cedgR)

variable (hM : M = 2 * (w j₀).length)

include hM

omit [NeZero M] in
theorem half_lt (p : Fin M) : p.val / 2 < (w j₀).length := by
  have := p.isLt
  omega

omit [NeZero M] in
theorem aFun_cVtx (p : Fin M) : aFun w (cVtx w j₀ p) = vertLab (w j₀) p.val := by
  obtain ⟨q, hq⟩ := getElem?_half (l := w j₀) (p := p.val) (by have := p.isLt; omega)
  by_cases h : p.val % 2 = 0
  · rw [cVtx, if_pos h, aFun_pt_cor, vertLab_of_even h]
  · rw [cVtx, if_neg h, aFun_pt_cmid_of_get w hq, vertLab_of_odd (by omega) hq]

omit [NeZero M] in
theorem aFun_cEdg (p : Fin M) : aFun w (cEdg w j₀ p) = edgeLab (w j₀) p.val := by
  obtain ⟨q, hq⟩ := getElem?_half (l := w j₀) (p := p.val) (by have := p.isLt; omega)
  by_cases h : p.val % 2 = 0
  · rw [cEdg, if_pos h, aFun_pt_cedgL_of_get w hq, edgeLab_eq hq, if_pos h]
  · rw [cEdg, if_neg h, aFun_pt_cedgR_of_get w hq, edgeLab_eq hq, if_neg h]

omit [NeZero M] in
theorem cVtx_le_cEdg (p : Fin M) : cVtx w j₀ p ≤ cEdg w j₀ p := by
  by_cases h : p.val % 2 = 0
  · rw [cVtx, cEdg, if_pos h, if_pos h]
    exact TCirc.cor_le_cedgL w (half_lt hM p)
  · rw [cVtx, cEdg, if_neg h, if_neg h]
    exact TCirc.cmid_le_cedgR w (half_lt hM p)

theorem cVtx_succ_le_cEdg (p : Fin M) : cVtx w j₀ (p + 1) ≤ cEdg w j₀ p := by
  have hlt := p.isLt
  have hsucc := fin_succ_val p
  by_cases h : p.val % 2 = 0
  · -- the next position is the midpoint of the same letter
    have hlt1 : p.val + 1 < M := by omega
    have hval : (p + 1).val = p.val + 1 := by rw [hsucc, Nat.mod_eq_of_lt hlt1]
    have hodd : (p + 1).val % 2 ≠ 0 := by rw [hval]; omega
    have hhalf : (p + 1).val / 2 = p.val / 2 := by rw [hval]; omega
    rw [cVtx, cEdg, if_neg hodd, if_pos h, hhalf]
    exact TCirc.cmid_le_cedgL w (half_lt hM p)
  · -- the next position is the corner in front of the next letter
    rw [cVtx, cEdg, if_neg h]
    rcases Nat.lt_or_ge (p.val + 1) M with hlt1 | hge
    · have hval : (p + 1).val = p.val + 1 := by rw [hsucc, Nat.mod_eq_of_lt hlt1]
      have heven : (p + 1).val % 2 = 0 := by rw [hval]; omega
      have hhalf : (p + 1).val / 2 = p.val / 2 + 1 := by rw [hval]; omega
      have hcs : TCirc.csucc w j₀ (p.val / 2) = p.val / 2 + 1 := by
        rw [TCirc.csucc, Nat.mod_eq_of_lt (by omega)]
      rw [if_pos heven, hhalf, ← hcs]
      exact TCirc.cor_csucc_le_cedgR w (half_lt hM p)
    · have hval : (p + 1).val = 0 := by
        rw [hsucc, show p.val + 1 = M by omega, Nat.mod_self]
      have heven : (p + 1).val % 2 = 0 := by rw [hval]
      have hhalf : (p + 1).val / 2 = 0 := by rw [hval]
      have hcs : TCirc.csucc w j₀ (p.val / 2) = 0 := by
        rw [TCirc.csucc, show p.val / 2 + 1 = (w j₀).length by omega, Nat.mod_self]
      rw [if_pos heven, hhalf, ← hcs]
      exact TCirc.cor_csucc_le_cedgR w (half_lt hM p)

/-! ### The labels of the boundary -/

omit [NeZero M] in
theorem vertLab_le_edgeLab' (p : Fin M) :
    vertLab (w j₀) p.val ≤ edgeLab (w j₀) p.val :=
  vertLab_le_edgeLab (by have := p.isLt; omega)

theorem vertLab_succ_le_edgeLab' (p : Fin M) :
    vertLab (w j₀) (p + 1).val ≤ edgeLab (w j₀) p.val := by
  have hlt := p.isLt
  have hsucc := fin_succ_val p
  rcases Nat.lt_or_ge (p.val + 1) M with hlt1 | hge
  · have hval : (p + 1).val = p.val + 1 := by rw [hsucc, Nat.mod_eq_of_lt hlt1]
    rw [hval]
    exact vertLab_succ_le_edgeLab (by omega)
  · have hval : (p + 1).val = 0 := by
      rw [hsucc, show p.val + 1 = M by omega, Nat.mod_self]
    rw [hval, vertLab_of_even rfl]
    exact base_le_edgeLab (by omega)

/-! ### The marking -/

variable (w j₀ vc ec vlab elb) in
/-- **The marking of the cells of the surface** by the cells of the model of the presentation
complex. -/
def gLab : Cell κ ι M → PresPos w
  | vtx v => iRose w (vlab v)
  | bed e => iRose w (elb e)
  | cvx p => iCirc w (cVtx w j₀ p)
  | ced p => iCirc w (cEdg w j₀ p)
  | dia p => iRose w (vlab (vc p))
  | gdi p => iRose w (elb (ec p))
  | tr1 p => iRose w (elb (ec p))
  | tr2 p => iRose w (elb (ec p))
  | ctr => apexOf w j₀
  | rad _ => apexOf w j₀
  | inn _ => apexOf w j₀

variable (hvlab : ∀ p : Fin M, vlab (vc p) = vertLab (w j₀) p.val)
  (helb : ∀ p : Fin M, elb (ec p) = edgeLab (w j₀) p.val)

include hvlab helb

/-! ### The marking is monotone -/

omit [NeZero M] [DecidableEq κ] [DecidableEq ι] hvlab helb in
theorem iCirc_cVtx_le_apex (p : Fin M) : iCirc w (cVtx w j₀ p) ≤ apexOf w j₀ :=
  iCirc_le_apexOf w _ (half_lt hM p)

omit [NeZero M] [DecidableEq κ] [DecidableEq ι] hvlab helb in
theorem iCirc_cEdg_le_apex (p : Fin M) : iCirc w (cEdg w j₀ p) ≤ apexOf w j₀ :=
  iCirc_le_apexOf w _ (half_lt hM p)

omit [NeZero M] [DecidableEq κ] [DecidableEq ι] helb in
theorem iCirc_cVtx_le_dia (p : Fin M) :
    iCirc w (cVtx w j₀ p) ≤ iRose w (vlab (vc p)) := by
  rw [hvlab p, ← aFun_cVtx hM p]
  exact iCirc_le_iRose_aFun w _

omit [NeZero M] [DecidableEq κ] [DecidableEq ι] hvlab in
theorem iCirc_cEdg_le_bed (p : Fin M) :
    iCirc w (cEdg w j₀ p) ≤ iRose w (elb (ec p)) := by
  rw [helb p, ← aFun_cEdg hM p]
  exact iCirc_le_iRose_aFun w _

omit [NeZero M] [DecidableEq κ] [DecidableEq ι] hvlab in
theorem iCirc_cVtx_le_bed (p : Fin M) :
    iCirc w (cVtx w j₀ p) ≤ iRose w (elb (ec p)) := by
  refine le_trans (iCirc_le_iRose_aFun w _) ((iRose_monotone w) ?_)
  rw [aFun_cVtx hM p, helb p]
  exact vertLab_le_edgeLab' hM p

omit [DecidableEq κ] [DecidableEq ι] hvlab in
theorem iCirc_cVtx_succ_le_bed (p : Fin M) :
    iCirc w (cVtx w j₀ (p + 1)) ≤ iRose w (elb (ec p)) := by
  refine le_trans (iCirc_le_iRose_aFun w _) ((iRose_monotone w) ?_)
  rw [aFun_cVtx hM (p + 1), helb p]
  exact vertLab_succ_le_edgeLab' hM p

omit [NeZero M] [DecidableEq κ] [DecidableEq ι] in
theorem vlab_le_elb (p : Fin M) : iRose w (vlab (vc p)) ≤ iRose w (elb (ec p)) := by
  refine (iRose_monotone w) ?_
  rw [hvlab p, helb p]
  exact vertLab_le_edgeLab' hM p

omit [DecidableEq κ] [DecidableEq ι] in
theorem vlab_succ_le_elb (p : Fin M) :
    iRose w (vlab (vc (p + 1))) ≤ iRose w (elb (ec p)) := by
  refine (iRose_monotone w) ?_
  rw [hvlab (p + 1), helb p]
  exact vertLab_succ_le_edgeLab' hM p

omit [DecidableEq κ] [DecidableEq ι] in
/-- **The marking is monotone on strict faces.** -/
theorem gLab_le_of_plt {x y : Cell κ ι M} (h : plt vc ec x y) :
    gLab w j₀ vc ec vlab elb x ≤ gLab w j₀ vc ec vlab elb y := by
  cases x with
  | vtx v =>
      cases y with
      | bed e =>
          obtain ⟨i, hi, hv⟩ := h
          show iRose w (vlab v) ≤ iRose w (elb e)
          rw [← hi]
          rcases hv with rfl | rfl
          · exact vlab_le_elb hM hvlab helb i
          · exact vlab_succ_le_elb hM hvlab helb i
      | dia p =>
          have hv : vc p = v := h
          show iRose w (vlab v) ≤ iRose w (vlab (vc p))
          rw [hv]
      | gdi p =>
          have hv : vc p = v := h
          show iRose w (vlab v) ≤ iRose w (elb (ec p))
          rw [← hv]
          exact vlab_le_elb hM hvlab helb p
      | tr1 p =>
          show iRose w (vlab v) ≤ iRose w (elb (ec p))
          rcases h with hv | hv
          · rw [← hv]; exact vlab_le_elb hM hvlab helb p
          · rw [← hv]; exact vlab_succ_le_elb hM hvlab helb p
      | tr2 p =>
          have hv : vc p = v := h
          show iRose w (vlab v) ≤ iRose w (elb (ec p))
          rw [← hv]
          exact vlab_le_elb hM hvlab helb p
      | _ => simp [plt] at h
  | cvx q =>
      cases y with
      | ced r =>
          show iCirc w (cVtx w j₀ q) ≤ iCirc w (cEdg w j₀ r)
          rcases h with rfl | rfl
          · exact (iCirc_monotone w) (cVtx_le_cEdg hM q)
          · exact (iCirc_monotone w) (cVtx_succ_le_cEdg hM r)
      | dia r =>
          have hq : q = r := h
          show iCirc w (cVtx w j₀ q) ≤ iRose w (vlab (vc r))
          rw [hq]
          exact iCirc_cVtx_le_dia hM hvlab r
      | gdi r =>
          have hq : q = r + 1 := h
          show iCirc w (cVtx w j₀ q) ≤ iRose w (elb (ec r))
          rw [hq]
          exact iCirc_cVtx_succ_le_bed hM helb r
      | rad r =>
          show iCirc w (cVtx w j₀ q) ≤ apexOf w j₀
          exact iCirc_cVtx_le_apex hM q
      | tr1 p =>
          have hq : q = p + 1 := h
          show iCirc w (cVtx w j₀ q) ≤ iRose w (elb (ec p))
          rw [hq]
          exact iCirc_cVtx_succ_le_bed hM helb p
      | tr2 p =>
          show iCirc w (cVtx w j₀ q) ≤ iRose w (elb (ec p))
          rcases h with rfl | rfl
          · exact iCirc_cVtx_le_bed hM helb q
          · exact iCirc_cVtx_succ_le_bed hM helb p
      | inn p =>
          show iCirc w (cVtx w j₀ q) ≤ apexOf w j₀
          exact iCirc_cVtx_le_apex hM q
      | _ => simp [plt] at h
  | ctr =>
      cases y with
      | rad p => exact le_refl _
      | inn p => exact le_refl _
      | _ => simp [plt] at h
  | bed e =>
      cases y with
      | tr1 p =>
          have he : e = ec p := h
          show iRose w (elb e) ≤ iRose w (elb (ec p))
          rw [he]
      | _ => simp [plt] at h
  | ced r =>
      cases y with
      | tr2 p =>
          have hr : r = p := h
          show iCirc w (cEdg w j₀ r) ≤ iRose w (elb (ec p))
          rw [hr]
          exact iCirc_cEdg_le_bed hM helb p
      | inn p =>
          show iCirc w (cEdg w j₀ r) ≤ apexOf w j₀
          exact iCirc_cEdg_le_apex hM r
      | _ => simp [plt] at h
  | dia r =>
      cases y with
      | tr1 p =>
          have hr : r = p + 1 := h
          show iRose w (vlab (vc r)) ≤ iRose w (elb (ec p))
          rw [hr]
          exact vlab_succ_le_elb hM hvlab helb p
      | tr2 p =>
          have hr : r = p := h
          show iRose w (vlab (vc r)) ≤ iRose w (elb (ec p))
          rw [hr]
          exact vlab_le_elb hM hvlab helb p
      | _ => simp [plt] at h
  | gdi r =>
      cases y with
      | tr1 p =>
          have hr : r = p := h
          show iRose w (elb (ec r)) ≤ iRose w (elb (ec p))
          rw [hr]
      | tr2 p =>
          have hr : r = p := h
          show iRose w (elb (ec r)) ≤ iRose w (elb (ec p))
          rw [hr]
      | _ => simp [plt] at h
  | rad r =>
      cases y with
      | inn p => exact le_refl _
      | _ => simp [plt] at h
  | tr1 p => simp [plt] at h
  | tr2 p => simp [plt] at h
  | inn p => simp [plt] at h

variable (hc : Compat vc ec)

/-- **The marking as a monotone map of the face poset of the surface.** -/
def gHom : SCell vc ec hc →o PresPos w where
  toFun x := gLab w j₀ vc ec vlab elb x
  monotone' := by
    rintro x y (rfl | h)
    · exact le_refl _
    · exact gLab_le_of_plt hM hvlab helb h

omit [DecidableEq κ] [DecidableEq ι] in
@[simp] theorem gHom_apply (x : Cell κ ι M) :
    gHom hM hvlab helb hc (toS vc ec hc x) = gLab w j₀ vc ec vlab elb x := rfl

/-- **The attaching map of the surface block**: the marking, read on the chains of the
barycentric subdivision. -/
noncomputable def surfAtt : NeSpx (cmpRel (SCell vc ec hc)) →o PresPos w :=
  nerveAtt (gHom hM hvlab helb hc)

end Label

end Davis
end FiniteChains
