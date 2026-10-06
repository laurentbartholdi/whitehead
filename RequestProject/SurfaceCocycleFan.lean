import RequestProject.SurfaceCocycleCollar
import RequestProject.SurfaceFilling

/-! A flat section on the boundary extends through the actual polygon fan. -/
namespace FiniteChains.Davis.SurfaceSection
open RACG Mirror Comb Cell
universe u v w
variable {κ ι : Type u} {M : ℕ} [NeZero M]
  {vc : Fin M → κ} {ec : Fin M → ι} (hc : Compat vc ec)
  {G : Type v} [Group G] {Ω : Type w} [MulAction G Ω]
  (c : OrdCocycle (SCell vc ec hc) G) (rv : κ → Ω) (re : ι → Ω)

def radialValue (p : Fin M) : Ω :=
  c.val (cC hc) (cR hc p) •
    ((c.val (cW hc p) (cR hc p))⁻¹ • collarValue hc c rv p)

theorem bridge_to_top {a b r t : SCell vc ec hc}
    (har : a ≤ r) (hbr : b ≤ r) (hrt : r ≤ t) :
    c.val a r * (c.val b r)⁻¹ = c.val a t * (c.val b t)⁻¹ := by
  rw [← c.comp har hrt, ← c.comp hbr hrt]
  group

variable (hb : ∀ p : Fin M,
  c.val (cV hc p) (cE hc p) • re (ec p) = rv (vc p) ∧
  c.val (cV hc (p + 1)) (cE hc p) • re (ec p) = rv (vc (p + 1)))

include hb in
theorem radialValue_step (p : Fin M) : radialValue hc c rv p = radialValue hc c rv (p + 1) := by
  let f := surfaceSection hc c rv re (rv (vc p)) (cF hc p)
  have h₀ : c.val (cW hc p) (cF hc p) • f = collarValue hc c rv p :=
    w_f hc c rv re (rv (vc p)) p
  have h₁ : c.val (cW hc (p + 1)) (cF hc p) • f = collarValue hc c rv (p + 1) :=
    w1_f hc c rv re (rv (vc p)) hb p
  have left : radialValue hc c rv p =
      (c.val (cC hc) (cI hc p) * (c.val (cF hc p) (cI hc p))⁻¹) • f := by
    rw [radialValue, ← mul_smul,
      bridge_to_top hc c (cC_le_cR hc p) (cW_le_cR hc p) (cR_le_cI hc p),
      ← h₀, ← c.comp (cW_le_cF hc p) (cF_le_cI hc p), mul_inv_rev]
    simp only [mul_smul, inv_smul_smul]
  have right : radialValue hc c rv (p + 1) =
      (c.val (cC hc) (cI hc p) * (c.val (cF hc p) (cI hc p))⁻¹) • f := by
    rw [radialValue, ← mul_smul,
      bridge_to_top hc c (cC_le_cR hc (p + 1)) (cW_le_cR hc (p + 1)) (cR1_le_cI hc p),
      ← h₁, ← c.comp (cW1_le_cF hc p) (cF_le_cI hc p), mul_inv_rev]
    simp only [mul_smul, inv_smul_smul]
  exact left.trans right.symm

def centreValue : Ω := radialValue hc c rv (cyc M 0)

include hb in
theorem radialValue_eq_centre (p : Fin M) : radialValue hc c rv p = centreValue hc c rv := by
  have hn : ∀ n : ℕ, radialValue hc c rv (cyc M n) = radialValue hc c rv (cyc M 0) := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih =>
      rw [cyc_succ, ← radialValue_step hc c rv re hb, ih]
  have hp : cyc M p.val = p := Fin.ext (Nat.mod_eq_of_lt p.isLt)
  rw [centreValue, ← hp]
  exact hn p.val

local notation "s" => surfaceSection hc c rv re (centreValue hc c rv)

theorem c_r (p : Fin M) : c.val (cC hc) (cR hc p) • s (cR hc p) = s (cC hc) := by
  change c.val _ _ • ((c.val _ _)⁻¹ • centreValue hc c rv) = centreValue hc c rv
  exact smul_inv_smul _ _

include hb in
theorem w_r (p : Fin M) : c.val (cW hc p) (cR hc p) • s (cR hc p) = s (cW hc p) := by
  change c.val _ _ • ((c.val _ _)⁻¹ • centreValue hc c rv) = collarValue hc c rv p
  rw [← radialValue_eq_centre hc c rv re hb p, radialValue, inv_smul_smul, smul_inv_smul]

theorem c_i (p : Fin M) : c.val (cC hc) (cI hc p) • s (cI hc p) = s (cC hc) := by
  change c.val _ _ • ((c.val _ _)⁻¹ • centreValue hc c rv) = centreValue hc c rv
  exact smul_inv_smul _ _

theorem r_i (p : Fin M) : c.val (cR hc p) (cI hc p) • s (cI hc p) = s (cR hc p) :=
  c.flat_edge_of_bottom s (cC_le_cR hc p) (cR_le_cI hc p)
    (c_r hc c rv re p) (c_i hc c rv re p)

theorem r1_i (p : Fin M) :
    c.val (cR hc (p + 1)) (cI hc p) • s (cI hc p) = s (cR hc (p + 1)) :=
  c.flat_edge_of_bottom s (cC_le_cR hc (p + 1)) (cR1_le_cI hc p)
    (c_r hc c rv re (p + 1)) (c_i hc c rv re p)

include hb in
theorem w_i (p : Fin M) : c.val (cW hc p) (cI hc p) • s (cI hc p) = s (cW hc p) :=
  c.flat_edge_trans s (cW_le_cR hc p) (cR_le_cI hc p)
    (w_r hc c rv re hb p) (r_i hc c rv re p)

include hb in
theorem w1_i (p : Fin M) :
    c.val (cW hc (p + 1)) (cI hc p) • s (cI hc p) = s (cW hc (p + 1)) :=
  c.flat_edge_trans s (cW_le_cR hc (p + 1)) (cR1_le_cI hc p)
    (w_r hc c rv re hb (p + 1)) (r1_i hc c rv re p)

include hb in
theorem f_i (p : Fin M) : c.val (cF hc p) (cI hc p) • s (cI hc p) = s (cF hc p) :=
  c.flat_edge_of_bottom s (cW_le_cF hc p) (cF_le_cI hc p)
    (w_f hc c rv re (centreValue hc c rv) p) (w_i hc c rv re hb p)

end FiniteChains.Davis.SurfaceSection
