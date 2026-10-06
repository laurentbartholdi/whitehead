import RequestProject.ChamberZPi1Base
import RequestProject.ChamberZAction
import RequestProject.RACGSpecialParity

/-!
# The quotient `Q = Z/Γ` of the complex of modified chambers

`RequestProject/ChamberZPoset.lean` builds the poset `Z` of modified chambers: the poset of
spherical cosets with the apex of every marked chamber replaced by a copy of the base poset `X`.
Here the marking is the one of the article,

    Γ = ker (phi : W → (ℤ/2)^S),

and this file builds the **quotient** of that poset and the projection onto it.

* `FiniteChains.Davis.QCube A` — a closed cube of `C(L)`: a simplex `T` of `L` together with the
  signs of the coordinates outside `T` (normalised to `0` on `T`), ordered by the face order
  `(T,η) ≤ (U,θ) ↔ T ⊆ U ∧ η|_{S∖U} = θ|_{S∖U}`;
* `FiniteChains.Davis.Qpos A X att` — the cubes other than the all-positive vertex `(∅,0)`,
  together with **one** adjoined copy of the base poset `X`, glued by the same attaching map
  `att` as in `Z`, in the same mapping-cylinder orientation;
* `FiniteChains.Davis.zProj` — the projection `Z → Q`, `w W_T ↦ (T, phi w |_{S∖T})` on old cells
  and the identity on the copies of the base;
* `zProj_monotone`, `zProj_surjective`, `zProj_zAct` (`Γ`-invariance) and
  `exists_zAct_of_zProj_eq` (**the fibres are exactly the `Γ`-orbits**).

The covering property of `zProj` is proved in `RequestProject/ChamberQuotientCover.lean`.
-/

namespace FiniteChains
namespace Davis

open RACG Mirror Comb

universe u

variable {V : Type u} [DecidableEq V] {A : CommRel V} {X : Type u} [Preorder X]

/-! ### The marking by `Γ` -/

/-- The marked chambers of the article: those indexed by `Γ = ker(W → (ℤ/2)^S)`. -/
def IsGamma (A : CommRel V) (w : CayGroup A) : Prop := phi A w = 0

theorem isGamma_one : IsGamma A (1 : CayGroup A) := by
  show phi A 1 = 0
  rw [← cword_nil A, phi_cword, parList_nil]
  rfl

theorem isGamma_mul_iff {k : CayGroup A} (hk : IsGamma A k) (w : CayGroup A) :
    IsGamma A (k * w) ↔ IsGamma A w := by
  have h : phi A (k * w) = phi A w := by
    rw [phi_mul, show phi A k = 0 from hk, zero_add]
  show phi A (k * w) = 0 ↔ phi A w = 0
  rw [h]

/-! ### The cubes of `C(L)` -/

/-- **A closed cube of `C(L)`**: a simplex `T` of `L` (the directions in which the cube is not
degenerate) together with the signs of the remaining coordinates; the signs on `T` are
normalised to zero. -/
structure QCube (A : CommRel V) : Type u where
  /-- The set of directions of the cube: a simplex of `L`. -/
  spx : Finset V
  /-- The fixed signs of the cube. -/
  sgn : V → ZMod 2
  /-- The directions form a simplex of `L`. -/
  isSimplex : IsSimplex A spx
  /-- The signs in the directions of the cube are normalised to zero. -/
  sgn_eq_zero : ∀ v ∈ spx, sgn v = 0

/-- Two cubes with the same directions and the same signs outside them are equal. -/
theorem QCube.ext' {c d : QCube A} (hs : c.spx = d.spx)
    (hv : ∀ v, v ∉ d.spx → c.sgn v = d.sgn v) : c = d := by
  have hsgn : c.sgn = d.sgn := by
    funext v
    by_cases h : v ∈ d.spx
    · rw [c.sgn_eq_zero v (by rw [hs]; exact h), d.sgn_eq_zero v h]
    · exact hv v h
  obtain ⟨s, e, h1, h2⟩ := c
  obtain ⟨s', e', h1', h2'⟩ := d
  simp only at hs hsgn
  subst hs
  subst hsgn
  rfl

/-- **The face order of the cubes**: a face has fewer directions and agrees with the signs of
the bigger cube outside it. -/
instance : PartialOrder (QCube A) where
  le c d := c.spx ⊆ d.spx ∧ ∀ v, v ∉ d.spx → c.sgn v = d.sgn v
  le_refl c := ⟨Finset.Subset.refl _, fun _ _ => rfl⟩
  le_trans c d e hcd hde :=
    ⟨hcd.1.trans hde.1, fun v hv =>
      (hcd.2 v (fun h => hv (hde.1 h))).trans (hde.2 v hv)⟩
  le_antisymm c d hcd hdc :=
    QCube.ext' (Finset.Subset.antisymm hcd.1 hdc.1) hcd.2

theorem QCube.le_def {c d : QCube A} :
    c ≤ d ↔ c.spx ⊆ d.spx ∧ ∀ v, v ∉ d.spx → c.sgn v = d.sgn v := Iff.rfl

/-! ### The quotient poset -/

/-- The cubes of `C(L)` other than the all-positive vertex: the vertex `(∅,0)` is removed and
replaced by the copy of the base poset. -/
def QOld (A : CommRel V) : Type u := {c : QCube A // ¬ (c.spx = ∅ ∧ c.sgn = 0)}

/-- **The quotient poset `Q = Z/Γ`**: the retained cubes of `C(L)` together with one copy of the
base poset `X`, glued along the same attaching map as in `Z`. -/
def Qpos (A : CommRel V) (X : Type u) [Preorder X] (_att : NeSpx A →o X) : Type u :=
  QOld A ⊕ X

variable {att : NeSpx A →o X}

/-- A retained cube of `Q`. -/
def qOld (c : QCube A) (hc : ¬ (c.spx = ∅ ∧ c.sgn = 0)) : Qpos A X att := Sum.inl ⟨c, hc⟩

/-- An element of the copy of the base poset in `Q`. -/
def qNew (x : X) : Qpos A X att := Sum.inr x

/-- The order of `Q`, the same mapping-cylinder orientation as in `Z`. -/
protected def Qle : Qpos A X att → Qpos A X att → Prop
  | Sum.inl c, Sum.inl d => c.1 ≤ d.1
  | Sum.inl _, Sum.inr _ => False
  | Sum.inr x, Sum.inl d =>
      d.1.sgn = 0 ∧ ∃ h : d.1.spx.Nonempty, x ≤ att ⟨d.1.spx, h, d.1.isSimplex⟩
  | Sum.inr x, Sum.inr y => x ≤ y

instance qposPreorder : Preorder (Qpos A X att) where
  le := Davis.Qle
  le_refl q := by
    cases q with
    | inl c => exact le_refl c.1
    | inr x => exact le_refl x
  le_trans q q' q'' hqq' hq'q'' := by
    cases q with
    | inl c =>
        cases q' with
        | inl d =>
            cases q'' with
            | inl e => exact le_trans hqq' hq'q''
            | inr y => exact hq'q''.elim
        | inr y => exact hqq'.elim
    | inr x =>
        cases q' with
        | inl d =>
            cases q'' with
            | inl e =>
                obtain ⟨hne, hx⟩ := hqq'.2
                have hsgn : e.1.sgn = 0 := by
                  funext v
                  show e.1.sgn v = 0
                  by_cases hv : v ∈ e.1.spx
                  · exact e.1.sgn_eq_zero v hv
                  · have hd : d.1.sgn v = 0 := by
                      simpa using congrFun (show d.1.sgn = 0 from hqq'.1) v
                    rw [← hq'q''.2 v hv, hd]
                refine ⟨hsgn, Finset.Nonempty.mono hq'q''.1 hne, ?_⟩
                exact le_trans hx (att.monotone (show (⟨d.1.spx, hne, d.1.isSimplex⟩ : NeSpx A) ≤
                  ⟨e.1.spx, Finset.Nonempty.mono hq'q''.1 hne, e.1.isSimplex⟩ from hq'q''.1))
            | inr y => exact hq'q''.elim
        | inr y =>
            cases q'' with
            | inl e =>
                obtain ⟨hne, hy⟩ := hq'q''.2
                exact ⟨hq'q''.1, hne, le_trans hqq' hy⟩
            | inr z => exact le_trans hqq' hq'q''

theorem qOld_le_qOld_iff {c d : QCube A} {hc : ¬ (c.spx = ∅ ∧ c.sgn = 0)}
    {hd : ¬ (d.spx = ∅ ∧ d.sgn = 0)} :
    qOld (X := X) (att := att) c hc ≤ qOld d hd ↔ c ≤ d := Iff.rfl

theorem qNew_le_qOld_iff {x : X} {d : QCube A} {hd : ¬ (d.spx = ∅ ∧ d.sgn = 0)} :
    qNew (A := A) (att := att) x ≤ qOld d hd ↔
      (d.sgn = 0 ∧ ∃ h : d.spx.Nonempty, x ≤ att ⟨d.spx, h, d.isSimplex⟩) := Iff.rfl

theorem not_qOld_le_qNew {c : QCube A} {hc : ¬ (c.spx = ∅ ∧ c.sgn = 0)} {x : X} :
    ¬ (qOld (X := X) (att := att) c hc ≤ qNew x) := id

theorem qNew_le_qNew_iff {x y : X} :
    qNew (A := A) (att := att) x ≤ qNew y ↔ x ≤ y := Iff.rfl

/-- The inclusion of the copy of the base poset in `Q` is monotone. -/
theorem qNew_monotone : Monotone (qNew (A := A) (X := X) (att := att)) := fun _ _ h => h

/-! ### Parity of the representative of a spherical coset -/

/-- The parity of the representative of a spherical coset is well defined outside its type. -/
theorem phi_rep_eq_of_inChamber {x : CayGroup A} {p : Sph A} (h : InChamber x p) {v : V}
    (hv : v ∉ p.spx) : phi A p.rep v = phi A x v := by
  have hmul : phi A x = phi A p.rep + phi A (p.rep⁻¹ * x) := by
    have := phi_mul A p.rep (p.rep⁻¹ * x)
    rwa [mul_inv_cancel_left] at this
  have hzero : phi A (p.rep⁻¹ * x) v = 0 :=
    phi_eq_zero_of_mem_specialSub A h (by simpa using hv)
  rw [congrFun hmul v, Pi.add_apply, hzero, add_zero]

/-- `p ≤ q` puts the representative of `p` in the coset of `q`. -/
theorem inChamber_rep_of_le {p q : Sph A} (h : p ≤ q) : InChamber p.rep q := by
  have := Subgroup.inv_mem _ h.2
  rwa [mul_inv_rev, inv_inv] at this

/-- **Two cells of one chamber with the same type coincide.** -/
theorem eq_of_inChamber_spx_eq {x : CayGroup A} {r r' : Sph A} (hr : InChamber x r)
    (hr' : InChamber x r') (hs : r.spx = r'.spx) : r = r' := by
  have hT : Commuting A (r.spx : Set V) := commuting_of_isSimplex r.isSimplex
  have huniq := existsUnique_shortest_coset A hT x
  refine Sph.ext' (huniq.unique ?_ ?_) hs
  · refine ⟨?_, fun s hs' => r.no_rdesc s (Finset.mem_coe.1 hs')⟩
    have := Subgroup.inv_mem _ hr
    rwa [mul_inv_rev, inv_inv] at this
  · refine ⟨?_, fun s hs' => r'.no_rdesc s (Finset.mem_coe.1 (by rw [← hs]; exact hs'))⟩
    have := Subgroup.inv_mem _ hr'
    rw [mul_inv_rev, inv_inv] at this
    rw [show (r.spx : Set V) = (r'.spx : Set V) by rw [hs]]
    exact this

/-! ### The projection -/

/-- The signs of the cube under a spherical coset. -/
noncomputable def qProjSgn (p : Sph A) : V → ZMod 2 :=
  fun v => if v ∈ p.spx then 0 else phi A p.rep v

/-- **The cube under a spherical coset**: `w W_T ↦ (T, phi w |_{S∖T})`. -/
noncomputable def qProjCube (p : Sph A) : QCube A where
  spx := p.spx
  sgn := qProjSgn p
  isSimplex := p.isSimplex
  sgn_eq_zero v hv := by simp [qProjSgn, hv]

@[simp] theorem qProjCube_spx (p : Sph A) : (qProjCube p).spx = p.spx := rfl

theorem qProjCube_sgn_of_not_mem {p : Sph A} {v : V} (hv : v ∉ p.spx) :
    (qProjCube p).sgn v = phi A p.rep v := by simp [qProjCube, qProjSgn, hv]

/-- The formula for the cube under a spherical coset is independent of the representative. -/
theorem qProjCube_eq_iff {p : Sph A} {c : QCube A} :
    qProjCube p = c ↔ p.spx = c.spx ∧ ∀ v, v ∉ c.spx → phi A p.rep v = c.sgn v := by
  constructor
  · rintro rfl
    exact ⟨rfl, fun v hv => (qProjCube_sgn_of_not_mem hv).symm⟩
  · rintro ⟨hs, hv⟩
    refine QCube.ext' hs (fun v hvc => ?_)
    rw [qProjCube_sgn_of_not_mem (show v ∉ p.spx by rw [hs]; exact hvc)]
    exact hv v hvc

/-- A cell whose cube is retained is not a marked apex. -/
theorem not_isMarkedApex_of_qProjCube_eq {r : Sph A} {c : QCube A}
    (hc : ¬ (c.spx = ∅ ∧ c.sgn = 0)) (h : qProjCube r = c) :
    ¬ IsMarkedApex (IsGamma A) r := by
  rintro ⟨hemp, hrep⟩
  refine hc ⟨by rw [← h]; exact hemp, ?_⟩
  funext v
  show c.sgn v = 0
  have hv : v ∉ r.spx := by rw [show r.spx = ∅ from hemp]; simp
  rw [← h, qProjCube_sgn_of_not_mem hv]
  simpa using congrFun (show phi A r.rep = 0 from hrep) v

theorem not_vplus_qProjCube {p : Sph A} (hp : ¬ IsMarkedApex (IsGamma A) p) :
    ¬ ((qProjCube p).spx = ∅ ∧ (qProjCube p).sgn = 0) := by
  rintro ⟨hemp, hsgn⟩
  refine hp ⟨hemp, ?_⟩
  funext v
  show phi A p.rep v = 0
  have hv : v ∉ p.spx := by rw [show p.spx = ∅ from hemp]; simp
  rw [← qProjCube_sgn_of_not_mem hv]
  simpa using congrFun hsgn v

/-- **The projection `Z → Q`.** -/
noncomputable def zProj : Zpos A X (IsGamma A) att → Qpos A X att
  | Sum.inl p => qOld (qProjCube p.1) (not_vplus_qProjCube p.2)
  | Sum.inr wx => qNew wx.2

@[simp] theorem zProj_zNew (w : {w : CayGroup A // IsGamma A w}) (x : X) :
    zProj (A := A) (att := att) (zNew w x) = qNew x := rfl

theorem zProj_zOld (p : Sph A) (hp : ¬ IsMarkedApex (IsGamma A) p) :
    zProj (X := X) (att := att) (zOld p hp) = qOld (qProjCube p) (not_vplus_qProjCube hp) := rfl

/-- **The projection is monotone.** -/
theorem zProj_monotone : Monotone (zProj (A := A) (X := X) (att := att)) := by
  rintro (p | ⟨u, x⟩) (q | ⟨v, y⟩) h
  · refine ⟨h.1, fun w hw => ?_⟩
    have hwp : w ∉ p.1.spx := fun hc => hw (h.1 hc)
    rw [qProjCube_sgn_of_not_mem hwp, qProjCube_sgn_of_not_mem hw]
    exact (phi_rep_eq_of_inChamber (inChamber_rep_of_le h) hw).symm
  · exact h.elim
  · obtain ⟨hne, hx⟩ := h.2
    refine ⟨?_, hne, hx⟩
    funext w
    show (qProjCube q.1).sgn w = 0
    by_cases hw : w ∈ q.1.spx
    · exact (qProjCube q.1).sgn_eq_zero w hw
    · rw [qProjCube_sgn_of_not_mem hw, phi_rep_eq_of_inChamber h.1 hw]
      simpa using congrFun (show phi A u.1 = 0 from u.2) w
  · exact h.2

/-! ### Surjectivity -/

section Surjective

variable [Fintype V]

/-- **Every cube of the quotient is the image of a cell of `Z`.** -/
theorem exists_zOld_qProjCube (c : QCube A) :
    ∃ p : Sph A, qProjCube p = c := by
  obtain ⟨w, hw⟩ := phi_surjective A c.sgn
  refine ⟨chamberPt w c.isSimplex, ?_⟩
  rw [qProjCube_eq_iff]
  refine ⟨rfl, fun v hv => ?_⟩
  rw [phi_rep_eq_of_inChamber (chamberPt_inChamber w c.isSimplex) (by simpa using hv), hw]

/-- **The projection is onto.** -/
theorem zProj_surjective : Function.Surjective (zProj (A := A) (X := X) (att := att)) := by
  rintro (⟨c, hc⟩ | x)
  · obtain ⟨p, hp⟩ := exists_zOld_qProjCube c
    refine ⟨zOld p (not_isMarkedApex_of_qProjCube_eq hc hp), ?_⟩
    show qOld _ _ = qOld c hc
    exact congrArg Sum.inl (Subtype.ext hp)
  · exact ⟨zNew ⟨1, isGamma_one⟩ x, rfl⟩

end Surjective

/-! ### `Γ`-invariance and the fibres -/

variable {k : CayGroup A}

theorem isGamma_stable (hk : IsGamma A k) : ∀ w : CayGroup A, IsGamma A (k * w) ↔ IsGamma A w :=
  fun w => isGamma_mul_iff hk w

/-- **The projection is `Γ`-invariant.** -/
theorem zProj_zAct (hk : IsGamma A k) (z : Zpos A X (IsGamma A) att) :
    zProj (zAct k (isGamma_stable hk) z) = zProj z := by
  cases z with
  | inl p =>
      refine congrArg Sum.inl (Subtype.ext ?_)
      refine QCube.ext' rfl (fun v hv => ?_)
      have hv' : v ∉ p.1.spx := hv
      rw [show (qProjCube (sphAct k p.1)).sgn v = phi A (sphAct k p.1).rep v from
        qProjCube_sgn_of_not_mem (by simpa using hv'),
        qProjCube_sgn_of_not_mem hv']
      rw [phi_rep_eq_of_inChamber (inChamber_sphAct_self k p.1) (by simpa using hv'),
        phi_mul, Pi.add_apply,
        show phi A k v = 0 from by simpa using congrFun (show phi A k = 0 from hk) v,
        zero_add]
  | inr wx => rfl

/-- **The fibres of the projection are exactly the `Γ`-orbits.** -/
theorem exists_zAct_of_zProj_eq {z z' : Zpos A X (IsGamma A) att} (h : zProj z = zProj z') :
    ∃ (k : CayGroup A) (hk : IsGamma A k), zAct k (isGamma_stable hk) z = z' := by
  cases z with
  | inl p =>
      cases z' with
      | inl q =>
          -- the two cells have the same type and the same signs outside it
          have hcube : qProjCube p.1 = qProjCube q.1 := congrArg Subtype.val (Sum.inl.inj h)
          have hspx : p.1.spx = q.1.spx := congrArg QCube.spx hcube
          have hsgn : ∀ v, v ∉ q.1.spx → phi A p.1.rep v = phi A q.1.rep v := by
            intro v hv
            have := congrFun (congrArg QCube.sgn hcube) v
            rwa [qProjCube_sgn_of_not_mem (by rw [hspx]; exact hv),
              qProjCube_sgn_of_not_mem hv] at this
          -- correct the representative of `q` inside its coset so that the parities agree
          obtain ⟨u, hu, hphiu⟩ := exists_mem_specialSub_phi_eq A q.1.spx
            (fun v => if v ∈ q.1.spx then phi A p.1.rep v + phi A q.1.rep v else 0)
            (fun v hv => by simp [hv])
          refine ⟨q.1.rep * u * p.1.rep⁻¹, ?_, ?_⟩
          · show phi A _ = 0
            funext v
            simp only [phi_mul, phi_inv, Pi.add_apply, Pi.zero_apply, hphiu]
            by_cases hv : v ∈ q.1.spx
            · rw [if_pos hv]
              have hre : phi A q.1.rep v + (phi A p.1.rep v + phi A q.1.rep v) + phi A p.1.rep v
                  = (phi A q.1.rep v + phi A q.1.rep v) + (phi A p.1.rep v + phi A p.1.rep v) := by
                ring
              rw [hre, zmod2_add_self, zmod2_add_self, add_zero]
            · rw [if_neg hv, add_zero, hsgn v hv, zmod2_add_self]
          · refine congrArg Sum.inl (Subtype.ext ?_)
            show sphAct (q.1.rep * u * p.1.rep⁻¹) p.1 = q.1
            have hin : InChamber (q.1.rep * u) q.1 := by
              show q.1.rep⁻¹ * (q.1.rep * u) ∈ specialSub A (q.1.spx : Set V)
              rw [inv_mul_cancel_left]
              exact hu
            refine eq_of_inChamber_spx_eq (x := q.1.rep * u) ?_ hin ?_
            · have := inChamber_sphAct_self (q.1.rep * u * p.1.rep⁻¹) p.1
              rwa [inv_mul_cancel_right] at this
            · rw [sphAct_spx]; exact hspx
      | inr vy => exact absurd h (by simp [zProj, qOld, qNew])
  | inr wx =>
      cases z' with
      | inl q => exact absurd h (by simp [zProj, qOld, qNew])
      | inr vy =>
          have hx : wx.2 = vy.2 := Sum.inr.inj h
          refine ⟨vy.1.1 * wx.1.1⁻¹, ?_, ?_⟩
          · show phi A _ = 0
            funext v
            simp only [phi_mul, phi_inv, Pi.add_apply, Pi.zero_apply,
              show phi A vy.1.1 = 0 from vy.1.2, show phi A wx.1.1 = 0 from wx.1.2]
            simp
          · refine congrArg Sum.inr ?_
            refine Prod.ext (Subtype.ext ?_) hx
            show vy.1.1 * wx.1.1⁻¹ * wx.1.1 = vy.1.1
            group

end Davis
end FiniteChains
