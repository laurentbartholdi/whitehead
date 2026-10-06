import RequestProject.CmpNerve

/-!
# The face poset of a polygon with identified boundary

This file builds the **cell structure of a closed surface presented by a polygon with identified
sides**, as a finite partial order — the face poset of a regular cell decomposition.  Its
comparability graph is the nerve used by the chamber construction
(`RequestProject/CmpNerve.lean`), so the corresponding simplicial complex is the barycentric
subdivision of that cell structure: a genuine triangulation of the surface.

The decomposition has three layers.

* **The identified boundary.**  The boundary of the polygon is a cycle of `M` edges; its
  positions are `Fin M`.  The identification of the sides of the polygon is given by the two
  labelling maps `vc : Fin M → κ` and `ec : Fin M → ι`: the vertex at the position `p` of the
  polygon is the vertex `vc p` of the surface, and the edge from the position `p` to the
  position `p+1` is the edge `ec p` of the surface.  Different positions carrying the same label
  are glued.  The cells are `vtx v` and `bed e`.
* **The collar.**  A parallel copy of the boundary cycle, *not* identified: the vertices
  `cvx p` and the edges `ced p`, together with the edges `dia p` (from the boundary vertex at
  `p` to the collar vertex at `p`), `gdi p` (from the boundary vertex at `p` to the collar
  vertex at `p+1`) and the two triangles `tr1 p`, `tr2 p` which fill the quadrilateral between
  the boundary edge `p` and the collar edge `p`.
* **The interior fan.**  A centre `ctr`, the radii `rad p` from the centre to the collar vertex
  at `p`, and the triangles `inn p` filling the cone over the collar.

The strict face order `plt` is transitive as soon as the identification of the boundary is
consistent with the identification of its endpoints, which is the hypothesis `hcompat`: two
positions carrying the same edge label carry, in one of the two possible orders, the same pair
of endpoint labels.
-/

namespace FiniteChains
namespace Davis

open RACG Mirror Comb

universe u

/-- The cells of the polygon with identified boundary. -/
inductive Cell (κ ι : Type u) (M : ℕ) : Type u
  /-- A vertex of the identified boundary. -/
  | vtx (v : κ) : Cell κ ι M
  /-- An edge of the identified boundary. -/
  | bed (e : ι) : Cell κ ι M
  /-- A vertex of the collar. -/
  | cvx (p : Fin M) : Cell κ ι M
  /-- An edge of the collar. -/
  | ced (p : Fin M) : Cell κ ι M
  /-- The edge joining the boundary vertex at `p` to the collar vertex at `p`. -/
  | dia (p : Fin M) : Cell κ ι M
  /-- The edge joining the boundary vertex at `p` to the collar vertex at `p+1`. -/
  | gdi (p : Fin M) : Cell κ ι M
  /-- The triangle on the boundary edge at `p` and the collar vertex at `p+1`. -/
  | tr1 (p : Fin M) : Cell κ ι M
  /-- The triangle on the collar edge at `p` and the boundary vertex at `p`. -/
  | tr2 (p : Fin M) : Cell κ ι M
  /-- The centre of the polygon. -/
  | ctr : Cell κ ι M
  /-- The radius from the centre to the collar vertex at `p`. -/
  | rad (p : Fin M) : Cell κ ι M
  /-- The triangle of the fan on the collar edge at `p`. -/
  | inn (p : Fin M) : Cell κ ι M
  deriving DecidableEq

namespace Cell

variable {κ ι : Type u} {M : ℕ}

/-- The dimension of a cell. -/
def rk : Cell κ ι M → ℕ
  | vtx _ => 0
  | bed _ => 1
  | cvx _ => 0
  | ced _ => 1
  | dia _ => 1
  | gdi _ => 1
  | tr1 _ => 2
  | tr2 _ => 2
  | ctr => 0
  | rad _ => 1
  | inn _ => 2

instance [Fintype κ] [Fintype ι] [DecidableEq κ] [DecidableEq ι] :
    Fintype (Cell κ ι M) where
  elems :=
    (Finset.univ.image vtx) ∪ (Finset.univ.image bed) ∪ (Finset.univ.image cvx) ∪
      (Finset.univ.image ced) ∪ (Finset.univ.image dia) ∪ (Finset.univ.image gdi) ∪
      (Finset.univ.image tr1) ∪ (Finset.univ.image tr2) ∪ {ctr} ∪
      (Finset.univ.image rad) ∪ (Finset.univ.image inn)
  complete := by
    intro x
    cases x <;> simp

end Cell

section Order

variable {κ ι : Type u} {M : ℕ} [NeZero M]

open Cell

/-- **The strict face order of the polygon with identified boundary.** -/
def plt (vc : Fin M → κ) (ec : Fin M → ι) : Cell κ ι M → Cell κ ι M → Prop
  | vtx v, bed e => ∃ i, ec i = e ∧ (vc i = v ∨ vc (i + 1) = v)
  | vtx v, dia p => vc p = v
  | vtx v, gdi p => vc p = v
  | cvx q, ced r => q = r ∨ q = r + 1
  | cvx q, dia r => q = r
  | cvx q, gdi r => q = r + 1
  | cvx q, rad r => q = r
  | ctr, rad _ => True
  | bed e, tr1 p => e = ec p
  | ced r, tr2 p => r = p
  | ced r, inn p => r = p
  | dia r, tr1 p => r = p + 1
  | dia r, tr2 p => r = p
  | gdi r, tr1 p => r = p
  | gdi r, tr2 p => r = p
  | rad r, inn p => r = p ∨ r = p + 1
  | vtx v, tr1 p => vc p = v ∨ vc (p + 1) = v
  | vtx v, tr2 p => vc p = v
  | cvx q, tr1 p => q = p + 1
  | cvx q, tr2 p => q = p ∨ q = p + 1
  | cvx q, inn p => q = p ∨ q = p + 1
  | ctr, inn _ => True
  | _, _ => False

variable {vc : Fin M → κ} {ec : Fin M → ι}

theorem rk_lt_of_plt {x y : Cell κ ι M} (h : plt vc ec x y) : x.rk < y.rk := by
  cases x <;> cases y <;> simp_all [plt, rk]

theorem plt_irrefl (x : Cell κ ι M) : ¬ plt vc ec x x := fun h => absurd (rk_lt_of_plt h) (by omega)

theorem not_plt_of_rk_le {x y : Cell κ ι M} (h : y.rk ≤ x.rk) : ¬ plt vc ec x y :=
  fun hh => absurd (rk_lt_of_plt hh) (by omega)

omit [NeZero M] in
theorem rk_le_two (x : Cell κ ι M) : x.rk ≤ 2 := by cases x <;> simp [rk]

theorem plt_asymm {x y : Cell κ ι M} (h : plt vc ec x y) : ¬ plt vc ec y x := by
  intro h'
  have := rk_lt_of_plt h
  have := rk_lt_of_plt h'
  omega

/-- **The compatibility of the identification of the boundary with the identification of its
endpoints**: two positions of the polygon carrying the same edge of the surface carry, in one of
the two orders, the same pair of endpoints. -/
def Compat (vc : Fin M → κ) (ec : Fin M → ι) : Prop :=
  ∀ i j : Fin M, ec i = ec j →
    (vc i = vc j ∧ vc (i + 1) = vc (j + 1)) ∨ (vc i = vc (j + 1) ∧ vc (i + 1) = vc j)

theorem plt_trans (hc : Compat vc ec) {x y z : Cell κ ι M} (hxy : plt vc ec x y)
    (hyz : plt vc ec y z) : plt vc ec x z := by
  cases y with
  | vtx _ => exact absurd hxy (not_plt_of_rk_le (Nat.zero_le _))
  | cvx _ => exact absurd hxy (not_plt_of_rk_le (Nat.zero_le _))
  | ctr => exact absurd hxy (not_plt_of_rk_le (Nat.zero_le _))
  | tr1 _ => exact absurd hyz (not_plt_of_rk_le (rk_le_two z))
  | tr2 _ => exact absurd hyz (not_plt_of_rk_le (rk_le_two z))
  | inn _ => exact absurd hyz (not_plt_of_rk_le (rk_le_two z))
  | bed e =>
      cases x with
      | vtx v =>
          cases z with
          | tr1 p =>
              obtain ⟨i, hi, hv⟩ := hxy
              have hep : ec i = ec p := by rw [hi]; exact hyz
              rcases hc i p hep with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rcases hv with rfl | rfl
              · exact Or.inl h1.symm
              · exact Or.inr h2.symm
              · exact Or.inr h1.symm
              · exact Or.inl h2.symm
          | _ => simp [plt] at hyz
      | _ => simp [plt] at hxy
  | ced r =>
      cases x with
      | cvx q =>
          cases z with
          | tr2 p =>
              have h : r = p := hyz
              subst h
              exact hxy
          | inn p =>
              have h : r = p := hyz
              subst h
              exact hxy
          | _ => simp [plt] at hyz
      | _ => simp [plt] at hxy
  | dia r =>
      cases x with
      | vtx v =>
          cases z with
          | tr1 p =>
              have hr : r = p + 1 := hyz
              subst hr
              exact Or.inr hxy
          | tr2 p =>
              have hr : r = p := hyz
              subst hr
              exact hxy
          | _ => simp [plt] at hyz
      | cvx q =>
          cases z with
          | tr1 p =>
              have hr : r = p + 1 := hyz
              have hq : q = r := hxy
              show q = p + 1
              rw [hq, hr]
          | tr2 p =>
              have hr : r = p := hyz
              have hq : q = r := hxy
              show q = p ∨ q = p + 1
              exact Or.inl (by rw [hq, hr])
          | _ => simp [plt] at hyz
      | _ => simp [plt] at hxy
  | gdi r =>
      cases x with
      | vtx v =>
          cases z with
          | tr1 p =>
              have hr : r = p := hyz
              subst hr
              exact Or.inl hxy
          | tr2 p =>
              have hr : r = p := hyz
              subst hr
              exact hxy
          | _ => simp [plt] at hyz
      | cvx q =>
          cases z with
          | tr1 p =>
              have hr : r = p := hyz
              have hq : q = r + 1 := hxy
              show q = p + 1
              rw [hq, hr]
          | tr2 p =>
              have hr : r = p := hyz
              have hq : q = r + 1 := hxy
              show q = p ∨ q = p + 1
              exact Or.inr (by rw [hq, hr])
          | _ => simp [plt] at hyz
      | _ => simp [plt] at hxy
  | rad r =>
      cases x with
      | cvx q =>
          cases z with
          | inn p =>
              have hq : q = r := hxy
              show q = p ∨ q = p + 1
              rcases hyz with hr | hr
              · exact Or.inl (by rw [hq, hr])
              · exact Or.inr (by rw [hq, hr])
          | _ => simp [plt] at hyz
      | ctr =>
          cases z with
          | inn p => trivial
          | _ => simp [plt] at hyz
      | _ => simp [plt] at hxy

/-! ### The face poset -/

/-- **The face poset of the polygon with identified boundary.** -/
def SCell (_vc : Fin M → κ) (_ec : Fin M → ι) (_hc : Compat vc ec) : Type u := Cell κ ι M

variable (vc ec) in
/-- The order of the face poset: equality or a strict face. -/
def sle (_hc : Compat vc ec) (x y : Cell κ ι M) : Prop := x = y ∨ plt vc ec x y

instance instPartialOrderSCell (hc : Compat vc ec) : PartialOrder (SCell vc ec hc) where
  le x y := sle vc ec hc x y
  le_refl _ := Or.inl rfl
  le_trans a b c hab hbc := by
    rcases hab with rfl | h1
    · exact hbc
    rcases hbc with rfl | h2
    · exact Or.inr h1
    exact Or.inr (plt_trans hc h1 h2)
  le_antisymm a b hab hba := by
    rcases hab with rfl | h1
    · rfl
    rcases hba with rfl | h2
    · rfl
    exact absurd h2 (plt_asymm h1)

instance instDecidableEqSCell [DecidableEq κ] [DecidableEq ι] (hc : Compat vc ec) :
    DecidableEq (SCell vc ec hc) := inferInstanceAs (DecidableEq (Cell κ ι M))

instance instFintypeSCell [Fintype κ] [Fintype ι] [DecidableEq κ] [DecidableEq ι]
    (hc : Compat vc ec) : Fintype (SCell vc ec hc) := inferInstanceAs (Fintype (Cell κ ι M))

variable (vc ec)

/-- A cell of the poset, from a cell of the polygon. -/
def toS (hc : Compat vc ec) (x : Cell κ ι M) : SCell vc ec hc := x

variable {vc ec}

theorem sle_iff (hc : Compat vc ec) {x y : Cell κ ι M} :
    (toS vc ec hc x ≤ toS vc ec hc y) ↔ (x = y ∨ plt vc ec x y) := Iff.rfl

theorem le_of_plt (hc : Compat vc ec) {x y : Cell κ ι M} (h : plt vc ec x y) :
    toS vc ec hc x ≤ toS vc ec hc y := Or.inr h

end Order

end Davis
end FiniteChains
