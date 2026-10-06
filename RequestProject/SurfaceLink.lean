import RequestProject.SurfaceRegular

/-!
# The links of the vertices of the surface are connected

The local conditions verified in `RequestProject/SurfaceRegular.lean` make every vertex link of
the subdivision a disjoint union of cycles.  A polygon with identified sides is a closed surface
exactly when each of these links is a *single* cycle, i.e. when the corners of the polygon lying
over one vertex of the surface are glued to one another in a single cycle.

* `FiniteChains.Davis.CornerAdj` — two positions of the boundary are corners at the same vertex
  of the surface which share a side of the polygon;
* `FiniteChains.Davis.CornersConnected` — the corners over each vertex form a single cycle;
* `FiniteChains.Davis.linkConnected_SCell` — **under this hypothesis every vertex link of the
  subdivision is connected**;
* `FiniteChains.Davis.closedSurfacePoset_SCell` — hence the polygon with identified sides is a
  closed surface, in the combinatorial sense of `FiniteChains.ASC.ClosedSurfacePoset`.

The proof is the expected walk.  Around the centre one goes from one radius to the next through
the triangle of the fan between them; around a collar vertex one goes once around the ten cells
through it; around a vertex of the identified boundary one first walks, inside one corner of the
polygon, from the outgoing side to the incoming side through the two triangles and the two
diagonals of that corner, and then passes to the next corner through the side which glues them.
-/

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains
namespace Davis

open Cell ASC Relation

universe u

section Link

variable {κ ι : Type u} {M : ℕ} [NeZero M] {vc : Fin M → κ} {ec : Fin M → ι}
variable (hc : Compat vc ec)

/-! ### Elementary steps of a link -/

theorem linkAdj_symmetric (v : SCell vc ec hc) : Symmetric (LinkAdj v) := by
  rintro x y ⟨h1, h2, h3⟩
  exact ⟨h2, h1, h3.symm⟩

theorem linkAdj_of_lt {v x y : SCell vc ec hc} (hx : v < x) (hy : v < y) (h : x ≤ y) :
    LinkAdj v x y := ⟨hx, hy, Or.inl h⟩

/-! ### The link of the centre -/

theorem ctr_lt_iff {y : Cell κ ι M} :
    (toS vc ec hc ctr < toS vc ec hc y) ↔ (∃ p : Fin M, y = rad p ∨ y = inn p) := by
  rw [lt_iff_plt]
  cases y <;> simp [plt]

theorem ctr_lt_rad (r : Fin M) : toS vc ec hc ctr < toS vc ec hc (rad r) :=
  (lt_rad_iff hc).2 (Or.inl rfl)

theorem ctr_lt_inn (r : Fin M) : toS vc ec hc ctr < toS vc ec hc (inn r) :=
  (lt_inn_iff hc).2 (Or.inr (Or.inr (Or.inr (Or.inl rfl))))

theorem conn_rad_step (q : Fin M) :
    ReflTransGen (LinkAdj (toS vc ec hc ctr)) (toS vc ec hc (rad q))
      (toS vc ec hc (rad (q + 1))) := by
  have s1 : LinkAdj (toS vc ec hc ctr) (toS vc ec hc (rad q)) (toS vc ec hc (inn q)) :=
    linkAdj_of_lt hc (ctr_lt_rad hc q) (ctr_lt_inn hc q)
      (le_of_lt ((lt_inn_iff hc).2 (Or.inr (Or.inl rfl))))
  have s2 : LinkAdj (toS vc ec hc ctr) (toS vc ec hc (inn q)) (toS vc ec hc (rad (q + 1))) :=
    ⟨ctr_lt_inn hc q, ctr_lt_rad hc _,
      Or.inr (le_of_lt ((lt_inn_iff hc).2 (Or.inr (Or.inr (Or.inl rfl)))))⟩
  exact (ReflTransGen.single s1).tail s2

theorem conn_rad (n : ℕ) : ∀ p : Fin M, p.val = n →
    ReflTransGen (LinkAdj (toS vc ec hc ctr)) (toS vc ec hc (rad 0)) (toS vc ec hc (rad p)) := by
  induction n with
  | zero =>
      intro p hp
      have hp0 : p = 0 := Fin.ext (by simpa using hp)
      subst hp0
      exact ReflTransGen.refl
  | succ n ih =>
      intro p hp
      have hM := Nat.pos_of_neZero M
      have h1 : (fpred p).val = n := by
        rw [fpred_val, if_neg (by omega)]
        omega
      have h2 := ih (fpred p) h1
      have h3 : (fpred p) + 1 = p := fpred_add_one p
      have h4 := conn_rad_step hc (fpred p)
      rw [h3] at h4
      exact h2.trans h4

private theorem reflTransGen_symm {α : Type*} {r : α → α → Prop}
    (hr : Symmetric r) {a b : α} (h : ReflTransGen r a b) : ReflTransGen r b a := by
  letI : Std.Symm r := ⟨fun _ _ h => hr h⟩
  exact Relation.ReflTransGen.stdSymm.symm _ _ h

/-- **The link of the centre of the polygon is connected**: it is the cycle of the collar. -/
theorem link_connected_ctr (x y : SCell vc ec hc) (hx : toS vc ec hc ctr < x)
    (hy : toS vc ec hc ctr < y) : ReflTransGen (LinkAdj (toS vc ec hc ctr)) x y := by
  have key : ∀ z : Cell κ ι M, toS vc ec hc ctr < toS vc ec hc z →
      ReflTransGen (LinkAdj (toS vc ec hc ctr)) (toS vc ec hc (rad 0)) (toS vc ec hc z) := by
    intro z hz
    obtain ⟨p, hp | hp⟩ := (ctr_lt_iff hc).1 hz
    · subst hp; exact conn_rad hc p.val p rfl
    · subst hp
      refine (conn_rad hc p.val p rfl).tail ?_
      exact linkAdj_of_lt hc (ctr_lt_rad hc p) (ctr_lt_inn hc p)
        (le_of_lt ((lt_inn_iff hc).2 (Or.inr (Or.inl rfl))))
  exact (reflTransGen_symm (linkAdj_symmetric hc _) (key x hx)).trans (key y hy)

/-! ### The link of a collar vertex -/

theorem cvx_lt_iff {p : Fin M} {y : Cell κ ι M} :
    (toS vc ec hc (cvx p) < toS vc ec hc y) ↔
      (y = ced p ∨ y = ced (fpred p) ∨ y = dia p ∨ y = gdi (fpred p) ∨ y = rad p ∨
        y = tr1 (fpred p) ∨ y = tr2 p ∨ y = tr2 (fpred p) ∨ y = inn p ∨ y = inn (fpred p)) := by
  rw [lt_iff_plt]
  have key : ∀ r : Fin M, (p = r + 1) ↔ (r = fpred p) := by
    intro r
    constructor
    · intro h; rw [h, fpred_succ]
    · intro h; rw [h, fpred_add_one]
  cases y <;> simp [plt, key, eq_comm]

/-- **The link of a collar vertex is connected**: it is the cycle of the ten cells through it. -/
theorem link_connected_cvx (q : Fin M) (x y : SCell vc ec hc)
    (hx : toS vc ec hc (cvx (q + 1)) < x) (hy : toS vc ec hc (cvx (q + 1)) < y) :
    ReflTransGen (LinkAdj (toS vc ec hc (cvx (q + 1)))) x y := by
  set v : SCell vc ec hc := toS vc ec hc (cvx (q + 1)) with hv
  have hced1 : v < toS vc ec hc (ced (q + 1)) := (lt_ced_iff hc).2 (Or.inl rfl)
  have hced0 : v < toS vc ec hc (ced q) := (lt_ced_iff hc).2 (Or.inr rfl)
  have hdia : v < toS vc ec hc (dia (q + 1)) := (lt_dia_iff hc).2 (Or.inr rfl)
  have hgdi : v < toS vc ec hc (gdi q) := (lt_gdi_iff hc).2 (Or.inr rfl)
  have hrad : v < toS vc ec hc (rad (q + 1)) := (lt_rad_iff hc).2 (Or.inr rfl)
  have htr1 : v < toS vc ec hc (tr1 q) :=
    (lt_tr1_iff hc).2 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl)))))
  have htr2a : v < toS vc ec hc (tr2 (q + 1)) :=
    (lt_tr2_iff hc).2 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have htr2b : v < toS vc ec hc (tr2 q) :=
    (lt_tr2_iff hc).2 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl)))))
  have hinna : v < toS vc ec hc (inn (q + 1)) :=
    (lt_inn_iff hc).2 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have hinnb : v < toS vc ec hc (inn q) :=
    (lt_inn_iff hc).2 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl)))))
  have key : ∀ z : Cell κ ι M, v < toS vc ec hc z →
      ReflTransGen (LinkAdj v) (toS vc ec hc z) (toS vc ec hc (ced (q + 1))) := by
    intro z hz
    have e_tr2a : ReflTransGen (LinkAdj v) (toS vc ec hc (tr2 (q + 1)))
        (toS vc ec hc (ced (q + 1))) :=
      ReflTransGen.single ((linkAdj_symmetric hc v)
        (linkAdj_of_lt hc hced1 htr2a (le_of_lt ((lt_tr2_iff hc).2 (Or.inl rfl)))))
    have e_dia : ReflTransGen (LinkAdj v) (toS vc ec hc (dia (q + 1)))
        (toS vc ec hc (ced (q + 1))) :=
      (ReflTransGen.single (linkAdj_of_lt hc hdia htr2a
        (le_of_lt ((lt_tr2_iff hc).2 (Or.inr (Or.inl rfl)))))).trans e_tr2a
    have e_inna : ReflTransGen (LinkAdj v) (toS vc ec hc (inn (q + 1)))
        (toS vc ec hc (ced (q + 1))) :=
      ReflTransGen.single ((linkAdj_symmetric hc v)
        (linkAdj_of_lt hc hced1 hinna (le_of_lt ((lt_inn_iff hc).2 (Or.inl rfl)))))
    have e_rad : ReflTransGen (LinkAdj v) (toS vc ec hc (rad (q + 1)))
        (toS vc ec hc (ced (q + 1))) :=
      (ReflTransGen.single (linkAdj_of_lt hc hrad hinna
        (le_of_lt ((lt_inn_iff hc).2 (Or.inr (Or.inl rfl)))))).trans e_inna
    have e_innb : ReflTransGen (LinkAdj v) (toS vc ec hc (inn q))
        (toS vc ec hc (ced (q + 1))) :=
      (ReflTransGen.single ((linkAdj_symmetric hc v) (linkAdj_of_lt hc hrad hinnb
        (le_of_lt ((lt_inn_iff hc).2 (Or.inr (Or.inr (Or.inl rfl)))))))).trans e_rad
    have e_ced0 : ReflTransGen (LinkAdj v) (toS vc ec hc (ced q))
        (toS vc ec hc (ced (q + 1))) :=
      (ReflTransGen.single (linkAdj_of_lt hc hced0 hinnb
        (le_of_lt ((lt_inn_iff hc).2 (Or.inl rfl))))).trans e_innb
    have e_tr2b : ReflTransGen (LinkAdj v) (toS vc ec hc (tr2 q))
        (toS vc ec hc (ced (q + 1))) :=
      (ReflTransGen.single ((linkAdj_symmetric hc v) (linkAdj_of_lt hc hced0 htr2b
        (le_of_lt ((lt_tr2_iff hc).2 (Or.inl rfl)))))).trans e_ced0
    have e_gdi : ReflTransGen (LinkAdj v) (toS vc ec hc (gdi q))
        (toS vc ec hc (ced (q + 1))) :=
      (ReflTransGen.single (linkAdj_of_lt hc hgdi htr2b
        (le_of_lt ((lt_tr2_iff hc).2 (Or.inr (Or.inr (Or.inl rfl))))))).trans e_tr2b
    have e_tr1 : ReflTransGen (LinkAdj v) (toS vc ec hc (tr1 q))
        (toS vc ec hc (ced (q + 1))) :=
      (ReflTransGen.single ((linkAdj_symmetric hc v) (linkAdj_of_lt hc hgdi htr1
        (le_of_lt ((lt_tr1_iff hc).2 (Or.inr (Or.inr (Or.inl rfl)))))))).trans e_gdi
    have hcases := (cvx_lt_iff hc).1 hz
    rw [fpred_succ] at hcases
    rcases hcases with h | h | h | h | h | h | h | h | h | h <;> subst h
    · exact ReflTransGen.refl
    · exact e_ced0
    · exact e_dia
    · exact e_gdi
    · exact e_rad
    · exact e_tr1
    · exact e_tr2a
    · exact e_tr2b
    · exact e_inna
    · exact e_innb
  exact (key x hx).trans (reflTransGen_symm (linkAdj_symmetric hc v) (key y hy))

/-! ### The cells at a corner of the polygon -/

theorem vtx_lt_bed_out {w : κ} {i : Fin M} (hi : vc i = w) :
    toS vc ec hc (vtx w) < toS vc ec hc (bed (ec i)) :=
  (lt_bed_iff hc).2 (Or.inl (by rw [hi]))

theorem vtx_lt_bed_in {w : κ} {i : Fin M} (hi : vc i = w) :
    toS vc ec hc (vtx w) < toS vc ec hc (bed (ec (fpred i))) := by
  refine (lt_bed_iff hc).2 (Or.inr ?_)
  rw [fpred_add_one, hi]

theorem vtx_lt_tr1_out {w : κ} {i : Fin M} (hi : vc i = w) :
    toS vc ec hc (vtx w) < toS vc ec hc (tr1 i) :=
  (lt_tr1_iff hc).2 (Or.inr (Or.inr (Or.inr (Or.inl (by rw [hi])))))

theorem vtx_lt_tr1_in {w : κ} {i : Fin M} (hi : vc i = w) :
    toS vc ec hc (vtx w) < toS vc ec hc (tr1 (fpred i)) := by
  refine (lt_tr1_iff hc).2 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ?_)))))
  rw [fpred_add_one, hi]

theorem vtx_lt_gdi {w : κ} {i : Fin M} (hi : vc i = w) :
    toS vc ec hc (vtx w) < toS vc ec hc (gdi i) :=
  (lt_gdi_iff hc).2 (Or.inl (by rw [hi]))

theorem vtx_lt_dia {w : κ} {i : Fin M} (hi : vc i = w) :
    toS vc ec hc (vtx w) < toS vc ec hc (dia i) :=
  (lt_dia_iff hc).2 (Or.inl (by rw [hi]))

theorem vtx_lt_tr2 {w : κ} {i : Fin M} (hi : vc i = w) :
    toS vc ec hc (vtx w) < toS vc ec hc (tr2 i) :=
  (lt_tr2_iff hc).2 (Or.inr (Or.inr (Or.inr (Or.inl (by rw [hi])))))

/-! ### Going around one corner of the polygon -/

theorem conn_tr1_bed {w : κ} {i : Fin M} (hi : vc i = w) :
    ReflTransGen (LinkAdj (toS vc ec hc (vtx w))) (toS vc ec hc (tr1 i))
      (toS vc ec hc (bed (ec i))) :=
  ReflTransGen.single ((linkAdj_symmetric hc _)
    (linkAdj_of_lt hc (vtx_lt_bed_out hc hi) (vtx_lt_tr1_out hc hi)
      (le_of_lt ((lt_tr1_iff hc).2 (Or.inl rfl)))))

theorem conn_gdi_bed {w : κ} {i : Fin M} (hi : vc i = w) :
    ReflTransGen (LinkAdj (toS vc ec hc (vtx w))) (toS vc ec hc (gdi i))
      (toS vc ec hc (bed (ec i))) :=
  (ReflTransGen.single (linkAdj_of_lt hc (vtx_lt_gdi hc hi) (vtx_lt_tr1_out hc hi)
    (le_of_lt ((lt_tr1_iff hc).2 (Or.inr (Or.inr (Or.inl rfl))))))).trans (conn_tr1_bed hc hi)

theorem conn_tr2_bed {w : κ} {i : Fin M} (hi : vc i = w) :
    ReflTransGen (LinkAdj (toS vc ec hc (vtx w))) (toS vc ec hc (tr2 i))
      (toS vc ec hc (bed (ec i))) :=
  (ReflTransGen.single ((linkAdj_symmetric hc _) (linkAdj_of_lt hc (vtx_lt_gdi hc hi)
    (vtx_lt_tr2 hc hi)
    (le_of_lt ((lt_tr2_iff hc).2 (Or.inr (Or.inr (Or.inl rfl)))))))).trans (conn_gdi_bed hc hi)

theorem conn_dia_bed {w : κ} {i : Fin M} (hi : vc i = w) :
    ReflTransGen (LinkAdj (toS vc ec hc (vtx w))) (toS vc ec hc (dia i))
      (toS vc ec hc (bed (ec i))) :=
  (ReflTransGen.single (linkAdj_of_lt hc (vtx_lt_dia hc hi) (vtx_lt_tr2 hc hi)
    (le_of_lt ((lt_tr2_iff hc).2 (Or.inr (Or.inl rfl)))))).trans (conn_tr2_bed hc hi)

theorem conn_tr1in_bed {w : κ} {i : Fin M} (hi : vc i = w) :
    ReflTransGen (LinkAdj (toS vc ec hc (vtx w))) (toS vc ec hc (tr1 (fpred i)))
      (toS vc ec hc (bed (ec i))) := by
  refine (ReflTransGen.single ((linkAdj_symmetric hc _) (linkAdj_of_lt hc (vtx_lt_dia hc hi)
    (vtx_lt_tr1_in hc hi) ?_))).trans (conn_dia_bed hc hi)
  refine le_of_lt ((lt_tr1_iff hc).2 (Or.inr (Or.inl ?_)))
  rw [fpred_add_one]

/-- **The two sides of the polygon at one corner are joined inside the link.** -/
theorem conn_bedin_bed {w : κ} {i : Fin M} (hi : vc i = w) :
    ReflTransGen (LinkAdj (toS vc ec hc (vtx w))) (toS vc ec hc (bed (ec (fpred i))))
      (toS vc ec hc (bed (ec i))) :=
  (ReflTransGen.single (linkAdj_of_lt hc (vtx_lt_bed_in hc hi) (vtx_lt_tr1_in hc hi)
    (le_of_lt ((lt_tr1_iff hc).2 (Or.inl rfl))))).trans (conn_tr1in_bed hc hi)

/-- Every cell through a vertex of the identified boundary is joined, inside the link, to the
side of the polygon at one of the corners over that vertex. -/
theorem conn_to_bed {w : κ} (z : Cell κ ι M) (hz : toS vc ec hc (vtx w) < toS vc ec hc z) :
    ∃ i : Fin M, vc i = w ∧ ReflTransGen (LinkAdj (toS vc ec hc (vtx w))) (toS vc ec hc z)
      (toS vc ec hc (bed (ec i))) := by
  rw [lt_iff_plt] at hz
  cases z with
  | bed e =>
      obtain ⟨j, hj, hv⟩ := hz
      subst hj
      rcases hv with hv | hv
      · exact ⟨j, hv, ReflTransGen.refl⟩
      · refine ⟨j + 1, hv, ?_⟩
        have hb := conn_bedin_bed hc hv
        rwa [fpred_succ] at hb
  | dia p => exact ⟨p, hz, conn_dia_bed hc hz⟩
  | gdi p => exact ⟨p, hz, conn_gdi_bed hc hz⟩
  | tr2 p => exact ⟨p, hz, conn_tr2_bed hc hz⟩
  | tr1 p =>
      rcases hz with hv | hv
      · exact ⟨p, hv, conn_tr1_bed hc hv⟩
      · refine ⟨p + 1, hv, ?_⟩
        have hb := conn_tr1in_bed hc hv
        rwa [fpred_succ] at hb
  | _ => simp [plt] at hz

/-! ### Passing from one corner to the next -/

/-- **Two corners of the polygon at the same vertex sharing a side**: the positions `i` and `j`
carry the same vertex, and one of the two sides through `i` is identified with one of the two
sides through `j`. -/
def CornerAdj (vc : Fin M → κ) (ec : Fin M → ι) (i j : Fin M) : Prop :=
  vc i = vc j ∧ (ec i = ec j ∨ ec i = ec (fpred j) ∨ ec (fpred i) = ec j ∨
    ec (fpred i) = ec (fpred j))

theorem cornerAdj_symm {i j : Fin M} (h : CornerAdj vc ec i j) : CornerAdj vc ec j i := by
  obtain ⟨hv, hh⟩ := h
  refine ⟨hv.symm, ?_⟩
  rcases hh with h | h | h | h
  · exact Or.inl h.symm
  · exact Or.inr (Or.inr (Or.inl h.symm))
  · exact Or.inr (Or.inl h.symm)
  · exact Or.inr (Or.inr (Or.inr h.symm))

theorem vc_eq_of_reflTransGen {i j : Fin M} (h : ReflTransGen (CornerAdj vc ec) i j) :
    vc i = vc j := by
  induction h with
  | refl => rfl
  | tail _ hstep ih => exact ih.trans hstep.1

/-- **The corners of the polygon over one vertex of the surface form a single cycle.** -/
def CornersConnected (vc : Fin M → κ) (ec : Fin M → ι) : Prop :=
  ∀ i j : Fin M, vc i = vc j → ReflTransGen (CornerAdj vc ec) i j

theorem conn_corner_step {w : κ} {i j : Fin M} (hi : vc i = w) (hj : vc j = w)
    (h : CornerAdj vc ec i j) :
    ReflTransGen (LinkAdj (toS vc ec hc (vtx w))) (toS vc ec hc (bed (ec i)))
      (toS vc ec hc (bed (ec j))) := by
  obtain ⟨-, hh⟩ := h
  rcases hh with h | h | h | h
  · rw [h]
  · rw [h]
    exact conn_bedin_bed hc hj
  · have hb := conn_bedin_bed hc hi
    rw [h] at hb
    exact reflTransGen_symm (linkAdj_symmetric hc _) hb
  · have hb := conn_bedin_bed hc hi
    rw [h] at hb
    exact (reflTransGen_symm (linkAdj_symmetric hc _) hb).trans (conn_bedin_bed hc hj)

theorem conn_corner {w : κ} {i j : Fin M} (hi : vc i = w)
    (h : ReflTransGen (CornerAdj vc ec) i j) :
    ReflTransGen (LinkAdj (toS vc ec hc (vtx w))) (toS vc ec hc (bed (ec i)))
      (toS vc ec hc (bed (ec j))) := by
  induction h with
  | refl => exact ReflTransGen.refl
  | @tail b c hib hbc ih =>
      have hb : vc b = w := (vc_eq_of_reflTransGen hib).symm.trans hi
      have hcv : vc c = w := hbc.1.symm.trans hb
      exact (ih).trans (conn_corner_step hc hb hcv hbc)

/-- **The link of a vertex of the identified boundary is connected.** -/
theorem link_connected_vtx (hcorners : CornersConnected vc ec) (w : κ) (x y : SCell vc ec hc)
    (hx : toS vc ec hc (vtx w) < x) (hy : toS vc ec hc (vtx w) < y) :
    ReflTransGen (LinkAdj (toS vc ec hc (vtx w))) x y := by
  obtain ⟨i, hi, hxi⟩ := conn_to_bed hc x hx
  obtain ⟨j, hj, hyj⟩ := conn_to_bed hc y hy
  have hij : ReflTransGen (CornerAdj vc ec) i j := hcorners i j (by rw [hi, hj])
  exact (hxi.trans (conn_corner hc hi hij)).trans
    (reflTransGen_symm (linkAdj_symmetric hc _) hyj)

/-! ### The closed surface -/

/-- **Every vertex link of the subdivision of the surface is connected.** -/
theorem linkConnected_SCell (hd : PolygonData vc ec) (hcorners : CornersConnected vc ec) :
    LinkConnected (surfaceRank_SCell hc hd) := by
  intro v hv x y hx hy
  cases v with
  | vtx w => exact link_connected_vtx hc hcorners w x y hx hy
  | cvx p =>
      have hp : fpred p + 1 = p := fpred_add_one p
      rw [← hp] at hx hy ⊢
      exact link_connected_cvx hc (fpred p) x y hx hy
  | ctr => exact link_connected_ctr hc x y hx hy
  | _ => simp [surfaceRank_SCell, Cell.rk] at hv

/-- **The polygon with identified sides is a closed surface**: the local incidence conditions
hold and all vertex links are connected. -/
def closedSurfacePoset_SCell (hd : PolygonData vc ec) (hcorners : CornersConnected vc ec) :
    ClosedSurfacePoset (SCell vc ec hc) where
  toSurfaceRank := surfaceRank_SCell hc hd
  link_connected := linkConnected_SCell hc hd hcorners

end Link

end Davis
end FiniteChains
