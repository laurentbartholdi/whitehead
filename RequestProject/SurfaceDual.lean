module

public import RequestProject.OrderComplexDual
public import RequestProject.SurfaceLink
public import RequestProject.SurfaceBlockCollapse

@[expose] public section

/-!
# The dual graph of the surface of the block, and the collapse of Lemma 3.2 (ii)

`RequestProject/SurfaceRegular.lean` and `RequestProject/SurfaceLink.lean` show that the face
poset `SCell vc ec hc` of a polygon with identified sides is a closed surface; its order complex
is the triangulation used by the construction.  `RequestProject/OrderComplexDual.lean` reduces
connectedness of the dual graph of that triangulation to two conditions on the cell poset.  This
file verifies both of them for `SCell vc ec hc`:

* `FiniteChains.Davis.faceEdges_SCell` — every two distinct vertices of a triangle of the surface
  are joined by a side of that triangle;
* `FiniteChains.Davis.facesConnected_SCell` — the triangles `tr1 p`, `tr2 p`, `inn p` of the
  surface are connected through shared edges (`tr1 p — tr2 p — inn p — inn (p+1) — …`).

The consequences are `FiniteChains.Davis.dual_connected_SCell` — the dual graph of the
triangulation is connected — and, with the local conditions already proved, the collapse itself:
`FiniteChains.Davis.exists_spine_collapse_SCell` removes all three-cubes of the truncated cube
complex over the triangulation of the surface, leaving a two-dimensional spine.
-/

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains
namespace Davis

open Cell ASC Relation

section Dual

variable {κ ι : Type} {M : ℕ} [NeZero M] [Fintype κ] [Fintype ι] [DecidableEq κ] [DecidableEq ι]
  {vc : Fin M → κ} {ec : Fin M → ι} (hc : Compat vc ec)

/-! ### Two vertices of a triangle are joined by a side -/

omit [Fintype κ] [Fintype ι] [DecidableEq κ] [DecidableEq ι] in
/-- The vertices of the triangle `tr1 p`. -/
theorem vtx_of_lt_tr1 {p : Fin M} {v : SCell vc ec hc} (hv : Cell.rk v = 0)
    (h : v < toS vc ec hc (tr1 p)) :
    v = vtx (vc p) ∨ v = vtx (vc (p + 1)) ∨ v = cvx (p + 1) := by
  rcases (lt_tr1_iff hc).1 h with rfl | rfl | rfl | rfl | rfl | rfl
  · simp [Cell.rk] at hv
  · simp [Cell.rk] at hv
  · simp [Cell.rk] at hv
  · exact Or.inl rfl
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr rfl)

omit [Fintype κ] [Fintype ι] [DecidableEq κ] [DecidableEq ι] in
/-- The vertices of the triangle `tr2 p`. -/
theorem vtx_of_lt_tr2 {p : Fin M} {v : SCell vc ec hc} (hv : Cell.rk v = 0)
    (h : v < toS vc ec hc (tr2 p)) :
    v = vtx (vc p) ∨ v = cvx p ∨ v = cvx (p + 1) := by
  rcases (lt_tr2_iff hc).1 h with rfl | rfl | rfl | rfl | rfl | rfl
  · simp [Cell.rk] at hv
  · simp [Cell.rk] at hv
  · simp [Cell.rk] at hv
  · exact Or.inl rfl
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr rfl)

omit [Fintype κ] [Fintype ι] [DecidableEq κ] [DecidableEq ι] in
/-- The vertices of the triangle `inn p`. -/
theorem vtx_of_lt_inn {p : Fin M} {v : SCell vc ec hc} (hv : Cell.rk v = 0)
    (h : v < toS vc ec hc (inn p)) :
    v = ctr ∨ v = cvx p ∨ v = cvx (p + 1) := by
  rcases (lt_inn_iff hc).1 h with rfl | rfl | rfl | rfl | rfl | rfl
  · simp [Cell.rk] at hv
  · simp [Cell.rk] at hv
  · simp [Cell.rk] at hv
  · exact Or.inl rfl
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr rfl)

omit [Fintype κ] [Fintype ι] [DecidableEq κ] [DecidableEq ι] in
/-- **Two distinct vertices of a triangle of the surface lie on a common side of it.** -/
theorem faceEdges_SCell (hd : PolygonData vc ec) : FaceEdges (surfaceRank_SCell hc hd) := by
  intro v v' f hv hv' hf hvf hv'f hne
  -- the three sides of `tr1 p`
  have Ebed : ∀ p : Fin M, toS vc ec hc (vtx (vc p)) < toS vc ec hc (bed (ec p)) ∧
      toS vc ec hc (vtx (vc (p + 1))) < toS vc ec hc (bed (ec p)) ∧
      toS vc ec hc (bed (ec p)) < toS vc ec hc (tr1 p) := fun p =>
    ⟨(lt_bed_iff hc).2 (Or.inl rfl), (lt_bed_iff hc).2 (Or.inr rfl),
      (bed_lt_iff hc).2 ⟨p, rfl, rfl⟩⟩
  have Egdi : ∀ p : Fin M, toS vc ec hc (vtx (vc p)) < toS vc ec hc (gdi p) ∧
      toS vc ec hc (cvx (p + 1)) < toS vc ec hc (gdi p) := fun p =>
    ⟨(lt_gdi_iff hc).2 (Or.inl rfl), (lt_gdi_iff hc).2 (Or.inr rfl)⟩
  have Edia : ∀ p : Fin M, toS vc ec hc (vtx (vc p)) < toS vc ec hc (dia p) ∧
      toS vc ec hc (cvx p) < toS vc ec hc (dia p) := fun p =>
    ⟨(lt_dia_iff hc).2 (Or.inl rfl), (lt_dia_iff hc).2 (Or.inr rfl)⟩
  have Eced : ∀ p : Fin M, toS vc ec hc (cvx p) < toS vc ec hc (ced p) ∧
      toS vc ec hc (cvx (p + 1)) < toS vc ec hc (ced p) := fun p =>
    ⟨(lt_ced_iff hc).2 (Or.inl rfl), (lt_ced_iff hc).2 (Or.inr rfl)⟩
  have Erad : ∀ p : Fin M, toS vc ec hc ctr < toS vc ec hc (rad p) ∧
      toS vc ec hc (cvx p) < toS vc ec hc (rad p) := fun p =>
    ⟨(lt_rad_iff hc).2 (Or.inl rfl), (lt_rad_iff hc).2 (Or.inr rfl)⟩
  cases f with
  | tr1 p =>
      have hdia : toS vc ec hc (dia (p + 1)) < toS vc ec hc (tr1 p) :=
        (dia_lt_iff hc).2 (Or.inr (by rw [fpred_succ]))
      have hgdi : toS vc ec hc (gdi p) < toS vc ec hc (tr1 p) := (gdi_lt_iff hc).2 (Or.inl rfl)
      rcases vtx_of_lt_tr1 hc hv hvf with rfl | rfl | rfl <;>
        rcases vtx_of_lt_tr1 hc hv' hv'f with rfl | rfl | rfl
      · exact absurd rfl hne
      · exact ⟨bed (ec p), (Ebed p).1, (Ebed p).2.1, (Ebed p).2.2⟩
      · exact ⟨gdi p, (Egdi p).1, (Egdi p).2, hgdi⟩
      · exact ⟨bed (ec p), (Ebed p).2.1, (Ebed p).1, (Ebed p).2.2⟩
      · exact absurd rfl hne
      · exact ⟨dia (p + 1), (Edia (p + 1)).1, (Edia (p + 1)).2, hdia⟩
      · exact ⟨gdi p, (Egdi p).2, (Egdi p).1, hgdi⟩
      · exact ⟨dia (p + 1), (Edia (p + 1)).2, (Edia (p + 1)).1, hdia⟩
      · exact absurd rfl hne
  | tr2 p =>
      have hced : toS vc ec hc (ced p) < toS vc ec hc (tr2 p) := (ced_lt_iff hc).2 (Or.inl rfl)
      have hdia : toS vc ec hc (dia p) < toS vc ec hc (tr2 p) := (dia_lt_iff hc).2 (Or.inl rfl)
      have hgdi : toS vc ec hc (gdi p) < toS vc ec hc (tr2 p) := (gdi_lt_iff hc).2 (Or.inr rfl)
      rcases vtx_of_lt_tr2 hc hv hvf with rfl | rfl | rfl <;>
        rcases vtx_of_lt_tr2 hc hv' hv'f with rfl | rfl | rfl
      · exact absurd rfl hne
      · exact ⟨dia p, (Edia p).1, (Edia p).2, hdia⟩
      · exact ⟨gdi p, (Egdi p).1, (Egdi p).2, hgdi⟩
      · exact ⟨dia p, (Edia p).2, (Edia p).1, hdia⟩
      · exact absurd rfl hne
      · exact ⟨ced p, (Eced p).1, (Eced p).2, hced⟩
      · exact ⟨gdi p, (Egdi p).2, (Egdi p).1, hgdi⟩
      · exact ⟨ced p, (Eced p).2, (Eced p).1, hced⟩
      · exact absurd rfl hne
  | inn p =>
      have hced : toS vc ec hc (ced p) < toS vc ec hc (inn p) := (ced_lt_iff hc).2 (Or.inr rfl)
      have hrad : toS vc ec hc (rad p) < toS vc ec hc (inn p) := (rad_lt_iff hc).2 (Or.inl rfl)
      have hrad' : toS vc ec hc (rad (p + 1)) < toS vc ec hc (inn p) :=
        (rad_lt_iff hc).2 (Or.inr (by rw [fpred_succ]))
      rcases vtx_of_lt_inn hc hv hvf with rfl | rfl | rfl <;>
        rcases vtx_of_lt_inn hc hv' hv'f with rfl | rfl | rfl
      · exact absurd rfl hne
      · exact ⟨rad p, (Erad p).1, (Erad p).2, hrad⟩
      · exact ⟨rad (p + 1), (Erad (p + 1)).1, (Erad (p + 1)).2, hrad'⟩
      · exact ⟨rad p, (Erad p).2, (Erad p).1, hrad⟩
      · exact absurd rfl hne
      · exact ⟨ced p, (Eced p).1, (Eced p).2, hced⟩
      · exact ⟨rad (p + 1), (Erad (p + 1)).2, (Erad (p + 1)).1, hrad'⟩
      · exact ⟨ced p, (Eced p).2, (Eced p).1, hced⟩
      · exact absurd rfl hne
  | _ => simp [surfaceRank_SCell, Cell.rk] at hf

/-! ### The triangles of the surface are connected through shared edges -/

variable (hd : PolygonData vc ec)

omit [Fintype κ] [Fintype ι] [DecidableEq κ] [DecidableEq ι] in
/-- The two triangles of the collar at the position `p` share the edge `gdi p`. -/
theorem faceAdj_tr1_tr2 (p : Fin M) :
    FaceAdj (surfaceRank_SCell hc hd) (tr1 p) (tr2 p) :=
  ⟨gdi p, rfl, (gdi_lt_iff hc).2 (Or.inl rfl), (gdi_lt_iff hc).2 (Or.inr rfl)⟩

omit [Fintype κ] [Fintype ι] [DecidableEq κ] [DecidableEq ι] in
/-- The inner triangle of the collar and the triangle of the fan at `p` share the edge `ced p`. -/
theorem faceAdj_tr2_inn (p : Fin M) :
    FaceAdj (surfaceRank_SCell hc hd) (tr2 p) (inn p) :=
  ⟨ced p, rfl, (ced_lt_iff hc).2 (Or.inl rfl), (ced_lt_iff hc).2 (Or.inr rfl)⟩

omit [Fintype κ] [Fintype ι] [DecidableEq κ] [DecidableEq ι] in
/-- Consecutive triangles of the fan share a radius. -/
theorem faceAdj_inn_inn (p : Fin M) :
    FaceAdj (surfaceRank_SCell hc hd) (inn p) (inn (p + 1)) :=
  ⟨rad (p + 1), rfl, (rad_lt_iff hc).2 (Or.inr (by rw [fpred_succ])),
    (rad_lt_iff hc).2 (Or.inl rfl)⟩

omit [Fintype κ] [Fintype ι] [DecidableEq κ] [DecidableEq ι] in
/-- Face adjacency is symmetric. -/
theorem faceAdj_symm {f f' : SCell vc ec hc} (h : FaceAdj (surfaceRank_SCell hc hd) f f') :
    FaceAdj (surfaceRank_SCell hc hd) f' f := by
  obtain ⟨e, he, h1, h2⟩ := h
  exact ⟨e, he, h2, h1⟩

omit [Fintype κ] [Fintype ι] [DecidableEq κ] [DecidableEq ι] in
/-- Every triangle of the fan is reached from the one at the position `0`. -/
theorem conn_inn_zero (p : Fin M) :
    ReflTransGen (FaceAdj (surfaceRank_SCell hc hd)) (inn 0) (inn p) := by
  have key : ∀ k : ℕ, ∀ r : Fin M, r.val = k →
      ReflTransGen (FaceAdj (surfaceRank_SCell hc hd)) (inn 0) (inn r) := by
    intro k
    induction k with
    | zero =>
        intro r hr
        have : r = 0 := by
          apply Fin.ext
          simpa [Fin.val_zero] using hr
        subst this
        exact ReflTransGen.refl
    | succ n ih =>
        intro r hr
        have hval : (fpred r).val = n := by
          rw [fpred_val, if_neg (by omega)]
          omega
        have hstep : FaceAdj (surfaceRank_SCell hc hd) (inn (fpred r)) (inn r) := by
          have := faceAdj_inn_inn hc hd (fpred r)
          rwa [fpred_add_one] at this
        exact (ih (fpred r) hval).tail hstep
  exact key p.val p rfl

omit [Fintype κ] [Fintype ι] [DecidableEq κ] [DecidableEq ι] in
/-- Every triangle of the surface is reached from the triangle `inn 0` of the fan. -/
theorem conn_from_inn_zero (f : SCell vc ec hc) (hf : Cell.rk f = 2) :
    ReflTransGen (FaceAdj (surfaceRank_SCell hc hd)) (inn 0) f := by
  cases f with
  | tr1 p =>
      exact ((conn_inn_zero hc hd p).tail
        (faceAdj_symm hc hd (faceAdj_tr2_inn hc hd p))).tail
        (faceAdj_symm hc hd (faceAdj_tr1_tr2 hc hd p))
  | tr2 p =>
      exact (conn_inn_zero hc hd p).tail (faceAdj_symm hc hd (faceAdj_tr2_inn hc hd p))
  | inn p => exact conn_inn_zero hc hd p
  | _ => simp [Cell.rk] at hf

omit [Fintype κ] [Fintype ι] [DecidableEq κ] [DecidableEq ι] in
/-- **The triangles of the surface are connected through shared edges.** -/
theorem facesConnected_SCell (hd : PolygonData vc ec) : FacesConnected (surfaceRank_SCell hc hd) := by
  intro f f' hf hf'
  have hsymm : Symmetric (FaceAdj (surfaceRank_SCell hc hd)) :=
    fun _ _ h => faceAdj_symm hc hd h
  letI : Std.Symm (FaceAdj (surfaceRank_SCell hc hd)) := ⟨fun _ _ h => hsymm h⟩
  exact (ReflTransGen.stdSymm.symm _ _ (conn_from_inn_zero hc hd f hf)).trans
    (conn_from_inn_zero hc hd f' hf')

/-! ### The dual graph of the triangulation, and the collapse -/

omit [Fintype κ] [Fintype ι] in
/-- **The dual graph of the triangulation of the surface is connected.** -/
theorem dual_connected_SCell (hd : PolygonData vc ec) :
    ∀ σ σ' : Finset (SCell vc ec hc), IsTri (orderComplex (SCell vc ec hc)) σ →
      IsTri (orderComplex (SCell vc ec hc)) σ' →
      ReflTransGen (TriAdj (orderComplex (SCell vc ec hc))) σ σ' :=
  (surfaceRank_SCell hc hd).dual_connected (faceEdges_SCell hc hd) (facesConnected_SCell hc hd)

omit [Fintype κ] [Fintype ι] in
/-- Every cell of the surface is a vertex of a triangle of the triangulation. -/
theorem cover_SCell (hd : PolygonData vc ec) (v : SCell vc ec hc) :
    ∃ σ, IsTri (orderComplex (SCell vc ec hc)) σ ∧ v ∈ σ := by
  obtain ⟨s, hs, hcard, hv⟩ := (surfaceRank_SCell hc hd).vertexInTriangle v
  exact ⟨s, ⟨hs, hcard⟩, hv⟩

omit [Fintype κ] [Fintype ι] in
/-- The flag `ctr < rad 0 < inn 0` is a triangle of the triangulation. -/
theorem isTri_base_SCell :
    IsTri (orderComplex (SCell vc ec hc)) ({ctr, rad 0, inn 0} : Finset (SCell vc ec hc)) :=
  isTri_of_flag ((lt_rad_iff hc).2 (Or.inl rfl)) ((rad_lt_iff hc).2 (Or.inl rfl))

/-- **Lemma 3.2 (ii) for the surface of the block.**  All three-cubes of the truncated cube
complex over the triangulation of the closed surface `SCell vc ec hc` are removed by elementary
collapses, leaving a two-dimensional spine. -/
theorem exists_spine_collapse_SCell (hd : PolygonData vc ec) :
    ∃ l : List (Cube (SCell vc ec hc)),
      Collapse.IsCollapse (spineInc (orderComplex (SCell vc ec hc))) l
        (topCubes (orderComplex (SCell vc ec hc))) :=
  exists_spine_collapse_of_surface (edgeInTwoTriangles_SCell hc hd) (dual_connected_SCell hc hd)
    (cover_SCell hc hd) (isTri_base_SCell hc)

end Dual

end Davis
end FiniteChains
