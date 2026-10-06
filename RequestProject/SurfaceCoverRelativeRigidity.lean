module

public import RequestProject.GenusReceivedPolygonCoefficient
public import RequestProject.SurfaceDual

@[expose] public section

/-! Relative coefficient propagation in actual covers of the polygon surface. -/
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains.Comb
open ASC
variable {P Q : Type} [PartialOrder P] [PartialOrder Q]
  {f : P → Q} (hf : IsPosetCover f)

theorem cover_lt_of_image {a b : P} (hab : a ≤ b) (h : f a < f b) : a < b :=
  lt_of_le_of_ne hab (fun he => h.ne (congrArg f he))

/-- All local surface incidences lift through a genuine poset cover. -/
noncomputable def coveredSurfaceRank (S : SurfaceRank Q) : SurfaceRank P where
  rk a := S.rk (f a)
  rk_lt_of_lt h := S.rk_lt_of_lt (hf.strictMono h)
  rk_le_two a := S.rk_le_two (f a)
  two_vertices e he := by
    obtain ⟨a, b, hab, ha, hb, hall⟩ := S.two_vertices (f e) he
    obtain ⟨a', ⟨ha'e, hfa⟩, _⟩ := hf.down e a ha.le
    obtain ⟨b', ⟨hb'e, hfb⟩, _⟩ := hf.down e b hb.le
    have ha' : a' < e := cover_lt_of_image ha'e (hfa.symm ▸ ha)
    have hb' : b' < e := cover_lt_of_image hb'e (hfb.symm ▸ hb)
    refine ⟨a', b', ?_, ha', hb', ?_⟩
    · intro heq
      exact hab (hfa.symm.trans ((congrArg f heq).trans hfb))
    · intro z hz
      rcases hall (f z) (hf.strictMono hz) with hz' | hz'
      · exact Or.inl (hf.down_inj hz.le ha'e (hz'.trans hfa.symm))
      · exact Or.inr (hf.down_inj hz.le hb'e (hz'.trans hfb.symm))
  two_faces e he := by
    obtain ⟨a, b, hab, ha, hb, hall⟩ := S.two_faces (f e) he
    obtain ⟨a', ⟨hea', hfa⟩, _⟩ := hf.up e a ha.le
    obtain ⟨b', ⟨heb', hfb⟩, _⟩ := hf.up e b hb.le
    have ha' : e < a' := cover_lt_of_image hea' (hfa.symm ▸ ha)
    have hb' : e < b' := cover_lt_of_image heb' (hfb.symm ▸ hb)
    refine ⟨a', b', ?_, ha', hb', ?_⟩
    · intro heq
      exact hab (hfa.symm.trans ((congrArg f heq).trans hfb))
    · intro z hz
      rcases hall (f z) (hf.strictMono hz) with hz' | hz'
      · exact Or.inl (hf.up_inj hz.le hea' (hz'.trans hfa.symm))
      · exact Or.inr (hf.up_inj hz.le heb' (hz'.trans hfb.symm))
  two_edges v t hv ht hvt := by
    obtain ⟨a, b, hab, ha, hb, hall⟩ := S.two_edges (f v) (f t) hv ht (hf.strictMono hvt)
    obtain ⟨a', hva', ha't, hfa⟩ := hf.exists_interval_lift hvt.le a ha.1.le ha.2.le
    obtain ⟨b', hvb', hb't, hfb⟩ := hf.exists_interval_lift hvt.le b hb.1.le hb.2.le
    have ha' : v < a' ∧ a' < t :=
      ⟨cover_lt_of_image hva' (hfa.symm ▸ ha.1),
        cover_lt_of_image ha't (hfa.symm ▸ ha.2)⟩
    have hb' : v < b' ∧ b' < t :=
      ⟨cover_lt_of_image hvb' (hfb.symm ▸ hb.1),
        cover_lt_of_image hb't (hfb.symm ▸ hb.2)⟩
    refine ⟨a', b', ?_, ha', hb', ?_⟩
    · intro heq
      exact hab (hfa.symm.trans ((congrArg f heq).trans hfb))
    · intro z hz
      rcases hall (f z) ⟨hf.strictMono hz.1, hf.strictMono hz.2⟩ with hz' | hz'
      · exact Or.inl (hf.up_inj hz.1.le hva' (hz'.trans hfa.symm))
      · exact Or.inr (hf.up_inj hz.1.le hvb' (hz'.trans hfb.symm))
  exists_face x := by
    obtain ⟨t, ht, hxt⟩ := S.exists_face (f x)
    obtain ⟨t', ⟨hxt', hft⟩, _⟩ := hf.up x t hxt
    exact ⟨t', hft.symm ▸ ht, hxt'⟩
  exists_vertex t ht := by
    obtain ⟨v, hv, hvt⟩ := S.exists_vertex (f t) ht
    obtain ⟨v', ⟨hv't, hfv⟩, _⟩ := hf.down t v hvt.le
    exact ⟨v', hfv.symm ▸ hv, cover_lt_of_image hv't (hfv.symm ▸ hvt)⟩

/-- Triangular face geometry is preserved in every actual lifted face. -/
theorem coveredSurfaceRank_faceEdges (S : SurfaceRank Q) (hfe : FaceEdges S) :
    FaceEdges (coveredSurfaceRank hf S) := by
  intro v w t hv hw ht hvt hwt hvw
  have hne : f v ≠ f w := fun he => hvw (hf.down_inj hvt.le hwt.le he)
  obtain ⟨e, hve, hwe, het⟩ := hfe (f v) (f w) (f t) hv hw ht
    (hf.strictMono hvt) (hf.strictMono hwt) hne
  obtain ⟨e', hve', he't, hfe'⟩ := hf.exists_interval_lift hvt.le e hve.le het.le
  have hwe' : w ≤ e' := hf.le_of_le_below hwt.le he't (hfe'.symm ▸ hwe.le)
  exact ⟨e', cover_lt_of_image hve' (hfe'.symm ▸ hve),
    cover_lt_of_image hwe' (hfe'.symm ▸ hwe),
    cover_lt_of_image he't (hfe'.symm ▸ het)⟩

section Coefficients
variable (S : SurfaceRank P)
include S

theorem triangle_rank (r : StrictOrdTri P) :
    S.rk r.1.1 = 0 ∧ S.rk r.1.2.1 = 1 ∧ S.rk r.1.2.2 = 2 :=
  S.rk_flag r.2.1 r.2.2

/-- At a fixed edge/face incidence the only boundary contributions are the
two actual flags formed with the edge's endpoints. -/
theorem surfaceBoundary_vertex_pair {a b e t : P}
    (hae : a < e) (hbe : b < e) (het : e < t) (hab : a ≠ b)
    (hall : ∀ x, x < e → x = a ∨ x = b)
    (c : StrictOrdTri P →₀ ℤ) :
    Comb.bdry2 (strictOrderCx P) c ⟨(e, t), het⟩ =
      c ⟨(a, e, t), hae, het⟩ + c ⟨(b, e, t), hbe, het⟩ := by
  classical
  let A : StrictOrdTri P := ⟨(a, e, t), hae, het⟩
  let B : StrictOrdTri P := ⟨(b, e, t), hbe, het⟩
  let E : StrictOrdEdge P := ⟨(e, t), het⟩
  have hAB : A ≠ B := fun h => hab (congrArg (fun r : StrictOrdTri P => r.1.1) h)
  have hrk := S.rk_flag hae het
  have h01 (r : StrictOrdTri P) : strictTriangleEdge01 r ≠ E := by
    intro h
    have hh := congrArg (fun d : StrictOrdEdge P => S.rk d.1.1) h
    have hr := triangle_rank S r
    change S.rk r.1.1 = S.rk e at hh
    omega
  have h02 (r : StrictOrdTri P) : strictTriangleEdge02 r ≠ E := by
    intro h
    have hh := congrArg (fun d : StrictOrdEdge P => S.rk d.1.1) h
    have hr := triangle_rank S r
    change S.rk r.1.1 = S.rk e at hh
    omega
  have h12 (r : StrictOrdTri P) : strictTriangleEdge12 r = E ↔ r = A ∨ r = B := by
    constructor
    · intro h
      have he : r.1.2.1 = e := congrArg (fun d : StrictOrdEdge P => d.1.1) h
      have ht : r.1.2.2 = t := congrArg (fun d : StrictOrdEdge P => d.1.2) h
      rcases hall r.1.1 (he ▸ r.2.1) with hv | hv
      · exact Or.inl (Subtype.ext (Prod.ext hv (Prod.ext he ht)))
      · exact Or.inr (Subtype.ext (Prod.ext hv (Prod.ext he ht)))
    · rintro (rfl | rfl) <;> rfl
  change Comb.bdry2 (strictOrderCx P) c E = c A + c B
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd => simp only [map_add, Finsupp.add_apply, hc, hd]; ring
  | single r n =>
    rw (config := { transparency := .default }) [strictTriangle_bdry2_single, Finsupp.sub_apply, Finsupp.add_apply]
    by_cases hA : r = A
    · subst r
      simp [Finsupp.single_apply, h01, h02, h12, hAB]
    · by_cases hB : r = B
      · subst r
        simp [Finsupp.single_apply, h01, h02, h12, hAB.symm]
      · simp [h01, h02, h12, hA, hB]

/-- At a vertex/face diagonal the two incident flags both occur negatively. -/
theorem surfaceBoundary_edge_pair {v a b t : P}
    (hva : v < a) (hat : a < t) (hvb : v < b) (hbt : b < t) (hab : a ≠ b)
    (hall : ∀ x, v < x ∧ x < t → x = a ∨ x = b)
    (c : StrictOrdTri P →₀ ℤ) :
    Comb.bdry2 (strictOrderCx P) c ⟨(v, t), hva.trans hat⟩ =
      -c ⟨(v, a, t), hva, hat⟩ - c ⟨(v, b, t), hvb, hbt⟩ := by
  classical
  let A : StrictOrdTri P := ⟨(v, a, t), hva, hat⟩
  let B : StrictOrdTri P := ⟨(v, b, t), hvb, hbt⟩
  let E : StrictOrdEdge P := ⟨(v, t), hva.trans hat⟩
  have hAB : A ≠ B := fun h => hab (congrArg (fun r : StrictOrdTri P => r.1.2.1) h)
  have hrk := S.rk_flag hva hat
  have h01 (r : StrictOrdTri P) : strictTriangleEdge01 r ≠ E := by
    intro h
    have hh := congrArg (fun d : StrictOrdEdge P => S.rk d.1.2) h
    have hr := triangle_rank S r
    change S.rk r.1.2.1 = S.rk t at hh
    omega
  have h12 (r : StrictOrdTri P) : strictTriangleEdge12 r ≠ E := by
    intro h
    have hh := congrArg (fun d : StrictOrdEdge P => S.rk d.1.1) h
    have hr := triangle_rank S r
    change S.rk r.1.2.1 = S.rk v at hh
    omega
  have h02 (r : StrictOrdTri P) : strictTriangleEdge02 r = E ↔ r = A ∨ r = B := by
    constructor
    · intro h
      have hv : r.1.1 = v := congrArg (fun d : StrictOrdEdge P => d.1.1) h
      have ht : r.1.2.2 = t := congrArg (fun d : StrictOrdEdge P => d.1.2) h
      rcases hall r.1.2.1 ⟨hv ▸ r.2.1, ht ▸ r.2.2⟩ with he | he
      · exact Or.inl (Subtype.ext (Prod.ext hv (Prod.ext he ht)))
      · exact Or.inr (Subtype.ext (Prod.ext hv (Prod.ext he ht)))
    · rintro (rfl | rfl) <;> rfl
  change Comb.bdry2 (strictOrderCx P) c E = -c A - c B
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd => simp only [map_add, Finsupp.add_apply, hc, hd]; ring
  | single r n =>
    rw (config := { transparency := .default }) [strictTriangle_bdry2_single, Finsupp.sub_apply, Finsupp.add_apply]
    by_cases hA : r = A
    · subst r
      simp [Finsupp.single_apply, h01, h12, h02, hAB]
    · by_cases hB : r = B
      · subst r
        simp [Finsupp.single_apply, h01, h12, h02, hAB.symm]
      · simp [h01, h12, h02, hA, hB]

/-- At a vertex/edge incidence the two flags in the adjacent faces occur positively. -/
theorem surfaceBoundary_face_pair {v e a b : P}
    (hve : v < e) (hea : e < a) (heb : e < b) (hab : a ≠ b)
    (hall : ∀ x, e < x → x = a ∨ x = b)
    (c : StrictOrdTri P →₀ ℤ) :
    Comb.bdry2 (strictOrderCx P) c ⟨(v, e), hve⟩ =
      c ⟨(v, e, a), hve, hea⟩ + c ⟨(v, e, b), hve, heb⟩ := by
  classical
  let A : StrictOrdTri P := ⟨(v, e, a), hve, hea⟩
  let B : StrictOrdTri P := ⟨(v, e, b), hve, heb⟩
  let E : StrictOrdEdge P := ⟨(v, e), hve⟩
  have hAB : A ≠ B := fun h => hab (congrArg (fun r : StrictOrdTri P => r.1.2.2) h)
  have hrk := S.rk_flag hve hea
  have h12 (r : StrictOrdTri P) : strictTriangleEdge12 r ≠ E := by
    intro h
    have hh := congrArg (fun d : StrictOrdEdge P => S.rk d.1.1) h
    have hr := triangle_rank S r
    change S.rk r.1.2.1 = S.rk v at hh
    omega
  have h02 (r : StrictOrdTri P) : strictTriangleEdge02 r ≠ E := by
    intro h
    have hh := congrArg (fun d : StrictOrdEdge P => S.rk d.1.2) h
    have hr := triangle_rank S r
    change S.rk r.1.2.2 = S.rk e at hh
    omega
  have h01 (r : StrictOrdTri P) : strictTriangleEdge01 r = E ↔ r = A ∨ r = B := by
    constructor
    · intro h
      have hv : r.1.1 = v := congrArg (fun d : StrictOrdEdge P => d.1.1) h
      have he : r.1.2.1 = e := congrArg (fun d : StrictOrdEdge P => d.1.2) h
      rcases hall r.1.2.2 (he ▸ r.2.2) with ht | ht
      · exact Or.inl (Subtype.ext (Prod.ext hv (Prod.ext he ht)))
      · exact Or.inr (Subtype.ext (Prod.ext hv (Prod.ext he ht)))
    · rintro (rfl | rfl) <;> rfl
  change Comb.bdry2 (strictOrderCx P) c E = c A + c B
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd => simp only [map_add, Finsupp.add_apply, hc, hd]; ring
  | single r n =>
    rw (config := { transparency := .default }) [strictTriangle_bdry2_single, Finsupp.sub_apply, Finsupp.add_apply]
    by_cases hA : r = A
    · subst r
      simp [Finsupp.single_apply, h01, h12, h02, hAB]
    · by_cases hB : r = B
      · subst r
        simp [Finsupp.single_apply, h01, h12, h02, hAB.symm]
      · simp [h01, h12, h02, hA, hB]

end Coefficients

theorem exactlyTwo_exhaust {X : Type} {R : X → Prop} (h : ExactlyTwo R)
    {a b : X} (ha : R a) (hb : R b) (hab : a ≠ b) :
    ∀ x, R x → x = a ∨ x = b := by
  obtain ⟨x, y, _, _, _, hall⟩ := h
  rcases hall a ha with hax | hay
  · rcases hall b hb with hbx | hby
    · exact False.elim (hab (hax.trans hbx.symm))
    · intro z hz
      rcases hall z hz with hzx | hzy
      · exact Or.inl (hzx.trans hax.symm)
      · exact Or.inr (hzy.trans hby.symm)
  · rcases hall b hb with hbx | hby
    · intro z hz
      rcases hall z hz with hzx | hzy
      · exact Or.inr (hzx.trans hbx.symm)
      · exact Or.inl (hzy.trans hay.symm)
    · exact False.elim (hab (hay.trans hby.symm))

section Propagation
variable (S : SurfaceRank P) (c : StrictOrdTri P →₀ ℤ)
include S

/-- A zero flag coefficient propagates across a vertex change inside a face. -/
theorem surface_zero_change_vertex {a b e t : P}
    (hae : a < e) (hbe : b < e) (het : e < t)
    (hd : Comb.bdry2 (strictOrderCx P) c ⟨(e, t), het⟩ = 0)
    (hz : c ⟨(a, e, t), hae, het⟩ = 0) :
    c ⟨(b, e, t), hbe, het⟩ = 0 := by
  by_cases hab : a = b
  · subst b
    exact hz
  · have he : S.rk e = 1 := (S.rk_flag hae het).2.1
    have hpair := surfaceBoundary_vertex_pair S hae hbe het hab
      (exactlyTwo_exhaust (S.two_vertices e he) hae hbe hab) c
    rw (config := { transparency := .default }) [hd, hz] at hpair
    omega

/-- A zero flag coefficient propagates across an edge change inside a face. -/
theorem surface_zero_change_edge {v a b t : P}
    (hva : v < a) (hat : a < t) (hvb : v < b) (hbt : b < t)
    (hd : Comb.bdry2 (strictOrderCx P) c ⟨(v, t), hva.trans hat⟩ = 0)
    (hz : c ⟨(v, a, t), hva, hat⟩ = 0) :
    c ⟨(v, b, t), hvb, hbt⟩ = 0 := by
  by_cases hab : a = b
  · subst b
    exact hz
  · have hrk := S.rk_flag hva hat
    have hpair := surfaceBoundary_edge_pair S hva hat hvb hbt hab
      (exactlyTwo_exhaust (S.two_edges v t hrk.1 hrk.2.2 (hva.trans hat))
        ⟨hva, hat⟩ ⟨hvb, hbt⟩ hab) c
    rw (config := { transparency := .default }) [hd, hz] at hpair
    omega

/-- A zero flag coefficient crosses an actual shared old edge as soon as the
relative boundary vanishes at that edge incidence. -/
theorem surface_zero_change_face {v e a b : P}
    (hve : v < e) (hea : e < a) (heb : e < b)
    (hd : Comb.bdry2 (strictOrderCx P) c ⟨(v, e), hve⟩ = 0)
    (hz : c ⟨(v, e, a), hve, hea⟩ = 0) :
    c ⟨(v, e, b), hve, heb⟩ = 0 := by
  by_cases hab : a = b
  · subst b
    exact hz
  · have he : S.rk e = 1 := (S.rk_flag hve hea).2.1
    have hpair := surfaceBoundary_face_pair S hve hea heb hab
      (exactlyTwo_exhaust (S.two_faces e he) hea heb hab) c
    rw (config := { transparency := .default }) [hd, hz] at hpair
    omega

/-- One zero flag coefficient determines all flags of its actual triangular
face.  Only the internal vertex/face and edge/face boundary entries are used. -/
theorem surface_zero_in_face (hfe : FaceEdges S)
    (hrel : ∀ e : StrictOrdEdge P, S.rk e.1.2 = 2 →
      Comb.bdry2 (strictOrderCx P) c e = 0)
    (a b : StrictOrdTri P) (htop : a.1.2.2 = b.1.2.2) (ha : c a = 0) : c b = 0 := by
  rcases a with ⟨⟨v, e, t⟩, hve, het⟩
  rcases b with ⟨⟨w, d, t'⟩, hwd, hdt⟩
  dsimp only at htop
  subst t'
  have hrk := S.rk_flag hve het
  have hrk' := S.rk_flag hwd hdt
  by_cases hvw : v = w
  · subst w
    exact surface_zero_change_edge S c hve het hwd hdt (hrel _ hrk.2.2) ha
  · obtain ⟨r, hvr, hwr, hrt⟩ := hfe v w t hrk.1 hrk'.1 hrk.2.2
      (hve.trans het) (hwd.trans hdt) hvw
    have h₁ : c ⟨(v, r, t), hvr, hrt⟩ = 0 :=
      surface_zero_change_edge S c hve het hvr hrt (hrel _ hrk.2.2) ha
    have h₂ : c ⟨(w, r, t), hwr, hrt⟩ = 0 :=
      surface_zero_change_vertex S c hvr hwr hrt (hrel _ hrk.2.2) h₁
    exact surface_zero_change_edge S c hwr hrt hwd hdt (hrel _ hrk.2.2) h₂

end Propagation
end FiniteChains.Comb

namespace FiniteChains.Davis
open Comb ASC Cell
variable {κ ι P : Type} {M : ℕ} [NeZero M] [PartialOrder P]
  {vc : Fin M → κ} {ec : Fin M → ι} (hc : Compat vc ec)
  (hd : PolygonData vc ec) (f : P → SCell vc ec hc) (hf : IsPosetCover f)

/-- The boundary of a relative surface chain is supported on the actual
identified polygon boundary, in both endpoints of each edge. -/
def PolygonRelativeChain (c : StrictOrdTri P →₀ ℤ) : Prop :=
  ∀ e ∈ (Comb.bdry2 (strictOrderCx P) c).support,
    InPolygonBoundary hc (f e.1.1) ∧ InPolygonBoundary hc (f e.1.2)

theorem polygonBoundary_rank_le_one {a : SCell vc ec hc}
    (ha : InPolygonBoundary hc a) : Cell.rk a ≤ 1 := by
  cases a <;> simp_all [InPolygonBoundary, Cell.rk]

theorem polygonRelative_boundary_zero_of_target
    (c : StrictOrdTri P →₀ ℤ) (hrel : PolygonRelativeChain hc f c)
    (e : StrictOrdEdge P) (he : ¬ InPolygonBoundary hc (f e.1.2)) :
    Comb.bdry2 (strictOrderCx P) c e = 0 := by
  by_contra hn
  exact he ((hrel e (Finsupp.mem_support_iff.mpr hn)).2)

theorem polygonRelative_boundary_zero_at_face
    (c : StrictOrdTri P →₀ ℤ) (hrel : PolygonRelativeChain hc f c)
    (e : StrictOrdEdge P) (he : Cell.rk (f e.1.2) = 2) :
    Comb.bdry2 (strictOrderCx P) c e = 0 := by
  apply polygonRelative_boundary_zero_of_target hc f c hrel e
  intro hb
  have hr := polygonBoundary_rank_le_one hc hb
  omega

include hd hf in
theorem polygonRelative_zero_in_face
    (c : StrictOrdTri P →₀ ℤ) (hrel : PolygonRelativeChain hc f c)
    (a b : StrictOrdTri P) (ht : a.1.2.2 = b.1.2.2) (ha : c a = 0) : c b = 0 :=
  surface_zero_in_face (coveredSurfaceRank hf (surfaceRank_SCell hc hd)) c
    (coveredSurfaceRank_faceEdges hf (surfaceRank_SCell hc hd) (faceEdges_SCell hc hd))
    (polygonRelative_boundary_zero_at_face hc f c hrel) a b ht ha

include hd in
/-- Every flag of every actual lifted inner triangle is forced by the pole
coefficients.  This propagates across all six flags, not only the two centre flags. -/
theorem polygonRelative_zero_inner
    (c : StrictOrdTri P →₀ ℤ) (hrel : PolygonRelativeChain hc f c)
    (hpoles : polygonCoverPoleCoefficients hc f hf c = 0)
    (p : Fin M) (t : StrictOrdTri P) (ht : f t.1.2.2 = cI hc p) : c t = 0 := by
  let S := coveredSurfaceRank hf (surfaceRank_SCell hc hd)
  have hM : 2 ≤ M := by have := hd.three_le; omega
  have hsource : ∀ e : StrictOrdEdge P,
      f e.1.1 = cC hc → Comb.bdry2 (strictOrderCx P) c e = 0 :=
    polygonCover_boundary_vanishes_at_poles hc f c (fun e he => (hrel e he).1)
  have hpole : ∀ a : StrictOrdTri P, f a.1.1 = cC hc → c a = 0 := by
    intro a ha
    have he : polygonCoverPoleCoefficients hc f hf c =
        polygonCoverPoleCoefficients hc f hf 0 := by rw (config := { transparency := .default }) [map_zero]; exact hpoles
    have hh := polygonCoverPole_relative_ext hc f hf hM c 0 hsource
      (by intro e _; simp) he a ha
    exact hh
  obtain ⟨v, ⟨hvt, hfv⟩, _⟩ := hf.down t.1.2.2 (cC hc)
    (by rw (config := { transparency := .default }) [ht]; exact (ctr_lt_inn hc p).le)
  have hvT : v < t.1.2.2 := lt_of_le_of_ne hvt (by
    intro he
    have hh := hfv.symm.trans ((congrArg f he).trans ht)
    exact (ctr_lt_inn hc p).ne hh)
  have hvrk : S.rk v = 0 := by change Cell.rk (f v) = 0; rw (config := { transparency := .default }) [hfv]; rfl
  have hTrk : S.rk t.1.2.2 = 2 := (S.rk_flag t.2.1 t.2.2).2.2
  obtain ⟨e, _, _, ⟨hve, heT⟩, _, _⟩ := S.two_edges v t.1.2.2 hvrk hTrk hvT
  let a : StrictOrdTri P := ⟨(v, e, t.1.2.2), hve, heT⟩
  exact polygonRelative_zero_in_face hc hd f hf c hrel a t rfl (hpole a hfv)

include hd hf in
/-- Move a zero coefficient from all flags over one actual face across an
internal edge to all flags over its adjacent actual face. -/
theorem polygonRelative_zero_across
    (c : StrictOrdTri P →₀ ℤ) (hrel : PolygonRelativeChain hc f c)
    (t : StrictOrdTri P) (e a : SCell vc ec hc)
    (herk : Cell.rk e = 1) (het : e < f t.1.2.2) (hea : e < a)
    (heboundary : ¬ InPolygonBoundary hc e)
    (ha : ∀ z : StrictOrdTri P, f z.1.2.2 = a → c z = 0) : c t = 0 := by
  let S := coveredSurfaceRank hf (surfaceRank_SCell hc hd)
  obtain ⟨d, ⟨hdT, hfd⟩, _⟩ := hf.down t.1.2.2 e het.le
  have hdT' : d < t.1.2.2 := lt_of_le_of_ne hdT (by
    intro he
    exact het.ne (hfd.symm.trans (congrArg f he)))
  obtain ⟨a', ⟨hda, hfa⟩, _⟩ := hf.up d a (by rw (config := { transparency := .default }) [hfd]; exact hea.le)
  have hda' : d < a' := lt_of_le_of_ne hda (by
    intro he
    exact hea.ne (hfd.symm.trans ((congrArg f he).trans hfa)))
  have hdrk : S.rk d = 1 := by change Cell.rk (f d) = 1; rw (config := { transparency := .default }) [hfd]; exact herk
  obtain ⟨v, _, _, hvd, _, _⟩ := S.two_vertices d hdrk
  let z : StrictOrdTri P := ⟨(v, d, a'), hvd, hda'⟩
  let w : StrictOrdTri P := ⟨(v, d, t.1.2.2), hvd, hdT'⟩
  have hbd : Comb.bdry2 (strictOrderCx P) c ⟨(v, d), hvd⟩ = 0 :=
    polygonRelative_boundary_zero_of_target hc f c hrel _ (hfd.symm ▸ heboundary)
  have hw : c w = 0 := surface_zero_change_face S c hvd hda' hdT' hbd (ha z hfa)
  exact polygonRelative_zero_in_face hc hd f hf c hrel w t rfl hw

include hd in
/-- The genuine `ced` incidence carries rigidity from the fan into every
lifted inner collar triangle. -/
theorem polygonRelative_zero_inner_collar
    (c : StrictOrdTri P →₀ ℤ) (hrel : PolygonRelativeChain hc f c)
    (hpoles : polygonCoverPoleCoefficients hc f hf c = 0)
    (p : Fin M) (t : StrictOrdTri P) (ht : f t.1.2.2 = cT2 hc p) : c t = 0 := by
  apply polygonRelative_zero_across hc hd f hf c hrel t (cF hc p) (cI hc p) rfl
  · rw (config := { transparency := .default }) [ht]
    exact lt_of_le_of_ne (cF_le_cT2 hc p) (by intro h; cases h)
  · exact lt_of_le_of_ne (cF_le_cI hc p) (by intro h; cases h)
  · exact fun h => h
  · exact polygonRelative_zero_inner hc hd f hf c hrel hpoles p

include hd in
/-- The genuine `gdi` incidence carries rigidity to every lifted outer
collar triangle.  The identified boundary is never crossed. -/
theorem polygonRelative_zero_outer_collar
    (c : StrictOrdTri P →₀ ℤ) (hrel : PolygonRelativeChain hc f c)
    (hpoles : polygonCoverPoleCoefficients hc f hf c = 0)
    (p : Fin M) (t : StrictOrdTri P) (ht : f t.1.2.2 = cT1 hc p) : c t = 0 := by
  apply polygonRelative_zero_across hc hd f hf c hrel t (cG hc p) (cT2 hc p) rfl
  · rw (config := { transparency := .default }) [ht]
    exact lt_of_le_of_ne (cG_le_cT1 hc p) (by intro h; cases h)
  · exact lt_of_le_of_ne (cG_le_cT2 hc p) (by intro h; cases h)
  · exact fun h => h
  · exact polygonRelative_zero_inner_collar hc hd f hf c hrel hpoles p

include hd in
/-- The complete relative two-chain in an actual surface cover is detected by
its actual pole coefficients, after propagation through every fan and collar
flag.  No global connectedness or group faithfulness premise is used. -/
theorem polygonRelative_zero_of_pole_coefficients
    (c : StrictOrdTri P →₀ ℤ) (hrel : PolygonRelativeChain hc f c)
    (hpoles : polygonCoverPoleCoefficients hc f hf c = 0) : c = 0 := by
  ext t
  have hrk := (surfaceRank_SCell hc hd).rk_flag (hf.strictMono t.2.1) (hf.strictMono t.2.2)
  have ht : Cell.rk (f t.1.2.2) = 2 := hrk.2.2
  generalize he : f t.1.2.2 = a at ht
  cases a with
  | inn p => exact polygonRelative_zero_inner hc hd f hf c hrel hpoles p t he
  | tr2 p => exact polygonRelative_zero_inner_collar hc hd f hf c hrel hpoles p t he
  | tr1 p => exact polygonRelative_zero_outer_collar hc hd f hf c hrel hpoles p t he
  | _ => simp [Cell.rk] at ht

theorem PolygonRelativeChain.sub {c d : StrictOrdTri P →₀ ℤ}
    (hc' : PolygonRelativeChain hc f c) (hd' : PolygonRelativeChain hc f d) :
    PolygonRelativeChain hc f (c - d) := by
  intro e he
  have hn : Comb.bdry2 (strictOrderCx P) (c - d) e ≠ 0 := Finsupp.mem_support_iff.mp he
  by_cases hce : Comb.bdry2 (strictOrderCx P) c e = 0
  · have hde : Comb.bdry2 (strictOrderCx P) d e ≠ 0 := by
      intro hd0
      apply hn
      rw (config := { transparency := .default }) [map_sub, Finsupp.sub_apply, hce, hd0, sub_self]
    exact hd' e (Finsupp.mem_support_iff.mpr hde)
  · exact hc' e (Finsupp.mem_support_iff.mpr hce)

theorem PolygonRelativeChain.zero : PolygonRelativeChain hc f (0 : StrictOrdTri P →₀ ℤ) := by
  intro e he
  simp at he

theorem PolygonRelativeChain.add {c d : StrictOrdTri P →₀ ℤ}
    (hc' : PolygonRelativeChain hc f c) (hd' : PolygonRelativeChain hc f d) :
    PolygonRelativeChain hc f (c + d) := by
  intro e he
  have hn : Comb.bdry2 (strictOrderCx P) (c + d) e ≠ 0 := Finsupp.mem_support_iff.mp he
  by_cases hce : Comb.bdry2 (strictOrderCx P) c e = 0
  · have hde : Comb.bdry2 (strictOrderCx P) d e ≠ 0 := by
      intro hd0
      apply hn
      rw (config := { transparency := .default }) [map_add, Finsupp.add_apply, hce, hd0, add_zero]
    exact hd' e (Finsupp.mem_support_iff.mpr hde)
  · exact hc' e (Finsupp.mem_support_iff.mpr hce)

theorem PolygonRelativeChain.smul {c : StrictOrdTri P →₀ ℤ}
    (hc' : PolygonRelativeChain hc f c) (n : ℤ) : PolygonRelativeChain hc f (n • c) := by
  intro e he
  have hn : Comb.bdry2 (strictOrderCx P) (n • c) e ≠ 0 := Finsupp.mem_support_iff.mp he
  have hce : Comb.bdry2 (strictOrderCx P) c e ≠ 0 := by
    intro hzero
    apply hn
    rw (config := { transparency := .default }) [map_smul, Finsupp.smul_apply, hzero, smul_zero]
  exact hc' e (Finsupp.mem_support_iff.mpr hce)

include hd in
/-- Full relative surface-chain reconstruction is unique for its finite family
of pole coefficients, including all six flags and both collar triangles. -/
theorem polygonRelative_ext
    (c d : StrictOrdTri P →₀ ℤ)
    (hc' : PolygonRelativeChain hc f c) (hd' : PolygonRelativeChain hc f d)
    (hpoles : polygonCoverPoleCoefficients hc f hf c =
      polygonCoverPoleCoefficients hc f hf d) : c = d := by
  apply sub_eq_zero.mp
  apply polygonRelative_zero_of_pole_coefficients hc hd f hf (c - d)
    (PolygonRelativeChain.sub hc f hc' hd')
  rw (config := { transparency := .default }) [map_sub, hpoles, sub_self]

end FiniteChains.Davis
