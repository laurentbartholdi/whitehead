module

public import RequestProject.BarycentricSurface
public import RequestProject.MomentAngleConnected

@[expose] public section

/-!
# The dual graph of the barycentric subdivision is connected

The collapse of Lemma 3.2 (ii), carried out for the cube complex `C(L)` in
`RequestProject/SpineCollapse.lean`, needs three combinatorial properties of `L`: every
edge lies in at most two triangles, every vertex lies in a triangle, and the dual graph of
`L` (triangles joined along shared edges) is connected.  For `L_q`, the barycentric
subdivision of a triangulation of the surface, the first two are proved in
`RequestProject/BarycentricSurface.lean`.  This file proves the third one: if the dual
graph of `K` is connected, then so is the dual graph of the barycentric subdivision.

The triangles of the subdivision are the flags `v ⊂ e ⊂ t` of `K`, and the proof is the
standard one:

* two flags with the same triangle `t` are joined by at most three moves, each changing one
  entry of the flag (the flags of a triangle form a hexagon);
* two flags whose triangles share an edge `e` are joined through the flags `(v, e, t)` and
  `(v, e, t')`, which differ in one entry;
* a path in the dual graph of `K` therefore lifts to a path of flags.
-/

namespace FiniteChains

namespace ASC

variable {V : Type} [DecidableEq V] {K : ASC V}

/-! ### Sorting a triple of pairwise comparable elements -/

theorem exists_sorted_triple {P : Type} [Preorder P] [DecidableEq P] {a b c : P}
    (hab : a ≤ b ∨ b ≤ a) (hbc : b ≤ c ∨ c ≤ b) (hac : a ≤ c ∨ c ≤ a) :
    ∃ x y z : P, ({a, b, c} : Finset P) = {x, y, z} ∧ x ≤ y ∧ y ≤ z := by
  rcases hab with hab | hab
  · rcases hbc with hbc | hbc
    · exact ⟨a, b, c, rfl, hab, hbc⟩
    · rcases hac with hac | hac
      · refine ⟨a, c, b, ?_, hac, hbc⟩
        ext x; simp; tauto
      · refine ⟨c, a, b, ?_, hac, hab⟩
        ext x; simp; tauto
  · rcases hac with hac | hac
    · refine ⟨b, a, c, ?_, hab, hac⟩
      ext x; simp; tauto
    · rcases hbc with hbc | hbc
      · refine ⟨b, c, a, ?_, hbc, hac⟩
        ext x; simp; tauto
      · refine ⟨c, b, a, ?_, hbc, hab⟩
        ext x; simp; tauto

/-! ### Triangles of the subdivision are flags -/

/-- A triangle of the barycentric subdivision is a flag `v ⊂ e ⊂ t`. -/
theorem exists_flag_of_isTri (hdim : ∀ s ∈ K.faces, s.card ≤ 3) {σ : Finset K.Face}
    (h : IsTri K.barycentric σ) :
    ∃ c₁ c₂ c₃ : K.Face, σ = {c₁, c₂, c₃} ∧ c₁ ≤ c₂ ∧ c₂ ≤ c₃ ∧
      c₁.1.card = 1 ∧ c₂.1.card = 2 ∧ c₃.1.card = 3 := by
  obtain ⟨hface, hcard⟩ := h
  obtain ⟨a, b, c, hab, hac, hbc, hσ⟩ := Finset.card_eq_three.mp hcard
  have hchain : IsChain (· ≤ ·) ((σ : Finset K.Face) : Set K.Face) := by
    rw [barycentric, mem_orderComplex] at hface; exact hface
  have hmem : ∀ x ∈ σ, (x : K.Face) ∈ ((σ : Finset K.Face) : Set K.Face) := by
    intro x hx; exact_mod_cast hx
  have hcompab : a ≤ b ∨ b ≤ a :=
    le_or_le_of_isChain hchain (hmem a (by rw [hσ]; simp)) (hmem b (by rw [hσ]; simp))
  have hcompbc : b ≤ c ∨ c ≤ b :=
    le_or_le_of_isChain hchain (hmem b (by rw [hσ]; simp)) (hmem c (by rw [hσ]; simp))
  have hcompac : a ≤ c ∨ c ≤ a :=
    le_or_le_of_isChain hchain (hmem a (by rw [hσ]; simp)) (hmem c (by rw [hσ]; simp))
  obtain ⟨x, y, z, hxyz, hxy, hyz⟩ := exists_sorted_triple hcompab hcompbc hcompac
  have hσ' : σ = {x, y, z} := by rw [hσ, hxyz]
  -- the three faces are distinct, so their cardinalities strictly increase
  have hcard3 : ({x, y, z} : Finset K.Face).card = 3 := by rw [← hσ']; exact hcard
  have hxy' : x ≠ y := by
    intro hcon
    rw [hcon] at hcard3
    have : ({y, y, z} : Finset K.Face).card ≤ 2 := by
      have : ({y, y, z} : Finset K.Face) = {y, z} := by ext w; simp
      rw [this]
      exact (Finset.card_insert_le _ _).trans (by simp)
    omega
  have hyz' : y ≠ z := by
    intro hcon
    rw [hcon] at hcard3
    have : ({x, z, z} : Finset K.Face).card ≤ 2 := by
      have : ({x, z, z} : Finset K.Face) = {x, z} := by ext w; simp
      rw [this]
      exact (Finset.card_insert_le _ _).trans (by simp)
    omega
  have hxlt : x.1.card < y.1.card :=
    Finset.card_lt_card ⟨hxy, fun hcon => hxy' (Subtype.ext (Finset.Subset.antisymm hxy hcon))⟩
  have hylt : y.1.card < z.1.card :=
    Finset.card_lt_card ⟨hyz, fun hcon => hyz' (Subtype.ext (Finset.Subset.antisymm hyz hcon))⟩
  have hx1 : 1 ≤ x.1.card := Finset.card_pos.2 x.2.2
  have hz3 : z.1.card ≤ 3 := hdim _ z.2.1
  exact ⟨x, y, z, hσ', hxy, hyz, by omega, by omega, by omega⟩

/-! ### Moves between flags -/

theorem triple_swap23 {α : Type} [DecidableEq α] (a b c : α) :
    ({a, b, c} : Finset α) = {a, c, b} := by
  ext x; simp; tauto

theorem triple_rot {α : Type} [DecidableEq α] (a b c : α) :
    ({a, b, c} : Finset α) = {b, c, a} := by
  ext x; simp; tauto

omit [DecidableEq V] in
theorem ne_of_card_ne {c c' : K.Face} (h : c.1.card ≠ c'.1.card) : c ≠ c' := by
  intro hcon
  exact h (by rw [hcon])

/-- A flag spans a triangle of the subdivision. -/
theorem isTri_flag {c₁ c₂ c₃ : K.Face} (h12 : c₁ ≤ c₂) (h23 : c₂ ≤ c₃)
    (hc1 : c₁.1.card = 1) (hc2 : c₂.1.card = 2) (hc3 : c₃.1.card = 3) :
    IsTri K.barycentric ({c₁, c₂, c₃} : Finset K.Face) :=
  ⟨(flag_isTriangle h12 h23 hc1 hc2 hc3).1, (flag_isTriangle h12 h23 hc1 hc2 hc3).2⟩

/-- Two triangles of the subdivision sharing two vertices are adjacent in the dual graph. -/
theorem triAdj_of_two_common {x y z z' : K.Face}
    (h1 : IsTri K.barycentric ({x, y, z} : Finset K.Face))
    (h2 : IsTri K.barycentric ({x, y, z'} : Finset K.Face))
    (hxy : x ≠ y) (hzx : z ≠ x) (hzy : z ≠ y) (hz'x : z' ≠ x) (hz'y : z' ≠ y)
    (hzz' : z ≠ z') :
    TriAdj K.barycentric ({x, y, z} : Finset K.Face) ({x, y, z'} : Finset K.Face) := by
  refine ⟨h1, h2, ?_⟩
  have hinter : ({x, y, z} : Finset K.Face) ∩ {x, y, z'} = {x, y} := by
    ext w
    simp only [Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨hw | hw | hw, hw' | hw' | hw'⟩
      · exact Or.inl hw
      · exact Or.inl hw
      · exact Or.inl hw
      · exact Or.inr hw
      · exact Or.inr hw
      · exact Or.inr hw
      · subst hw; exact absurd hw' hzx
      · subst hw; exact absurd hw' hzy
      · subst hw; exact absurd hw' hzz'
    · rintro (rfl | rfl) <;> simp
  rw [hinter, Finset.card_pair hxy]

/-! ### Flags with the same triangle -/

/-- Two flags with the same triangle are joined by at most three moves. -/
theorem conn_same_triangle {v v' e e' t : K.Face} (hv : v ≤ e) (he : e ≤ t)
    (hv' : v' ≤ e') (he' : e' ≤ t) (hcv : v.1.card = 1) (hce : e.1.card = 2)
    (hct : t.1.card = 3) (hcv' : v'.1.card = 1) (hce' : e'.1.card = 2) :
    Relation.ReflTransGen (TriAdj K.barycentric)
      ({v, e, t} : Finset K.Face) ({v', e', t} : Finset K.Face) := by
  -- the elementary moves
  have move_e : ∀ {w f f' : K.Face}, w ≤ f → f ≤ t → w ≤ f' → f' ≤ t →
      w.1.card = 1 → f.1.card = 2 → f'.1.card = 2 → f ≠ f' →
      Relation.ReflTransGen (TriAdj K.barycentric)
        ({w, f, t} : Finset K.Face) ({w, f', t} : Finset K.Face) := by
    intro w f f' hwf hft hwf' hf't hcw hcf hcf' hff'
    refine Relation.ReflTransGen.single ?_
    rw [triple_swap23 w f t, triple_swap23 w f' t]
    refine triAdj_of_two_common ?_ ?_ ?_ ?_ ?_ ?_ ?_ hff'
    · rw [← triple_swap23 w f t]; exact isTri_flag hwf hft hcw hcf hct
    · rw [← triple_swap23 w f' t]; exact isTri_flag hwf' hf't hcw hcf' hct
    · exact ne_of_card_ne (by rw [hcw, hct]; norm_num)
    · exact ne_of_card_ne (by rw [hcf, hcw]; norm_num)
    · exact ne_of_card_ne (by rw [hcf, hct]; norm_num)
    · exact ne_of_card_ne (by rw [hcf', hcw]; norm_num)
    · exact ne_of_card_ne (by rw [hcf', hct]; norm_num)
  have move_v : ∀ {w w' f : K.Face}, w ≤ f → f ≤ t → w' ≤ f →
      w.1.card = 1 → w'.1.card = 1 → f.1.card = 2 → w ≠ w' →
      Relation.ReflTransGen (TriAdj K.barycentric)
        ({w, f, t} : Finset K.Face) ({w', f, t} : Finset K.Face) := by
    intro w w' f hwf hft hw'f hcw hcw' hcf hww'
    refine Relation.ReflTransGen.single ?_
    rw [triple_rot w f t, triple_rot w' f t]
    refine triAdj_of_two_common ?_ ?_ ?_ ?_ ?_ ?_ ?_ hww'
    · rw [← triple_rot w f t]; exact isTri_flag hwf hft hcw hcf hct
    · rw [← triple_rot w' f t]; exact isTri_flag hw'f hft hcw' hcf hct
    · exact ne_of_card_ne (by rw [hcf, hct]; norm_num)
    · exact ne_of_card_ne (by rw [hcw, hcf]; norm_num)
    · exact ne_of_card_ne (by rw [hcw, hct]; norm_num)
    · exact ne_of_card_ne (by rw [hcw', hcf]; norm_num)
    · exact ne_of_card_ne (by rw [hcw', hct]; norm_num)
  by_cases hee' : e = e'
  · subst hee'
    by_cases hvv' : v = v'
    · subst hvv'; exact Relation.ReflTransGen.refl
    · exact move_v hv he hv' hcv hcv' hce hvv'
  · by_cases hvv' : v = v'
    · subst hvv'
      exact move_e hv he hv' he' hcv hce hce' hee'
    · -- the vertex `v` may or may not lie on the edge `e'`
      by_cases hve' : v ≤ e'
      · exact (move_e hv he hve' he' hcv hce hce' hee').trans
          (move_v hve' he' hv' hcv hcv' hce' hvv')
      · -- `e'` is the edge of `t` opposite to `v`; the second vertex of `e` lies on it
        obtain ⟨p, hp⟩ := Finset.card_eq_one.mp hcv
        have hpe : p ∈ e.1 := hv (show p ∈ v.1 by rw [hp]; simp)
        have hpe' : p ∉ e'.1 := by
          intro hcon
          refine hve' ?_
          show v.1 ⊆ e'.1
          rw [hp]
          simpa using hcon
        have hpt : p ∈ t.1 := he hpe
        have hcard_erase : (e.1.erase p).card = 1 := by
          rw [Finset.card_erase_of_mem hpe, hce]
        obtain ⟨w, hw⟩ := Finset.card_eq_one.mp hcard_erase
        have hwmem : w ∈ e.1.erase p := by rw [hw]; simp
        have hwe : w ∈ e.1 := Finset.mem_of_mem_erase hwmem
        have hwp : w ≠ p := Finset.ne_of_mem_erase hwmem
        have hwt : w ∈ t.1 := he hwe
        -- `e'` has two vertices inside the three vertices of `t` and misses `p`
        have hsub : e'.1 ⊆ t.1.erase p := by
          intro x hx
          exact Finset.mem_erase.2 ⟨fun hcon => hpe' (hcon ▸ hx), he' hx⟩
        have hcard_t_erase : (t.1.erase p).card = 2 := by
          rw [Finset.card_erase_of_mem hpt, hct]
        have he'eq : e'.1 = t.1.erase p :=
          Finset.eq_of_subset_of_card_le hsub (by rw [hcard_t_erase, hce'])
        have hwe' : w ∈ e'.1 := by
          rw [he'eq]
          exact Finset.mem_erase.2 ⟨hwp, hwt⟩
        -- the vertex `w`, as a face
        have hwface : ({w} : Finset V) ∈ K.faces :=
          K.down_closed e.2.1 (by simpa using hwe)
        set cw : K.Face := ⟨{w}, hwface, ⟨w, by simp⟩⟩ with hcw_def
        have hcwcard : cw.1.card = 1 := by simp [hcw_def]
        have hcwe : cw ≤ e := by
          show cw.1 ⊆ e.1
          intro x hx
          simp only [hcw_def, Finset.mem_singleton] at hx
          subst hx; exact hwe
        have hcwe' : cw ≤ e' := by
          show cw.1 ⊆ e'.1
          intro x hx
          simp only [hcw_def, Finset.mem_singleton] at hx
          subst hx; exact hwe'
        have hvcw : v ≠ cw := by
          intro hcon
          have : v.1 = ({w} : Finset V) := congrArg Subtype.val hcon
          rw [hp] at this
          have : p = w := by simpa using this
          exact hwp this.symm
        refine ((move_v hv he hcwe hcv hcwcard hce hvcw).trans
          (move_e hcwe he hcwe' he' hcwcard hce hce' hee')).trans ?_
        by_cases hcwv' : cw = v'
        · rw [hcwv']
        · exact move_v hcwe' he' hv' hcwcard hcv' hce' hcwv'

/-! ### Connectivity of the dual graph of the subdivision -/

/-- **The dual graph of the barycentric subdivision is connected** as soon as the dual graph
of `K` is: a path of triangles of `K` lifts to a path of flags. -/
theorem barycentric_dual_connected (hdim : ∀ s ∈ K.faces, s.card ≤ 3)
    (hdual : ∀ u u' : Finset V, IsTri K u → IsTri K u' →
      Relation.ReflTransGen (TriAdj K) u u')
    {σ σ' : Finset K.Face} (hσ : IsTri K.barycentric σ) (hσ' : IsTri K.barycentric σ') :
    Relation.ReflTransGen (TriAdj K.barycentric) σ σ' := by
  obtain ⟨v, e, t, rfl, hve, het, hcv, hce, hct⟩ := exists_flag_of_isTri hdim hσ
  obtain ⟨v', e', t', rfl, hve', he't', hcv', hce', hct'⟩ := exists_flag_of_isTri hdim hσ'
  have key : ∀ {u : Finset V}, Relation.ReflTransGen (TriAdj K) t.1 u → IsTri K u →
      ∀ x f cu : K.Face, x ≤ f → f ≤ cu → cu.1 = u → x.1.card = 1 → f.1.card = 2 →
        Relation.ReflTransGen (TriAdj K.barycentric)
          ({v, e, t} : Finset K.Face) ({x, f, cu} : Finset K.Face) := by
    intro u hpath
    induction hpath with
    | refl =>
        intro _ x f cu hxf hfcu hcu hcx hcf
        have hcut : cu = t := Subtype.ext hcu
        subst hcut
        exact conn_same_triangle hve het hxf hfcu hcv hce hct hcx hcf
    | @tail b c hpath₀ hstep ih =>
        intro hc x f cu hxf hfcu hcu hcx hcf
        have hb : IsTri K b := hstep.1
        have hinter : (b ∩ c).card = 2 := hstep.2.2
        have hebface : (b ∩ c) ∈ K.faces := K.down_closed hb.1 Finset.inter_subset_left
        have hne : (b ∩ c).Nonempty := Finset.card_pos.1 (by rw [hinter]; norm_num)
        obtain ⟨w, hw⟩ := hne
        have hwface : ({w} : Finset V) ∈ K.faces :=
          K.down_closed hebface (by simpa using hw)
        have hbne : b.Nonempty := Finset.card_pos.1 (by rw [hb.2]; norm_num)
        -- the intermediate flags `(w, b ∩ c, b)` and `(w, b ∩ c, c)`
        let cw : K.Face := ⟨{w}, hwface, ⟨w, by simp⟩⟩
        let ce : K.Face := ⟨b ∩ c, hebface, ⟨w, hw⟩⟩
        let cb : K.Face := ⟨b, hb.1, hbne⟩
        have hcwcard : cw.1.card = 1 := by simp [cw]
        have hcecard : ce.1.card = 2 := hinter
        have hcbcard : cb.1.card = 3 := hb.2
        have hcucard : cu.1.card = 3 := by rw [hcu]; exact hc.2
        have hcwce : cw ≤ ce := by
          show ({w} : Finset V) ⊆ b ∩ c
          simpa using hw
        have hcecb : ce ≤ cb := Finset.inter_subset_left
        have hcecu : ce ≤ cu := by
          show (b ∩ c) ⊆ cu.1
          rw [hcu]
          exact Finset.inter_subset_right
        have hbc : b ≠ c := by
          intro hcon
          rw [hcon, Finset.inter_self, hc.2] at hinter
          exact absurd hinter (by norm_num)
        have hcbcu : cb ≠ cu := by
          intro hcon
          exact hbc (by rw [← hcu]; exact congrArg Subtype.val hcon)
        have step1 : Relation.ReflTransGen (TriAdj K.barycentric)
            ({v, e, t} : Finset K.Face) ({cw, ce, cb} : Finset K.Face) :=
          ih hb cw ce cb hcwce hcecb rfl hcwcard hcecard
        have step2 : Relation.ReflTransGen (TriAdj K.barycentric)
            ({cw, ce, cb} : Finset K.Face) ({cw, ce, cu} : Finset K.Face) := by
          refine Relation.ReflTransGen.single ?_
          refine triAdj_of_two_common (isTri_flag hcwce hcecb hcwcard hcecard hcbcard)
            (isTri_flag hcwce hcecu hcwcard hcecard hcucard) ?_ ?_ ?_ ?_ ?_ hcbcu
          · exact ne_of_card_ne (by rw [hcwcard, hcecard]; norm_num)
          · exact ne_of_card_ne (by rw [hcbcard, hcwcard]; norm_num)
          · exact ne_of_card_ne (by rw [hcbcard, hcecard]; norm_num)
          · exact ne_of_card_ne (by rw [hcucard, hcwcard]; norm_num)
          · exact ne_of_card_ne (by rw [hcucard, hcecard]; norm_num)
        have step3 : Relation.ReflTransGen (TriAdj K.barycentric)
            ({cw, ce, cu} : Finset K.Face) ({x, f, cu} : Finset K.Face) :=
          conn_same_triangle hcwce hcecu hxf hfcu hcwcard hcecard hcucard hcx hcf
        exact (step1.trans step2).trans step3
  exact key (hdual t.1 t'.1 ⟨t.2.1, hct⟩ ⟨t'.2.1, hct'⟩) ⟨t'.2.1, hct'⟩ v' e' t'
    hve' he't' rfl hcv' hce'

end ASC

end FiniteChains
