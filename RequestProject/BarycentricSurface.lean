module

public import RequestProject.FlagComplex

@[expose] public section

/-!
# The barycentric subdivision of a closed surface is again a closed surface

The block construction of Section 3.3 uses, for `L_q`, the barycentric subdivision of a
triangulation of the closed surface `Σ_q`, and it needs two properties of `L_q`:

* `L_q` is flag (proved in `RequestProject/FlagComplex.lean`);
* every edge of `L_q` lies in exactly two triangles — this is the incidence count behind
  "every square meets exactly two three-cubes, because every edge of `L` meets two
  triangles", the hypothesis of the collapse and of the fundamental-cycle computation
  (`RequestProject/MomentAngle.lean`, `RequestProject/SpineCollapse.lean`).

This file proves the second property: if every face of `K` has at most three vertices and
every edge of `K` lies in exactly two triangles, then the same holds for the barycentric
subdivision of `K`.  The subdivision is the order complex of the poset of nonempty faces,
so its triangles are the flags `v ⊂ e ⊂ t` of `K`, and the proof is the usual case
distinction on the type of an edge of the subdivision:

* an edge `v ⊂ e` extends by the two triangles of `K` containing `e`;
* an edge `v ⊂ t` extends by the two edges of `t` through `v`;
* an edge `e ⊂ t` extends by the two vertices of `e`.

Together with `RequestProject/FlagComplex.lean` this verifies, for the subdivision, both
combinatorial hypotheses that the cube complex `C(L_q)` of the paper requires.
-/

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains

namespace ASC

universe u

variable {V : Type u} [DecidableEq V]

/-- "The predicate `P` has exactly two witnesses." -/
def ExactlyTwo {α : Sort*} (P : α → Prop) : Prop :=
  ∃ x y, x ≠ y ∧ P x ∧ P y ∧ ∀ z, P z → z = x ∨ z = y

/-- Every edge of `K` lies in exactly two triangles: for every edge `e` there are exactly
two vertices outside `e` spanning a triangle with it. -/
def EdgeInTwoTriangles (K : ASC V) : Prop :=
  ∀ e ∈ K.faces, e.card = 2 → ExactlyTwo (fun v => v ∉ e ∧ insert v e ∈ K.faces)

section Chains

variable {P : Type u} [Preorder P]

theorem isChain_triple {x y z : P} (hxy : x ≤ y ∨ y ≤ x) (hxz : x ≤ z ∨ z ≤ x)
    (hyz : y ≤ z ∨ z ≤ y) : IsChain (· ≤ ·) ({x, y, z} : Set P) := by
  rintro p (rfl | rfl | rfl) q (rfl | rfl | rfl) hpq <;> first
    | exact absurd rfl hpq
    | exact hxy | exact hxy.symm | exact hxz | exact hxz.symm | exact hyz | exact hyz.symm

theorem le_or_le_of_isChain {s : Set P} (hs : IsChain (· ≤ ·) s) {x y : P} (hx : x ∈ s)
    (hy : y ∈ s) : x ≤ y ∨ y ≤ x := by
  by_cases hxy : x = y
  · exact Or.inl (le_of_eq hxy)
  · exact hs hx hy hxy

end Chains

instance faceDecidableEq (K : ASC V) : DecidableEq K.Face := fun a b =>
  decidable_of_iff (a.1 = b.1) (by
    constructor
    · intro h; exact Subtype.ext h
    · intro h; rw [h])

/-- The poset of faces of a complex on a finite vertex type is finite. -/
noncomputable instance faceFintype (K : ASC V) [Fintype V] : Fintype K.Face :=
  Fintype.ofInjective (fun a : K.Face => (a.1 : Finset V)) (fun _ _ h => Subtype.ext h)

omit [DecidableEq V] in
theorem le_face_iff {K : ASC V} {a b : K.Face} : a ≤ b ↔ a.1 ⊆ b.1 := Iff.rfl

/-- Faces of the barycentric subdivision are chains; for a triple this is pairwise
comparability. -/
theorem mem_barycentric_triple {K : ASC V} {a b c : K.Face} :
    insert c ({a, b} : Finset K.Face) ∈ K.barycentric.faces ↔
      IsChain (· ≤ ·) ({c, a, b} : Set K.Face) := by
  rw [barycentric, mem_orderComplex]
  simp

/-- The statement "the edge `{a, b}` of the barycentric subdivision lies in exactly two
triangles", spelled out. -/
def TwoFlags (K : ASC V) (a b : K.Face) : Prop :=
  ExactlyTwo (fun c : K.Face => c ∉ ({a, b} : Finset K.Face) ∧
    insert c ({a, b} : Finset K.Face) ∈ K.barycentric.faces)

/-- Case `v ⊂ e`: an edge of the subdivision joining a vertex to an edge of `K` extends by
the two triangles of `K` containing that edge. -/
theorem twoFlags_vertex_edge {K : ASC V} (h2 : EdgeInTwoTriangles K)
    (hdim : ∀ s ∈ K.faces, s.card ≤ 3) {a b : K.Face} (hab : a ≤ b) (hA : a.1.card = 1)
    (hB : b.1.card = 2) : TwoFlags K a b := by
  obtain ⟨v₁, v₂, hv, hv1, hv2, huniq⟩ := h2 b.1 b.2.1 hB
  have hcard_ins : ∀ w : V, w ∉ b.1 → (insert w b.1).card = 3 := by
    intro w hw
    rw [Finset.card_insert_of_notMem hw, hB]
  have hsub_ins : ∀ w : V, b.1 ⊆ insert w b.1 := fun w => Finset.subset_insert _ _
  refine ⟨⟨insert v₁ b.1, hv1.2, ⟨v₁, by simp⟩⟩, ⟨insert v₂ b.1, hv2.2, ⟨v₂, by simp⟩⟩,
    ?_, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ?_⟩
  · intro hcon
    have hset : insert v₁ b.1 = insert v₂ b.1 := congrArg Subtype.val hcon
    have : v₁ ∈ insert v₂ b.1 := by rw [← hset]; simp
    rcases Finset.mem_insert.1 this with h | h
    · exact hv h
    · exact hv1.1 h
  · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    refine ⟨fun hcon => ?_, fun hcon => ?_⟩
    · have hc : (insert v₁ b.1).card = a.1.card := congrArg (fun z : K.Face => z.1.card) hcon
      rw [hcard_ins v₁ hv1.1, hA] at hc
      exact absurd hc (by norm_num)
    · have hc : (insert v₁ b.1).card = b.1.card := congrArg (fun z : K.Face => z.1.card) hcon
      rw [hcard_ins v₁ hv1.1, hB] at hc
      exact absurd hc (by norm_num)
  · refine mem_barycentric_triple.2 (isChain_triple ?_ ?_ (Or.inl hab))
    · exact Or.inr (le_trans hab (hsub_ins v₁))
    · exact Or.inr (hsub_ins v₁)
  · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    refine ⟨fun hcon => ?_, fun hcon => ?_⟩
    · have hc : (insert v₂ b.1).card = a.1.card := congrArg (fun z : K.Face => z.1.card) hcon
      rw [hcard_ins v₂ hv2.1, hA] at hc
      exact absurd hc (by norm_num)
    · have hc : (insert v₂ b.1).card = b.1.card := congrArg (fun z : K.Face => z.1.card) hcon
      rw [hcard_ins v₂ hv2.1, hB] at hc
      exact absurd hc (by norm_num)
  · refine mem_barycentric_triple.2 (isChain_triple ?_ ?_ (Or.inl hab))
    · exact Or.inr (le_trans hab (hsub_ins v₂))
    · exact Or.inr (hsub_ins v₂)
  · rintro z ⟨hzmem, hzchain⟩
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hzmem
    obtain ⟨hza, hzb⟩ := hzmem
    have hchain := mem_barycentric_triple.1 hzchain
    have hcomp_a : z ≤ a ∨ a ≤ z := le_or_le_of_isChain hchain (by simp) (by simp)
    have hcomp_b : z ≤ b ∨ b ≤ z := le_or_le_of_isChain hchain (by simp) (by simp)
    have hzdim : z.1.card ≤ 3 := hdim _ z.2.1
    -- `z` cannot be contained in the edge `b`
    have hbz : b.1 ⊆ z.1 := by
      rcases hcomp_b with h | h
      · exfalso
        have hzcard : z.1.card = 1 := by
          have h1 : 1 ≤ z.1.card := Finset.card_pos.2 z.2.2
          have h2' : z.1.card ≤ 2 := by
            rw [← hB]; exact Finset.card_le_card h
          have hne2 : z.1.card ≠ 2 := by
            intro hcon
            have hle : b.1.card ≤ z.1.card := by rw [hB, hcon]
            exact hzb (Subtype.ext (Finset.eq_of_subset_of_card_le h hle))
          omega
        rcases hcomp_a with h' | h'
        · have hle : a.1.card ≤ z.1.card := by rw [hA, hzcard]
          exact hza (Subtype.ext (Finset.eq_of_subset_of_card_le h' hle))
        · have hle : z.1.card ≤ a.1.card := by rw [hA, hzcard]
          exact hza (Subtype.ext (Finset.eq_of_subset_of_card_le h' hle).symm)
      · exact h
    have hzcard3 : z.1.card = 3 := by
      have h2' : 2 ≤ z.1.card := by
        rw [← hB]; exact Finset.card_le_card hbz
      have hne2 : z.1.card ≠ 2 := by
        intro hcon
        have hle : z.1.card ≤ b.1.card := by rw [hB, hcon]
        exact hzb (Subtype.ext (Finset.eq_of_subset_of_card_le hbz hle).symm)
      omega
    -- the extra vertex of `z`
    have hdiff : (z.1 \ b.1).card = 1 := by
      rw [Finset.card_sdiff, Finset.inter_eq_left.2 hbz, hzcard3, hB]
    obtain ⟨w, hw⟩ := Finset.card_eq_one.mp hdiff
    have hwmem : w ∈ z.1 \ b.1 := by rw [hw]; simp
    have hwz : w ∈ z.1 := (Finset.mem_sdiff.1 hwmem).1
    have hwb : w ∉ b.1 := (Finset.mem_sdiff.1 hwmem).2
    have hsub : insert w b.1 ⊆ z.1 := by
      intro x hx
      rcases Finset.mem_insert.1 hx with rfl | hx'
      · exact hwz
      · exact hbz hx'
    have hzeq : insert w b.1 = z.1 :=
      Finset.eq_of_subset_of_card_le hsub (by rw [hcard_ins w hwb, hzcard3])
    have hwface : insert w b.1 ∈ K.faces := by rw [hzeq]; exact z.2.1
    rcases huniq w ⟨hwb, hwface⟩ with rfl | rfl
    · exact Or.inl (Subtype.ext hzeq.symm)
    · exact Or.inr (Subtype.ext hzeq.symm)

/-- Case `v ⊂ t`: an edge of the subdivision joining a vertex to a triangle of `K` extends
by the two edges of that triangle through the vertex. -/
theorem twoFlags_vertex_triangle {K : ASC V} (hdim : ∀ s ∈ K.faces, s.card ≤ 3)
    {a b : K.Face} (hab : a ≤ b) (hA : a.1.card = 1) (hB : b.1.card = 3) :
    TwoFlags K a b := by
  obtain ⟨v, hv⟩ := Finset.card_eq_one.mp hA
  have hvb : v ∈ b.1 := hab (show v ∈ a.1 by rw [hv]; simp)
  have hcard_erase : (b.1.erase v).card = 2 := by
    rw [Finset.card_erase_of_mem hvb, hB]
  obtain ⟨p, q, hpq, hpq2⟩ := Finset.card_eq_two.mp hcard_erase
  have hpe : p ∈ b.1.erase v := by rw [hpq2]; simp
  have hqe : q ∈ b.1.erase v := by rw [hpq2]; simp
  have hpb : p ∈ b.1 := Finset.mem_of_mem_erase hpe
  have hqb : q ∈ b.1 := Finset.mem_of_mem_erase hqe
  have hpv : p ≠ v := Finset.ne_of_mem_erase hpe
  have hqv : q ≠ v := Finset.ne_of_mem_erase hqe
  have hface : ∀ w ∈ b.1, ({v, w} : Finset V) ∈ K.faces := by
    intro w hw
    refine K.down_closed b.2.1 ?_
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact hvb
    · exact hw
  have hsubb : ∀ w ∈ b.1, ({v, w} : Finset V) ⊆ b.1 := by
    intro w hw x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact hvb
    · exact hw
  have hcard_pair : ∀ w : V, w ≠ v → ({v, w} : Finset V).card = 2 := by
    intro w hw
    exact Finset.card_pair (Ne.symm hw)
  refine ⟨⟨{v, p}, hface p hpb, ⟨v, by simp⟩⟩, ⟨{v, q}, hface q hqb, ⟨v, by simp⟩⟩,
    ?_, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ?_⟩
  · intro hcon
    have hset : ({v, p} : Finset V) = {v, q} := congrArg Subtype.val hcon
    have : q ∈ ({v, p} : Finset V) := by rw [hset]; simp
    simp only [Finset.mem_insert, Finset.mem_singleton] at this
    rcases this with rfl | rfl
    · exact hqv rfl
    · exact hpq rfl
  · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    refine ⟨fun hcon => ?_, fun hcon => ?_⟩
    · have hc : ({v, p} : Finset V).card = a.1.card :=
        congrArg (fun z : K.Face => z.1.card) hcon
      rw [hcard_pair p hpv, hA] at hc
      exact absurd hc (by norm_num)
    · have hc : ({v, p} : Finset V).card = b.1.card :=
        congrArg (fun z : K.Face => z.1.card) hcon
      rw [hcard_pair p hpv, hB] at hc
      exact absurd hc (by norm_num)
  · refine mem_barycentric_triple.2 (isChain_triple ?_ ?_ (Or.inl hab))
    · exact Or.inr (show a.1 ⊆ ({v, p} : Finset V) by rw [hv]; simp)
    · exact Or.inl (hsubb p hpb)
  · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    refine ⟨fun hcon => ?_, fun hcon => ?_⟩
    · have hc : ({v, q} : Finset V).card = a.1.card :=
        congrArg (fun z : K.Face => z.1.card) hcon
      rw [hcard_pair q hqv, hA] at hc
      exact absurd hc (by norm_num)
    · have hc : ({v, q} : Finset V).card = b.1.card :=
        congrArg (fun z : K.Face => z.1.card) hcon
      rw [hcard_pair q hqv, hB] at hc
      exact absurd hc (by norm_num)
  · refine mem_barycentric_triple.2 (isChain_triple ?_ ?_ (Or.inl hab))
    · exact Or.inr (show a.1 ⊆ ({v, q} : Finset V) by rw [hv]; simp)
    · exact Or.inl (hsubb q hqb)
  · rintro z ⟨hzmem, hzchain⟩
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hzmem
    obtain ⟨hza, hzb⟩ := hzmem
    have hchain := mem_barycentric_triple.1 hzchain
    have hcomp_a : z ≤ a ∨ a ≤ z := le_or_le_of_isChain hchain (by simp) (by simp)
    have hcomp_b : z ≤ b ∨ b ≤ z := le_or_le_of_isChain hchain (by simp) (by simp)
    have hzdim : z.1.card ≤ 3 := hdim _ z.2.1
    -- `a ⊆ z`
    have haz : a.1 ⊆ z.1 := by
      rcases hcomp_a with h | h
      · exfalso
        have hle : a.1.card ≤ z.1.card := by
          rw [hA]; exact Finset.card_pos.2 z.2.2
        exact hza (Subtype.ext (Finset.eq_of_subset_of_card_le h hle))
      · exact h
    have hvz : v ∈ z.1 := haz (by rw [hv]; simp)
    -- `z ⊆ b`
    have hzb' : z.1 ⊆ b.1 := by
      rcases hcomp_b with h | h
      · exact h
      · exfalso
        have hle : z.1.card ≤ b.1.card := by rw [hB]; exact hzdim
        exact hzb (Subtype.ext (Finset.eq_of_subset_of_card_le h hle).symm)
    have hzcard : z.1.card = 2 := by
      have h1 : 1 ≤ z.1.card := Finset.card_pos.2 z.2.2
      have h2 : z.1.card ≤ 3 := hzdim
      have hne3 : z.1.card ≠ 3 := by
        intro hcon
        have hle : b.1.card ≤ z.1.card := by rw [hB, hcon]
        exact hzb (Subtype.ext (Finset.eq_of_subset_of_card_le hzb' hle))
      have hne1 : z.1.card ≠ 1 := by
        intro hcon
        have hle : z.1.card ≤ a.1.card := by rw [hA, hcon]
        exact hza (Subtype.ext (Finset.eq_of_subset_of_card_le haz hle).symm)
      omega
    -- so `z = {v, w}` for a second vertex `w` of `b`
    have hcard_erase_z : (z.1.erase v).card = 1 := by
      rw [Finset.card_erase_of_mem hvz, hzcard]
    obtain ⟨w, hw⟩ := Finset.card_eq_one.mp hcard_erase_z
    have hwz : w ∈ z.1 := Finset.mem_of_mem_erase (by rw [hw]; simp)
    have hzeq : z.1 = {v, w} := by
      have : insert v (z.1.erase v) = z.1 := Finset.insert_erase hvz
      rw [← this, hw]
    have hwe : w ∈ b.1.erase v := by
      refine Finset.mem_erase.2 ⟨?_, hzb' hwz⟩
      exact Finset.ne_of_mem_erase (by rw [hw]; simp)
    rw [hpq2] at hwe
    simp only [Finset.mem_insert, Finset.mem_singleton] at hwe
    rcases hwe with rfl | rfl
    · exact Or.inl (Subtype.ext hzeq)
    · exact Or.inr (Subtype.ext hzeq)

/-- Case `e ⊂ t`: an edge of the subdivision joining an edge to a triangle of `K` extends by
the two vertices of that edge. -/
theorem twoFlags_edge_triangle {K : ASC V} (hdim : ∀ s ∈ K.faces, s.card ≤ 3)
    {a b : K.Face} (hab : a ≤ b) (hA : a.1.card = 2) (hB : b.1.card = 3) :
    TwoFlags K a b := by
  obtain ⟨p, q, hpq, hab2⟩ := Finset.card_eq_two.mp hA
  have hp : ({p} : Finset V) ∈ K.faces :=
    K.down_closed a.2.1 (by rw [hab2]; simp)
  have hq : ({q} : Finset V) ∈ K.faces :=
    K.down_closed a.2.1 (by rw [hab2]; simp)
  refine ⟨⟨{p}, hp, ⟨p, by simp⟩⟩, ⟨{q}, hq, ⟨q, by simp⟩⟩, ?_, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ?_⟩
  · intro hcon
    exact hpq (by simpa using congrArg Subtype.val hcon)
  · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    constructor
    · intro hcon
      have := congrArg (fun z : K.Face => z.1.card) hcon
      simp [hA] at this
    · intro hcon
      have := congrArg (fun z : K.Face => z.1.card) hcon
      simp [hB] at this
  · refine mem_barycentric_triple.2 (isChain_triple ?_ ?_ (Or.inl hab))
    · exact Or.inl (show ({p} : Finset V) ⊆ a.1 by rw [hab2]; simp)
    · exact Or.inl (le_trans (show ({p} : Finset V) ⊆ a.1 by rw [hab2]; simp) hab)
  · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    constructor
    · intro hcon
      have := congrArg (fun z : K.Face => z.1.card) hcon
      simp [hA] at this
    · intro hcon
      have := congrArg (fun z : K.Face => z.1.card) hcon
      simp [hB] at this
  · refine mem_barycentric_triple.2 (isChain_triple ?_ ?_ (Or.inl hab))
    · exact Or.inl (show ({q} : Finset V) ⊆ a.1 by rw [hab2]; simp)
    · exact Or.inl (le_trans (show ({q} : Finset V) ⊆ a.1 by rw [hab2]; simp) hab)
  · rintro z ⟨hzmem, hzchain⟩
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hzmem
    obtain ⟨hza, hzb⟩ := hzmem
    have hchain := mem_barycentric_triple.1 hzchain
    have hcomp_a : z ≤ a ∨ a ≤ z := le_or_le_of_isChain hchain (by simp) (by simp)
    have hcomp_b : z ≤ b ∨ b ≤ z := le_or_le_of_isChain hchain (by simp) (by simp)
    have hzle : z.1 ⊆ a.1 := by
      rcases hcomp_a with h | h
      · exact h
      · exfalso
        have hzdim : z.1.card ≤ 3 := hdim _ z.2.1
        have h2le : 2 ≤ z.1.card := by rw [← hA]; exact Finset.card_le_card h
        rcases hcomp_b with h' | h'
        · -- `a ⊆ z ⊆ b`, so `z` is `a` or `b`
          have hzb' : z.1.card ≤ b.1.card := by
            rw [hB]; exact hzdim
          rcases Nat.lt_or_ge z.1.card 3 with hlt | hge
          · have hle : z.1.card ≤ a.1.card := by rw [hA]; omega
            exact hza (Subtype.ext (Finset.eq_of_subset_of_card_le h hle).symm)
          · have hle : b.1.card ≤ z.1.card := by rw [hB]; omega
            exact hzb (Subtype.ext (Finset.eq_of_subset_of_card_le h' hle))
        · have hle : z.1.card ≤ b.1.card := by rw [hB]; exact hzdim
          exact hzb (Subtype.ext (Finset.eq_of_subset_of_card_le h' hle).symm)
    -- `z` is a nonempty proper subset of the edge `a`
    have hzne : z.1 ≠ a.1 := fun hcon => hza (Subtype.ext hcon)
    have hzcard : z.1.card = 1 := by
      have h1 : 1 ≤ z.1.card := Finset.card_pos.2 z.2.2
      have h2 : z.1.card ≤ 2 := by rw [← hA]; exact Finset.card_le_card hzle
      rcases Nat.lt_or_ge z.1.card 2 with hlt | hge
      · omega
      · have hle : a.1.card ≤ z.1.card := by rw [hA]; omega
        exact absurd (Finset.eq_of_subset_of_card_le hzle hle) hzne
    obtain ⟨x, hx⟩ := Finset.card_eq_one.mp hzcard
    have hxmem : x ∈ a.1 := hzle (by rw [hx]; simp)
    rw [hab2] at hxmem
    simp only [Finset.mem_insert, Finset.mem_singleton] at hxmem
    rcases hxmem with rfl | rfl
    · exact Or.inl (Subtype.ext (by simpa using hx))
    · exact Or.inr (Subtype.ext (by simpa using hx))

/-- **The barycentric subdivision of a closed surface triangulation is again one**: if every
face of `K` has at most three vertices and every edge of `K` lies in exactly two triangles,
then every edge of the barycentric subdivision lies in exactly two triangles. -/
theorem barycentric_edgeInTwoTriangles (K : ASC V) (hdim : ∀ s ∈ K.faces, s.card ≤ 3)
    (h2 : EdgeInTwoTriangles K) : EdgeInTwoTriangles K.barycentric := by
  intro e he hecard
  obtain ⟨x, y, hxy, rfl⟩ := Finset.card_eq_two.mp hecard
  have hchain : IsChain (· ≤ ·) (({x, y} : Finset K.Face) : Set K.Face) := by
    rw [barycentric, mem_orderComplex] at he; exact he
  have hcomp : x ≤ y ∨ y ≤ x := le_or_le_of_isChain hchain (by simp) (by simp)
  -- the ordered case, then symmetry in the two endpoints
  have main : ∀ a b : K.Face, a ≤ b → a ≠ b → TwoFlags K a b := by
    intro a b hab hne
    have hsub : a.1 ⊂ b.1 :=
      ⟨hab, fun hcon => hne (Subtype.ext (Finset.Subset.antisymm hab hcon))⟩
    have hcardlt : a.1.card < b.1.card := Finset.card_lt_card hsub
    have ha1 : 1 ≤ a.1.card := Finset.card_pos.2 a.2.2
    have hb3 : b.1.card ≤ 3 := hdim _ b.2.1
    have hcases : (a.1.card = 1 ∧ b.1.card = 2) ∨ (a.1.card = 1 ∧ b.1.card = 3) ∨
        (a.1.card = 2 ∧ b.1.card = 3) := by omega
    rcases hcases with ⟨hA, hB⟩ | ⟨hA, hB⟩ | ⟨hA, hB⟩
    · exact twoFlags_vertex_edge h2 hdim hab hA hB
    · exact twoFlags_vertex_triangle hdim hab hA hB
    · exact twoFlags_edge_triangle hdim hab hA hB
  rcases hcomp with h | h
  · exact main x y h hxy
  · simp only [show ({x, y} : Finset K.Face) = {y, x} from Finset.pair_comm x y]
    exact main y x h (Ne.symm hxy)

/-! ### Every vertex of the subdivision lies in a triangle -/

/-- A flag `c₁ ⊂ c₂ ⊂ c₃` spans a triangle of the barycentric subdivision. -/
theorem flag_isTriangle {K : ASC V} {c₁ c₂ c₃ : K.Face} (h12 : c₁ ≤ c₂) (h23 : c₂ ≤ c₃)
    (hc1 : c₁.1.card = 1) (hc2 : c₂.1.card = 2) (hc3 : c₃.1.card = 3) :
    ({c₁, c₂, c₃} : Finset K.Face) ∈ K.barycentric.faces ∧
      ({c₁, c₂, c₃} : Finset K.Face).card = 3 := by
  have hne12 : c₁ ≠ c₂ := by
    intro hcon
    rw [hcon, hc2] at hc1
    exact absurd hc1 (by norm_num)
  have hne13 : c₁ ≠ c₃ := by
    intro hcon
    rw [hcon, hc3] at hc1
    exact absurd hc1 (by norm_num)
  have hne23 : c₂ ≠ c₃ := by
    intro hcon
    rw [hcon, hc3] at hc2
    exact absurd hc2 (by norm_num)
  constructor
  · rw [barycentric, mem_orderComplex]
    have : (({c₁, c₂, c₃} : Finset K.Face) : Set K.Face) = ({c₁, c₂, c₃} : Set K.Face) := by
      simp
    rw [this]
    exact isChain_triple (Or.inl h12) (Or.inl (le_trans h12 h23)) (Or.inl h23)
  · rw [Finset.card_insert_of_notMem (by simp [hne12, hne13]),
      Finset.card_insert_of_notMem (by simp [hne23])]
    simp

/-- **Every vertex of the barycentric subdivision lies in a triangle.**  The hypotheses are
that `K` is at most two-dimensional, that every edge lies in a triangle (a consequence of
the closed surface condition) and that every vertex lies in an edge. -/
theorem barycentric_vertex_in_triangle (K : ASC V) (hdim : ∀ s ∈ K.faces, s.card ≤ 3)
    (hedge_tri : ∀ e ∈ K.faces, e.card = 2 → ∃ t ∈ K.faces, t.card = 3 ∧ e ⊆ t)
    (hvert_edge : ∀ v : V, ({v} : Finset V) ∈ K.faces →
      ∃ e ∈ K.faces, e.card = 2 ∧ v ∈ e)
    (a : K.Face) :
    ∃ σ : Finset K.Face, σ ∈ K.barycentric.faces ∧ σ.card = 3 ∧ a ∈ σ := by
  have ha1 : 1 ≤ a.1.card := Finset.card_pos.2 a.2.2
  have ha3 : a.1.card ≤ 3 := hdim _ a.2.1
  have hsubface : ∀ s : Finset V, s ⊆ a.1 → s ∈ K.faces := fun s hs => K.down_closed a.2.1 hs
  interval_cases h : a.1.card
  · -- `a` is a vertex
    obtain ⟨v, hv⟩ := Finset.card_eq_one.mp h
    have hvface : ({v} : Finset V) ∈ K.faces := by rw [← hv]; exact a.2.1
    obtain ⟨e, heface, hecard, hve⟩ := hvert_edge v hvface
    obtain ⟨t, htface, htcard, het⟩ := hedge_tri e heface hecard
    refine ⟨{a, ⟨e, heface, ⟨v, hve⟩⟩, ⟨t, htface, ⟨v, het hve⟩⟩}, ?_, ?_, by simp⟩
    · exact (flag_isTriangle (c₁ := a) (c₂ := ⟨e, heface, ⟨v, hve⟩⟩)
        (c₃ := ⟨t, htface, ⟨v, het hve⟩⟩)
        (show a.1 ⊆ e by rw [hv]; simpa using hve) het h hecard htcard).1
    · exact (flag_isTriangle (c₁ := a) (c₂ := ⟨e, heface, ⟨v, hve⟩⟩)
        (c₃ := ⟨t, htface, ⟨v, het hve⟩⟩)
        (show a.1 ⊆ e by rw [hv]; simpa using hve) het h hecard htcard).2
  · -- `a` is an edge
    obtain ⟨v, hv⟩ := a.2.2
    have hvface : ({v} : Finset V) ∈ K.faces := hsubface _ (by simpa using hv)
    obtain ⟨t, htface, htcard, hat⟩ := hedge_tri a.1 a.2.1 h
    refine ⟨{⟨{v}, hvface, ⟨v, by simp⟩⟩, a, ⟨t, htface, ⟨v, hat hv⟩⟩}, ?_, ?_, by simp⟩
    · exact (flag_isTriangle (c₁ := ⟨{v}, hvface, ⟨v, by simp⟩⟩) (c₂ := a)
        (c₃ := ⟨t, htface, ⟨v, hat hv⟩⟩)
        (show ({v} : Finset V) ⊆ a.1 by simpa using hv) hat (by simp) h htcard).1
    · exact (flag_isTriangle (c₁ := ⟨{v}, hvface, ⟨v, by simp⟩⟩) (c₂ := a)
        (c₃ := ⟨t, htface, ⟨v, hat hv⟩⟩)
        (show ({v} : Finset V) ⊆ a.1 by simpa using hv) hat (by simp) h htcard).2
  · -- `a` is a triangle
    obtain ⟨v, hv⟩ := a.2.2
    have hcard_erase : (a.1.erase v).card = 2 := by
      rw [Finset.card_erase_of_mem hv, h]
    have hne : (a.1.erase v).Nonempty := Finset.card_pos.1 (by rw [hcard_erase]; norm_num)
    obtain ⟨w, hwe⟩ := hne
    have hwa : w ∈ a.1 := Finset.mem_of_mem_erase hwe
    have hwv : w ≠ v := Finset.ne_of_mem_erase hwe
    have hesub : ({v, w} : Finset V) ⊆ a.1 := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl
      · exact hv
      · exact hwa
    have heface : ({v, w} : Finset V) ∈ K.faces := hsubface _ hesub
    have hvface : ({v} : Finset V) ∈ K.faces := hsubface _ (by simpa using hv)
    have hecard : ({v, w} : Finset V).card = 2 := Finset.card_pair (Ne.symm hwv)
    refine ⟨{⟨{v}, hvface, ⟨v, by simp⟩⟩, ⟨{v, w}, heface, ⟨v, by simp⟩⟩, a}, ?_, ?_, by simp⟩
    · exact (flag_isTriangle (c₁ := ⟨{v}, hvface, ⟨v, by simp⟩⟩)
        (c₂ := ⟨{v, w}, heface, ⟨v, by simp⟩⟩) (c₃ := a)
        (by intro x hx; simp only [Finset.mem_singleton] at hx; subst hx; simp)
        hesub (by simp) hecard h).1
    · exact (flag_isTriangle (c₁ := ⟨{v}, hvface, ⟨v, by simp⟩⟩)
        (c₂ := ⟨{v, w}, heface, ⟨v, by simp⟩⟩) (c₃ := a)
        (by intro x hx; simp only [Finset.mem_singleton] at hx; subst hx; simp)
        hesub (by simp) hecard h).2

end ASC

end FiniteChains
