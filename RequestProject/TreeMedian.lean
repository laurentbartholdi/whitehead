import RequestProject.MedianSimplyConnected

/-!
# Trees are median graphs

The criterion cited in the paper — *a simply connected cube complex with flag links has median
one-skeleton* — is proved here in dimension one, where the cube complex has no two-cells: such
a complex is a tree, and **every tree is a median graph**.

Everything is proved from scratch out of the unique-path property of a tree:

* `FiniteChains.Tree.treePath` — the unique path between two vertices, and
  `FiniteChains.Tree.treePath_length` — its length is the distance;
* `FiniteChains.Tree.mem_support_iff_between` — a vertex lies on that path exactly when it lies
  between the endpoints metrically;
* `FiniteChains.Tree.eq_of_between_of_dist_eq` — two vertices between the same pair and at the
  same distance from the first one coincide;
* `FiniteChains.Tree.exists_median` — three vertices have a median: the last vertex the paths
  from `a` to `b` and from `a` to `c` have in common;
* `FiniteChains.Tree.toMedianSimpleGraph` — consequently a tree, with any base vertex, is a
  median graph in the sense used throughout this project, so all the results proved for median
  graphs (walls, halfspaces, the dual cube complex, `ker d₂ = im d₃`, simple connectivity of the
  square complex) apply to it.
-/

namespace FiniteChains

namespace Tree

universe u

variable {V : Type u} [DecidableEq V] {G : SimpleGraph V}

/-- The unique path between two vertices of a tree. -/
noncomputable def treePath (hT : G.IsTree) (a b : V) : G.Walk a b :=
  (hT.existsUnique_path a b).choose

omit [DecidableEq V] in
theorem treePath_isPath (hT : G.IsTree) (a b : V) : (treePath hT a b).IsPath :=
  (hT.existsUnique_path a b).choose_spec.1

omit [DecidableEq V] in
/-- Any path between two vertices of a tree is *the* path. -/
theorem eq_treePath (hT : G.IsTree) {a b : V} (p : G.Walk a b) (hp : p.IsPath) :
    p = treePath hT a b :=
  (hT.existsUnique_path a b).choose_spec.2 p hp

omit [DecidableEq V] in
/-- Vertices at distance zero in a tree are equal. -/
theorem eq_of_dist_eq_zero (hT : G.IsTree) {a b : V} (h : G.dist a b = 0) : a = b := by
  rcases SimpleGraph.dist_eq_zero_iff_eq_or_not_reachable.1 h with h' | h'
  · exact h'
  · exact absurd (hT.isConnected.preconnected a b) h'

/-- The unique path realises the distance. -/
theorem treePath_length (hT : G.IsTree) (a b : V) : (treePath hT a b).length = G.dist a b := by
  refine le_antisymm ?_ (SimpleGraph.dist_le _)
  obtain ⟨p, hp⟩ := hT.isConnected.exists_walk_length_eq_dist a b
  have hbp : p.bypass = treePath hT a b := eq_treePath hT _ p.bypass_isPath
  calc (treePath hT a b).length = p.bypass.length := by rw [hbp]
    _ ≤ p.length := p.length_bypass_le
    _ = G.dist a b := hp

/-- A path of a tree is the path between its endpoints, so its length is their distance. -/
theorem length_eq_dist_of_isPath (hT : G.IsTree) {a b : V} {p : G.Walk a b} (hp : p.IsPath) :
    p.length = G.dist a b := by
  rw [eq_treePath hT p hp, treePath_length]

/-- **The vertices of the path are exactly the vertices lying between the endpoints.** -/
theorem mem_support_iff_between (hT : G.IsTree) {a b z : V} :
    z ∈ (treePath hT a b).support ↔ G.dist a z + G.dist z b = G.dist a b := by
  constructor
  · intro hz
    have hsplit := (treePath hT a b).take_spec hz
    have h1 : ((treePath hT a b).takeUntil z hz).length = G.dist a z :=
      length_eq_dist_of_isPath hT ((treePath_isPath hT a b).takeUntil hz)
    have h2 : ((treePath hT a b).dropUntil z hz).length = G.dist z b :=
      length_eq_dist_of_isPath hT ((treePath_isPath hT a b).dropUntil hz)
    have h3 := congrArg SimpleGraph.Walk.length hsplit
    rw [SimpleGraph.Walk.length_append, h1, h2, treePath_length] at h3
    exact h3
  · intro hz
    obtain ⟨p, hp⟩ := hT.isConnected.exists_walk_length_eq_dist a z
    obtain ⟨q, hq⟩ := hT.isConnected.exists_walk_length_eq_dist z b
    have hlen : (p.append q).length = G.dist a b := by
      rw [SimpleGraph.Walk.length_append, hp, hq, hz]
    have hpath : (p.append q).IsPath := SimpleGraph.Walk.isPath_of_length_eq_dist _ hlen
    have hpq : p.append q = treePath hT a b := eq_treePath hT _ hpath
    rw [← hpq, SimpleGraph.Walk.support_append]
    exact List.mem_append_left _ (SimpleGraph.Walk.end_mem_support p)

/-- **Two vertices between the same pair and at the same distance from the first coincide.** -/
theorem eq_of_between_of_dist_eq (hT : G.IsTree) {a b z z' : V}
    (hz : G.dist a z + G.dist z b = G.dist a b) (hz' : G.dist a z' + G.dist z' b = G.dist a b)
    (h : G.dist a z = G.dist a z') : z = z' := by
  have hmz : z ∈ (treePath hT a b).support := (mem_support_iff_between hT).2 hz
  have hmz' : z' ∈ (treePath hT a b).support := (mem_support_iff_between hT).2 hz'
  have hsplit := (treePath hT a b).take_spec hmz
  have hsup : (treePath hT a b).support =
      ((treePath hT a b).takeUntil z hmz).support ++
        ((treePath hT a b).dropUntil z hmz).support.tail := by
    conv_lhs => rw [← hsplit]
    exact SimpleGraph.Walk.support_append _ _
  rw [hsup, List.mem_append] at hmz'
  rcases hmz' with hmem | hmem
  · -- `z'` lies on the path from `a` to `z`
    have hpath : (treePath hT a b).takeUntil z hmz = treePath hT a z :=
      eq_treePath hT _ ((treePath_isPath hT a b).takeUntil hmz)
    rw [hpath] at hmem
    have hbtw := (mem_support_iff_between hT).1 hmem
    have hzz : G.dist z' z = 0 := by omega
    exact (eq_of_dist_eq_zero hT hzz).symm
  · -- `z'` lies on the path from `z` to `b`
    have hpath : (treePath hT a b).dropUntil z hmz = treePath hT z b :=
      eq_treePath hT _ ((treePath_isPath hT a b).dropUntil hmz)
    rw [hpath] at hmem
    have hmem' : z' ∈ (treePath hT z b).support := List.mem_of_mem_tail hmem
    have hbtw := (mem_support_iff_between hT).1 hmem'
    have hzz : G.dist z z' = 0 := by omega
    exact eq_of_dist_eq_zero hT hzz

/-- **Three vertices of a tree have a median**: the last common vertex of the paths from `a` to
`b` and from `a` to `c`. -/
theorem exists_median (hT : G.IsTree) (a b c : V) :
    ∃ x : V, G.dist a x + G.dist x b = G.dist a b ∧
      G.dist b x + G.dist x c = G.dist b c ∧ G.dist a x + G.dist x c = G.dist a c := by
  classical
  set L : List V :=
    (treePath hT a b).support.filter (fun x => decide (x ∈ (treePath hT a c).support)) with hL
  have haL : a ∈ L := by
    rw [hL, List.mem_filter]
    exact ⟨SimpleGraph.Walk.start_mem_support _, by simp⟩
  obtain ⟨x, hx⟩ : ∃ x, L.argmax (fun y => G.dist a y) = some x := by
    cases h : L.argmax (fun y => G.dist a y) with
    | none =>
        have : L = [] := List.argmax_eq_none.1 h
        rw [this] at haL
        simp at haL
    | some m => exact ⟨m, rfl⟩
  have hxL : x ∈ L := List.argmax_mem hx
  have hxmax : ∀ y ∈ L, G.dist a y ≤ G.dist a x := fun y hy => List.le_of_mem_argmax hy hx
  have hxb : x ∈ (treePath hT a b).support := (List.mem_filter.1 hxL).1
  have hxc : x ∈ (treePath hT a c).support := by simpa using (List.mem_filter.1 hxL).2
  have hax : G.dist a x + G.dist x b = G.dist a b := (mem_support_iff_between hT).1 hxb
  refine ⟨x, hax, ?_, (mem_support_iff_between hT).1 hxc⟩
  set Q1 := (treePath hT a b).dropUntil x hxb with hQ1def
  set Q2 := (treePath hT a c).dropUntil x hxc with hQ2def
  have hQ1 : Q1.IsPath := (treePath_isPath hT a b).dropUntil hxb
  have hQ2 : Q2.IsPath := (treePath_isPath hT a c).dropUntil hxc
  have hQ1eq : Q1 = treePath hT x b := eq_treePath hT _ hQ1
  have hQ2eq : Q2 = treePath hT x c := eq_treePath hT _ hQ2
  -- the two branches meet only at `x`
  have hdisj : ∀ y, y ∈ Q1.support → y ∈ Q2.support → y = x := by
    intro y hy1 hy2
    have h1 : G.dist x y + G.dist y b = G.dist x b := by
      rw [hQ1eq] at hy1; exact (mem_support_iff_between hT).1 hy1
    have hyb : y ∈ (treePath hT a b).support :=
      SimpleGraph.Walk.support_dropUntil_subset _ hxb hy1
    have hyc : y ∈ (treePath hT a c).support :=
      SimpleGraph.Walk.support_dropUntil_subset _ hxc hy2
    have hyL : y ∈ L := List.mem_filter.2 ⟨hyb, by simpa using hyc⟩
    have hay : G.dist a y + G.dist y b = G.dist a b := (mem_support_iff_between hT).1 hyb
    have hle := hxmax y hyL
    have hzero : G.dist x y = 0 := by omega
    exact (eq_of_dist_eq_zero hT hzero).symm
  -- so the two branches glue to the path from `b` to `c`
  have hpath : (Q1.reverse.append Q2).IsPath := by
    rw [SimpleGraph.Walk.isPath_def, SimpleGraph.Walk.support_append,
      SimpleGraph.Walk.support_reverse]
    refine List.Nodup.append (List.nodup_reverse.2 hQ1.support_nodup) ?_ ?_
    · have := hQ2.support_nodup
      rw [SimpleGraph.Walk.support_eq_cons Q2] at this
      exact this.of_cons
    · intro y hy1 hy2
      have hy1' : y ∈ Q1.support := by simpa using hy1
      have hy2' : y ∈ Q2.support := by
        rw [SimpleGraph.Walk.support_eq_cons Q2]
        exact List.mem_cons_of_mem _ hy2
      have hyx : y = x := hdisj y hy1' hy2'
      subst hyx
      have := hQ2.support_nodup
      rw [SimpleGraph.Walk.support_eq_cons Q2] at this
      exact (List.nodup_cons.1 this).1 hy2
  have hlen : (Q1.reverse.append Q2).length = G.dist b c := length_eq_dist_of_isPath hT hpath
  rw [SimpleGraph.Walk.length_append, SimpleGraph.Walk.length_reverse] at hlen
  have h1 : Q1.length = G.dist x b := length_eq_dist_of_isPath hT hQ1
  have h2 : Q2.length = G.dist x c := length_eq_dist_of_isPath hT hQ2
  have hbx : G.dist b x = G.dist x b := SimpleGraph.dist_comm
  omega

/-- The median of three vertices of a tree. -/
noncomputable def treeMed (hT : G.IsTree) (a b c : V) : V := (exists_median hT a b c).choose

theorem treeMed_spec (hT : G.IsTree) (a b c : V) :
    G.dist a (treeMed hT a b c) + G.dist (treeMed hT a b c) b = G.dist a b ∧
      G.dist b (treeMed hT a b c) + G.dist (treeMed hT a b c) c = G.dist b c ∧
      G.dist a (treeMed hT a b c) + G.dist (treeMed hT a b c) c = G.dist a c :=
  (exists_median hT a b c).choose_spec

/-- **Uniqueness of the median.** -/
theorem eq_treeMed (hT : G.IsTree) (a b c z : V) (h1 : G.dist a z + G.dist z b = G.dist a b)
    (h2 : G.dist b z + G.dist z c = G.dist b c) (h3 : G.dist a z + G.dist z c = G.dist a c) :
    z = treeMed hT a b c := by
  obtain ⟨k1, k2, k3⟩ := treeMed_spec hT a b c
  refine eq_of_between_of_dist_eq hT (b := b) h1 k1 ?_
  have hb : G.dist b z = G.dist z b := SimpleGraph.dist_comm
  have hb' : G.dist b (treeMed hT a b c) = G.dist (treeMed hT a b c) b := SimpleGraph.dist_comm
  omega

/-- **A tree is a median graph.**  With any base vertex a tree satisfies all the axioms of
`FiniteChains.MedianSimpleGraph`; in particular every vertex has at most one neighbour closer to
the base vertex, so the dimension bound holds. -/
noncomputable def toMedianSimpleGraph (hT : G.IsTree) (base : V) : MedianSimpleGraph V where
  G := G
  conn := hT.isConnected
  base := base
  med := treeMed hT
  med_ab a b c := (treeMed_spec hT a b c).1
  med_bc a b c := (treeMed_spec hT a b c).2.1
  med_ac a b c := (treeMed_spec hT a b c).2.2
  med_unique a b c z h1 h2 h3 := eq_treeMed hT a b c z h1 h2 h3
  dim_le := by
    intro w s hs
    have hcard : s.card ≤ 1 := by
      refine Finset.card_le_one.2 ?_
      intro u hu v hv
      obtain ⟨huadj, hudist⟩ := hs u hu
      obtain ⟨hvadj, hvdist⟩ := hs v hv
      have hu1 : G.dist u w = 1 := SimpleGraph.dist_eq_one_iff_adj.2 huadj
      have hv1 : G.dist v w = 1 := SimpleGraph.dist_eq_one_iff_adj.2 hvadj
      refine eq_of_between_of_dist_eq hT (a := base) (b := w) (by omega) (by omega) (by omega)
    omega

end Tree

end FiniteChains
