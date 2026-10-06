import RequestProject.SquareComplexMonodromy
import RequestProject.SquareComplexUniversalCover

/-!
# Existence of the universal cover of a square complex

`RequestProject/SquareComplexUniversalCover.lean` proves that a connected, simply connected
covering of a square complex is unique up to isomorphism over the base.  This file constructs
one, so that the universal cover exists for every square complex:

* `FiniteChains.SquareComplex.UnivVx` — the vertices are pairs (a vertex `y`, a homotopy class
  of walks from the base point to `y`);
* `FiniteChains.SquareComplex.univCover` — the square complex structure: an edge joins two
  classes when one is obtained from the other by appending an edge, and a square is a square of
  the base whose four corners are joined in this way;
* `FiniteChains.SquareComplex.isCovering_univProj` — the projection to the base is a covering;
* `FiniteChains.SquareComplex.univCover_walkConnected`,
  `FiniteChains.SquareComplex.univCover_simplyConnectedW` — it is connected and simply connected;
* `FiniteChains.SquareComplex.exists_universal_cover` — hence every square complex has a
  connected, simply connected covering, which by
  `FiniteChains.SquareComplex.exists_iso_of_universal` is unique over the base.
-/

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains

namespace SquareComplex

universe u

variable {Vx : Type u}

/-- The vertex set of the universal cover: a vertex of the base together with a homotopy class,
through walks, of walks from the base point to it. -/
def UnivVx (S : SquareComplex Vx) (b₀ : Vx) : Type u := Σ y : Vx, Quotient (walkSetoid S b₀ y)

variable {S : SquareComplex Vx} {b₀ : Vx}

/-- Appending an edge to a homotopy class of walks. -/
def extendCls {y z : Vx} (h : S.adj y z) (c : Quotient (walkSetoid S b₀ y)) :
    Quotient (walkSetoid S b₀ z) :=
  Quotient.lift
    (fun w : (toSimpleGraph S).Walk b₀ y => Quotient.mk (walkSetoid S b₀ z)
      (w.append (SimpleGraph.Walk.cons h SimpleGraph.Walk.nil)))
    (fun _ _ hpq => Quotient.sound (walkHtpy_append_right hpq _)) c

@[simp] theorem extendCls_mk {y z : Vx} (h : S.adj y z) (w : (toSimpleGraph S).Walk b₀ y) :
    extendCls (b₀ := b₀) h (Quotient.mk (walkSetoid S b₀ y) w)
      = Quotient.mk (walkSetoid S b₀ z)
          (w.append (SimpleGraph.Walk.cons h SimpleGraph.Walk.nil)) := rfl

/-- Appending an edge and then the same edge backwards changes nothing. -/
theorem extendCls_extendCls {y z : Vx} (h : S.adj y z) (h' : S.adj z y)
    (c : Quotient (walkSetoid S b₀ y)) : extendCls h' (extendCls h c) = c := by
  refine Quotient.inductionOn c fun w => ?_
  refine Quotient.sound ?_
  set e : (toSimpleGraph S).Walk y z := SimpleGraph.Walk.cons h SimpleGraph.Walk.nil with he
  have hrev : (SimpleGraph.Walk.cons h' SimpleGraph.Walk.nil : (toSimpleGraph S).Walk z y)
      = e.reverse := by
    rw [he]
    simp
  show S.WalkHtpy ((w.append e).append (SimpleGraph.Walk.cons h' SimpleGraph.Walk.nil)) w
  rw [hrev, ← SimpleGraph.Walk.append_assoc]
  have h1 : S.WalkHtpy (w.append (e.append e.reverse)) (w.append SimpleGraph.Walk.nil) :=
    walkHtpy_append_left w (walkHtpy_append_reverse e)
  rwa [SimpleGraph.Walk.append_nil] at h1

/-- Running once around a square changes nothing. -/
theorem extendCls_sq {a b c d : Vx} (hsq : S.sq a b c d) (hab : S.adj a b) (hbc : S.adj b c)
    (hcd : S.adj c d) (hda : S.adj d a) (c₀ : Quotient (walkSetoid S b₀ a)) :
    extendCls hda (extendCls hcd (extendCls hbc (extendCls hab c₀))) = c₀ := by
  refine Quotient.inductionOn c₀ fun w => ?_
  refine Quotient.sound ?_
  set bdry : (toSimpleGraph S).Walk a a :=
    SimpleGraph.Walk.cons hab (SimpleGraph.Walk.cons hbc
      (SimpleGraph.Walk.cons hcd (SimpleGraph.Walk.cons hda SimpleGraph.Walk.nil))) with hbdry
  have hassoc :
      ((((w.append (SimpleGraph.Walk.cons hab SimpleGraph.Walk.nil)).append
          (SimpleGraph.Walk.cons hbc SimpleGraph.Walk.nil)).append
          (SimpleGraph.Walk.cons hcd SimpleGraph.Walk.nil)).append
          (SimpleGraph.Walk.cons hda SimpleGraph.Walk.nil)) = w.append bdry := by
    rw [hbdry, ← SimpleGraph.Walk.append_assoc, ← SimpleGraph.Walk.append_assoc,
      ← SimpleGraph.Walk.append_assoc]
    rfl
  show S.WalkHtpy _ w
  rw [hassoc]
  have hcontr : S.WalkHtpy bdry SimpleGraph.Walk.nil := by
    have hsupp : bdry.support = [a, b, c, d, a] := by
      rw [hbdry]; simp
    show S.WalkHomotopic bdry.support (SimpleGraph.Walk.nil : (toSimpleGraph S).Walk a a).support
    rw [hsupp]
    simpa using walkHomotopic_sq_boundary hsq
  have h1 : S.WalkHtpy (w.append bdry) (w.append SimpleGraph.Walk.nil) :=
    walkHtpy_append_left w hcontr
  rwa [SimpleGraph.Walk.append_nil] at h1

/-- Adjacency in the universal cover: the class of the second vertex is that of the first,
extended by the edge joining them. -/
def univAdj (P Q : UnivVx S b₀) : Prop := ∃ h : S.adj P.1 Q.1, Q.2 = extendCls h P.2

/-- The vertex of the universal cover obtained by extending `P` along an edge. -/
def extVx (P : UnivVx S b₀) {z : Vx} (h : S.adj P.1 z) : UnivVx S b₀ := ⟨z, extendCls h P.2⟩

theorem univAdj_extVx (P : UnivVx S b₀) {z : Vx} (h : S.adj P.1 z) : univAdj P (extVx P h) :=
  ⟨h, rfl⟩

theorem univAdj_symm {P Q : UnivVx S b₀} (h : univAdj P Q) : univAdj Q P := by
  obtain ⟨hadj, hc⟩ := h
  refine ⟨S.adj_symm hadj, ?_⟩
  rw [hc, extendCls_extendCls]

theorem univAdj_irrefl (P : UnivVx S b₀) : ¬ univAdj P P := by
  rintro ⟨hadj, -⟩
  exact S.adj_irrefl P.1 hadj

/-- Two-cells of the universal cover: a two-cell of the base whose four corners are joined by
edges of the cover. -/
def univSq (P Q R T : UnivVx S b₀) : Prop :=
  S.sq P.1 Q.1 R.1 T.1 ∧ univAdj P Q ∧ univAdj Q R ∧ univAdj R T ∧ univAdj T P

/-- **The universal cover** of a square complex, based at `b₀`. -/
def univCover (S : SquareComplex Vx) (b₀ : Vx) : SquareComplex (UnivVx S b₀) where
  adj := univAdj
  adj_symm := univAdj_symm
  adj_irrefl := univAdj_irrefl
  sq := univSq
  sq_adj := by
    rintro P Q R T ⟨-, h1, h2, h3, h4⟩
    exact ⟨h1, h2, h3, h4⟩
  sq_rotate := by
    rintro P Q R T ⟨hsq, h1, h2, h3, h4⟩
    exact ⟨S.sq_rotate hsq, h2, h3, h4, h1⟩
  sq_reverse := by
    rintro P Q R T ⟨hsq, h1, h2, h3, h4⟩
    exact ⟨S.sq_reverse hsq, univAdj_symm h3, univAdj_symm h2, univAdj_symm h1,
      univAdj_symm h4⟩

/-- The projection of the universal cover to the base. -/
def univProj (S : SquareComplex Vx) (b₀ : Vx) : UnivVx S b₀ → Vx := Sigma.fst

@[simp] theorem univProj_apply (P : UnivVx S b₀) : univProj S b₀ P = P.1 := rfl

/-- **The projection of the universal cover is a covering.** -/
theorem isCovering_univProj (S : SquareComplex Vx) (b₀ : Vx) :
    IsCovering (univCover S b₀) S (univProj S b₀) where
  map_adj := by
    rintro P Q ⟨hadj, -⟩
    exact hadj
  map_sq := by
    rintro P Q R T ⟨hsq, -⟩
    exact hsq
  lift_adj := by
    intro P w hw
    refine ⟨extVx P hw, ⟨univAdj_extVx P hw, rfl⟩, ?_⟩
    rintro ⟨y, cy⟩ ⟨⟨hadj, hc⟩, hy⟩
    have hy' : y = w := hy
    subst hy'
    exact congrArg (fun c => (⟨y, c⟩ : UnivVx S b₀)) hc
  lift_sq := by
    intro P b c d hsq
    obtain ⟨hab, hbc, hcd, hda⟩ := S.sq_adj hsq
    refine ⟨extVx P hab, extVx (extVx P hab) hbc, extVx (extVx (extVx P hab) hbc) hcd,
      ⟨?_, ?_, ?_, ?_, ?_⟩, rfl, rfl, rfl⟩
    · exact hsq
    · exact univAdj_extVx _ _
    · exact univAdj_extVx _ _
    · exact univAdj_extVx _ _
    · refine ⟨hda, ?_⟩
      exact (extendCls_sq hsq hab hbc hcd hda P.2).symm

/-! ### The universal cover is connected and simply connected -/

/-- The base point of the universal cover. -/
def univBase (S : SquareComplex Vx) (b₀ : Vx) : UnivVx S b₀ :=
  ⟨b₀, Quotient.mk (walkSetoid S b₀ b₀) SimpleGraph.Walk.nil⟩

@[simp] theorem univProj_univBase : univProj S b₀ (univBase S b₀) = b₀ := rfl

/-- Lifting a walk of the base to the universal cover appends it to the class of the starting
vertex. -/
theorem liftEnd_univ : ∀ {y z : Vx} (v : (toSimpleGraph S).Walk y z)
    (w : (toSimpleGraph S).Walk b₀ y),
    (isCovering_univProj S b₀).liftEnd v ⟨y, Quotient.mk (walkSetoid S b₀ y) w⟩
      = ⟨z, Quotient.mk (walkSetoid S b₀ z) (w.append v)⟩ := by
  intro y z v
  induction v with
  | nil => intro w; simp
  | @cons y' m z' hadj q ih =>
      intro w
      set P : UnivVx S b₀ := ⟨y', Quotient.mk (walkSetoid S b₀ y') w⟩ with hPdef
      have hadj' : S.adj (univProj S b₀ P) m := hadj
      obtain ⟨h1, h2⟩ := (isCovering_univProj S b₀).edgeLift_spec hadj'
      have hstep : (isCovering_univProj S b₀).edgeLift P m = extVx P hadj :=
        (isCovering_univProj S b₀).edge_unique h1 (univAdj_extVx P hadj) (by rw [h2]; rfl)
      rw [IsCovering.liftEnd_cons, hstep]
      have hext : extVx P hadj
          = ⟨m, Quotient.mk (walkSetoid S b₀ m)
              (w.append (SimpleGraph.Walk.cons hadj SimpleGraph.Walk.nil))⟩ := rfl
      rw [hext, ih (w.append (SimpleGraph.Walk.cons hadj SimpleGraph.Walk.nil))]
      have hw : (w.append (SimpleGraph.Walk.cons hadj SimpleGraph.Walk.nil)).append q
          = w.append (SimpleGraph.Walk.cons hadj q) := by
        rw [← SimpleGraph.Walk.append_assoc]
        rfl
      rw [hw]

/-- **The universal cover is connected.** -/
theorem univCover_walkConnected (S : SquareComplex Vx) (b₀ : Vx) :
    (univCover S b₀).WalkConnected := by
  have key : ∀ P : UnivVx S b₀, (univCover S b₀).ReachableFrom (univBase S b₀) P := by
    rintro ⟨y, c⟩
    refine Quotient.inductionOn c ?_
    intro w
    obtain ⟨lt, hw, hh, hlast, -⟩ :=
      (isCovering_univProj S b₀).liftEnd_spec w (univBase S b₀) rfl
    have hend : (isCovering_univProj S b₀).liftEnd w (univBase S b₀)
        = ⟨y, Quotient.mk (walkSetoid S b₀ y) w⟩ :=
      liftEnd_univ w SimpleGraph.Walk.nil
    rw [hend] at hlast
    exact ⟨lt, hw, hh, hlast⟩
  intro P Q
  exact (key P).symm.trans (key Q)

/-- **The universal cover is simply connected.** -/
theorem univCover_simplyConnectedW (S : SquareComplex Vx) (b₀ : Vx) :
    (univCover S b₀).SimplyConnectedW := by
  intro P lt hlt
  have hp := isCovering_univProj S b₀
  obtain ⟨y, c⟩ := P
  obtain ⟨u, rfl⟩ := Quotient.exists_rep c
  have hmapwalk : S.IsWalkFrom y y (lt.map (univProj S b₀)) := by
    refine ⟨hp.map_isWalk hlt.1, ?_, ?_⟩
    · rw [List.head?_map, hlt.2.1]; rfl
    · rw [List.getLast?_map, hlt.2.2]; rfl
  obtain ⟨w, hwsupp⟩ := exists_walk_of_isWalkFrom hmapwalk
  have hlift : lt.getLast? = some (hp.liftEnd w ⟨y, Quotient.mk (walkSetoid S b₀ y) u⟩) :=
    hp.liftEnd_eq_of_lift w hlt.1 hlt.2.1 (by rw [hwsupp])
  rw [liftEnd_univ w u, hlt.2.2] at hlift
  have hlift' : (⟨y, Quotient.mk (walkSetoid S b₀ y) u⟩ :
        Σ z : Vx, Quotient (walkSetoid S b₀ z))
      = ⟨y, Quotient.mk (walkSetoid S b₀ y) (u.append w)⟩ := Option.some.inj hlift
  have hcls : Quotient.mk (walkSetoid S b₀ y) u
      = Quotient.mk (walkSetoid S b₀ y) (u.append w) := by
    simp only [Sigma.mk.injEq, heq_eq_eq, true_and] at hlift'
    exact hlift'
  have h1 : S.WalkHtpy (u.append w) u := (Quotient.eq.1 hcls).symm
  have hB : S.WalkHtpy (u.reverse.append u) SimpleGraph.Walk.nil := by
    have := walkHtpy_append_reverse u.reverse
    rwa [SimpleGraph.Walk.reverse_reverse] at this
  have hw_nil : S.WalkHtpy w SimpleGraph.Walk.nil := by
    have hC : S.WalkHtpy ((u.reverse.append u).append w) w := by
      have := walkHtpy_append_right hB w
      rwa [SimpleGraph.Walk.nil_append] at this
    have hA : S.WalkHtpy (u.reverse.append (u.append w)) (u.reverse.append u) :=
      walkHtpy_append_left u.reverse h1
    rw [SimpleGraph.Walk.append_assoc] at hA
    exact ((WalkHtpy.symm hC).trans hA).trans hB
  have hdown : S.WalkHomotopic (lt.map (univProj S b₀)) [y] := by
    have hws : S.WalkHomotopic w.support
        (SimpleGraph.Walk.nil : (toSimpleGraph S).Walk y y).support := hw_nil
    rw [hwsupp] at hws
    simpa using hws
  obtain ⟨lt', hw', hh', hmap', hhom⟩ := hp.lift_walkHomotopic hdown hlt.1 rfl
  have hlt' : lt' = [(⟨y, Quotient.mk (walkSetoid S b₀ y) u⟩ : UnivVx S b₀)] := by
    cases lt' with
    | nil => simp at hmap'
    | cons z t =>
        have hz : univProj S b₀ z = y ∧ t.map (univProj S b₀) = [] := by
          simpa using hmap'
        have ht : t = [] := List.map_eq_nil_iff.1 hz.2
        subst ht
        have hzP : z = (⟨y, Quotient.mk (walkSetoid S b₀ y) u⟩ : UnivVx S b₀) := by
          rw [hlt.2.1] at hh'
          simpa using hh'
        rw [hzP]
  rw [hlt'] at hhom
  exact hhom

/-- **Every square complex has a universal cover**: a connected, simply connected covering. -/
theorem exists_universal_cover (S : SquareComplex Vx) (b₀ : Vx) :
    ∃ (Vu : Type u) (U : SquareComplex Vu) (q : Vu → Vx) (u₀ : Vu),
      IsCovering U S q ∧ U.WalkConnected ∧ U.SimplyConnectedW ∧ q u₀ = b₀ :=
  ⟨UnivVx S b₀, univCover S b₀, univProj S b₀, univBase S b₀, isCovering_univProj S b₀,
    univCover_walkConnected S b₀, univCover_simplyConnectedW S b₀, rfl⟩

/-- **Uniqueness of the universal cover**: every connected, simply connected covering of `S` is
isomorphic, over `S`, to the cover constructed here. -/
theorem univCover_unique {Vu : Type u} {U : SquareComplex Vu} {q : Vu → Vx}
    (hq : IsCovering U S q) (hUC : U.WalkConnected) (hUSC : U.SimplyConnectedW)
    {u₀ : Vu} (h0 : q u₀ = b₀) :
    ∃ f : Vu → UnivVx S b₀, Function.Bijective f ∧ f u₀ = univBase S b₀ ∧
      (∀ u, univProj S b₀ (f u) = q u) ∧
      (∀ u w, U.adj u w ↔ (univCover S b₀).adj (f u) (f w)) ∧
      (∀ a b c d, U.sq a b c d ↔ (univCover S b₀).sq (f a) (f b) (f c) (f d)) :=
  exists_iso_of_universal (isCovering_univProj S b₀) hq (univCover_walkConnected S b₀)
    (univCover_simplyConnectedW S b₀) hUC hUSC (t₀ := univBase S b₀) h0

end SquareComplex

end FiniteChains
