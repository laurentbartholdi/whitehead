import RequestProject.MedianWallSpace
import RequestProject.SquareComplexWallsSeparation

/-!
# Nonpositive curvature supplies the missing separation property

`RequestProject/SquareComplexWallsSphere.lean` shows that in a connected, simply connected
square complex the walls need not separate distinct vertices, and
`RequestProject/SquareComplexWallsSeparation.lean` isolates the standard criterion that repairs
this: *a shortest walk crosses every wall at most once*.  In the literature that criterion is
obtained from nonpositive curvature.  Here it is **proved**, with no further hypothesis, for a
square complex whose one-skeleton is a median graph — the standard combinatorial form of the
CAT(0) condition, and exactly the hypothesis under which
`RequestProject/CubeMedianGraph.lean` proves `ker d₂ = im d₃`.

The results, for a square complex `S` whose one-skeleton is the median graph `M` and whose
two-cells are nondegenerate:

* `FiniteChains.SquareComplex.medianWallSystem` — the partitions of the vertex set into the two
  sides of an edge form a system of walls of `S`;
* `FiniteChains.SquareComplex.median_geodesic_crossings` — **the criterion**: a shortest walk
  crosses every wall at most once;
* `FiniteChains.SquareComplex.median_separation` — hence distinct vertices are separated by a
  wall, which is the hypothesis `hsep` of `FiniteChains.SquareComplex.wallSpaceOf`;
* `FiniteChains.SquareComplex.medianWallSpace` — hence the vertices form a wall space and embed
  into its median dual cube complex.
-/

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains

universe u

namespace SquareComplex

open MedianGraph

variable {Vx : Type u} {S : SquareComplex Vx} {M : MedianSimpleGraph Vx}

section Compatible

variable (hadj : ∀ a b : Vx, S.adj a b ↔ M.G.Adj a b)

include hadj

/-- A walk of the complex is at least as long as the distance in the one-skeleton. -/
theorem dist_le_of_walk : ∀ (l : List Vx) (u v : Vx), S.IsWalkFrom u v l →
    M.G.dist u v + 1 ≤ l.length := by
  intro l
  induction l with
  | nil => intro u v h; exact absurd h.2.1 (by simp)
  | cons p t ih =>
      intro u v h
      obtain ⟨hw, hhead, hlast⟩ := h
      have hpu : p = u := by simpa using hhead
      subst hpu
      match t with
      | [] =>
          have hpv : p = v := by simpa using hlast
          subst hpv
          simp [SimpleGraph.dist_self]
      | q :: t' =>
          have hpq : S.adj p q := (List.isChain_cons_cons.mp hw).1
          have hw' : S.IsWalk (q :: t') := (List.isChain_cons_cons.mp hw).2
          have hlast' : (q :: t').getLast? = some v := by simpa using hlast
          have hih := ih q v ⟨hw', by simp, hlast'⟩
          have hd1 : M.G.dist p q = 1 :=
            SimpleGraph.dist_eq_one_iff_adj.mpr ((hadj p q).mp hpq)
          have htri : M.G.dist p v ≤ M.G.dist p q + M.G.dist q v := M.conn.dist_triangle
          simp only [List.length_cons] at hih ⊢
          omega

/-- Between any two vertices there is a walk of the complex with exactly `dist + 1` vertices. -/
theorem exists_walk_dist : ∀ (n : ℕ) (u v : Vx), M.G.dist u v = n →
    ∃ l : List Vx, S.IsWalkFrom u v l ∧ l.length = n + 1 := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro u v hd
  rcases Nat.eq_zero_or_pos n with rfl | hpos
  · have huv : u = v := (M.toMedianGraph).eq_of_dist_eq_zero hd
    subst huv
    exact ⟨[u], ⟨by simp [IsWalk], by simp, by simp⟩, by simp⟩
  · have huv : u ≠ v := by
      rintro rfl
      rw [SimpleGraph.dist_self] at hd
      omega
    obtain ⟨c, huc, hcv⟩ := M.hasSteps u v huv
    simp only [MedianSimpleGraph.toMedianGraph_dist] at huc hcv
    have hadjuc : S.adj u c := (hadj u c).mpr (SimpleGraph.dist_eq_one_iff_adj.mp huc)
    obtain ⟨l, hl, hlen⟩ := ih (M.G.dist c v) (by omega) c v rfl
    obtain ⟨hw, hhead, hlast⟩ := hl
    refine ⟨u :: l, ⟨?_, by simp, ?_⟩, ?_⟩
    · rcases List.exists_cons_of_ne_nil (show l ≠ [] by
        rintro rfl; simp at hhead) with ⟨a, t, rfl⟩
      have hac : a = c := by simpa using hhead
      subst hac
      exact List.isChain_cons_cons.mpr ⟨hadjuc, hw⟩
    · rcases List.exists_cons_of_ne_nil (show l ≠ [] by
        rintro rfl; simp at hhead) with ⟨a, t, rfl⟩
      simpa using hlast
    · simp only [List.length_cons, hlen]
      omega

/-- **A shortest walk of the complex has exactly `dist + 1` vertices.** -/
theorem geodesic_length (hgeo : S.IsGeodesic u v l) : l.length = M.G.dist u v + 1 := by
  obtain ⟨m, hm, hmlen⟩ := exists_walk_dist hadj (M.G.dist u v) u v rfl
  have h1 := dist_le_of_walk hadj l u v hgeo.1
  have h2 := hgeo.2 m hm
  omega

end Compatible

/-! ### The walls of a median square complex -/

section Walls

variable (hadj : ∀ a b : Vx, S.adj a b ↔ M.G.Adj a b)
    (hsq : ∀ {a b c d : Vx}, S.sq a b c d → a ≠ c ∧ b ≠ d)

include hadj hsq

/-- **Opposite sides of a two-cell cross the same walls.**  This is where convexity of the
halfspaces of a median graph is used. -/
theorem square_not_wallRel {R : Vx → Vx → Prop} (hR : R ∈ (M.toMedianGraph).Walls)
    {a b c d : Vx} (hsquare : S.sq a b c d) (h : ¬ R a b) : ¬ R c d := by
  obtain ⟨X, Y, hXY, rfl⟩ := hR
  obtain ⟨hac, hbd⟩ := hsq hsquare
  obtain ⟨hab, hbc, hcd, hda⟩ := S.sq_adj hsquare
  have dab : M.G.dist a b = 1 := SimpleGraph.dist_eq_one_iff_adj.mpr ((hadj a b).mp hab)
  have dbc : M.G.dist b c = 1 := SimpleGraph.dist_eq_one_iff_adj.mpr ((hadj b c).mp hbc)
  have dcd : M.G.dist c d = 1 := SimpleGraph.dist_eq_one_iff_adj.mpr ((hadj c d).mp hcd)
  have dda : M.G.dist d a = 1 := SimpleGraph.dist_eq_one_iff_adj.mpr ((hadj d a).mp hda)
  have dba : M.G.dist b a = 1 := by rw [SimpleGraph.dist_comm]; exact dab
  have dad : M.G.dist a d = 1 := by rw [SimpleGraph.dist_comm]; exact dda
  have hYX : (M.toMedianGraph).dist Y X = 1 := by
    rw [(M.toMedianGraph).dist_comm]; exact hXY
  have dcb : M.G.dist c b = 1 := by rw [SimpleGraph.dist_comm]; exact dbc
  have hac2 : M.G.dist a c = 2 :=
    MedianGraph.dist_eq_two_of_common_neighbour (G := M.toMedianGraph) dab dcb hac
  have hbd2 : M.G.dist b d = 2 :=
    MedianGraph.dist_eq_two_of_common_neighbour (G := M.toMedianGraph) dba dda hbd
  intro hcd'
  unfold wallRel at h hcd'
  by_cases ha : (M.toMedianGraph).Side X Y a
  · have hb : ¬ (M.toMedianGraph).Side X Y b := fun hb => h (iff_of_true ha hb)
    by_cases hc : (M.toMedianGraph).Side X Y c
    · -- `b` lies between `a` and `c`, both on the `X`-side
      refine hb (MedianGraph.side_convex hXY M.hasSteps a c b ha hc ?_)
      show M.G.dist a b + M.G.dist b c = M.G.dist a c
      rw [dab, dbc, hac2]
    · -- `d` is on the far side too, and `a` lies between `b` and `d`
      have hd : ¬ (M.toMedianGraph).Side X Y d := fun hd => hc (hcd'.mpr hd)
      have hb' : (M.toMedianGraph).Side Y X b := by
        rcases MedianGraph.side_dichotomy hXY b with h' | h'
        · exact absurd h' hb
        · exact h'
      have hd' : (M.toMedianGraph).Side Y X d := by
        rcases MedianGraph.side_dichotomy hXY d with h' | h'
        · exact absurd h' hd
        · exact h'
      refine absurd (MedianGraph.side_convex hYX M.hasSteps b d a hb' hd' ?_) ?_
      · show M.G.dist b a + M.G.dist a d = M.G.dist b d
        rw [dba, dad, hbd2]
      · intro hcon
        exact MedianGraph.not_side_both ha hcon
  · have hb : (M.toMedianGraph).Side X Y b := by
      by_contra hb
      exact h (iff_of_false ha hb)
    have ha' : (M.toMedianGraph).Side Y X a := by
      rcases MedianGraph.side_dichotomy hXY a with h' | h'
      · exact absurd h' ha
      · exact h'
    by_cases hc : (M.toMedianGraph).Side X Y c
    · -- `a` is on the far side, `b` and `d` on the `X`-side, and `a` lies between them
      have hd : (M.toMedianGraph).Side X Y d := hcd'.mp hc
      refine absurd (MedianGraph.side_convex hXY M.hasSteps b d a hb hd ?_) ?_
      · show M.G.dist b a + M.G.dist a d = M.G.dist b d
        rw [dba, dad, hbd2]
      · intro hcon
        exact MedianGraph.not_side_both hcon ha'
    · have hd : ¬ (M.toMedianGraph).Side X Y d := fun hd => hc (hcd'.mpr hd)
      have hc' : (M.toMedianGraph).Side Y X c := by
        rcases MedianGraph.side_dichotomy hXY c with h' | h'
        · exact absurd h' hc
        · exact h'
      -- `b` lies between `a` and `c`, both on the `Y`-side
      refine absurd (MedianGraph.side_convex hYX M.hasSteps a c b ha' hc' ?_) ?_
      · show M.G.dist a b + M.G.dist b c = M.G.dist a c
        rw [dab, dbc, hac2]
      · intro hcon
        exact MedianGraph.not_side_both hb hcon

open Classical in
/-- The label of the wall `R`: an edge crosses it when its endpoints lie on different sides. -/
noncomputable def wallLabel (R : (M.toMedianGraph).Walls) : Vx → Vx → ZMod 2 :=
  fun a b => if R.1 a b then 0 else 1

open Classical in
/-- **The walls of the one-skeleton form a system of walls of the square complex.** -/
noncomputable def medianWallSystem : S.WallSystem (M.toMedianGraph).Walls where
  χ := wallLabel
  isWall := by
    intro R
    refine ⟨?_, ?_⟩
    · intro a b
      simp only [wallLabel]
      by_cases h : R.1 a b
      · rw [if_pos h, if_pos (walls_symm R.2 h)]
      · rw [if_neg h, if_neg (fun hcon => h (walls_symm R.2 hcon))]
    · intro a b c d hsquare
      simp only [wallLabel]
      by_cases h : R.1 a b
      · have hcd2 : R.1 c d := by
          by_contra hno
          exact square_not_wallRel hadj hsq R.2 (S.sq_rotate (S.sq_rotate hsquare)) hno h
        rw [if_pos h, if_pos hcd2]
      · rw [if_neg h, if_neg (square_not_wallRel hadj hsq R.2 hsquare h)]
  edge_unique := by
    intro u v huv
    have hd : (M.toMedianGraph).dist u v = 1 :=
      SimpleGraph.dist_eq_one_iff_adj.mpr ((hadj u v).mp huv)
    refine ⟨⟨(M.toMedianGraph).wallRel u v, wallRel_mem_walls hd⟩, ?_, ?_⟩
    · simp only [wallLabel]
      rw [if_neg (not_wallRel_self hd)]
    · intro R hR
      have hno : ¬ R.1 u v := by
        simp only [wallLabel] at hR
        by_cases h : R.1 u v
        · rw [if_pos h] at hR
          exact absurd hR (by decide)
        · exact h
      exact Subtype.ext (walls_eq_of_crossing M.hasSteps R.2 hd hno)

open Classical in
/-- The halfspace coordinates of the vertices: which side of each wall a vertex is on, relative
to the base vertex `x₀`. -/
noncomputable def wallCoord (x₀ : Vx) (R : (M.toMedianGraph).Walls) : Vx → ZMod 2 :=
  fun v => if R.1 v x₀ then 0 else 1

open Classical in
theorem wallCoord_add (x₀ : Vx) (R : (M.toMedianGraph).Walls) (u v : Vx) :
    wallCoord x₀ R u + wallCoord x₀ R v = (medianWallSystem hadj hsq).χ R u v := by
  have hkey := walls_side_ne_iff R.2 x₀ u v
  simp only [wallCoord, medianWallSystem, wallLabel]
  by_cases huv : R.1 u v
  · have : (R.1 u x₀ ↔ R.1 v x₀) := by
      by_contra hcon
      exact (hkey.1 hcon) huv
    rw [if_pos huv]
    by_cases hu : R.1 u x₀
    · rw [if_pos hu, if_pos (this.mp hu)]; decide
    · rw [if_neg hu, if_neg (fun hv => hu (this.mpr hv))]; decide
  · have hne : ¬ (R.1 u x₀ ↔ R.1 v x₀) := hkey.2 huv
    rw [if_neg huv]
    by_cases hu : R.1 u x₀
    · have hv : ¬ R.1 v x₀ := fun hv => hne (iff_of_true hu hv)
      rw [if_pos hu, if_neg hv]; decide
    · have hv : R.1 v x₀ := by
        by_contra hv
        exact hne (iff_of_false hu hv)
      rw [if_neg hu, if_pos hv]; decide

open Classical in
/-- **The criterion, proved**: in a square complex whose one-skeleton is a median graph, a
shortest walk crosses every wall at most once. -/
theorem median_geodesic_crossings (x₀ : Vx) :
    ∀ (u v : Vx) (l : List Vx), S.IsGeodesic u v l →
      ∀ R : (M.toMedianGraph).Walls, crossCount ((medianWallSystem hadj hsq).χ R) l ≤ 1 := by
  classical
  refine geodesic_crossings_of_metric (medianWallSystem hadj hsq)
    (σ := wallCoord x₀) (fun R u v _ => wallCoord_add hadj hsq x₀ R u v) ?_ ?_
  · intro u v
    obtain ⟨T, hT, -⟩ := MedianGraph.dist_eq_card_sepWalls M.hasSteps u v
    refine ⟨T, fun R => ?_⟩
    rw [hT R]
    constructor
    · intro hR
      have hne : ¬ (R.1 u x₀ ↔ R.1 v x₀) := (walls_side_ne_iff R.2 x₀ u v).2 hR
      simp only [wallCoord]
      by_cases hu : R.1 u x₀
      · have hv : ¬ R.1 v x₀ := fun hv => hne (iff_of_true hu hv)
        rw [if_pos hu, if_neg hv]
        decide
      · have hv : R.1 v x₀ := by
          by_contra hv
          exact hne (iff_of_false hu hv)
        rw [if_neg hu, if_pos hv]
        decide
    · intro hR
      refine (walls_side_ne_iff R.2 x₀ u v).1 ?_
      intro hiff
      refine hR ?_
      simp only [wallCoord]
      by_cases hu : R.1 u x₀
      · rw [if_pos hu, if_pos (hiff.mp hu)]
      · rw [if_neg hu, if_neg (fun hv => hu (hiff.mpr hv))]
  · intro u v l hg T hT
    obtain ⟨T', hT', hcard⟩ := MedianGraph.dist_eq_card_sepWalls M.hasSteps u v
    have hTT : T = T' := by
      ext R
      rw [hT R, hT' R]
      constructor
      · intro hR
        refine (walls_side_ne_iff R.2 x₀ u v).1 ?_
        intro hiff
        refine hR ?_
        simp only [wallCoord]
        by_cases hu : R.1 u x₀
        · rw [if_pos hu, if_pos (hiff.mp hu)]
        · rw [if_neg hu, if_neg (fun hv => hu (hiff.mpr hv))]
      · intro hR
        have hne : ¬ (R.1 u x₀ ↔ R.1 v x₀) := (walls_side_ne_iff R.2 x₀ u v).2 hR
        simp only [wallCoord]
        by_cases hu : R.1 u x₀
        · have hv : ¬ R.1 v x₀ := fun hv => hne (iff_of_true hu hv)
          rw [if_pos hu, if_neg hv]
          decide
        · have hv : R.1 v x₀ := by
            by_contra hv
            exact hne (iff_of_false hu hv)
          rw [if_neg hu, if_pos hv]
          decide
    rw [hTT, hcard, geodesic_length hadj hg]
    rfl

open Classical in
/-- **Separation, unconditionally, in the nonpositively curved case**: in a square complex whose
one-skeleton is a median graph distinct vertices lie on different sides of some wall.  This is
the hypothesis `hsep` of `FiniteChains.SquareComplex.wallSpaceOf`, shown in
`RequestProject/SquareComplexWallsSphere.lean` not to follow from simple connectivity alone. -/
theorem median_separation (x₀ : Vx) :
    ∀ u v : Vx, u ≠ v → ∃ R : (M.toMedianGraph).Walls, wallCoord x₀ R u ≠ wallCoord x₀ R v := by
  classical
  refine separation_of_geodesic_crossings (medianWallSystem hadj hsq)
    (fun R u v _ => wallCoord_add hadj hsq x₀ R u v) ?_
    (median_geodesic_crossings hadj hsq x₀)
  intro u v
  obtain ⟨l, hl, -⟩ := exists_walk_dist hadj (M.G.dist u v) u v rfl
  exact ⟨l, hl⟩

omit hsq in
/-- The complex is connected: any two vertices are joined by a walk. -/
theorem median_conn : ∀ u v : Vx, ∃ l : List Vx, S.IsWalkFrom u v l := by
  intro u v
  obtain ⟨l, hl, -⟩ := exists_walk_dist hadj (M.G.dist u v) u v rfl
  exact ⟨l, hl⟩

omit hadj hsq in
open Classical in
/-- Only finitely many walls separate a vertex from the base vertex. -/
theorem wallCoord_finite (x₀ v : Vx) :
    {R : (M.toMedianGraph).Walls | wallCoord x₀ R v ≠ wallCoord x₀ R x₀}.Finite := by
  classical
  refine Set.Finite.subset (MedianGraph.sepWalls_finite M.hasSteps v x₀) ?_
  intro R hR
  simp only [Set.mem_setOf_eq, wallCoord] at hR ⊢
  intro hv
  rw [if_pos hv, if_pos (walls_refl R.2 x₀)] at hR
  exact hR rfl

open Classical in
/-- **The vertices of a median square complex form a wall space**, and hence (by
`FiniteChains.SquareComplex.wallSpaceOf_coord_injective`) embed into its median dual cube
complex.  No simple connectivity or finiteness is assumed: the one-skeleton being median is
enough. -/
noncomputable def medianWallSpace (x₀ : Vx) : WallSpace Vx (M.toMedianGraph).Walls :=
  wallSpaceOf_of_geodesic_crossings (medianWallSystem hadj hsq) (x₀ := x₀)
    (wallCoord_finite x₀) (fun R u v _ => wallCoord_add hadj hsq x₀ R u v)
    (median_conn hadj) (median_geodesic_crossings hadj hsq x₀)

end Walls

end SquareComplex

namespace MedianSimpleGraph

variable {Vx : Type u} (M : MedianSimpleGraph Vx)

/-- The square complex of a median graph: its one-skeleton is the graph, and its two-cells are
the four-cycles of the graph. -/
def toSquareComplex : SquareComplex Vx where
  adj := M.G.Adj
  adj_symm := fun h => M.G.symm.symm _ _ h
  adj_irrefl := fun _ h => M.G.irrefl h
  sq a b c d := M.G.Adj a b ∧ M.G.Adj b c ∧ M.G.Adj c d ∧ M.G.Adj d a ∧ a ≠ c ∧ b ≠ d
  sq_adj := fun h => ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1⟩
  sq_rotate := fun ⟨hab, hbc, hcd, hda, hac, hbd⟩ =>
    ⟨hbc, hcd, hda, hab, hbd, fun h => hac h.symm⟩
  sq_reverse := fun ⟨hab, hbc, hcd, hda, hac, hbd⟩ =>
    ⟨M.G.symm.symm _ _ hcd, M.G.symm.symm _ _ hbc, M.G.symm.symm _ _ hab, M.G.symm.symm _ _ hda, fun h => hbd h.symm, fun h =>
      hac h.symm⟩

theorem toSquareComplex_adj (a b : Vx) : (M.toSquareComplex).adj a b ↔ M.G.Adj a b := Iff.rfl

theorem toSquareComplex_sq_nondeg {a b c d : Vx} (h : (M.toSquareComplex).sq a b c d) :
    a ≠ c ∧ b ≠ d := ⟨h.2.2.2.2.1, h.2.2.2.2.2⟩

open Classical in
/-- **Non-vacuity of the criterion**: for the square complex of a median graph, distinct
vertices are separated by a wall. -/
theorem toSquareComplex_separation (x₀ : Vx) :
    ∀ u v : Vx, u ≠ v → ∃ R : (M.toMedianGraph).Walls,
      SquareComplex.wallCoord x₀ R u ≠ SquareComplex.wallCoord x₀ R v :=
  SquareComplex.median_separation (S := M.toSquareComplex) (M := M)
    (fun _ _ => Iff.rfl) (fun h => M.toSquareComplex_sq_nondeg h) x₀

end MedianSimpleGraph

end FiniteChains
