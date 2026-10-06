import RequestProject.MedianHalfspaces
import RequestProject.WallSpaceDualConnected

/-!
# A median graph is a wall space, and its walls count the distance

`RequestProject/MedianHalfspaces.lean` proves that the halfspaces of an edge of a median graph
are convex and that distinct vertices are separated by the wall of some edge.  This file draws
the consequences on the side of Sageev's construction developed in
`RequestProject/WallSpaceDual.lean`.

A **wall** of a median graph is the partition of the vertex set into the two sides of an edge,
recorded as the relation `wallRel X Y a b` — "`a` and `b` lie on the same side of the edge
`X–Y`".  The results are:

* `FiniteChains.MedianGraph.wallRel_eq_of_crossing` — a wall is determined by any edge crossing
  it, so every edge crosses exactly one wall;
* `FiniteChains.MedianGraph.exists_sepWalls_card` — the walls separating two vertices are
  finite in number, and that number is **exactly** the distance between them
  (`FiniteChains.MedianGraph.dist_eq_card_sepWalls`); in particular a shortest path crosses
  every wall at most once, which is the criterion isolated in
  `RequestProject/SquareComplexWallsSeparation.lean`;
* `FiniteChains.MedianGraph.wallSpace` — hence the vertices of a median graph form a wall space
  in the sense of `FiniteChains.WallSpace`, and
  `FiniteChains.MedianGraph.wallSpace_coord_injective`,
  `FiniteChains.MedianGraph.wallSpace_dsym_coord` — they embed isometrically into its median
  dual cube complex.

Together with `FiniteChains.WallSpace.dualModel` (the dual complex of a wall space is median)
this closes the circle: median graphs and wall spaces determine one another.
-/

namespace FiniteChains

universe u

namespace MedianGraph

variable {Vx : Type u} {G : MedianGraph Vx}

/-- The wall of the edge `X–Y`, recorded as the relation "lie on the same side of `X–Y`". -/
def wallRel (G : MedianGraph Vx) (X Y : Vx) : Vx → Vx → Prop :=
  fun a b => (G.Side X Y a ↔ G.Side X Y b)

/-- The walls of a median graph: the partitions given by the two sides of an edge. -/
def Walls (G : MedianGraph Vx) : Set (Vx → Vx → Prop) :=
  {R | ∃ X Y : Vx, G.dist X Y = 1 ∧ R = G.wallRel X Y}

/-- The two sides of an edge are complementary. -/
theorem side_swap_iff {u c : Vx} (huc : G.dist u c = 1) (t : Vx) :
    G.Side c u t ↔ ¬ G.Side u c t := by
  constructor
  · intro h hcon
    exact not_side_both hcon h
  · intro h
    rcases side_dichotomy huc t with h' | h'
    · exact absurd h' h
    · exact h'

/-- The wall of an edge does not depend on the order of its endpoints. -/
theorem wallRel_swap {u c : Vx} (huc : G.dist u c = 1) : G.wallRel u c = G.wallRel c u := by
  funext a b
  simp only [wallRel, eq_iff_iff]
  rw [side_swap_iff huc a, side_swap_iff huc b]
  tauto

/-- **A halfspace is determined by any edge crossing it**: if the edge `u–c` crosses the wall of
`X–Y`, the two sides of `X–Y` are the two sides of `u–c`. -/
theorem side_iff_of_crossing {X Y u c : Vx} (hXY : G.dist X Y = 1) (hstep : G.HasSteps)
    (huc : G.dist u c = 1) (hu : G.Side X Y u) (hc : G.Side Y X c) (t : Vx) :
    G.Side X Y t ↔ G.Side u c t := by
  have e1 : G.dist u t = G.dist t u := G.dist_comm u t
  have e2 : G.dist c t = G.dist t c := G.dist_comm c t
  constructor
  · intro htX
    rcases side_dichotomy huc t with h | h
    · exact h
    · exfalso
      have hle := side_dist_le hXY hstep huc hu hc htX
      unfold Side at h
      omega
  · intro htu
    rcases side_dichotomy hXY t with h | h
    · exact h
    · exfalso
      have hcu : G.dist c u = 1 := by rw [G.dist_comm]; exact huc
      have hYX : G.dist Y X = 1 := by rw [G.dist_comm]; exact hXY
      have hle := side_dist_le hYX hstep hcu hc hu h
      unfold Side at htu
      omega

/-- **Every edge crosses exactly one wall**: a wall separating the endpoints of an edge is the
wall of that edge. -/
theorem wallRel_eq_of_crossing {X Y u c : Vx} (hXY : G.dist X Y = 1) (hstep : G.HasSteps)
    (huc : G.dist u c = 1) (hsep : ¬ G.wallRel X Y u c) : G.wallRel X Y = G.wallRel u c := by
  have hcu : G.dist c u = 1 := by rw [G.dist_comm]; exact huc
  unfold wallRel at hsep
  by_cases hu : G.Side X Y u
  · have hc : ¬ G.Side X Y c := fun hc => hsep (iff_of_true hu hc)
    have hc' : G.Side Y X c := by
      rcases side_dichotomy hXY c with h | h
      · exact absurd h hc
      · exact h
    funext a b
    simp only [wallRel, eq_iff_iff]
    rw [side_iff_of_crossing hXY hstep huc hu hc' a, side_iff_of_crossing hXY hstep huc hu hc' b]
  · have hc : G.Side X Y c := by
      by_contra hc
      exact hsep (iff_of_false hu hc)
    have hu' : G.Side Y X u := by
      rcases side_dichotomy hXY u with h | h
      · exact absurd h hu
      · exact h
    rw [wallRel_swap huc]
    funext a b
    simp only [wallRel, eq_iff_iff]
    rw [side_iff_of_crossing hXY hstep hcu hc hu' a, side_iff_of_crossing hXY hstep hcu hc hu' b]

/-- The wall of an edge is a wall. -/
theorem wallRel_mem_walls {u c : Vx} (huc : G.dist u c = 1) : G.wallRel u c ∈ G.Walls :=
  ⟨u, c, huc, rfl⟩

/-- **The wall of an edge separates its endpoints.** -/
theorem not_wallRel_self {u c : Vx} (huc : G.dist u c = 1) : ¬ G.wallRel u c u c := by
  intro h
  have hu : G.Side u c u := by
    show G.dist u c = G.dist u u + 1
    rw [G.dist_self u, huc]
  have hc : G.Side u c c := h.mp hu
  have : G.dist c c = G.dist c u + 1 := hc
  rw [G.dist_self c, G.dist_comm c u, huc] at this
  omega

/-- **The wall of a first step of a geodesic separates the two endpoints.** -/
theorem not_wallRel_of_step {u c v : Vx} (huc : G.dist u c = 1)
    (hstep : G.HasSteps) (hcv : G.dist c v + 1 = G.dist u v) : ¬ G.wallRel u c u v := by
  intro h
  have hu : G.Side u c u := by
    show G.dist u c = G.dist u u + 1
    rw [G.dist_self u, huc]
  have hv : G.Side u c v := h.mp hu
  have hcc : G.Side c u c := by
    show G.dist c u = G.dist c c + 1
    rw [G.dist_self c, G.dist_comm c u, huc]
  have hle := side_dist_le huc hstep huc hu hcc hv
  omega

/-- A wall, being a partition into two sides, is a reflexive relation. -/
theorem walls_refl {R : Vx → Vx → Prop} (hR : R ∈ G.Walls) (a : Vx) : R a a := by
  obtain ⟨X, Y, -, rfl⟩ := hR
  unfold wallRel
  tauto

/-- A wall is a symmetric relation. -/
theorem walls_symm {R : Vx → Vx → Prop} (hR : R ∈ G.Walls) {a b : Vx} (h : R a b) : R b a := by
  obtain ⟨X, Y, -, rfl⟩ := hR
  unfold wallRel at h ⊢
  tauto

/-- A wall is a transitive relation. -/
theorem walls_trans {R : Vx → Vx → Prop} (hR : R ∈ G.Walls) {a b c : Vx} (h1 : R a b)
    (h2 : R b c) : R a c := by
  obtain ⟨X, Y, -, rfl⟩ := hR
  unfold wallRel at h1 h2 ⊢
  tauto

/-- A wall has only two classes: two vertices on the far side of it are on the same side. -/
theorem walls_of_not_not {R : Vx → Vx → Prop} (hR : R ∈ G.Walls) {a b c : Vx} (h1 : ¬ R a b)
    (h2 : ¬ R b c) : R a c := by
  obtain ⟨X, Y, -, rfl⟩ := hR
  unfold wallRel at h1 h2 ⊢
  tauto

/-- **A wall crossed by an edge is the wall of that edge.** -/
theorem walls_eq_of_crossing (hstep : G.HasSteps) {R : Vx → Vx → Prop} (hR : R ∈ G.Walls)
    {u c : Vx} (huc : G.dist u c = 1) (hsep : ¬ R u c) : R = G.wallRel u c := by
  obtain ⟨X, Y, hXY, rfl⟩ := hR
  exact wallRel_eq_of_crossing hXY hstep huc hsep

/-- **The walls separating two vertices are finite in number, and that number is exactly the
distance between them.** -/
theorem exists_sepWalls_card (hstep : G.HasSteps) :
    ∀ (n : ℕ) (u v : Vx), G.dist u v = n →
      ∃ T : Finset G.Walls, (∀ R : G.Walls, R ∈ T ↔ ¬ R.1 u v) ∧ T.card = n := by
  classical
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro u v hd
  rcases Nat.eq_zero_or_pos n with rfl | hpos
  · have huv : u = v := G.eq_of_dist_eq_zero hd
    subst huv
    refine ⟨∅, ?_, rfl⟩
    intro R
    simp only [Finset.notMem_empty, false_iff, not_not]
    exact walls_refl R.2 u
  · have huv : u ≠ v := by
      rintro rfl
      rw [G.dist_self u] at hd
      omega
    obtain ⟨c, huc, hcv⟩ := hstep u v huv
    obtain ⟨T', hT', hcard'⟩ := ih (G.dist c v) (by omega) c v rfl
    set R₀ : G.Walls := ⟨G.wallRel u c, wallRel_mem_walls huc⟩ with hR₀
    have hR₀uv : ¬ R₀.1 u v := not_wallRel_of_step huc hstep hcv
    have hR₀uc : ¬ R₀.1 u c := not_wallRel_self huc
    have hR₀cv : R₀.1 c v := walls_of_not_not R₀.2 (fun h => hR₀uc (walls_symm R₀.2 h)) hR₀uv
    have hR₀notT : R₀ ∉ T' := fun hmem => ((hT' R₀).1 hmem) hR₀cv
    -- a wall other than `R₀` does not separate the endpoints of the edge `u–c`
    have hother : ∀ R : G.Walls, R ≠ R₀ → R.1 u c := by
      intro R hne
      by_contra hno
      exact hne (Subtype.ext (walls_eq_of_crossing hstep R.2 huc hno))
    refine ⟨insert R₀ T', ?_, ?_⟩
    · intro R
      constructor
      · intro hmem
        rcases Finset.mem_insert.mp hmem with rfl | hmem
        · exact hR₀uv
        · have hne : R ≠ R₀ := by
            rintro rfl
            exact hR₀notT hmem
          have hcv' : ¬ R.1 c v := (hT' R).1 hmem
          intro huv'
          exact hcv' (walls_trans R.2 (walls_symm R.2 (hother R hne)) huv')
      · intro hsep
        by_cases hne : R = R₀
        · exact hne ▸ Finset.mem_insert_self _ _
        · refine Finset.mem_insert_of_mem ((hT' R).2 ?_)
          intro hcv'
          exact hsep (walls_trans R.2 (hother R hne) hcv')
    · rw [Finset.card_insert_of_notMem hR₀notT, hcard']
      omega

/-- **The distance in a median graph is the number of separating walls.** -/
theorem dist_eq_card_sepWalls (hstep : G.HasSteps) (u v : Vx) :
    ∃ T : Finset G.Walls, (∀ R : G.Walls, R ∈ T ↔ ¬ R.1 u v) ∧ T.card = G.dist u v :=
  exists_sepWalls_card hstep (G.dist u v) u v rfl

/-- The set of walls separating two vertices is finite. -/
theorem sepWalls_finite (hstep : G.HasSteps) (u v : Vx) :
    {R : G.Walls | ¬ R.1 u v}.Finite := by
  classical
  obtain ⟨T, hT, -⟩ := dist_eq_card_sepWalls hstep u v
  refine Set.Finite.subset T.finite_toSet ?_
  intro R hR
  exact (hT R).2 hR

/-! ### The wall space of a median graph -/

/-- Two vertices lie on different sides of the wall `R` exactly when `R` separates them from the
base vertex differently. -/
theorem walls_side_ne_iff {R : Vx → Vx → Prop} (hR : R ∈ G.Walls) (x₀ u v : Vx) :
    (¬ (R u x₀ ↔ R v x₀)) ↔ ¬ R u v := by
  constructor
  · intro h huv
    exact h ⟨fun hu => walls_trans hR (walls_symm hR huv) hu,
      fun hv => walls_trans hR huv hv⟩
  · intro h hiff
    by_cases hu : R u x₀
    · exact h (walls_trans hR hu (walls_symm hR (hiff.mp hu)))
    · have hv : ¬ R v x₀ := fun hv => hu (hiff.mpr hv)
      exact h (walls_of_not_not hR hu (fun hx => hv (walls_symm hR hx)))

open Classical in
/-- **The vertices of a median graph form a wall space**, the walls being the partitions into the
two sides of an edge. -/
noncomputable def wallSpace (hstep : G.HasSteps) (x₀ : Vx) : WallSpace Vx G.Walls where
  side R v := decide (R.1 v x₀)
  sep := by
    intro u v huv
    obtain ⟨X, Y, hXY, hu, hv⟩ := exists_separating_edge hstep huv
    refine ⟨⟨G.wallRel X Y, ⟨X, Y, hXY, rfl⟩⟩, ?_⟩
    have hsep : ¬ (G.wallRel X Y) u v := by
      intro h
      exact not_side_both (h.mp hu) hv
    have := (walls_side_ne_iff (R := G.wallRel X Y) ⟨X, Y, hXY, rfl⟩ x₀ u v).2 hsep
    simpa [decide_eq_decide] using this
  fin := by
    intro u v
    refine Set.Finite.subset (sepWalls_finite hstep u v) ?_
    intro R hR
    have : ¬ (R.1 u x₀ ↔ R.1 v x₀) := by
      simpa [decide_eq_decide] using hR
    exact (walls_side_ne_iff R.2 x₀ u v).1 this

/-- The vertices of a median graph embed into the dual cube complex of its wall space. -/
theorem wallSpace_coord_injective [DecidableEq G.Walls] (hstep : G.HasSteps) (x₀ y₀ : Vx) :
    Function.Injective ((wallSpace hstep x₀).coord y₀) :=
  WallSpace.coord_injective y₀

open RollerBridge in
/-- **The embedding into the dual complex is isometric**: the halfspace coordinates of two
vertices differ in exactly `dist u v` walls. -/
theorem wallSpace_dsym_coord [DecidableEq G.Walls] (hstep : G.HasSteps) (x₀ y₀ u v : Vx) :
    dsym ((wallSpace hstep x₀).coord y₀ u) ((wallSpace hstep x₀).coord y₀ v) = G.dist u v := by
  classical
  obtain ⟨T, hT, hcard⟩ := dist_eq_card_sepWalls hstep u v
  rw [WallSpace.dsym_coord, ← hcard]
  congr 1
  ext R
  simp only [Set.Finite.mem_toFinset, Set.mem_setOf_eq, hT R]
  constructor
  · intro h
    have : ¬ (R.1 u x₀ ↔ R.1 v x₀) := by
      simpa [wallSpace, decide_eq_decide] using h
    exact (walls_side_ne_iff R.2 x₀ u v).1 this
  · intro h
    have : ¬ (R.1 u x₀ ↔ R.1 v x₀) := (walls_side_ne_iff R.2 x₀ u v).2 h
    simpa [wallSpace, decide_eq_decide] using this

end MedianGraph

namespace MedianSimpleGraph

variable {Vx : Type u} (M : MedianSimpleGraph Vx)

/-- **The distance in a median graph is the number of separating walls**, the walls being the
partitions of the vertex set into the two sides of an edge. -/
theorem dist_eq_card_sepWalls (u v : Vx) :
    ∃ T : Finset (M.toMedianGraph).Walls,
      (∀ R : (M.toMedianGraph).Walls, R ∈ T ↔ ¬ R.1 u v) ∧ T.card = M.G.dist u v :=
  MedianGraph.dist_eq_card_sepWalls M.hasSteps u v

/-- **The vertices of a median graph form a wall space.** -/
noncomputable def wallSpace (x₀ : Vx) : WallSpace Vx (M.toMedianGraph).Walls :=
  MedianGraph.wallSpace M.hasSteps x₀

open RollerBridge in
/-- **The vertices embed isometrically into the dual cube complex of that wall space.** -/
theorem wallSpace_dsym_coord [DecidableEq (M.toMedianGraph).Walls] (x₀ y₀ u v : Vx) :
    dsym ((M.wallSpace x₀).coord y₀ u) ((M.wallSpace x₀).coord y₀ v) = M.G.dist u v :=
  MedianGraph.wallSpace_dsym_coord M.hasSteps x₀ y₀ u v

end MedianSimpleGraph

end FiniteChains
