module

public import RequestProject.CubeCartanHadamard

@[expose] public section

/-!
# Median graphs and the descending-cube axioms

`RequestProject/CubeCartanHadamard.lean` proves `H₂ = 0` for the cellular chains of an at most
three-dimensional cube complex satisfying the descending-cube axioms
(`FiniteChains.DescCubeStr`).  `RequestProject/CubeRollerModel.lean` derives those axioms from
the Roller (halfspace) description of a CAT(0) cube complex.  This file derives them from the
other standard combinatorial description: the one-skeleton of a CAT(0) cube complex is a
*median graph*, that is, a graph in which any three vertices have a unique median — a vertex
lying simultaneously on a geodesic between each pair.

The structure `FiniteChains.MedianGraph` records exactly this, the graph being given through
its distance function:

* a metric `dist` with values in `ℕ` (edges are the pairs at distance one);
* a base vertex;
* a median operation `med`, with the statement that `med a b c` lies on a geodesic between
  each pair and that it is the only vertex that does;
* the dimension bound: a vertex has at most three descending neighbours.

Everything else is proved:

* `FiniteChains.MedianGraph.dist_eq_two_of_common_neighbour` — a median graph has no
  triangles: two distinct vertices with a common neighbour are at distance two;
* `FiniteChains.MedianGraph.not_three_common_neighbours` — a median graph has no `K₂,₃`;
* `FiniteChains.MedianGraph.med_square` — two descending edges at a vertex span a square;
* `FiniteChains.MedianGraph.med_ne_med` — distinct pairs of descending edges span distinct
  squares;
* `FiniteChains.MedianGraph.med_bottom` — three descending edges at a vertex span a
  three-cube (the *cube condition*), which is the combinatorial content of the CAT(0)
  (Cartan–Hadamard) input of the paper;
* `FiniteChains.MedianGraph.toDescCubeStr` — hence all the descending-cube axioms hold, and
* `FiniteChains.MedianGraph.exists_d₃_eq`, `FiniteChains.MedianGraph.ker_d₂_eq_range_d₃` —
  hence every two-cycle of the cellular chain complex bounds.
-/

namespace FiniteChains

universe u

/-- A **median graph**, recorded through its distance function: a metric with values in `ℕ`
together with a median operation assigning to three vertices the unique vertex lying on a
geodesic between each pair.  `base` is the vertex from which heights are measured, and
`dim_le` says that the complex is at most three dimensional. -/
structure MedianGraph (Vx : Type u) where
  /-- The graph distance. -/
  dist : Vx → Vx → ℕ
  /-- The base vertex. -/
  base : Vx
  dist_self : ∀ x, dist x x = 0
  eq_of_dist_eq_zero : ∀ {x y : Vx}, dist x y = 0 → x = y
  dist_comm : ∀ x y : Vx, dist x y = dist y x
  dist_triangle : ∀ x y z : Vx, dist x z ≤ dist x y + dist y z
  /-- The median of three vertices. -/
  med : Vx → Vx → Vx → Vx
  med_ab : ∀ a b c : Vx, dist a (med a b c) + dist (med a b c) b = dist a b
  med_bc : ∀ a b c : Vx, dist b (med a b c) + dist (med a b c) c = dist b c
  med_ac : ∀ a b c : Vx, dist a (med a b c) + dist (med a b c) c = dist a c
  med_unique : ∀ a b c z : Vx, dist a z + dist z b = dist a b → dist b z + dist z c = dist b c →
    dist a z + dist z c = dist a c → z = med a b c
  /-- The complex is at most three dimensional: a vertex has at most three neighbours closer
  to the base vertex. -/
  dim_le : ∀ (w : Vx) (s : Finset Vx),
    (∀ a ∈ s, dist a w = 1 ∧ dist base a + 1 = dist base w) → s.card ≤ 3

namespace MedianGraph

variable {Vx : Type u} (G : MedianGraph Vx)

/-- The distance to the base vertex. -/
def ht (x : Vx) : ℕ := G.dist G.base x

/-- The descending neighbours of a vertex. -/
def dnM (w : Vx) : Set Vx := {a : Vx | G.dist a w = 1 ∧ G.ht a + 1 = G.ht w}

variable {G}

theorem mem_dnM {a w : Vx} : a ∈ G.dnM w ↔ G.dist a w = 1 ∧ G.ht a + 1 = G.ht w := Iff.rfl

theorem ht_eq (x : Vx) : G.ht x = G.dist x G.base := G.dist_comm G.base x

theorem dist_pos_of_ne {x y : Vx} (h : x ≠ y) : 0 < G.dist x y := by
  rcases Nat.eq_zero_or_pos (G.dist x y) with h0 | h0
  · exact absurd (G.eq_of_dist_eq_zero h0) h
  · exact h0

/-- The median is symmetric in its first two arguments. -/
theorem med_swap (a b c : Vx) : G.med a b c = G.med b a c := by
  refine (G.med_unique a b c (G.med b a c) ?_ ?_ ?_).symm
  · have h := G.med_ab b a c
    rw [G.dist_comm a (G.med b a c), G.dist_comm (G.med b a c) b, G.dist_comm a b]
    omega
  · exact G.med_ac b a c
  · exact G.med_bc b a c

/-- Heights differ by at most the distance. -/
theorem ht_le_ht_add_dist (x y : Vx) : G.ht x ≤ G.ht y + G.dist y x :=
  G.dist_triangle G.base y x

/-- **No triangles.**  Two distinct vertices with a common neighbour are at distance two. -/
theorem dist_eq_two_of_common_neighbour {a b p : Vx} (ha : G.dist a p = 1) (hb : G.dist b p = 1)
    (hab : a ≠ b) : G.dist a b = 2 := by
  have hpb : G.dist p b = 1 := by rw [G.dist_comm]; exact hb
  have hle : G.dist a b ≤ 2 := by
    have h := G.dist_triangle a p b
    omega
  have hpos : 0 < G.dist a b := dist_pos_of_ne hab
  by_contra hne
  have h1 : G.dist a b = 1 := by omega
  have e1 : G.dist a (G.med a b p) + G.dist (G.med a b p) b = G.dist a b := G.med_ab a b p
  have e2 : G.dist b (G.med a b p) + G.dist (G.med a b p) p = G.dist b p := G.med_bc a b p
  have e3 : G.dist a (G.med a b p) + G.dist (G.med a b p) p = G.dist a p := G.med_ac a b p
  rw [h1] at e1
  rw [hb] at e2
  rw [ha] at e3
  rcases Nat.eq_zero_or_pos (G.dist a (G.med a b p)) with h0 | h0
  · have hza : a = G.med a b p := G.eq_of_dist_eq_zero h0
    rw [← hza] at e2
    have hba : G.dist b a = 1 := by rw [G.dist_comm]; exact h1
    rw [hba, ha] at e2
    omega
  · have hzb : G.dist (G.med a b p) b = 0 := by omega
    have hbz : G.med a b p = b := G.eq_of_dist_eq_zero hzb
    rw [hbz, h1, hb] at e3
    omega

/-- **No `K₂,₃`.**  Two vertices at distance two have at most two common neighbours. -/
theorem not_three_common_neighbours {x y u v t : Vx} (hxy : G.dist x y = 2)
    (hux : G.dist u x = 1) (huy : G.dist u y = 1)
    (hvx : G.dist v x = 1) (hvy : G.dist v y = 1)
    (htx : G.dist t x = 1) (hty : G.dist t y = 1)
    (huv : u ≠ v) (hut : u ≠ t) (hvt : v ≠ t) : False := by
  have hxu : G.dist x u = 1 := by rw [G.dist_comm]; exact hux
  have hyu : G.dist y u = 1 := by rw [G.dist_comm]; exact huy
  have hxv : G.dist x v = 1 := by rw [G.dist_comm]; exact hvx
  have hyv : G.dist y v = 1 := by rw [G.dist_comm]; exact hvy
  have hxt : G.dist x t = 1 := by rw [G.dist_comm]; exact htx
  have hyt : G.dist y t = 1 := by rw [G.dist_comm]; exact hty
  have duv : G.dist u v = 2 := dist_eq_two_of_common_neighbour hux hvx huv
  have dut : G.dist u t = 2 := dist_eq_two_of_common_neighbour hux htx hut
  have dvt : G.dist v t = 2 := dist_eq_two_of_common_neighbour hvx htx hvt
  have hxmed : x = G.med u v t := by
    refine G.med_unique u v t x ?_ ?_ ?_ <;> omega
  have hymed : y = G.med u v t := by
    refine G.med_unique u v t y ?_ ?_ ?_ <;> omega
  have hxy0 : x = y := hxmed.trans hymed.symm
  rw [hxy0, G.dist_self] at hxy
  omega

/-- Two distinct descending neighbours of a vertex are at distance two. -/
theorem dist_dn_eq_two {w a b : Vx} (ha : a ∈ G.dnM w) (hb : b ∈ G.dnM w) (hab : a ≠ b) :
    G.dist a b = 2 :=
  dist_eq_two_of_common_neighbour ha.1 hb.1 hab

/-- **Two descending edges span a square.**  The median of two distinct descending neighbours
of `w` with the base vertex is a common neighbour of them, one level lower. -/
theorem med_square {w a b : Vx} (ha : a ∈ G.dnM w) (hb : b ∈ G.dnM w) (hab : a ≠ b) :
    G.dist (G.med a b G.base) a = 1 ∧ G.dist (G.med a b G.base) b = 1 ∧
      G.ht (G.med a b G.base) + 1 = G.ht a := by
  have dab : G.dist a b = 2 := dist_dn_eq_two ha hb hab
  have e1 : G.dist a (G.med a b G.base) + G.dist (G.med a b G.base) b = G.dist a b :=
    G.med_ab a b G.base
  have e2 : G.dist b (G.med a b G.base) + G.dist (G.med a b G.base) G.base = G.dist b G.base :=
    G.med_bc a b G.base
  have e3 : G.dist a (G.med a b G.base) + G.dist (G.med a b G.base) G.base = G.dist a G.base :=
    G.med_ac a b G.base
  have hta : G.dist a G.base = G.ht a := (ht_eq a).symm
  have htb : G.dist b G.base = G.ht b := (ht_eq b).symm
  have htp : G.dist (G.med a b G.base) G.base = G.ht (G.med a b G.base) :=
    (ht_eq (G.med a b G.base)).symm
  have s1 : G.dist (G.med a b G.base) a = G.dist a (G.med a b G.base) :=
    G.dist_comm (G.med a b G.base) a
  have s2 : G.dist (G.med a b G.base) b = G.dist b (G.med a b G.base) :=
    G.dist_comm (G.med a b G.base) b
  have h1 := ha.2
  have h2 := hb.2
  refine ⟨by omega, by omega, by omega⟩

/-- The square spanned by two descending edges: its bottom vertex is a descending neighbour of
each of them. -/
theorem med_mem_dn {w a b : Vx} (ha : a ∈ G.dnM w) (hb : b ∈ G.dnM w) (hab : a ≠ b) :
    G.med a b G.base ∈ G.dnM a := by
  obtain ⟨h1, _, h3⟩ := med_square ha hb hab
  exact ⟨h1, h3⟩

/-- A vertex two levels below `w` and at distance at most two from it is at distance exactly
two. -/
theorem dist_eq_two_of_ht {w p : Vx} (h : G.ht p + 2 = G.ht w) (hd : G.dist p w ≤ 2) :
    G.dist p w = 2 := by
  have h' := ht_le_ht_add_dist (G := G) w p
  omega

/-- The bottom vertex of a square is at distance two from its top vertex. -/
theorem dist_med_top {w a b : Vx} (ha : a ∈ G.dnM w) (hb : b ∈ G.dnM w) (hab : a ≠ b) :
    G.dist (G.med a b G.base) w = 2 := by
  obtain ⟨hpa, _, hph⟩ := med_square ha hb hab
  have h1 := ha.1
  have h2 := ha.2
  refine dist_eq_two_of_ht (by omega) ?_
  have h := G.dist_triangle (G.med a b G.base) a w
  omega

/-- **Distinct squares.**  Two distinct descending neighbours `b`, `c` of `w` span distinct
squares with a third descending neighbour `a`. -/
theorem med_ne_med {w a b c : Vx} (ha : a ∈ G.dnM w) (hb : b ∈ G.dnM w) (hc : c ∈ G.dnM w)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    G.med a b G.base ≠ G.med a c G.base := by
  intro hcon
  obtain ⟨hpa, hpb, hph⟩ := med_square ha hb hab
  obtain ⟨hqa, hqc, hqh⟩ := med_square ha hc hac
  have hpc : G.dist (G.med a b G.base) c = 1 := by rw [hcon]; exact hqc
  have hwp : G.dist (G.med a b G.base) w = 2 := dist_med_top ha hb hab
  refine not_three_common_neighbours (x := G.med a b G.base) (y := w) (u := a) (v := b) (t := c)
    hwp ?_ ha.1 ?_ hb.1 ?_ hc.1 hab hac hbc
  · rw [G.dist_comm a (G.med a b G.base)]; exact hpa
  · rw [G.dist_comm b (G.med a b G.base)]; exact hpb
  · rw [G.dist_comm c (G.med a b G.base)]; exact hpc

/-- **The cube condition.**  Three descending edges at `w` span a three-cube: the bottom
vertices of the three squares they span have a common lower neighbour, so the three squares
of the cube at the level below agree. -/
theorem med_bottom {w a b c : Vx} (ha : a ∈ G.dnM w) (hb : b ∈ G.dnM w) (hc : c ∈ G.dnM w)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    G.med (G.med a b G.base) (G.med a c G.base) G.base
      = G.med (G.med a b G.base) (G.med b c G.base) G.base ∧
    G.med (G.med a b G.base) (G.med a c G.base) G.base
      = G.med (G.med a c G.base) (G.med b c G.base) G.base := by
  obtain ⟨hpa, hpb, hph⟩ := med_square ha hb hab
  obtain ⟨hqa, hqc, hqh⟩ := med_square ha hc hac
  obtain ⟨hrb, hrc, hrh⟩ := med_square hb hc hbc
  have hta := ha.2
  have htb := hb.2
  have htc := hc.2
  set p := G.med a b G.base with hpdef
  set q := G.med a c G.base with hqdef
  set r := G.med b c G.base with hrdef
  have hpq : p ≠ q := med_ne_med ha hb hc hab hac hbc
  have hpr : p ≠ r := by
    have h := med_ne_med hb ha hc (Ne.symm hab) hbc hac
    rwa [med_swap b a G.base] at h
  have hqr : q ≠ r := by
    have h := med_ne_med hc ha hb (Ne.symm hac) (Ne.symm hbc) hab
    rwa [med_swap c a G.base, med_swap c b G.base] at h
  -- the three square bottoms are pairwise at distance two
  have dpq : G.dist p q = 2 := dist_eq_two_of_common_neighbour hpa hqa hpq
  have dpr : G.dist p r = 2 := dist_eq_two_of_common_neighbour hpb hrb hpr
  have dqr : G.dist q r = 2 := dist_eq_two_of_common_neighbour hqc hrc hqr
  -- their median is adjacent to all three
  have e1 : G.dist p (G.med p q r) + G.dist (G.med p q r) q = G.dist p q := G.med_ab p q r
  have e2 : G.dist q (G.med p q r) + G.dist (G.med p q r) r = G.dist q r := G.med_bc p q r
  have e3 : G.dist p (G.med p q r) + G.dist (G.med p q r) r = G.dist p r := G.med_ac p q r
  have c1 : G.dist (G.med p q r) p = G.dist p (G.med p q r) := G.dist_comm _ _
  have c2 : G.dist (G.med p q r) q = G.dist q (G.med p q r) := G.dist_comm _ _
  have c3 : G.dist (G.med p q r) r = G.dist r (G.med p q r) := G.dist_comm _ _
  have c2' : G.dist q (G.med p q r) = G.dist (G.med p q r) q := G.dist_comm _ _
  have hβp : G.dist (G.med p q r) p = 1 := by omega
  have hβq : G.dist (G.med p q r) q = 1 := by omega
  have hβr : G.dist (G.med p q r) r = 1 := by omega
  -- the median is not one of `a`, `b`, `c`
  have hβa : G.med p q r ≠ a := by
    intro hcon
    have har : G.dist a r = 1 := by rw [← hcon]; exact hβr
    have hwr : G.dist r w = 2 := dist_med_top hb hc hbc
    refine not_three_common_neighbours (x := r) (y := w) (u := a) (v := b) (t := c) hwr har ha.1
      ?_ hb.1 ?_ hc.1 hab hac hbc
    · rw [G.dist_comm b r]; exact hrb
    · rw [G.dist_comm c r]; exact hrc
  have hβb : G.med p q r ≠ b := by
    intro hcon
    have hbq : G.dist b q = 1 := by rw [← hcon]; exact hβq
    have hwq : G.dist q w = 2 := dist_med_top ha hc hac
    refine not_three_common_neighbours (x := q) (y := w) (u := a) (v := b) (t := c) hwq ?_ ha.1
      hbq hb.1 ?_ hc.1 hab hac hbc
    · rw [G.dist_comm a q]; exact hqa
    · rw [G.dist_comm c q]; exact hqc
  have hβc : G.med p q r ≠ c := by
    intro hcon
    have hcp : G.dist c p = 1 := by rw [← hcon]; exact hβp
    have hwp : G.dist p w = 2 := dist_med_top ha hb hab
    refine not_three_common_neighbours (x := p) (y := w) (u := a) (v := b) (t := c) hwp ?_ ha.1
      ?_ hb.1 hcp hc.1 hab hac hbc
    · rw [G.dist_comm a p]; exact hpa
    · rw [G.dist_comm b p]; exact hpb
  -- `p, q` are descending neighbours of `a`, and similarly for the other two pairs
  have hpdn : p ∈ G.dnM a := ⟨hpa, hph⟩
  have hqdn : q ∈ G.dnM a := ⟨hqa, hqh⟩
  have hpdnb : p ∈ G.dnM b := ⟨hpb, by omega⟩
  have hrdnb : r ∈ G.dnM b := ⟨hrb, hrh⟩
  have hqdnc : q ∈ G.dnM c := ⟨hqc, by omega⟩
  have hrdnc : r ∈ G.dnM c := ⟨hrc, by omega⟩
  -- the median coincides with the bottom vertex of each of the three squares
  have hβpq : G.med p q r = G.med p q G.base := by
    by_contra hcon
    obtain ⟨hγp, hγq, hγh⟩ := med_square hpdn hqdn hpq
    refine not_three_common_neighbours (x := p) (y := q) (u := a) (v := G.med p q r)
      (t := G.med p q G.base) dpq ?_ ?_ hβp hβq hγp hγq (Ne.symm hβa) ?_ hcon
    · rw [G.dist_comm a p]; exact hpa
    · rw [G.dist_comm a q]; exact hqa
    · intro hcon'
      rw [← hcon'] at hγh
      omega
  have hβpr : G.med p q r = G.med p r G.base := by
    by_contra hcon
    obtain ⟨hγp, hγr, hγh⟩ := med_square hpdnb hrdnb hpr
    refine not_three_common_neighbours (x := p) (y := r) (u := b) (v := G.med p q r)
      (t := G.med p r G.base) dpr ?_ ?_ hβp hβr hγp hγr (Ne.symm hβb) ?_ hcon
    · rw [G.dist_comm b p]; exact hpb
    · rw [G.dist_comm b r]; exact hrb
    · intro hcon'
      rw [← hcon'] at hγh
      omega
  have hβqr : G.med p q r = G.med q r G.base := by
    by_contra hcon
    obtain ⟨hγq, hγr, hγh⟩ := med_square hqdnc hrdnc hqr
    refine not_three_common_neighbours (x := q) (y := r) (u := c) (v := G.med p q r)
      (t := G.med q r G.base) dqr ?_ ?_ hβq hβr hγq hγr (Ne.symm hβc) ?_ hcon
    · rw [G.dist_comm c q]; exact hqc
    · rw [G.dist_comm c r]; exact hrc
    · intro hcon'
      rw [← hcon'] at hγh
      omega
  exact ⟨hβpq.symm.trans hβpr, hβpq.symm.trans hβqr⟩

variable (G)

/-- **A median graph of dimension at most three satisfies the descending-cube axioms.** -/
def toDescCubeStr [LinearOrder Vx] : DescCubeStr Vx where
  ht := G.ht
  dn := G.dnM
  med _ a b := G.med a b G.base
  ht_dn := fun ha => ha.2
  dim_le := fun w s hs => G.dim_le w s fun _a haS => ⟨(hs haS).1, (hs haS).2⟩
  med_comm := fun _ a b => med_swap a b G.base
  med_mem := fun ha hb hab => med_mem_dn ha hb hab
  med_ne := fun ha hb hc hab hac hbc => med_ne_med ha hb hc hab hac hbc
  med_bottom₁ := fun ha hb hc hab hac hbc => (med_bottom ha hb hc hab hac hbc).1
  med_bottom₂ := fun ha hb hc hab hac hbc => (med_bottom ha hb hc hab hac hbc).2

/-- **Every two-cycle of a three-dimensional median graph complex bounds**: the second
homology of the cellular chain complex vanishes. -/
theorem exists_d₃_eq [LinearOrder Vx] (z : (G.toDescCubeStr).SqC →₀ ℤ)
    (hz : (G.toDescCubeStr).d₂ z = 0) :
    ∃ c : (G.toDescCubeStr).CbC →₀ ℤ, (G.toDescCubeStr).d₃ c = z :=
  (G.toDescCubeStr).exists_d₃_eq z hz

/-- The kernel–image form of the previous statement. -/
theorem ker_d₂_eq_range_d₃ [LinearOrder Vx] :
    LinearMap.ker (G.toDescCubeStr).d₂ = LinearMap.range (G.toDescCubeStr).d₃ :=
  (G.toDescCubeStr).ker_d₂_eq_range_d₃

end MedianGraph

end FiniteChains
