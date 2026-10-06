import Mathlib

/-!
# A chain-level Cartan–Hadamard step for three-dimensional cube complexes

This file contains the combinatorial core of the step

  `H₂(V; ℤ) = 0`,  i.e.  `ker (d₂ : C₂(V) → C₁(V)) = im (d₃ : C₃(V) → C₂(V))`,

for the space `V` of the paper (the universal cover of the double cylinder with each
component of the preimage of `X` collapsed to a vertex), in the only form in which the
algebraic assembly of `RequestProject/RelativeH2.lean` uses it: as a statement about
cellular chains in degrees `1, 2, 3`.

## What is assumed and what is proved

The input is *local* combinatorial data of the cube complex `V` seen from a base vertex:

* a height function `ht` (the combinatorial distance to the base vertex);
* for every vertex `w` the set `dn w` of *descending* neighbours (the vertices of the
  complex joined to `w` by an edge of `V` and closer to the base vertex);
* for two distinct descending neighbours `a, b` of `w` the fourth vertex `med w a b` of the
  square that they span.

The axioms of `DescCubeStr` say exactly that:

* every edge changes the height by one (`ht_dn`);
* the complex is at most three-dimensional (`dim_le`: descending neighbours of a vertex span
  a cube, so no four of them are distinct) — no finiteness of links is assumed, and indeed
  the links of the new vertices of `V` are infinite in the application;
* any two descending neighbours span a square, any three span a three-cube
  (`med_mem`, `med_ne`, `med_bottom₁`, `med_bottom₂`).

The last group of axioms is the *descending-cube property*, which is the combinatorial
shadow of the CAT(0) (Cartan–Hadamard) input of the paper: in a CAT(0) cube complex the
edges at a vertex pointing towards the base vertex span a cube.

From this data the file builds the cellular chain complex in degrees `1, 2, 3`
(`FiniteChains.DescCubeStr.d₂`, `FiniteChains.DescCubeStr.d₃`) and proves

* `FiniteChains.DescCubeStr.d₂_d₃` — it is a chain complex;
* `FiniteChains.DescCubeStr.ker_d₂_le_range_d₃` — every two-cycle is a boundary;
* `FiniteChains.DescCubeStr.ker_d₂_eq_range_d₃` — `ker d₂ = im d₃`.

The proof is the "corner cancellation" induction: a nonzero two-cycle has a square whose top
vertex `w` is at maximal height; the cycle condition on the two edges of that square at `w`
forces `w` to have three descending neighbours and the three squares at `w` to occur with
coefficients `λ, -λ, λ`; subtracting `λ` times the boundary of the three-cube spanned by the
three descending neighbours removes all squares at `w` and creates only squares whose top
vertex is strictly lower.  This terminates.
-/

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains

open Finsupp

universe u

/-- Combinatorial data of an at most three-dimensional cube complex, seen from a base
vertex: heights, descending neighbours and the squares and cubes they span. -/
structure DescCubeStr (Vx : Type u) [LinearOrder Vx] where
  /-- Combinatorial distance to the base vertex. -/
  ht : Vx → ℕ
  /-- The descending neighbours of a vertex. -/
  dn : Vx → Set Vx
  /-- The fourth vertex of the square spanned by two descending neighbours. -/
  med : Vx → Vx → Vx → Vx
  ht_dn : ∀ {w a : Vx}, a ∈ dn w → ht a + 1 = ht w
  dim_le : ∀ (w : Vx) (s : Finset Vx), ↑s ⊆ dn w → s.card ≤ 3
  med_comm : ∀ w a b : Vx, med w a b = med w b a
  med_mem : ∀ {w a b : Vx}, a ∈ dn w → b ∈ dn w → a ≠ b → med w a b ∈ dn a
  med_ne : ∀ {w a b c : Vx}, a ∈ dn w → b ∈ dn w → c ∈ dn w → a ≠ b → a ≠ c → b ≠ c →
    med w a b ≠ med w a c
  med_bottom₁ : ∀ {w a b c : Vx}, a ∈ dn w → b ∈ dn w → c ∈ dn w → a ≠ b → a ≠ c → b ≠ c →
    med a (med w a b) (med w a c) = med b (med w a b) (med w b c)
  med_bottom₂ : ∀ {w a b c : Vx}, a ∈ dn w → b ∈ dn w → c ∈ dn w → a ≠ b → a ≠ c → b ≠ c →
    med a (med w a b) (med w a c) = med c (med w a c) (med w b c)

namespace DescCubeStr

variable {Vx : Type u} [LinearOrder Vx] (S : DescCubeStr Vx)

/-- An oriented edge, recorded as the pair (upper endpoint, lower endpoint).  Pairs that
are not edges of the complex are allowed as generators of `C₁`; boundaries never use
them, so this does not affect the statements below. -/
abbrev EdgeC (_S : DescCubeStr Vx) : Type u := Vx × Vx

/-- A square: a vertex together with two distinct descending neighbours, listed in the
order of `Vx`. -/
def SqC : Type u :=
  {t : Vx × Vx × Vx // t.2.1 ∈ S.dn t.1 ∧ t.2.2 ∈ S.dn t.1 ∧ t.2.1 < t.2.2}

/-- A three-cube: a vertex together with three distinct descending neighbours, listed in the
order of `Vx`. -/
def CbC : Type u :=
  {t : Vx × Vx × Vx × Vx //
    t.2.1 ∈ S.dn t.1 ∧ t.2.2.1 ∈ S.dn t.1 ∧ t.2.2.2 ∈ S.dn t.1 ∧
      t.2.1 < t.2.2.1 ∧ t.2.2.1 < t.2.2.2}

variable {S}

/-- The vertex of a square at the highest level. -/
def SqC.top (F : S.SqC) : Vx := F.1.1
/-- The smaller of the two descending directions of a square. -/
def SqC.x (F : S.SqC) : Vx := F.1.2.1
/-- The larger of the two descending directions of a square. -/
def SqC.y (F : S.SqC) : Vx := F.1.2.2

theorem SqC.x_mem (F : S.SqC) : F.x ∈ S.dn F.top := F.2.1
theorem SqC.y_mem (F : S.SqC) : F.y ∈ S.dn F.top := F.2.2.1
theorem SqC.x_lt_y (F : S.SqC) : F.x < F.y := F.2.2.2

/-- The vertex of a three-cube at the highest level. -/
def CbC.top (Q : S.CbC) : Vx := Q.1.1
/-- The smallest descending direction of a three-cube. -/
def CbC.x (Q : S.CbC) : Vx := Q.1.2.1
/-- The middle descending direction of a three-cube. -/
def CbC.y (Q : S.CbC) : Vx := Q.1.2.2.1
/-- The largest descending direction of a three-cube. -/
def CbC.z (Q : S.CbC) : Vx := Q.1.2.2.2

theorem CbC.x_mem (Q : S.CbC) : Q.x ∈ S.dn Q.top := Q.2.1
theorem CbC.y_mem (Q : S.CbC) : Q.y ∈ S.dn Q.top := Q.2.2.1
theorem CbC.z_mem (Q : S.CbC) : Q.z ∈ S.dn Q.top := Q.2.2.2.1
theorem CbC.x_lt_y (Q : S.CbC) : Q.x < Q.y := Q.2.2.2.2.1
theorem CbC.y_lt_z (Q : S.CbC) : Q.y < Q.z := Q.2.2.2.2.2

variable (S)

/-- The edge from `w` down to a descending neighbour `a`. -/
def edge (w a : Vx) : S.EdgeC := (w, a)

@[simp] theorem edge_eq_iff {w a w' a' : Vx} : S.edge w a = S.edge w' a' ↔ w = w' ∧ a = a' :=
  Prod.ext_iff

/-- The square spanned at `w` by two distinct descending neighbours `x`, `y`. -/
def sqCell (w x y : Vx) (hx : x ∈ S.dn w) (hy : y ∈ S.dn w) (hne : x ≠ y) : S.SqC :=
  if h : x < y then ⟨(w, x, y), hx, hy, h⟩
  else ⟨(w, y, x), hy, hx, lt_of_le_of_ne (not_lt.mp h) (Ne.symm hne)⟩

@[simp] theorem sqCell_top (w x y : Vx) (hx : x ∈ S.dn w) (hy : y ∈ S.dn w) (hne : x ≠ y) :
    (S.sqCell w x y hx hy hne).top = w := by
  unfold sqCell; split <;> rfl

theorem sqCell_swap (w x y : Vx) (hx : x ∈ S.dn w) (hy : y ∈ S.dn w) (hne : x ≠ y) :
    S.sqCell w y x hy hx (Ne.symm hne) = S.sqCell w x y hx hy hne := by
  unfold sqCell
  rcases lt_trichotomy x y with h | h | h
  · rw [dif_neg (asymm h), dif_pos h]
  · exact absurd h hne
  · rw [dif_pos h, dif_neg (asymm h)]

theorem sqCell_of_lt (w x y : Vx) (hx : x ∈ S.dn w) (hy : y ∈ S.dn w) (h : x < y) :
    S.sqCell w x y hx hy (ne_of_lt h) = ⟨(w, x, y), hx, hy, h⟩ := dif_pos h

/-- The sign used to orient an unordered pair of directions. -/
def sqSign (x y : Vx) : ℤ := if x < y then 1 else -1

/-- The oriented square spanned at `w` by `x` and `y`, as a two-chain. -/
noncomputable def sqGen (w x y : Vx) (hx : x ∈ S.dn w) (hy : y ∈ S.dn w) (hne : x ≠ y) :
    S.SqC →₀ ℤ :=
  Finsupp.single (S.sqCell w x y hx hy hne) (sqSign x y)

theorem sqGen_swap (w x y : Vx) (hx : x ∈ S.dn w) (hy : y ∈ S.dn w) (hne : x ≠ y) :
    S.sqGen w y x hy hx (Ne.symm hne) = -S.sqGen w x y hx hy hne := by
  unfold sqGen
  rw [sqCell_swap S w x y hx hy hne]
  rcases lt_or_gt_of_ne hne with h | h
  · rw [show sqSign y x = -1 from if_neg (asymm h), show sqSign x y = 1 from if_pos h]
    simp
  · rw [show sqSign y x = 1 from if_pos h, show sqSign x y = -1 from if_neg (asymm h)]
    simp

theorem sqGen_support_subset (w x y : Vx) (hx : x ∈ S.dn w) (hy : y ∈ S.dn w) (hne : x ≠ y) :
    (S.sqGen w x y hx hy hne).support ⊆ {S.sqCell w x y hx hy hne} := by
  unfold sqGen
  exact Finsupp.support_single_subset

/-- The boundary of the square spanned at `w` by the descending directions `x`, `y`, written
so that it makes sense for `x`, `y` in either order. -/
noncomputable def d2chain (w x y : Vx) : S.EdgeC →₀ ℤ :=
  Finsupp.single (S.edge w y) 1 - Finsupp.single (S.edge x (S.med w x y)) 1
    - Finsupp.single (S.edge w x) 1 + Finsupp.single (S.edge y (S.med w x y)) 1

theorem d2chain_swap (w x y : Vx) : S.d2chain w y x = -S.d2chain w x y := by
  unfold d2chain
  rw [S.med_comm w y x]
  abel

/-- The boundary of a square, as a one-chain. -/
noncomputable def d2gen (F : S.SqC) : S.EdgeC →₀ ℤ := S.d2chain F.top F.x F.y

/-- The cellular boundary `C₂ → C₁`. -/
noncomputable def d₂ : (S.SqC →₀ ℤ) →ₗ[ℤ] (S.EdgeC →₀ ℤ) :=
  Finsupp.linearCombination ℤ (S.d2gen)

/-- The three faces of a three-cube containing its top vertex. -/
noncomputable def d3top (Q : S.CbC) : S.SqC →₀ ℤ :=
  Finsupp.single ⟨(Q.top, Q.y, Q.z), Q.y_mem, Q.z_mem, Q.y_lt_z⟩ 1
    - Finsupp.single ⟨(Q.top, Q.x, Q.z), Q.x_mem, Q.z_mem, lt_trans Q.x_lt_y Q.y_lt_z⟩ 1
    + Finsupp.single ⟨(Q.top, Q.x, Q.y), Q.x_mem, Q.y_mem, Q.x_lt_y⟩ 1

/-- The three faces of a three-cube opposite to its top vertex; their top vertices are one
level lower. -/
noncomputable def d3low (Q : S.CbC) : S.SqC →₀ ℤ :=
  let w := Q.top; let a := Q.x; let b := Q.y; let c := Q.z
  let hab := ne_of_lt Q.x_lt_y
  let hbc := ne_of_lt Q.y_lt_z
  let hac := ne_of_lt (lt_trans Q.x_lt_y Q.y_lt_z)
  let ab := S.med w a b
  let ac := S.med w a c
  let bc := S.med w b c
  have hab_b : ab ∈ S.dn b := by
    rw [show ab = S.med w b a from S.med_comm _ _ _]
    exact S.med_mem Q.y_mem Q.x_mem (Ne.symm hab)
  have hac_c : ac ∈ S.dn c := by
    rw [show ac = S.med w c a from S.med_comm _ _ _]
    exact S.med_mem Q.z_mem Q.x_mem (Ne.symm hac)
  have hbc_c : bc ∈ S.dn c := by
    rw [show bc = S.med w c b from S.med_comm _ _ _]
    exact S.med_mem Q.z_mem Q.y_mem (Ne.symm hbc)
  have hne_b : ab ≠ bc := by
    rw [show ab = S.med w b a from S.med_comm _ _ _]
    exact S.med_ne Q.y_mem Q.x_mem Q.z_mem (Ne.symm hab) hbc hac
  have hne_c : ac ≠ bc := by
    rw [show ac = S.med w c a from S.med_comm _ _ _,
      show bc = S.med w c b from S.med_comm _ _ _]
    exact S.med_ne Q.z_mem Q.x_mem Q.y_mem (Ne.symm hac) (Ne.symm hbc) hab
  have hab_a : ab ∈ S.dn a := S.med_mem Q.x_mem Q.y_mem hab
  have hac_a : ac ∈ S.dn a := S.med_mem Q.x_mem Q.z_mem hac
  have hbc_b : bc ∈ S.dn b := S.med_mem Q.y_mem Q.z_mem hbc
  have hne_a : ab ≠ ac := S.med_ne Q.x_mem Q.y_mem Q.z_mem hab hac hbc
  S.sqGen b ab bc hab_b hbc_b hne_b - S.sqGen a ab ac hab_a hac_a hne_a
    - S.sqGen c ac bc hac_c hbc_c hne_c

/-- The boundary of a three-cube, as a two-chain: the three faces at the top vertex and the
three opposite faces. -/
noncomputable def d3gen (Q : S.CbC) : S.SqC →₀ ℤ := S.d3top Q + S.d3low Q

/-- The cellular boundary `C₃ → C₂`. -/
noncomputable def d₃ : (S.CbC →₀ ℤ) →ₗ[ℤ] (S.SqC →₀ ℤ) :=
  Finsupp.linearCombination ℤ (S.d3gen)


/-! ## The chain complex -/

theorem d₂_sqGen (w x y : Vx) (hx : x ∈ S.dn w) (hy : y ∈ S.dn w) (hne : x ≠ y) :
    S.d₂ (S.sqGen w x y hx hy hne) = S.d2chain w x y := by
  unfold sqGen d₂
  rw [Finsupp.linearCombination_single]
  rcases lt_or_gt_of_ne hne with h | h
  · rw [show S.sqCell w x y hx hy hne = ⟨(w, x, y), hx, hy, h⟩ from dif_pos h,
      show sqSign x y = 1 from if_pos h]
    simp [d2gen, SqC.top, SqC.x, SqC.y]
  · rw [show S.sqCell w x y hx hy hne = ⟨(w, y, x), hy, hx, h⟩ from dif_neg (asymm h),
      show sqSign x y = -1 from if_neg (asymm h)]
    have : S.d2gen ⟨(w, y, x), hy, hx, h⟩ = S.d2chain w y x := rfl
    rw [this, S.d2chain_swap w x y]
    simp

theorem d2chain_cube_sum {w a b c : Vx} (ha : a ∈ S.dn w) (hb : b ∈ S.dn w) (hc : c ∈ S.dn w)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    (S.d2chain w b c - S.d2chain a (S.med w a b) (S.med w a c))
      - (S.d2chain w a c - S.d2chain b (S.med w a b) (S.med w b c))
      + (S.d2chain w a b - S.d2chain c (S.med w a c) (S.med w b c)) = 0 := by
  have h1 := S.med_bottom₁ ha hb hc hab hac hbc
  have h2 := S.med_bottom₂ ha hb hc hab hac hbc
  unfold d2chain
  rw [← h1, ← h2]
  abel

theorem d₂_d3top (Q : S.CbC) :
    S.d₂ (S.d3top Q) = S.d2chain Q.top Q.y Q.z - S.d2chain Q.top Q.x Q.z
      + S.d2chain Q.top Q.x Q.y := by
  unfold d3top d₂
  simp only [map_add, map_sub, Finsupp.linearCombination_single, one_smul]
  rfl

theorem d₂_d3low (Q : S.CbC) :
    S.d₂ (S.d3low Q) = -S.d2chain Q.x (S.med Q.top Q.x Q.y) (S.med Q.top Q.x Q.z)
      + S.d2chain Q.y (S.med Q.top Q.x Q.y) (S.med Q.top Q.y Q.z)
      - S.d2chain Q.z (S.med Q.top Q.x Q.z) (S.med Q.top Q.y Q.z) := by
  simp only [d3low, map_sub, d₂_sqGen]
  abel

theorem d₂_d3gen (Q : S.CbC) : S.d₂ (S.d3gen Q) = 0 := by
  rw [d3gen, map_add, S.d₂_d3top, S.d₂_d3low]
  have := S.d2chain_cube_sum Q.x_mem Q.y_mem Q.z_mem (ne_of_lt Q.x_lt_y)
    (ne_of_lt (lt_trans Q.x_lt_y Q.y_lt_z)) (ne_of_lt Q.y_lt_z)
  linear_combination (norm := abel) this

/-- The cellular chains of the complex form a chain complex in degrees `1, 2, 3`. -/
theorem d₂_d₃ (c : S.CbC →₀ ℤ) : S.d₂ (S.d₃ c) = 0 := by
  unfold d₃
  rw [Finsupp.linearCombination_apply, Finsupp.sum, map_sum]
  refine Finset.sum_eq_zero fun Q _ => ?_
  rw [map_smul, S.d₂_d3gen, smul_zero]

/-! ## Coefficients of a boundary -/

theorem d₂_apply (z : S.SqC →₀ ℤ) (e : S.EdgeC) :
    (S.d₂ z) e = ∑ F ∈ z.support, z F * (S.d2gen F) e := by
  unfold d₂
  rw [Finsupp.linearCombination_apply, Finsupp.sum, Finset.sum_apply']
  exact Finset.sum_congr rfl fun F _ => rfl

theorem d2gen_apply_edge (F : S.SqC) {w : Vx} (hw : S.ht F.top ≤ S.ht w) (a : Vx) :
    (S.d2gen F) (S.edge w a)
      = (if F.top = w ∧ F.y = a then (1 : ℤ) else 0)
        - (if F.top = w ∧ F.x = a then (1 : ℤ) else 0) := by
  have hx : S.ht F.x + 1 = S.ht F.top := S.ht_dn F.x_mem
  have hy : S.ht F.y + 1 = S.ht F.top := S.ht_dn F.y_mem
  have h2 : ¬ (F.x = w ∧ S.med F.top F.x F.y = a) := by
    rintro ⟨h, -⟩
    rw [h] at hx
    omega
  have h4 : ¬ (F.y = w ∧ S.med F.top F.x F.y = a) := by
    rintro ⟨h, -⟩
    rw [h] at hy
    omega
  unfold d2gen d2chain
  simp only [Finsupp.coe_sub, Finsupp.coe_add, Pi.sub_apply, Pi.add_apply,
    Finsupp.single_apply, S.edge_eq_iff, if_neg h2, if_neg h4]
  ring


/-! ## Supports of the boundary of a three-cube -/

theorem support_sub_sub_subset {ι : Type*} [DecidableEq ι] {A B C : ι →₀ ℤ} :
    (A - B - C).support ⊆ A.support ∪ B.support ∪ C.support := by
  classical
  intro F hF
  by_contra h
  simp only [Finset.mem_union, not_or, Finsupp.mem_support_iff, not_not] at h
  obtain ⟨⟨hA, hB⟩, hC⟩ := h
  simp only [Finsupp.mem_support_iff, Finsupp.coe_sub, Pi.sub_apply, hA, hB, hC,
    sub_zero, ne_eq, not_true_eq_false] at hF

theorem support_sub_sub_card {ι : Type*} [DecidableEq ι] {A B C : ι →₀ ℤ} (hA : A.support.card ≤ 1)
    (hB : B.support.card ≤ 1) (hC : C.support.card ≤ 1) : (A - B - C).support.card ≤ 3 := by
  classical
  refine le_trans (Finset.card_le_card support_sub_sub_subset) ?_
  refine le_trans (Finset.card_union_le _ _) ?_
  have := Finset.card_union_le A.support B.support
  omega

theorem sqGen_support_card (w x y : Vx) (hx : x ∈ S.dn w) (hy : y ∈ S.dn w) (hne : x ≠ y) :
    (S.sqGen w x y hx hy hne).support.card ≤ 1 := by
  refine le_trans (Finset.card_le_card (S.sqGen_support_subset w x y hx hy hne)) ?_
  simp

theorem sqGen_support_top (w x y : Vx) (hx : x ∈ S.dn w) (hy : y ∈ S.dn w) (hne : x ≠ y)
    {F : S.SqC} (hF : F ∈ (S.sqGen w x y hx hy hne).support) : F.top = w := by
  have h := S.sqGen_support_subset w x y hx hy hne hF
  rw [Finset.mem_singleton] at h
  rw [h]
  exact S.sqCell_top w x y hx hy hne

theorem d3low_support_card (Q : S.CbC) : (S.d3low Q).support.card ≤ 3 := by
  classical
  simp only [d3low]
  exact support_sub_sub_card (S.sqGen_support_card _ _ _ _ _ _)
    (S.sqGen_support_card _ _ _ _ _ _) (S.sqGen_support_card _ _ _ _ _ _)

theorem d3low_support_ht (Q : S.CbC) {F : S.SqC} (hF : F ∈ (S.d3low Q).support) :
    S.ht F.top + 1 = S.ht Q.top := by
  classical
  simp only [d3low] at hF
  have h := support_sub_sub_subset hF
  simp only [Finset.mem_union] at h
  rcases h with (h | h) | h
  · rw [S.sqGen_support_top _ _ _ _ _ _ h]; exact S.ht_dn Q.y_mem
  · rw [S.sqGen_support_top _ _ _ _ _ _ h]; exact S.ht_dn Q.x_mem
  · rw [S.sqGen_support_top _ _ _ _ _ _ h]; exact S.ht_dn Q.z_mem

theorem d3low_apply_top (Q : S.CbC) {F : S.SqC} (hF : F.top = Q.top) : (S.d3low Q) F = 0 := by
  by_contra h
  have hmem : F ∈ (S.d3low Q).support := Finsupp.mem_support_iff.mpr h
  have := S.d3low_support_ht Q hmem
  rw [hF] at this
  omega


/-! ## Small order-theoretic helpers -/

theorem pair_of_mem_pair {α : Type*} [LinearOrder α] [DecidableEq α] {x y a b : α} (hab : a < b)
    (hx : x ∈ ({a, b} : Finset α)) (hy : y ∈ ({a, b} : Finset α)) (hxy : x < y) :
    x = a ∧ y = b := by
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
  rcases hx with rfl | rfl
  · rcases hy with rfl | rfl
    · exact absurd hxy (lt_irrefl _)
    · exact ⟨rfl, rfl⟩
  · rcases hy with rfl | rfl
    · exact absurd hab (asymm hxy)
    · exact absurd hxy (lt_irrefl _)

theorem triple_of_mem_triple {α : Type*} [LinearOrder α] [DecidableEq α] {x y a b c : α}
    (hab : a < b) (hbc : b < c) (hx : x ∈ ({a, b, c} : Finset α))
    (hy : y ∈ ({a, b, c} : Finset α)) (hxy : x < y) :
    (x = a ∧ y = b) ∨ (x = a ∧ y = c) ∨ (x = b ∧ y = c) := by
  have hac : a < c := hab.trans hbc
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
  rcases hx with rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl <;>
    first
      | exact absurd hxy (lt_irrefl _)
      | exact absurd hab (asymm hxy)
      | exact absurd hbc (asymm hxy)
      | exact absurd hac (asymm hxy)
      | exact Or.inl ⟨rfl, rfl⟩
      | exact Or.inr (Or.inl ⟨rfl, rfl⟩)
      | exact Or.inr (Or.inr ⟨rfl, rfl⟩)

theorem exists_sorted_two {α : Type*} [LinearOrder α] [DecidableEq α] {s : Finset α}
    (h : s.card = 2) : ∃ a b, a < b ∧ s = {a, b} := by
  obtain ⟨x, y, hxy, rfl⟩ := Finset.card_eq_two.mp h
  rcases lt_or_gt_of_ne hxy with h' | h'
  · exact ⟨x, y, h', rfl⟩
  · exact ⟨y, x, h', Finset.pair_comm x y⟩

theorem exists_sorted_three {α : Type*} [LinearOrder α] [DecidableEq α] {s : Finset α}
    (h : s.card = 3) : ∃ a b c, a < b ∧ b < c ∧ s = {a, b, c} := by
  obtain ⟨x, y, z, hxy, hxz, hyz, rfl⟩ := Finset.card_eq_three.mp h
  rcases lt_trichotomy x y with h1 | h1 | h1
  · rcases lt_trichotomy y z with h2 | h2 | h2
    · exact ⟨x, y, z, h1, h2, rfl⟩
    · exact absurd h2 hyz
    · rcases lt_trichotomy x z with h3 | h3 | h3
      · exact ⟨x, z, y, h3, h2, by ext t; simp; tauto⟩
      · exact absurd h3 hxz
      · exact ⟨z, x, y, h3, h1, by ext t; simp; tauto⟩
  · exact absurd h1 hxy
  · rcases lt_trichotomy x z with h2 | h2 | h2
    · exact ⟨y, x, z, h1, h2, by ext t; simp; tauto⟩
    · exact absurd h2 hxz
    · rcases lt_trichotomy y z with h3 | h3 | h3
      · exact ⟨y, z, x, h3, h2, by ext t; simp; tauto⟩
      · exact absurd h3 hyz
      · exact ⟨z, y, x, h3, h1, by ext t; simp; tauto⟩


/-! ## The local cycle condition at a vertex of maximal height -/

/-- If `z` is a two-cycle all of whose squares have top vertex of height at most `ht w`, and
`P` collects all squares of `z` with top vertex `w`, then for every direction `a` the signed
count of the squares of `P` having `a` as a direction at `w` vanishes. -/
theorem sum_coeff_eq_zero [DecidableEq S.SqC] {z : S.SqC →₀ ℤ} (hz : S.d₂ z = 0) {w : Vx}
    (hmax : ∀ F ∈ z.support, S.ht F.top ≤ S.ht w)
    (P : Finset S.SqC) (hP : ∀ F ∈ z.support, F.top = w → F ∈ P) (a : Vx) :
    ∑ F ∈ P, z F * ((if F.top = w ∧ F.y = a then (1 : ℤ) else 0)
      - (if F.top = w ∧ F.x = a then (1 : ℤ) else 0)) = 0 := by
  set g : S.SqC → ℤ := fun F => z F * ((if F.top = w ∧ F.y = a then (1 : ℤ) else 0)
      - (if F.top = w ∧ F.x = a then (1 : ℤ) else 0)) with hg
  have h0 : ∑ F ∈ z.support, g F = 0 := by
    have hval := S.d₂_apply z (S.edge w a)
    rw [hz] at hval
    simp only [Finsupp.coe_zero, Pi.zero_apply] at hval
    refine Eq.trans (Finset.sum_congr rfl fun F hF => ?_) hval.symm
    rw [S.d2gen_apply_edge F (hmax F hF) a]
  have hsub1 : ∑ F ∈ z.support, g F = ∑ F ∈ z.support ∪ P, g F := by
    refine Finset.sum_subset Finset.subset_union_left ?_
    intro F _ hF
    have : z F = 0 := by
      by_contra hne
      exact hF (Finsupp.mem_support_iff.mpr hne)
    simp [hg, this]
  have hsub2 : ∑ F ∈ P, g F = ∑ F ∈ z.support ∪ P, g F := by
    refine Finset.sum_subset Finset.subset_union_right ?_
    intro F hFu hFP
    rcases Finset.mem_union.mp hFu with hF | hF
    · by_cases htop : F.top = w
      · exact absurd (hP F hF htop) hFP
      · simp [hg, htop]
    · exact absurd hF hFP
  rw [show (∑ F ∈ P, z F * ((if F.top = w ∧ F.y = a then (1 : ℤ) else 0)
      - (if F.top = w ∧ F.x = a then (1 : ℤ) else 0))) = ∑ F ∈ P, g F from rfl,
    hsub2, ← hsub1, h0]


/-- Explicit constructor for a square, with its projections as simp lemmas. -/
def sq3 (w x y : Vx) (hx : x ∈ S.dn w) (hy : y ∈ S.dn w) (h : x < y) : S.SqC :=
  ⟨(w, x, y), hx, hy, h⟩

@[simp] theorem sq3_top (w x y : Vx) (hx : x ∈ S.dn w) (hy : y ∈ S.dn w) (h : x < y) :
    (S.sq3 w x y hx hy h).top = w := rfl
@[simp] theorem sq3_x (w x y : Vx) (hx : x ∈ S.dn w) (hy : y ∈ S.dn w) (h : x < y) :
    (S.sq3 w x y hx hy h).x = x := rfl
@[simp] theorem sq3_y (w x y : Vx) (hx : x ∈ S.dn w) (hy : y ∈ S.dn w) (h : x < y) :
    (S.sq3 w x y hx hy h).y = y := rfl

theorem SqC.val_eq (F : S.SqC) : F.1 = (F.top, F.x, F.y) := rfl

/-! ## Every two-cycle is a boundary -/

/-- **Chain-level Cartan–Hadamard.**  In an at most three-dimensional cube complex with the
descending-cube property, every two-cycle is the boundary of a three-chain. -/
theorem exists_d₃_eq (z : S.SqC →₀ ℤ) (hz : S.d₂ z = 0) : ∃ c : S.CbC →₀ ℤ, S.d₃ c = z := by
  classical
  suffices H : ∀ n : ℕ, ∀ z : S.SqC →₀ ℤ, (∑ F ∈ z.support, 2 ^ S.ht F.top) = n →
      S.d₂ z = 0 → ∃ c : S.CbC →₀ ℤ, S.d₃ c = z by
    exact H _ z rfl hz
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro z hn hz
  rcases eq_or_ne z 0 with rfl | hz0
  · exact ⟨0, by simp⟩
  obtain ⟨F₀, hF₀, hmax⟩ :=
    z.support.exists_max_image (fun F => S.ht F.top) (Finsupp.support_nonempty_iff.mpr hz0)
  set w : Vx := F₀.top with hwdef
  set T : Finset S.SqC := z.support.filter (fun F => F.top = w) with hTdef
  have hmemT : ∀ {F : S.SqC}, F ∈ T ↔ F ∈ z.support ∧ F.top = w := by
    intro F; simp [hTdef]
  have hF₀T : F₀ ∈ T := hmemT.mpr ⟨hF₀, rfl⟩
  set A : Finset Vx := T.image SqC.x ∪ T.image SqC.y with hAdef
  have hmemA : ∀ {v : Vx}, v ∈ A ↔ (∃ F ∈ T, F.x = v) ∨ (∃ F ∈ T, F.y = v) := by
    intro v; simp [hAdef]
  have hAsub : ↑A ⊆ S.dn w := by
    intro v hv
    rcases hmemA.mp hv with ⟨F, hF, rfl⟩ | ⟨F, hF, rfl⟩
    · rw [← (hmemT.mp hF).2]; exact F.x_mem
    · rw [← (hmemT.mp hF).2]; exact F.y_mem
  have hcard_le : A.card ≤ 3 := S.dim_le w A hAsub
  have hxA : F₀.x ∈ A := hmemA.mpr (Or.inl ⟨F₀, hF₀T, rfl⟩)
  have hyA : F₀.y ∈ A := hmemA.mpr (Or.inr ⟨F₀, hF₀T, rfl⟩)
  have hcard_ge : 2 ≤ A.card := by
    have hsub : ({F₀.x, F₀.y} : Finset Vx) ⊆ A := by
      intro v hv
      rcases Finset.mem_insert.mp hv with rfl | hv
      · exact hxA
      · rw [Finset.mem_singleton.mp hv]; exact hyA
    have hle := Finset.card_le_card hsub
    rwa [Finset.card_pair (ne_of_lt F₀.x_lt_y)] at hle
  have hzF₀ : z F₀ ≠ 0 := Finsupp.mem_support_iff.mp hF₀
  rcases (show A.card = 2 ∨ A.card = 3 by omega) with hA2 | hA3
  · -- two directions: the single square at `w` cannot occur in a cycle
    exfalso
    obtain ⟨a, b, hab, hAeq⟩ := exists_sorted_two hA2
    have ha : a ∈ S.dn w := hAsub (by rw [hAeq]; simp)
    have hb : b ∈ S.dn w := hAsub (by rw [hAeq]; simp)
    set P1 : S.SqC := S.sq3 w a b ha hb hab with hP1def
    have hPmem : ∀ F ∈ z.support, F.top = w → F ∈ ({P1} : Finset S.SqC) := by
      intro F hF htop
      have hFT : F ∈ T := hmemT.mpr ⟨hF, htop⟩
      have hx : F.x ∈ A := hmemA.mpr (Or.inl ⟨F, hFT, rfl⟩)
      have hy : F.y ∈ A := hmemA.mpr (Or.inr ⟨F, hFT, rfl⟩)
      rw [hAeq] at hx hy
      obtain ⟨hxa, hyb⟩ := pair_of_mem_pair hab hx hy F.x_lt_y
      rw [Finset.mem_singleton, hP1def]
      exact Subtype.ext (by rw [F.val_eq, htop, hxa, hyb]; rfl)
    have hkey : ∀ v : Vx,
        z P1 * ((if b = v then (1 : ℤ) else 0) - (if a = v then (1 : ℤ) else 0)) = 0 := by
      intro v
      have h := S.sum_coeff_eq_zero hz hmax ({P1}) hPmem v
      rw [Finset.sum_singleton] at h
      simpa [hP1def] using h
    have hka := hkey a
    rw [if_neg (ne_of_gt hab), if_pos rfl] at hka
    have hzP1 : z P1 = 0 := by linarith
    have hF₀P1 : F₀ = P1 := by
      have hm := hPmem F₀ hF₀ rfl
      rwa [Finset.mem_singleton] at hm
    rw [hF₀P1] at hzF₀
    exact hzF₀ hzP1
  · -- three directions: cancel the corner of the three-cube they span
    obtain ⟨a, b, c, hab, hbc, hAeq⟩ := exists_sorted_three hA3
    have hac : a < c := hab.trans hbc
    have ha : a ∈ S.dn w := hAsub (by rw [hAeq]; simp)
    have hb : b ∈ S.dn w := hAsub (by rw [hAeq]; simp)
    have hc : c ∈ S.dn w := hAsub (by rw [hAeq]; simp)
    set P1 : S.SqC := S.sq3 w a b ha hb hab with hP1def
    set P2 : S.SqC := S.sq3 w a c ha hc hac with hP2def
    set P3 : S.SqC := S.sq3 w b c hb hc hbc with hP3def
    have h12 : P1 ≠ P2 := by
      rw [hP1def, hP2def]
      intro h
      exact absurd (congrArg SqC.y h) (ne_of_lt hbc)
    have h13 : P1 ≠ P3 := by
      rw [hP1def, hP3def]
      intro h
      exact absurd (congrArg SqC.x h) (ne_of_lt hab)
    have h23 : P2 ≠ P3 := by
      rw [hP2def, hP3def]
      intro h
      exact absurd (congrArg SqC.x h) (ne_of_lt hab)
    have hPmem : ∀ F ∈ z.support, F.top = w → F ∈ ({P1, P2, P3} : Finset S.SqC) := by
      intro F hF htop
      have hFT : F ∈ T := hmemT.mpr ⟨hF, htop⟩
      have hx : F.x ∈ A := hmemA.mpr (Or.inl ⟨F, hFT, rfl⟩)
      have hy : F.y ∈ A := hmemA.mpr (Or.inr ⟨F, hFT, rfl⟩)
      rw [hAeq] at hx hy
      simp only [Finset.mem_insert, Finset.mem_singleton, hP1def, hP2def, hP3def]
      rcases triple_of_mem_triple hab hbc hx hy F.x_lt_y with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact Or.inl (Subtype.ext (by rw [F.val_eq, htop, h1, h2]; rfl))
      · exact Or.inr (Or.inl (Subtype.ext (by rw [F.val_eq, htop, h1, h2]; rfl)))
      · exact Or.inr (Or.inr (Subtype.ext (by rw [F.val_eq, htop, h1, h2]; rfl)))
    have hsum3 : ∀ f : S.SqC → ℤ, ∑ F ∈ ({P1, P2, P3} : Finset S.SqC), f F
        = f P1 + f P2 + f P3 := by
      intro f
      rw [Finset.sum_insert (by simp [h12, h13]), Finset.sum_insert (by simp [h23]),
        Finset.sum_singleton, add_assoc]
    have hkey : ∀ v : Vx,
        z P1 * ((if b = v then (1 : ℤ) else 0) - (if a = v then (1 : ℤ) else 0))
        + z P2 * ((if c = v then (1 : ℤ) else 0) - (if a = v then (1 : ℤ) else 0))
        + z P3 * ((if c = v then (1 : ℤ) else 0) - (if b = v then (1 : ℤ) else 0)) = 0 := by
      intro v
      have h := S.sum_coeff_eq_zero hz hmax ({P1, P2, P3}) hPmem v
      rw [hsum3] at h
      simpa [hP1def, hP2def, hP3def] using h
    have hba : ¬ (b = a) := ne_of_gt hab
    have hca : ¬ (c = a) := ne_of_gt hac
    have hcb : ¬ (c = b) := ne_of_gt hbc
    have hka := hkey a
    have hkb := hkey b
    norm_num [hba, hca, hcb, ne_of_lt hab] at hka hkb
    have hP2val : z P2 = -z P1 := by linarith
    have hP3val : z P3 = z P1 := by linarith
    have hlam : z P1 ≠ 0 := by
      intro h0
      have hm := hPmem F₀ hF₀ rfl
      simp only [Finset.mem_insert, Finset.mem_singleton] at hm
      rcases hm with h | h | h
      · exact hzF₀ (by rw [h, h0])
      · exact hzF₀ (by rw [h, hP2val, h0, neg_zero])
      · exact hzF₀ (by rw [h, hP3val, h0])
    -- the three-cube spanned by the three descending directions
    set Q : S.CbC := ⟨(w, a, b, c), ha, hb, hc, hab, hbc⟩ with hQdef
    have hQtop : Q.top = w := rfl
    have hd3top : S.d3top Q
        = Finsupp.single P3 1 - Finsupp.single P2 1 + Finsupp.single P1 1 := rfl
    have hd3 : ∀ F : S.SqC, F.top = w → (S.d3gen Q) F
        = (if P3 = F then (1 : ℤ) else 0) - (if P2 = F then (1 : ℤ) else 0)
          + (if P1 = F then (1 : ℤ) else 0) := by
      intro F hF
      rw [d3gen, Finsupp.add_apply, S.d3low_apply_top Q (by rw [hF, hQtop]), add_zero, hd3top]
      simp [Finsupp.single_apply]
    have hv1 : (S.d3gen Q) P1 = 1 := by
      rw [hd3 P1 (by rw [hP1def]; rfl), if_neg (Ne.symm h13), if_neg (Ne.symm h12), if_pos rfl]
      ring
    have hv2 : (S.d3gen Q) P2 = -1 := by
      rw [hd3 P2 (by rw [hP2def]; rfl), if_neg (Ne.symm h23), if_pos rfl, if_neg h12]
      ring
    have hv3 : (S.d3gen Q) P3 = 1 := by
      rw [hd3 P3 (by rw [hP3def]; rfl), if_pos rfl, if_neg h23, if_neg h13]
      ring
    set lam : ℤ := z P1 with hlamdef
    set z' : S.SqC →₀ ℤ := z - lam • S.d3gen Q with hz'def
    have hz' : S.d₂ z' = 0 := by
      rw [hz'def, map_sub, map_smul, S.d₂_d3gen, smul_zero, hz, sub_zero]
    have hz'1 : z' P1 = 0 := by
      simp [hz'def, hv1, hlamdef]
    have hz'2 : z' P2 = 0 := by
      simp [hz'def, hv2, hlamdef, hP2val]
    have hz'3 : z' P3 = 0 := by
      simp [hz'def, hv3, hlamdef, hP3val]
    have hPsub : ({P1, P2, P3} : Finset S.SqC) ⊆ z.support := by
      intro F hF
      simp only [Finset.mem_insert, Finset.mem_singleton] at hF
      rcases hF with rfl | rfl | rfl
      · exact Finsupp.mem_support_iff.mpr hlam
      · exact Finsupp.mem_support_iff.mpr (by rw [hP2val]; simpa using hlam)
      · exact Finsupp.mem_support_iff.mpr (by rw [hP3val]; exact hlam)
    have hz'supp : z'.support ⊆
        (z.support \ ({P1, P2, P3} : Finset S.SqC)) ∪ (S.d3low Q).support := by
      intro F hF
      by_cases hmem : F ∈ ({P1, P2, P3} : Finset S.SqC)
      · exfalso
        simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
        rcases hmem with rfl | rfl | rfl
        · exact (Finsupp.mem_support_iff.mp hF) hz'1
        · exact (Finsupp.mem_support_iff.mp hF) hz'2
        · exact (Finsupp.mem_support_iff.mp hF) hz'3
      · by_cases hlow : F ∈ (S.d3low Q).support
        · exact Finset.mem_union_right _ hlow
        · refine Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨?_, hmem⟩)
          have hlow0 : (S.d3low Q) F = 0 := by
            by_contra hne
            exact hlow (Finsupp.mem_support_iff.mpr hne)
          have htop0 : (S.d3top Q) F = 0 := by
            simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hmem
            rw [hd3top]
            simp [Ne.symm hmem.1, Ne.symm hmem.2.1, Ne.symm hmem.2.2]
          have : z' F = z F := by
            rw [hz'def]
            simp [d3gen, hlow0, htop0]
          refine Finsupp.mem_support_iff.mpr ?_
          rw [← this]
          exact Finsupp.mem_support_iff.mp hF
    -- the weight strictly decreases
    have hht : ∀ F ∈ (S.d3low Q).support, S.ht F.top = S.ht a := by
      intro F hF
      have h1 := S.d3low_support_ht Q hF
      have h2 : S.ht a + 1 = S.ht w := S.ht_dn ha
      rw [hQtop] at h1
      omega
    have hsumlow : ∑ F ∈ (S.d3low Q).support, 2 ^ S.ht F.top ≤ 3 * 2 ^ S.ht a := by
      have h1 : ∑ F ∈ (S.d3low Q).support, 2 ^ S.ht F.top
          ≤ (S.d3low Q).support.card • 2 ^ S.ht a :=
        Finset.sum_le_card_nsmul _ _ _ (fun F hF => by rw [hht F hF])
      have h2 := S.d3low_support_card Q
      calc ∑ F ∈ (S.d3low Q).support, 2 ^ S.ht F.top
          ≤ (S.d3low Q).support.card • 2 ^ S.ht a := h1
        _ = (S.d3low Q).support.card * 2 ^ S.ht a := by simp [smul_eq_mul]
        _ ≤ 3 * 2 ^ S.ht a := Nat.mul_le_mul_right _ h2
    have hsumP : ∑ F ∈ ({P1, P2, P3} : Finset S.SqC), 2 ^ S.ht F.top = 6 * 2 ^ S.ht a := by
      rw [Finset.sum_insert (by simp [h12, h13]), Finset.sum_insert (by simp [h23]),
        Finset.sum_singleton]
      have hP1t : P1.top = w := by rw [hP1def]; rfl
      have hP2t : P2.top = w := by rw [hP2def]; rfl
      have hP3t : P3.top = w := by rw [hP3def]; rfl
      have h2 : S.ht w = S.ht a + 1 := (S.ht_dn ha).symm
      rw [hP1t, hP2t, hP3t, h2, pow_succ]
      ring
    have hsplit : (∑ F ∈ z.support \ ({P1, P2, P3} : Finset S.SqC), 2 ^ S.ht F.top)
        + 6 * 2 ^ S.ht a = n := by
      rw [← hsumP, Finset.sum_sdiff hPsub, hn]
    have hlt : (∑ F ∈ z'.support, 2 ^ S.ht F.top) < n := by
      have hstep1 : (∑ F ∈ z'.support, 2 ^ S.ht F.top)
          ≤ ∑ F ∈ (z.support \ ({P1, P2, P3} : Finset S.SqC)) ∪ (S.d3low Q).support,
              2 ^ S.ht F.top :=
        Finset.sum_le_sum_of_subset hz'supp
      have hstep2 : ∑ F ∈ (z.support \ ({P1, P2, P3} : Finset S.SqC)) ∪ (S.d3low Q).support,
              2 ^ S.ht F.top
          ≤ (∑ F ∈ z.support \ ({P1, P2, P3} : Finset S.SqC), 2 ^ S.ht F.top)
            + ∑ F ∈ (S.d3low Q).support, 2 ^ S.ht F.top := by
        have := Finset.sum_union_inter (s₁ := z.support \ ({P1, P2, P3} : Finset S.SqC))
          (s₂ := (S.d3low Q).support) (f := fun F => 2 ^ S.ht F.top)
        omega
      have hpos : 0 < 2 ^ S.ht a := pow_pos (by norm_num) _
      omega
    obtain ⟨c', hc'⟩ := ih _ hlt z' rfl hz'
    refine ⟨c' + lam • Finsupp.single Q 1, ?_⟩
    have hsingle : S.d₃ (Finsupp.single Q (1 : ℤ)) = S.d3gen Q := by
      unfold d₃
      rw [Finsupp.linearCombination_single, one_smul]
    rw [map_add, hc', map_smul, hsingle, hz'def, sub_add_cancel]

/-- **`ker d₂ = im d₃`** for the cellular chains of an at most three-dimensional cube complex
with the descending-cube property: the second homology of the complex vanishes. -/
theorem ker_d₂_eq_range_d₃ :
    LinearMap.ker S.d₂ = LinearMap.range S.d₃ := by
  ext z
  constructor
  · intro hz
    obtain ⟨c, hc⟩ := S.exists_d₃_eq z (LinearMap.mem_ker.mp hz)
    exact ⟨c, hc⟩
  · rintro ⟨c, rfl⟩
    exact LinearMap.mem_ker.mpr (S.d₂_d₃ c)

end DescCubeStr

end FiniteChains
