module

/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license.
Adapted to Lean 4.28.0 from Vilin97/homotopy-groups-lean, commit
c66523531ff172d7f41913d94e56921e790a1b47.
The simplex-specific dependency has been removed; cube-face definitions
are copied from the same revision of Hurewicz/StickSimplex.lean.
-/
public import Mathlib.Topology.Homotopy.HomotopyGroup
public import Mathlib.Topology.UnitInterval
public import Mathlib.Tactic

@[expose] public section

/-!
# Cubical shells in a pointed space

A map on a `(d+1)`-cube which is constant on the codimension-two cubical skeleton restricts on
each of its `2(d+1)` facets to a based `d`-loop.  This file packages that construction independently
of the stick-breaking simplex used later in the Hurewicz argument.

The first two supported homotopy-addition cases are also proved here.  If only one opposite pair
of facets can be nonconstant, varying its coordinate gives the required relative homotopy.  If
only two adjacent pairs can be nonconstant, convex interpolation between the bottom-right and
left-top routes across their square gives the four-face relation.  Consequently the full oriented
cubical boundary class vanishes in both cases.
-/

open scoped Topology Topology.Homotopy unitInterval

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains.TopologicalSingular

variable {d : ℕ} {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
  {x : X} {y : Y}

/-- Insert a fixed coordinate into a cube. -/
def cubeFace {d : ℕ} (i : Fin (d + 1)) (a : I) : C(I^Fin d, I^Fin (d + 1)) where
  toFun t := i.insertNth a t
  continuous_toFun := by
    apply continuous_pi
    intro j
    refine Fin.succAboveCases i ?_ (fun k => ?_) j
    · simp only [Fin.insertNth_apply_same]
      exact continuous_const
    · simp only [Fin.insertNth_apply_succAbove]
      exact continuous_apply k

@[simp]
theorem cubeFace_apply {d : ℕ} (i : Fin (d + 1)) (a : I) (t : I^Fin d) :
    cubeFace i a t = i.insertNth a t :=
  rfl

@[simp]
theorem cubeFace_apply_same {d : ℕ} (i : Fin (d + 1)) (a : I) (t : I^Fin d) :
    cubeFace i a t i = a := by
  simp [cubeFace]

@[simp]
theorem cubeFace_apply_succAbove {d : ℕ} (i : Fin (d + 1)) (a : I)
    (t : I^Fin d) (j : Fin d) :
    cubeFace i a t (i.succAbove j) = t j := by
  simp [cubeFace]


/-- The codimension-two cubical skeleton: at least two distinct coordinates are endpoints. -/
def cubeCodimTwo (d : ℕ) : Set (I^Fin d) :=
  {t | ∃ i j : Fin d, i ≠ j ∧ (t i = 0 ∨ t i = 1) ∧ (t j = 0 ∨ t j = 1)}

theorem cubeFace_mem_cubeCodimTwo {d : ℕ} (i : Fin (d + 1)) (a : I)
    (ha : a = 0 ∨ a = 1) (t : I^Fin d) (ht : t ∈ Cube.boundary (Fin d)) :
    cubeFace i a t ∈ cubeCodimTwo (d + 1) := by
  obtain ⟨j, hj⟩ := ht
  refine ⟨i, i.succAbove j, (Fin.succAbove_ne i j).symm, ?_, ?_⟩
  · simpa using ha
  · simpa using hj

/-- Insert a varying coordinate into a cube. -/
def cubeFaceVary {d : ℕ} (i : Fin (d + 1)) : C(I × (I^Fin d), I^Fin (d + 1)) where
  toFun p := i.insertNth p.1 p.2
  continuous_toFun := by
    apply continuous_pi
    intro j
    refine Fin.succAboveCases i ?_ (fun k ↦ ?_) j
    · simpa only [Fin.insertNth_apply_same] using (continuous_fst :
        Continuous fun p : I × (I^Fin d) ↦ p.1)
    · simpa only [Fin.insertNth_apply_succAbove]
        using (by fun_prop : Continuous fun p : I × (I^Fin d) ↦ p.2 k)

@[simp]
theorem cubeFaceVary_apply {d : ℕ} (i : Fin (d + 1)) (a : I) (t : I^Fin d) :
    cubeFaceVary i (a, t) = cubeFace i a t :=
  rfl

/-! ### The two routes around a square -/

/-- The bottom edge of the unit square, directed from left to right. -/
def squareBottom : Path ((0, 0) : I × I) (1, 0) where
  toFun t := (t, 0)
  continuous_toFun := by fun_prop
  source' := rfl
  target' := rfl

/-- The right edge of the unit square, directed from bottom to top. -/
def squareRight : Path ((1, 0) : I × I) (1, 1) where
  toFun t := (1, t)
  continuous_toFun := by fun_prop
  source' := rfl
  target' := rfl

/-- The left edge of the unit square, directed from bottom to top. -/
def squareLeft : Path ((0, 0) : I × I) (0, 1) where
  toFun t := (0, t)
  continuous_toFun := by fun_prop
  source' := rfl
  target' := rfl

/-- The top edge of the unit square, directed from left to right. -/
def squareTop : Path ((0, 1) : I × I) (1, 1) where
  toFun t := (t, 1)
  continuous_toFun := by fun_prop
  source' := rfl
  target' := rfl

/-- The bottom-then-right route around the unit square. -/
def squareBottomRight : Path ((0, 0) : I × I) (1, 1) :=
  squareBottom.trans squareRight

/-- The left-then-top route around the unit square. -/
def squareLeftTop : Path ((0, 0) : I × I) (1, 1) :=
  squareLeft.trans squareTop

/-- Convex interpolation across the square gives a path homotopy between its two monotone
edge routes. -/
noncomputable def squareBoundaryHomotopy :
    Path.Homotopy squareBottomRight squareLeftTop where
  toFun p :=
    (Set.Icc.convexComb (squareBottomRight p.2).1 (squareLeftTop p.2).1 p.1,
      Set.Icc.convexComb (squareBottomRight p.2).2 (squareLeftTop p.2).2 p.1)
  continuous_toFun := by
    apply Continuous.prodMk
    all_goals
      apply Continuous.subtype_mk
      fun_prop
  map_zero_left t := by
    ext <;> simp [squareBottomRight, squareLeftTop]
  map_one_left t := by
    ext <;> simp [squareBottomRight, squareLeftTop]
  prop' s t ht := by
    rcases ht with rfl | ht
    · simp [squareBottomRight, squareLeftTop, Set.Icc.convexComb]
    · rw [Set.mem_singleton_iff] at ht
      subst t
      simp [squareBottomRight, squareLeftTop, Set.Icc.convexComb]

@[simp]
theorem cubeFace_last_eq_snoc {m : ℕ} (a : I) (t : I^Fin m) :
    cubeFace (Fin.last m) a t = Fin.snoc t a := by
  simp [cubeFace]

@[simp]
theorem cubeFace_penultimate_snoc {m : ℕ} (a b : I) (t : I^Fin m) :
    cubeFace (Fin.last m).castSucc a (Fin.snoc t b) = Fin.snoc (Fin.snoc t a) b := by
  funext j
  induction j using Fin.lastCases with
  | last =>
      have hlast : (Fin.last m).castSucc.succAbove (Fin.last m) = Fin.last (m + 1) := by
        apply Fin.ext
        simp
      rw [← hlast, cubeFace_apply_succAbove]
      simp
  | cast j =>
      induction j using Fin.lastCases with
      | last => simp [cubeFace]
      | cast j => simp [cubeFace, Fin.insertNth_apply_below, Fin.snoc]

@[simp]
theorem update_last_eq_snoc_init {m : ℕ} (t : I^Fin (m + 1)) (a : I) :
    Function.update t (Fin.last m) a = Fin.snoc (Fin.init t) a := by
  conv_lhs => rw [← Fin.snoc_init_self t]
  exact Fin.update_snoc_last _ _ _

/-- The convex sweep from the bottom-right route to the left-top route, with `m` passive
coordinates prepended. -/
noncomputable def squareSweepCube (m : ℕ) :
    C(I × (I^Fin (m + 1)), I^Fin (m + 2)) where
  toFun st :=
    Fin.snoc (Fin.snoc (Fin.init st.2) (squareBoundaryHomotopy (st.1, st.2 (Fin.last m))).1)
      (squareBoundaryHomotopy (st.1, st.2 (Fin.last m))).2
  continuous_toFun := by
    have hc : Continuous (fun st : I × (I^Fin (m + 1)) =>
        squareBoundaryHomotopy (st.1, st.2 (Fin.last m))) :=
      squareBoundaryHomotopy.continuous.comp (by fun_prop)
    apply continuous_pi
    intro j
    refine Fin.lastCases ?_ (fun k => ?_) j
    · simp only [Fin.snoc_last]
      exact hc.snd
    · simp only [Fin.snoc_castSucc]
      refine Fin.lastCases ?_ (fun l => ?_) k
      · simp only [Fin.snoc_last]
        exact hc.fst
      · simp only [Fin.snoc_castSucc, Fin.init_def]
        fun_prop

/-- Pointwise concatenation formula with the unclamped half-interval coordinates exposed. -/
theorem genLoop_transAt_apply_path {N : Type*} [DecidableEq N] (i : N)
    (f g : Ω^ N X x) (t : I^N) :
    (GenLoop.transAt i f g).val t =
      if h : (t i : ℝ) ≤ 1 / 2 then
        f (Function.update t i
          ⟨2 * t i, (unitInterval.mul_pos_mem_iff zero_lt_two).2 ⟨(t i).2.1, h⟩⟩)
      else
        g (Function.update t i
          ⟨2 * t i - 1, unitInterval.two_mul_sub_one_mem_iff.2
            ⟨(not_le.1 h).le, (t i).2.2⟩⟩) := by
  change (if (t i : ℝ) ≤ 1 / 2 then
      f (Function.update t i (Set.projIcc 0 1 zero_le_one (2 * t i)))
    else g (Function.update t i (Set.projIcc 0 1 zero_le_one (2 * t i - 1)))) = _
  split_ifs with h
  · rw [Set.projIcc_of_mem _ ((unitInterval.mul_pos_mem_iff zero_lt_two).2 ⟨(t i).2.1, h⟩)]
  · rw [Set.projIcc_of_mem _ (unitInterval.two_mul_sub_one_mem_iff.2
      ⟨(not_le.1 h).le, (t i).2.2⟩)]

/-- A cubical shell is a map on a cube which collapses the codimension-two skeleton to the
chosen basepoint. -/
structure CubicalShell (d : ℕ) (X : Type*) [TopologicalSpace X] (x : X) where
  /-- The map on the ambient `(d+1)`-cube. -/
  map : C(I^Fin (d + 1), X)
  /-- The map is constant on the codimension-two cubical skeleton. -/
  codimTwo (t : I^Fin (d + 1)) (ht : t ∈ cubeCodimTwo (d + 1)) : map t = x

namespace CubicalShell

/-- The facet of a cubical shell at coordinate `i` and endpoint `a`, as a based generalized
loop. -/
noncomputable def faceLoop (S : CubicalShell d X x) (i : Fin (d + 1)) (a : I)
    (ha : a = 0 ∨ a = 1) : Ω^ (Fin d) X x :=
  ⟨S.map.comp (cubeFace i a), fun t ht ↦ S.codimTwo _
    (cubeFace_mem_cubeCodimTwo i a ha t ht)⟩

@[simp]
theorem faceLoop_apply (S : CubicalShell d X x) (i : Fin (d + 1)) (a : I)
    (ha : a = 0 ∨ a = 1) (t : I^Fin d) :
    (S.faceLoop i a ha).val t = S.map (cubeFace i a t) :=
  rfl

/-- The lower facet loop. -/
noncomputable def lowerFaceLoop (S : CubicalShell d X x) (i : Fin (d + 1)) :
    Ω^ (Fin d) X x :=
  S.faceLoop i 0 (Or.inl rfl)

/-- The upper facet loop. -/
noncomputable def upperFaceLoop (S : CubicalShell d X x) (i : Fin (d + 1)) :
    Ω^ (Fin d) X x :=
  S.faceLoop i 1 (Or.inr rfl)

@[simp]
theorem lowerFaceLoop_apply (S : CubicalShell d X x) (i : Fin (d + 1))
    (t : I^Fin d) :
    (S.lowerFaceLoop i).val t = S.map (cubeFace i 0 t) :=
  rfl

@[simp]
theorem upperFaceLoop_apply (S : CubicalShell d X x) (i : Fin (d + 1))
    (t : I^Fin d) :
    (S.upperFaceLoop i).val t = S.map (cubeFace i 1 t) :=
  rfl

/-- The sweep starts at the concatenation of the last lower face with the penultimate upper
face. -/
theorem squareSweepCube_zero {m : ℕ} (S : CubicalShell (m + 1) X x)
    (t : I^Fin (m + 1)) :
    S.map (squareSweepCube m (0, t)) =
      (GenLoop.transAt (Fin.last m) (S.lowerFaceLoop (Fin.last (m + 1)))
        (S.upperFaceLoop (Fin.last m).castSucc)).val t := by
  change S.map (Fin.snoc (Fin.snoc (Fin.init t)
    (squareBoundaryHomotopy (0, t (Fin.last m))).1)
    (squareBoundaryHomotopy (0, t (Fin.last m))).2) = _
  rw [ContinuousMap.HomotopyWith.apply_zero, squareBottomRight]
  simp only [Path.coe_toContinuousMap]
  rw [Path.trans_apply, genLoop_transAt_apply_path]
  split_ifs with h
  · change S.map _ = S.map (cubeFace (Fin.last (m + 1)) 0 _)
    apply congrArg S.map
    rw [cubeFace_last_eq_snoc, update_last_eq_snoc_init]
    rfl
  · change S.map _ = S.map (cubeFace (Fin.last m).castSucc 1 _)
    apply congrArg S.map
    rw [update_last_eq_snoc_init, cubeFace_penultimate_snoc]
    rfl

/-- The sweep ends at the concatenation of the penultimate lower face with the last upper
face. -/
theorem squareSweepCube_one {m : ℕ} (S : CubicalShell (m + 1) X x)
    (t : I^Fin (m + 1)) :
    S.map (squareSweepCube m (1, t)) =
      (GenLoop.transAt (Fin.last m) (S.lowerFaceLoop (Fin.last m).castSucc)
        (S.upperFaceLoop (Fin.last (m + 1)))).val t := by
  change S.map (Fin.snoc (Fin.snoc (Fin.init t)
    (squareBoundaryHomotopy (1, t (Fin.last m))).1)
    (squareBoundaryHomotopy (1, t (Fin.last m))).2) = _
  rw [ContinuousMap.HomotopyWith.apply_one, squareLeftTop]
  simp only [Path.coe_toContinuousMap]
  rw [Path.trans_apply, genLoop_transAt_apply_path]
  split_ifs with h
  · change S.map _ = S.map (cubeFace (Fin.last m).castSucc 0 _)
    apply congrArg S.map
    rw [update_last_eq_snoc_init, cubeFace_penultimate_snoc]
    rfl
  · change S.map _ = S.map (cubeFace (Fin.last (m + 1)) 1 _)
    apply congrArg S.map
    rw [cubeFace_last_eq_snoc, update_last_eq_snoc_init]
    rfl

/-- A facet of the ambient cube is constant at the shell basepoint. -/
def IsConstantFace (S : CubicalShell d X x) (i : Fin (d + 1)) (a : I) : Prop :=
  ∀ t : I^Fin (d + 1), t i = a → S.map t = x

theorem faceLoop_eq_const (S : CubicalShell d X x) (i : Fin (d + 1)) (a : I)
    (ha : a = 0 ∨ a = 1) (h : S.IsConstantFace i a) :
    S.faceLoop i a ha = GenLoop.const := by
  apply GenLoop.ext
  intro t
  exact h _ (by simp)

theorem lowerFaceLoop_eq_const (S : CubicalShell d X x) (i : Fin (d + 1))
    (h : S.IsConstantFace i 0) :
    S.lowerFaceLoop i = GenLoop.const :=
  S.faceLoop_eq_const i 0 (Or.inl rfl) h

theorem upperFaceLoop_eq_const (S : CubicalShell d X x) (i : Fin (d + 1))
    (h : S.IsConstantFace i 1) :
    S.upperFaceLoop i = GenLoop.const :=
  S.faceLoop_eq_const i 1 (Or.inr rfl) h

/-- Every facet transverse to coordinate `i` is constant. -/
def TransverseFacesConstant (S : CubicalShell d X x) (i : Fin (d + 1)) : Prop :=
  ∀ (j : Fin (d + 1)), j ≠ i → S.IsConstantFace j 0 ∧ S.IsConstantFace j 1

/-- All facets in the first `m` directions are constant, leaving only the last two coordinate
pairs potentially nonconstant. -/
def LeadingFacesConstant {m : ℕ} (S : CubicalShell (m + 1) X x) : Prop :=
  ∀ i : Fin m,
    S.IsConstantFace i.castSucc.castSucc 0 ∧ S.IsConstantFace i.castSucc.castSucc 1

/-- The square filling relates the two concatenations formed by the last four facets. -/
theorem lastTwoFaceLoops_homotopic {m : ℕ} (S : CubicalShell (m + 1) X x)
    (h : S.LeadingFacesConstant) :
    GenLoop.Homotopic
      (GenLoop.transAt (Fin.last m) (S.lowerFaceLoop (Fin.last (m + 1)))
        (S.upperFaceLoop (Fin.last m).castSucc))
      (GenLoop.transAt (Fin.last m) (S.lowerFaceLoop (Fin.last m).castSucc)
        (S.upperFaceLoop (Fin.last (m + 1)))) := by
  refine ⟨{
    toFun := fun st ↦ S.map (squareSweepCube m st)
    continuous_toFun := S.map.continuous.comp (squareSweepCube m).continuous
    map_zero_left := S.squareSweepCube_zero
    map_one_left := S.squareSweepCube_one
    prop' := fun s t ht ↦ ?_ }⟩
  have hstart := (GenLoop.transAt (Fin.last m) (S.lowerFaceLoop (Fin.last (m + 1)))
    (S.upperFaceLoop (Fin.last m).castSucc)).property t ht
  apply Eq.trans ?_ hstart.symm
  obtain ⟨j, hj⟩ := ht
  obtain ⟨i, rfl⟩ | rfl := j.eq_castSucc_or_eq_last
  · rcases h i with ⟨hi0, hi1⟩
    rcases hj with hj | hj
    · exact hi0 _ (by simpa [squareSweepCube, Fin.init_def] using hj)
    · exact hi1 _ (by simpa [squareSweepCube, Fin.init_def] using hj)
  · rcases hj with hj | hj
    · apply S.codimTwo
      refine ⟨(Fin.last m).castSucc, Fin.last (m + 1),
        Fin.castSucc_ne_last (Fin.last m), Or.inl ?_, Or.inl ?_⟩
      · simp [squareSweepCube, hj]
      · simp [squareSweepCube, hj]
    · apply S.codimTwo
      refine ⟨(Fin.last m).castSucc, Fin.last (m + 1),
        Fin.castSucc_ne_last (Fin.last m), Or.inr ?_, Or.inr ?_⟩
      · simp [squareSweepCube, hj]
      · simp [squareSweepCube, hj]

/-- If all transverse facets are constant, varying the chosen coordinate gives a homotopy
relative to the cubical boundary between its lower and upper facet loops. -/
theorem lowerFaceLoop_homotopic_upperFaceLoop (S : CubicalShell d X x)
    (i : Fin (d + 1)) (h : S.TransverseFacesConstant i) :
    GenLoop.Homotopic (S.lowerFaceLoop i) (S.upperFaceLoop i) := by
  refine ⟨{
    toFun := fun p ↦ S.map (cubeFaceVary i p)
    continuous_toFun := S.map.continuous.comp (cubeFaceVary i).continuous
    map_zero_left := fun t ↦ rfl
    map_one_left := fun t ↦ rfl
    prop' := fun a t ht ↦ ?_ }⟩
  have ht' := ht
  obtain ⟨j, hj⟩ := ht
  let k : Fin (d + 1) := i.succAbove j
  have hki : k ≠ i := Fin.succAbove_ne i j
  rcases h k hki with ⟨hk0, hk1⟩
  rcases hj with hj | hj
  · calc
      S.map (cubeFaceVary i (a, t)) = x := hk0 _ (by simpa [k] using hj)
      _ = (S.lowerFaceLoop i).val t := ((S.lowerFaceLoop i).property t ht').symm
  · calc
      S.map (cubeFaceVary i (a, t)) = x := hk1 _ (by simpa [k] using hj)
      _ = (S.lowerFaceLoop i).val t := ((S.lowerFaceLoop i).property t ht').symm

/-- The additive homotopy class of a lower facet. -/
noncomputable def lowerFaceClass (S : CubicalShell d X x) (i : Fin (d + 1)) :
    Additive (HomotopyGroup (Fin d) X x) :=
  Additive.ofMul (⟦S.lowerFaceLoop i⟧ : HomotopyGroup (Fin d) X x)

/-- The additive homotopy class of an upper facet. -/
noncomputable def upperFaceClass (S : CubicalShell d X x) (i : Fin (d + 1)) :
    Additive (HomotopyGroup (Fin d) X x) :=
  Additive.ofMul (⟦S.upperFaceLoop i⟧ : HomotopyGroup (Fin d) X x)

theorem lowerFaceClass_eq_upperFaceClass (S : CubicalShell d X x)
    (i : Fin (d + 1)) (h : S.TransverseFacesConstant i) :
    S.lowerFaceClass i = S.upperFaceClass i := by
  exact congrArg Additive.ofMul (Quotient.sound (S.lowerFaceLoop_homotopic_upperFaceLoop i h))

theorem lowerFaceClass_eq_zero [Nonempty (Fin d)] (S : CubicalShell d X x)
    (i : Fin (d + 1)) (h : S.IsConstantFace i 0) :
    S.lowerFaceClass i = 0 := by
  rw [lowerFaceClass, S.lowerFaceLoop_eq_const i h, ← HomotopyGroup.one_def]
  rfl

theorem upperFaceClass_eq_zero [Nonempty (Fin d)] (S : CubicalShell d X x)
    (i : Fin (d + 1)) (h : S.IsConstantFace i 1) :
    S.upperFaceClass i = 0 := by
  rw [upperFaceClass, S.upperFaceLoop_eq_const i h, ← HomotopyGroup.one_def]
  rfl

/-- The four face classes around the last-coordinate square satisfy the square boundary
relation. -/
theorem lastTwoFaceClass_relation {m : ℕ} [Nontrivial (Fin (m + 1))]
    (S : CubicalShell (m + 1) X x) (h : S.LeadingFacesConstant) :
    S.upperFaceClass (Fin.last m).castSucc + S.lowerFaceClass (Fin.last (m + 1)) =
      S.upperFaceClass (Fin.last (m + 1)) + S.lowerFaceClass (Fin.last m).castSucc := by
  have hq :
      ((· * ·) : HomotopyGroup (Fin (m + 1)) X x →
          HomotopyGroup (Fin (m + 1)) X x → HomotopyGroup (Fin (m + 1)) X x)
        ⟦S.upperFaceLoop (Fin.last m).castSucc⟧ ⟦S.lowerFaceLoop (Fin.last (m + 1))⟧ =
      ((· * ·) : HomotopyGroup (Fin (m + 1)) X x →
          HomotopyGroup (Fin (m + 1)) X x → HomotopyGroup (Fin (m + 1)) X x)
        ⟦S.upperFaceLoop (Fin.last (m + 1))⟧ ⟦S.lowerFaceLoop (Fin.last m).castSucc⟧ := by
    rw [HomotopyGroup.mul_spec (i := Fin.last m),
      HomotopyGroup.mul_spec (i := Fin.last m)]
    exact Quotient.sound (S.lastTwoFaceLoops_homotopic h)
  exact congrArg Additive.ofMul hq

/-- The two surviving signed face-pair terms cancel. -/
theorem lastTwoBoundaryTerms_eq_zero {m : ℕ} [Nontrivial (Fin (m + 1))]
    (S : CubicalShell (m + 1) X x) (h : S.LeadingFacesConstant) :
    (-1 : ℤ) ^ m •
        (S.upperFaceClass (Fin.last m).castSucc - S.lowerFaceClass (Fin.last m).castSucc) +
      (-1 : ℤ) ^ (m + 1) •
        (S.upperFaceClass (Fin.last (m + 1)) - S.lowerFaceClass (Fin.last (m + 1))) = 0 := by
  have hbase :
      (S.upperFaceClass (Fin.last m).castSucc - S.lowerFaceClass (Fin.last m).castSucc) -
        (S.upperFaceClass (Fin.last (m + 1)) - S.lowerFaceClass (Fin.last (m + 1))) = 0 := by
    calc
      _ = (S.upperFaceClass (Fin.last m).castSucc +
          S.lowerFaceClass (Fin.last (m + 1))) -
        (S.upperFaceClass (Fin.last (m + 1)) +
          S.lowerFaceClass (Fin.last m).castSucc) := by abel
      _ = 0 := by rw [S.lastTwoFaceClass_relation h, sub_self]
  rw [pow_succ]
  simp only [mul_neg, mul_one, neg_smul]
  rw [← sub_eq_add_neg]
  have hc := congrArg (fun z : Additive (HomotopyGroup (Fin (m + 1)) X x) =>
    ((-1 : ℤ) ^ m) • z) hbase
  simpa only [zsmul_sub, zsmul_zero] using hc

/-- The oriented sum of all upper and lower facet classes. -/
noncomputable def boundaryClass [Nontrivial (Fin d)] (S : CubicalShell d X x) :
    Additive (HomotopyGroup (Fin d) X x) :=
  ∑ i : Fin (d + 1),
    (-1 : ℤ) ^ (i : ℕ) • (S.upperFaceClass i - S.lowerFaceClass i)

/-- The second cubical homotopy-addition case: the oriented boundary class is zero when only
the last two opposite pairs of facets can be nonconstant. -/
theorem boundaryClass_eq_zero_of_leadingFacesConstant {m : ℕ}
    [Nontrivial (Fin (m + 1))] (S : CubicalShell (m + 1) X x)
    (h : S.LeadingFacesConstant) : S.boundaryClass = 0 := by
  let f := fun i : Fin (m + 2) ↦
    (-1 : ℤ) ^ (i : ℕ) • (S.upperFaceClass i - S.lowerFaceClass i)
  change ∑ i : Fin (m + 2), f i = 0
  rw [Fin.sum_univ_castSucc, Fin.sum_univ_castSucc]
  have hz : ∑ i : Fin m, f i.castSucc.castSucc = 0 := by
    apply Fintype.sum_eq_zero
    intro i
    rcases h i with ⟨hi0, hi1⟩
    simp only [f]
    rw [S.upperFaceClass_eq_zero i.castSucc.castSucc hi1,
      S.lowerFaceClass_eq_zero i.castSucc.castSucc hi0, sub_self, smul_zero]
  rw [hz, zero_add]
  simpa [f] using S.lastTwoBoundaryTerms_eq_zero h

/-- The first cubical homotopy-addition case: the oriented boundary class is zero when only one
opposite pair of facets can be nonconstant. -/
theorem boundaryClass_eq_zero_of_transverseFacesConstant [Nontrivial (Fin d)]
    (S : CubicalShell d X x) (i : Fin (d + 1)) (h : S.TransverseFacesConstant i) :
    S.boundaryClass = 0 := by
  rw [boundaryClass, Finset.sum_eq_single i]
  · rw [S.lowerFaceClass_eq_upperFaceClass i h, sub_self, smul_zero]
  · intro j hj hji
    have hji' : j ≠ i := by simpa [eq_comm] using hji
    rcases h j hji' with ⟨hj0, hj1⟩
    rw [S.upperFaceClass_eq_zero j hj1, S.lowerFaceClass_eq_zero j hj0, sub_zero,
      smul_zero]
  · simp

end CubicalShell

end FiniteChains.TopologicalSingular
