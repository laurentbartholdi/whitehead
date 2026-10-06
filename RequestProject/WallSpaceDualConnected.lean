import RequestProject.WallSpaceDual
import RequestProject.RollerGraphMetric

/-!
# The dual of a wall space is a connected median graph

`RequestProject/WallSpaceDual.lean` proves that the dual of a wall space — the consistent
orientations of the walls that differ from a base point in finitely many walls — is closed
under the median (majority) operation, i.e. that it is a `FiniteChains.RollerModel`.

Median-closedness alone does not say that the halfspace coordinates are the vertices of a
*graph*: as `RequestProject/RollerConnected.lean` records, a median-closed family need not be
connected by one-coordinate moves.  This file supplies the missing step for duals of wall
spaces.  The only extra hypothesis is that the walls are pairwise distinct as partitions of
the space (`FiniteChains.WallSpace.Reduced`); this is no loss of generality, since repeated
walls may simply be discarded.

The main result is `FiniteChains.WallSpace.exists_flip`: given two consistent orientations,
one of the walls on which they disagree may be flipped in the first one without destroying
consistency — take a wall whose chosen halfspace is minimal among the disputed ones.  In
halfspace coordinates this is `FiniteChains.WallSpace.dualW_step`, which gives

* `FiniteChains.WallSpace.gatedDualModel` — the dual is a `FiniteChains.GatedRollerModel`,
  hence its graph is connected, the number of separating walls is its edge metric, and it is
  a median graph in the graph-theoretic sense;
* `FiniteChains.WallSpace.dualGraph_connected`,
  `FiniteChains.WallSpace.dualGraph_dist_eq`,
  `FiniteChains.WallSpace.gatedDual_ker_d₂_eq_range_d₃`.
-/

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains

universe u v

open RollerBridge

namespace WallSpace

variable {X : Type u} {ι : Type v} [DecidableEq ι] {S : WallSpace X ι}

variable (S) in
/-- The halfspace chosen by an orientation at a wall. -/
def hs (o : ι → Bool) (i : ι) : Set X := {x | S.side i x = o i}

variable (S) in
/-- A wall space is **reduced** when distinct indices give distinct walls: if a side of the
wall `i` coincides with a side of the wall `j` as a subset of `X`, then `i = j`. -/
def Reduced : Prop :=
  ∀ (i j : ι) (b c : Bool), (∀ x : X, S.side i x = b ↔ S.side j x = c) → i = j

/-- **A disputed wall with a minimal halfspace can be flipped.**  If `oA` and `oB` are
consistent orientations differing in finitely many but at least one wall, then some wall `p`
on which they differ can be flipped in `oA` to the value of `oB`, keeping consistency. -/
theorem exists_flip (hred : S.Reduced) {oA oB : ι → Bool} (hA : S.Consistent oA)
    (hB : S.Consistent oB) (hfin : {i | oA i ≠ oB i}.Finite)
    (hne : {i | oA i ≠ oB i}.Nonempty) :
    ∃ p, oA p ≠ oB p ∧ S.Consistent (Function.update oA p (oB p)) := by
  obtain ⟨p, hpmem, hmin⟩ := hfin.exists_minimalFor (S.hs oA) _ hne
  refine ⟨p, hpmem, ?_⟩
  have hpne : oA p ≠ oB p := hpmem
  have hBp : oB p = !oA p := by
    cases h1 : oA p <;> cases h2 : oB p <;> simp_all
  -- the halfspace of `oB` at `p` meets every halfspace chosen by `oA` at another wall
  have key : ∀ j, j ≠ p → ∃ x : X, S.side p x = oB p ∧ S.side j x = oA j := by
    intro j hjp
    by_contra hcon
    push_neg at hcon
    -- then the halfspace of `oA` at `j` is contained in the one at `p`
    have hsub : S.hs oA j ⊆ S.hs oA p := by
      intro x hx
      have hxj : S.side j x = oA j := hx
      have := hcon x
      have hpx : S.side p x ≠ oB p := fun h => (this h) hxj
      show S.side p x = oA p
      rw [hBp] at hpx
      cases h1 : S.side p x <;> cases h2 : oA p <;> simp_all
    by_cases hjD : oA j ≠ oB j
    · -- `j` is disputed, so minimality forces the two halfspaces to be equal
      have hsub' : S.hs oA p ⊆ S.hs oA j := hmin hjD hsub
      exact hjp (hred j p (oA j) (oA p) (fun x => ⟨fun h => hsub h, fun h => hsub' h⟩))
    · -- `j` is undisputed, so `oB` chooses two disjoint halfspaces, contradicting consistency
      push_neg at hjD
      obtain ⟨x, hx1, hx2⟩ := hB j p
      have hxj : S.side j x = oA j := by rw [hjD]; exact hx1
      have hxp : S.side p x = oA p := hsub hxj
      rw [hBp] at hx2
      rw [hxp] at hx2
      cases h : oA p <;> simp [h] at hx2
  have hup : Function.update oA p (oB p) p = oB p := Function.update_self _ _ _
  have huk : ∀ k, k ≠ p → Function.update oA p (oB p) k = oA k :=
    fun k hk => Function.update_of_ne hk _ _
  intro i j
  by_cases hi : i = p
  · by_cases hj : j = p
    · obtain ⟨x, hx1, -⟩ := hB p p
      exact ⟨x, by rw [hi, hup]; exact hx1, by rw [hj, hup]; exact hx1⟩
    · obtain ⟨x, hx1, hx2⟩ := key j hj
      exact ⟨x, by rw [hi, hup]; exact hx1, by rw [huk j hj]; exact hx2⟩
  · by_cases hj : j = p
    · obtain ⟨x, hx1, hx2⟩ := key i hi
      exact ⟨x, by rw [huk i hi]; exact hx2, by rw [hj, hup]; exact hx1⟩
    · obtain ⟨x, hx1, hx2⟩ := hA i j
      exact ⟨x, by rw [huk i hi]; exact hx1, by rw [huk j hj]; exact hx2⟩

section Coordinates

theorem flipOn_ne_iff {x₀ : X} {A B : Finset ι} {i : ι} :
    S.flipOn x₀ A i ≠ S.flipOn x₀ B i ↔ (i ∈ A ↔ i ∉ B) := by
  by_cases hA : i ∈ A <;> by_cases hB : i ∈ B <;>
    simp [flipOn, hA, hB]

/-- **The one-step property of the dual of a reduced wall space**: from a vertex `A` one can
always move towards a different vertex `B` by flipping a single disputed wall. -/
theorem dualW_step (hred : S.Reduced) {x₀ : X} {A B : Finset ι} (hA : A ∈ S.dualW x₀)
    (hB : B ∈ S.dualW x₀) (hAB : A ≠ B) :
    ∃ p, ((p ∈ A ∧ p ∉ B) ∨ (p ∉ A ∧ p ∈ B)) ∧
      (if p ∈ A then A.erase p else insert p A) ∈ S.dualW x₀ := by
  set oA := S.flipOn x₀ A with hoA
  set oB := S.flipOn x₀ B with hoB
  have hDfin : {i | oA i ≠ oB i}.Finite := by
    refine Set.Finite.subset (A ∪ B).finite_toSet ?_
    intro i hi
    have := flipOn_ne_iff.1 hi
    by_cases hiA : i ∈ A
    · simp [hiA]
    · have : i ∈ B := by tauto
      simp [this]
  have hDne : {i | oA i ≠ oB i}.Nonempty := by
    by_contra hemp
    rw [Set.not_nonempty_iff_eq_empty] at hemp
    refine hAB (Finset.ext fun i => ?_)
    have : ¬ (oA i ≠ oB i) := fun h => by
      have : i ∈ {i | oA i ≠ oB i} := h
      rw [hemp] at this; exact this
    have := flipOn_ne_iff (S := S) (x₀ := x₀) (A := A) (B := B) (i := i)
    tauto
  obtain ⟨p, hp, hcons⟩ := exists_flip hred (mem_dualW.1 hA) (mem_dualW.1 hB) hDfin hDne
  have hpAB : (p ∈ A ∧ p ∉ B) ∨ (p ∉ A ∧ p ∈ B) := by
    have := flipOn_ne_iff.1 hp
    by_cases hpA : p ∈ A
    · exact Or.inl ⟨hpA, by tauto⟩
    · exact Or.inr ⟨hpA, by tauto⟩
  refine ⟨p, hpAB, ?_⟩
  set C : Finset ι := if p ∈ A then A.erase p else insert p A with hC
  have hmemC : ∀ i, i ∈ C ↔ (if i = p then p ∉ A else i ∈ A) := by
    intro i
    by_cases hpA : p ∈ A <;> by_cases hip : i = p <;>
      simp [hC, hpA, hip, Finset.mem_erase, Finset.mem_insert]
  have hflip : S.flipOn x₀ C = Function.update oA p (oB p) := by
    funext i
    by_cases hip : i = p
    · subst hip
      rcases hpAB with ⟨hpA, hpB⟩ | ⟨hpA, hpB⟩
      · simp [flipOn, hoA, hoB, (hmemC i).not.2 (by simp [hpA]), hpB]
      · simp [flipOn, hoA, hoB, (hmemC i).2 (by simp [hpA]), hpB]
    · have : (i ∈ C) = (i ∈ A) := by
        simp only [eq_iff_iff]
        rw [hmemC i, if_neg hip]
      simp [flipOn, hoA, Function.update_of_ne hip, this]
  rw [mem_dualW, hflip]
  exact hcons

/-- Every non-base vertex of the dual has a descending neighbour. -/
theorem dualW_desc (hred : S.Reduced) {x₀ : X} {A : Finset ι} (hA : A ∈ S.dualW x₀)
    (hne : A.Nonempty) : ∃ p ∈ A, A.erase p ∈ S.dualW x₀ := by
  have hAB : A ≠ (∅ : Finset ι) := Finset.nonempty_iff_ne_empty.1 hne
  obtain ⟨p, hp, hmem⟩ := dualW_step hred hA (empty_mem_dualW x₀) hAB
  have hpA : p ∈ A := by
    rcases hp with ⟨h, -⟩ | ⟨-, h⟩
    · exact h
    · exact absurd h (Finset.notMem_empty p)
  rw [if_pos hpA] at hmem
  exact ⟨p, hpA, hmem⟩

/-- **The embedding of `X` into the dual is isometric for the wall metric**: the number of
walls separating two points is exactly the number of coordinates in which their images
differ. -/
theorem dsym_coord (x₀ x y : X) :
    dsym (S.coord x₀ x) (S.coord x₀ y) = (S.fin x y).toFinset.card := by
  classical
  have hmem : ∀ (z : X) (i : ι), i ∈ S.coord x₀ z ↔ S.side i z ≠ S.side i x₀ := by
    intro z i
    simp [WallSpace.coord]
  have hunion :
      S.coord x₀ x \ S.coord x₀ y ∪ S.coord x₀ y \ S.coord x₀ x = (S.fin x y).toFinset := by
    ext i
    simp only [Finset.mem_union, Finset.mem_sdiff, hmem, Set.Finite.mem_toFinset,
      Set.mem_setOf_eq]
    cases hx : S.side i x <;> cases hy : S.side i y <;> cases h0 : S.side i x₀ <;> simp
  have hdisj : Disjoint (S.coord x₀ x \ S.coord x₀ y) (S.coord x₀ y \ S.coord x₀ x) := by
    refine Finset.disjoint_left.2 ?_
    intro i hi hi'
    exact (Finset.mem_sdiff.1 hi').2 (Finset.mem_sdiff.1 hi).1
  rw [dsym, ← Finset.card_union_of_disjoint hdisj, hunion]

/-! ## The dual as a gated Roller model -/

theorem dsym_erase {A B : Finset ι} {p : ι} (hpA : p ∈ A) (hpB : p ∉ B) :
    dsym A (A.erase p) = 1 ∧ dsym (A.erase p) B + 1 = dsym A B := by
  have h1 : A \ A.erase p = {p} := by
    ext x
    by_cases hxp : x = p
    · subst hxp; simp [hpA]
    · simp [hxp]
  have h2 : A.erase p \ A = ∅ :=
    Finset.sdiff_eq_empty_iff_subset.2 (Finset.erase_subset _ _)
  have h3 : A.erase p \ B = (A \ B).erase p := by
    ext x
    simp only [Finset.mem_sdiff, Finset.mem_erase]
    tauto
  have h4 : B \ A.erase p = B \ A := by
    ext x
    by_cases hxp : x = p
    · subst hxp; simp [hpB]
    · simp [hxp]
  have hpAB : p ∈ A \ B := Finset.mem_sdiff.2 ⟨hpA, hpB⟩
  refine ⟨?_, ?_⟩
  · simp [dsym, h1, h2]
  · simp only [dsym, h3, h4, Finset.card_erase_of_mem hpAB]
    have : 0 < (A \ B).card := Finset.card_pos.2 ⟨p, hpAB⟩
    omega

theorem dsym_insert {A B : Finset ι} {p : ι} (hpA : p ∉ A) (hpB : p ∈ B) :
    dsym A (insert p A) = 1 ∧ dsym (insert p A) B + 1 = dsym A B := by
  have h1 : A \ insert p A = ∅ :=
    Finset.sdiff_eq_empty_iff_subset.2 (Finset.subset_insert _ _)
  have h2 : insert p A \ A = {p} := by
    ext x
    by_cases hxp : x = p
    · subst hxp; simp [hpA]
    · simp [hxp]
  have h3 : insert p A \ B = A \ B := by
    ext x
    by_cases hxp : x = p
    · subst hxp; simp [hpB]
    · simp [hxp]
  have h4 : B \ insert p A = (B \ A).erase p := by
    ext x
    simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_erase]
    tauto
  have hpBA : p ∈ B \ A := Finset.mem_sdiff.2 ⟨hpB, hpA⟩
  refine ⟨?_, ?_⟩
  · simp [dsym, h1, h2]
  · simp only [dsym, h3, h4, Finset.card_erase_of_mem hpBA]
    have : 0 < (B \ A).card := Finset.card_pos.2 ⟨p, hpBA⟩
    omega

variable (S) in
/-- **The dual cube complex of a reduced, at most three-dimensional wall space is a gated
Roller model**: its halfspace coordinates form a median-closed family in which one can always
step towards another vertex by flipping one wall. -/
noncomputable def gatedDualModel (hred : S.Reduced) (x₀ : X)
    (hdim : ∀ A ∈ S.dualW x₀, ∀ s : Finset (Finset ι),
      (∀ B ∈ s, B ∈ S.dualW x₀ ∧ B ⊆ A ∧ B.card + 1 = A.card) → s.card ≤ 3) :
    GatedRollerModel ι where
  toRollerModel := S.dualModel x₀ hdim
  step := by
    intro A B hA hB hAB
    obtain ⟨p, hp, hmem⟩ := dualW_step hred hA hB hAB
    rcases hp with ⟨hpA, hpB⟩ | ⟨hpA, hpB⟩
    · rw [if_pos hpA] at hmem
      exact ⟨A.erase p, hmem, (dsym_erase hpA hpB).1, (dsym_erase hpA hpB).2⟩
    · rw [if_neg hpA] at hmem
      exact ⟨insert p A, hmem, (dsym_insert hpA hpB).1, (dsym_insert hpA hpB).2⟩

variable (S) in
/-- The graph of the dual: two vertices are adjacent when they differ in exactly one wall. -/
noncomputable def dualGraph (hred : S.Reduced) (x₀ : X)
    (hdim : ∀ A ∈ S.dualW x₀, ∀ s : Finset (Finset ι),
      (∀ B ∈ s, B ∈ S.dualW x₀ ∧ B ⊆ A ∧ B.card + 1 = A.card) → s.card ≤ 3) :
    SimpleGraph (S.gatedDualModel hred x₀ hdim).Vtx :=
  (S.gatedDualModel hred x₀ hdim).graph

/-- **The graph of the dual is connected.** -/
theorem dualGraph_connected (hred : S.Reduced) (x₀ : X)
    (hdim : ∀ A ∈ S.dualW x₀, ∀ s : Finset (Finset ι),
      (∀ B ∈ s, B ∈ S.dualW x₀ ∧ B ⊆ A ∧ B.card + 1 = A.card) → s.card ≤ 3) :
    (S.dualGraph hred x₀ hdim).Connected :=
  (S.gatedDualModel hred x₀ hdim).connected

/-- **The number of separating walls is the edge metric of the dual graph.** -/
theorem dualGraph_dist_eq (hred : S.Reduced) (x₀ : X)
    (hdim : ∀ A ∈ S.dualW x₀, ∀ s : Finset (Finset ι),
      (∀ B ∈ s, B ∈ S.dualW x₀ ∧ B ⊆ A ∧ B.card + 1 = A.card) → s.card ≤ 3)
    (u v : (S.gatedDualModel hred x₀ hdim).Vtx) :
    (S.dualGraph hred x₀ hdim).dist u v = dsym u.1 v.1 :=
  (S.gatedDualModel hred x₀ hdim).dist_eq_dsym u v

/-- **The points of `X` sit isometrically inside the dual graph**: the graph distance between
the images of two points is the number of walls separating them. -/
theorem dualGraph_dist_coord (hred : S.Reduced) (x₀ : X)
    (hdim : ∀ A ∈ S.dualW x₀, ∀ s : Finset (Finset ι),
      (∀ B ∈ s, B ∈ S.dualW x₀ ∧ B ⊆ A ∧ B.card + 1 = A.card) → s.card ≤ 3) (x y : X) :
    (S.dualGraph hred x₀ hdim).dist ⟨S.coord x₀ x, coord_mem_dualW x₀ x⟩
        ⟨S.coord x₀ y, coord_mem_dualW x₀ y⟩ = (S.fin x y).toFinset.card := by
  rw [dualGraph_dist_eq]
  exact dsym_coord x₀ x y

/-- **`ker d₂ = im d₃` for the dual of a reduced, at most three-dimensional wall space**, all
of whose cells are genuine cubes of its (connected, median) graph. -/
theorem gatedDual_ker_d₂_eq_range_d₃ (hred : S.Reduced) (x₀ : X)
    (hdim : ∀ A ∈ S.dualW x₀, ∀ s : Finset (Finset ι),
      (∀ B ∈ s, B ∈ S.dualW x₀ ∧ B ⊆ A ∧ B.card + 1 = A.card) → s.card ≤ 3) :
    LinearMap.ker (S.gatedDualModel hred x₀ hdim).toRollerModel.toDescCubeStr.d₂ =
      LinearMap.range (S.gatedDualModel hred x₀ hdim).toRollerModel.toDescCubeStr.d₃ :=
  (S.gatedDualModel hred x₀ hdim).toRollerModel.ker_d₂_eq_range_d₃

variable (S) in
/-- **The dual of a reduced wall space is a median graph in the graph-theoretic sense**: its
graph is connected, its distance is the edge metric, and every triple of vertices has a unique
median, the majority vote. -/
noncomputable def dualMedianGraph (hred : S.Reduced) (x₀ : X)
    (hdim : ∀ A ∈ S.dualW x₀, ∀ s : Finset (Finset ι),
      (∀ B ∈ s, B ∈ S.dualW x₀ ∧ B ⊆ A ∧ B.card + 1 = A.card) → s.card ≤ 3) :
    MedianSimpleGraph (S.gatedDualModel hred x₀ hdim).Vtx :=
  (S.gatedDualModel hred x₀ hdim).toMedianSimpleGraph

/-- `ker d₂ = im d₃` for the cells of the dual read as genuine cubes of its median graph. -/
theorem dualMedianGraph_ker_d₂_eq_range_d₃ (hred : S.Reduced) (x₀ : X)
    (hdim : ∀ A ∈ S.dualW x₀, ∀ s : Finset (Finset ι),
      (∀ B ∈ s, B ∈ S.dualW x₀ ∧ B ⊆ A ∧ B.card + 1 = A.card) → s.card ≤ 3) :
    LinearMap.ker ((S.dualMedianGraph hred x₀ hdim).toDescCubeStr).d₂ =
      LinearMap.range ((S.dualMedianGraph hred x₀ hdim).toDescCubeStr).d₃ :=
  (S.gatedDualModel hred x₀ hdim).ker_d₂_eq_range_d₃

end Coordinates

end WallSpace

end FiniteChains
