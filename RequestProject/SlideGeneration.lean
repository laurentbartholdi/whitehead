module

public import RequestProject.CoverChainComplex
public import RequestProject.PresentationDictionary
public import RequestProject.ExponentCorrection
public import RequestProject.Cockcroft

@[expose] public section

/-!
# Rule 2 of Section 3.4 does not change `π₂`

Rule 2 of the operation `T` replaces an extra relator `r*` by

  `r⁰ = r* ∏_j r_j^{c_j}`,

a product of `r*` with core relators (`RequestProject/ExponentCorrection.lean` produces the
exponents `c`).  The paper justifies the generation property for this rule by

> Rule 2 is a finite sequence of slides of each extra relator disk over retained core disks.
> The inverse slides undo it.  It is a homotopy equivalence relative to `D`.

This file proves the corresponding statement in the combinatorial model.  The slide does not
change the normal closure of the relators (`FiniteChains.relSub_slideRel`), so both
presentations have the same fundamental group, and their second homotopy groups are the
modules of two-cycles of the same complex of `RequestProject/CoverChainComplex.lean`, taken
over `N = ⟪relators⟫`.  In that vocabulary the slide multiplies the Fox matrix by an
invertible unitriangular matrix:

* `FiniteChains.foxVec_mem_range_bdry2` — the Fox vector of an element of the normal closure
  of a family of words is a `ℤ[Q]`-combination of the Fox vectors of that family;
* `FiniteChains.exists_slideCoeff` — hence the coefficient vector `λ` of the slide exists,
  with `λ` vanishing at the slid index;
* `FiniteChains.bdry2_slideRel` — the boundary of the slid presentation expressed through the
  old one;
* `FiniteChains.slideCycle_image` and `FiniteChains.slideCycle_image_isCycle` — **rule 2 has
  the generation property**: the two-cycles of the slid presentation are exactly the images
  of the two-cycles of the old one under the `ℤ[Q]`-linear isomorphism `y ↦ y - y_{j₀} λ`;
* `FiniteChains.slide_cockcroft` — consequently rule 2 preserves the Cockcroft property.
-/

namespace FiniteChains

open MonoidAlgebra

variable {α : Type*} [Fintype α] [DecidableEq α]
variable (Nsub : Subgroup (FreeGroup α)) [Nsub.Normal]

omit [Fintype α] in
/-- **The Fox vector of an element of a normal closure is a combination of the Fox vectors of
the generating words.**  These are the coefficients `λ` used by the slide; the proof is the
standard argument that the words with this property form a normal subgroup. -/
theorem foxVec_mem_range_bdry2 {Jσ : Type*} [Fintype Jσ] (σ : Jσ → FreeGroup α)
    (hσ : ∀ j, σ j ∈ Nsub) {w : FreeGroup α}
    (hw : w ∈ Subgroup.normalClosure (Set.range σ)) :
    ∃ y : Jσ → CoverRing Nsub, bdry2 Nsub σ y = foxVec Nsub w := by
  classical
  let T : Subgroup (FreeGroup α) :=
    { carrier := {v | v ∈ Nsub ∧ ∃ y : Jσ → CoverRing Nsub, bdry2 Nsub σ y = foxVec Nsub v}
      one_mem' := ⟨Subgroup.one_mem _, 0, by rw [bdry2_zero, foxVec_one]⟩
      mul_mem' := by
        rintro v w ⟨hv, y₁, hy₁⟩ ⟨hw, y₂, hy₂⟩
        exact ⟨Subgroup.mul_mem _ hv hw, y₁ + y₂, by
          rw [bdry2_add, hy₁, hy₂, foxVec_mul hv]⟩
      inv_mem' := by
        rintro w ⟨hw, y, hy⟩
        exact ⟨Subgroup.inv_mem _ hw, -y, by rw [bdry2_neg, hy, foxVec_inv hw]⟩ }
  have hTnormal : T.Normal := by
    constructor
    rintro w ⟨hw, y, hy⟩ f
    refine ⟨Subgroup.Normal.conj_mem ‹Nsub.Normal› w hw f, fun j => proj Nsub (grp f) * y j, ?_⟩
    rw [bdry2_smul, hy, foxVec_conj hw]
  have hrange : Set.range σ ⊆ (T : Set (FreeGroup α)) := by
    rintro _ ⟨j, rfl⟩
    refine ⟨hσ j, fun k => if k = j then 1 else 0, ?_⟩
    funext i
    simp [bdry2, foxVec]
  exact (Subgroup.normalClosure_le_normal hrange hw).2

section Slide

variable {J : Type*} [Fintype J] [DecidableEq J] (ρ : J → FreeGroup α) (j₀ : J)
  (u : FreeGroup α)

/-- **The slide**: the relator with index `j₀` is multiplied by a word `u` in the retained
core relators. -/
def slideRel : J → FreeGroup α := Function.update ρ j₀ (ρ j₀ * u)

omit [Fintype α] [DecidableEq α] [Fintype J] in
@[simp] theorem slideRel_self : slideRel ρ j₀ u j₀ = ρ j₀ * u := by
  simp [slideRel]

omit [Fintype α] [DecidableEq α] [Fintype J] in
@[simp] theorem slideRel_of_ne {j : J} (h : j ≠ j₀) : slideRel ρ j₀ u j = ρ j := by
  simp [slideRel, h]

/-- The words available for the correction: the relators other than the one being slid. -/
abbrev coreRel : {j : J // j ≠ j₀} → FreeGroup α := fun j => ρ j

omit [Fintype α] [DecidableEq α] [Fintype J] in
/-- **The slide does not change the presented group**: the normal closure of the relators is
unchanged, so rule 2 is a Tietze transformation. -/
theorem relSub_slideRel (hu : u ∈ Subgroup.normalClosure (Set.range (coreRel ρ j₀))) :
    relSub (slideRel ρ j₀ u) = relSub ρ := by
  have hcore : Subgroup.normalClosure (Set.range (coreRel ρ j₀)) ≤ relSub ρ := by
    refine Subgroup.normalClosure_le_normal ?_
    rintro _ ⟨j, rfl⟩
    exact Subgroup.subset_normalClosure ⟨(j : J), rfl⟩
  have hcore' : Subgroup.normalClosure (Set.range (coreRel ρ j₀)) ≤ relSub (slideRel ρ j₀ u) := by
    refine Subgroup.normalClosure_le_normal ?_
    rintro _ ⟨j, rfl⟩
    exact Subgroup.subset_normalClosure ⟨(j : J), slideRel_of_ne ρ j₀ u j.2⟩
  refine le_antisymm ?_ ?_
  · refine Subgroup.normalClosure_le_normal ?_
    rintro _ ⟨j, rfl⟩
    by_cases h : j = j₀
    · subst h
      rw [slideRel_self]
      exact Subgroup.mul_mem _ (Subgroup.subset_normalClosure ⟨j, rfl⟩) (hcore hu)
    · rw [slideRel_of_ne ρ j₀ u h]
      exact Subgroup.subset_normalClosure ⟨j, rfl⟩
  · refine Subgroup.normalClosure_le_normal ?_
    rintro _ ⟨j, rfl⟩
    by_cases h : j = j₀
    · subst h
      have hj : ρ j = (slideRel ρ j u j) * u⁻¹ := by
        rw [slideRel_self, mul_assoc, mul_inv_cancel, mul_one]
      rw [hj]
      exact Subgroup.mul_mem _ (Subgroup.subset_normalClosure ⟨j, rfl⟩)
        (Subgroup.inv_mem _ (hcore' hu))
    · rw [← slideRel_of_ne ρ j₀ u h]
      exact Subgroup.subset_normalClosure ⟨j, rfl⟩

omit [Fintype α] in
/-- **The coefficients of the slide exist.**  The Fox vector of the correcting word is a
`ℤ[Q]`-combination of the Fox vectors of the other relators; the coefficient at the slid
index is taken to be `0`. -/
theorem exists_slideCoeff (hρ : ∀ j, ρ j ∈ Nsub)
    (hu : u ∈ Subgroup.normalClosure (Set.range (coreRel ρ j₀))) :
    ∃ lam : J → CoverRing Nsub, lam j₀ = 0 ∧ bdry2 Nsub ρ lam = foxVec Nsub u := by
  classical
  obtain ⟨c, hc⟩ := foxVec_mem_range_bdry2 Nsub (coreRel ρ j₀) (fun k => hρ (k : J)) hu
  refine ⟨fun j => if h : j = j₀ then 0 else c ⟨j, h⟩, by simp, ?_⟩
  rw [← hc, bdry2_apply_eq, bdry2_apply_eq]
  have hval : ∀ x : {j : J // j ≠ j₀}, c x • foxVec Nsub (coreRel ρ j₀ x)
      = (fun j : J => (if h : j = j₀ then 0 else c ⟨j, h⟩) • foxVec Nsub (ρ j)) (x : J) := by
    rintro ⟨j, hj⟩
    simp [hj]
  rw [Finset.sum_congr rfl fun x _ => hval x,
    ← Finset.sum_subtype (s := (Finset.univ.filter (fun j : J => j ≠ j₀)))
      (p := fun j : J => j ≠ j₀) (by intro x; simp)
      (fun j : J => (if h : j = j₀ then 0 else c ⟨j, h⟩) • foxVec Nsub (ρ j))]
  refine (Finset.sum_subset (Finset.subset_univ _) ?_).symm
  intro x _ hx
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_not] at hx
  simp [hx]

variable {ρ j₀ u}

omit [Fintype α] in
/-- **The boundary after the slide.**  The column of the slid relator acquires the
combination `λ` of the other columns; the remaining columns are unchanged. -/
theorem bdry2_slideRel (hρ : ∀ j, ρ j ∈ Nsub) {lam : J → CoverRing Nsub}
    (hlam : bdry2 Nsub ρ lam = foxVec Nsub u) (v : J → CoverRing Nsub) :
    bdry2 Nsub (slideRel ρ j₀ u) v = bdry2 Nsub ρ (fun j => v j + v j₀ * lam j) := by
  classical
  have hcol : ∀ j : J, foxVec Nsub (slideRel ρ j₀ u j)
      = if j = j₀ then foxVec Nsub (ρ j₀) + foxVec Nsub u else foxVec Nsub (ρ j) := by
    intro j
    by_cases h : j = j₀
    · subst h
      rw [slideRel_self, if_pos rfl, foxVec_mul (hρ j)]
    · rw [slideRel_of_ne ρ j₀ u h, if_neg h]
  rw [bdry2_apply_eq, bdry2_apply_eq]
  have hleft : ∑ j : J, v j • foxVec Nsub (slideRel ρ j₀ u j)
      = (∑ j : J, v j • foxVec Nsub (ρ j)) + v j₀ • foxVec Nsub u := by
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ j₀),
      ← Finset.sum_erase_add (Finset.univ : Finset J) (fun j => v j • foxVec Nsub (ρ j))
        (Finset.mem_univ j₀)]
    have hsame : ∀ j ∈ (Finset.univ : Finset J).erase j₀,
        v j • foxVec Nsub (slideRel ρ j₀ u j) = v j • foxVec Nsub (ρ j) := by
      intro j hj
      rw [hcol j, if_neg (Finset.ne_of_mem_erase hj)]
    rw [Finset.sum_congr rfl hsame, hcol j₀, if_pos rfl, smul_add, add_assoc]
  have hlam' : ∑ j : J, lam j • foxVec Nsub (ρ j) = foxVec Nsub u := by
    rw [← bdry2_apply_eq]; exact hlam
  have hright : ∑ j : J, (v j + v j₀ * lam j) • foxVec Nsub (ρ j)
      = (∑ j : J, v j • foxVec Nsub (ρ j)) + v j₀ • foxVec Nsub u := by
    have hterm : ∀ j : J, (v j + v j₀ * lam j) • foxVec Nsub (ρ j)
        = v j • foxVec Nsub (ρ j) + v j₀ • (lam j • foxVec Nsub (ρ j)) := by
      intro j
      rw [add_smul, smul_smul]
    rw [Finset.sum_congr rfl fun j _ => hterm j, Finset.sum_add_distrib, ← Finset.smul_sum, hlam']
  rw [hleft, hright]

omit [Fintype α] in
/-- **Rule 2 has the generation property**: every two-cycle of the slid presentation is the
image of a two-cycle of the old one under the `ℤ[Q]`-linear isomorphism
`y ↦ (j ↦ y j - y_{j₀} λ j)`.  In particular `π₂` after the slide is generated by the image
of `π₂` before it, which is (3.3) for rule 2. -/
theorem slideCycle_image (hρ : ∀ j, ρ j ∈ Nsub) {lam : J → CoverRing Nsub} (hlam0 : lam j₀ = 0)
    (hlam : bdry2 Nsub ρ lam = foxVec Nsub u)
    {v : J → CoverRing Nsub} (hv : bdry2 Nsub (slideRel ρ j₀ u) v = 0) :
    ∃ y : J → CoverRing Nsub, bdry2 Nsub ρ y = 0 ∧ v = fun j => y j - y j₀ * lam j := by
  refine ⟨fun j => v j + v j₀ * lam j, ?_, ?_⟩
  · rw [← bdry2_slideRel Nsub hρ hlam v, hv]
  · funext j
    show v j = (v j + v j₀ * lam j) - (v j₀ + v j₀ * lam j₀) * lam j
    rw [hlam0, mul_zero, add_zero]
    abel

omit [Fintype α] in
/-- The converse: the image of a two-cycle is a two-cycle, so the correspondence of
`FiniteChains.slideCycle_image` is a bijection between the two second homotopy groups. -/
theorem slideCycle_image_isCycle (hρ : ∀ j, ρ j ∈ Nsub) {lam : J → CoverRing Nsub}
    (hlam0 : lam j₀ = 0) (hlam : bdry2 Nsub ρ lam = foxVec Nsub u)
    {y : J → CoverRing Nsub} (hy : bdry2 Nsub ρ y = 0) :
    bdry2 Nsub (slideRel ρ j₀ u) (fun j => y j - y j₀ * lam j) = 0 := by
  rw [bdry2_slideRel Nsub hρ hlam]
  have hcancel : (fun j => (y j - y j₀ * lam j) + (y j₀ - y j₀ * lam j₀) * lam j) = y := by
    funext j
    rw [hlam0, mul_zero, sub_zero]
    abel
  rw [hcancel, hy]

omit [Fintype α] in
/-- **Rule 2 preserves the Cockcroft property.**  The augmentation of the image of a
two-cycle is the corresponding integer combination of the augmentations of its coordinates,
hence zero. -/
theorem slide_cockcroft (hρ : ∀ j, ρ j ∈ Nsub) {lam : J → CoverRing Nsub} (hlam0 : lam j₀ = 0)
    (hlam : bdry2 Nsub ρ lam = foxVec Nsub u)
    (hcock : ∀ y : J → CoverRing Nsub, bdry2 Nsub ρ y = 0 → ∀ j, augQ Nsub (y j) = 0)
    {v : J → CoverRing Nsub} (hv : bdry2 Nsub (slideRel ρ j₀ u) v = 0) (j : J) :
    augQ Nsub (v j) = 0 := by
  obtain ⟨y, hy, rfl⟩ := slideCycle_image Nsub hρ hlam0 hlam hv
  rw [map_sub, map_mul, hcock y hy j, hcock y hy j₀, zero_mul, sub_zero]

end Slide

/-! ### In the vocabulary of the presentation complex

For `N = ⟪r_1, …, r_m⟫` the complex used above is the cellular chain complex of the
universal cover, so its two-cycles are the Fox cycles of `RequestProject/Cockcroft.lean` and
its augmentation is the Hurewicz map.  In these terms rule 2 preserves the Cockcroft
property. -/

section Presentation

variable {J : Type*} [Fintype J] [DecidableEq J] (ρ : J → FreeGroup α) (j₀ : J)
  (u : FreeGroup α)

omit [Fintype α] [DecidableEq α] [Fintype J] [DecidableEq J] in
theorem rel_mem_relSub (j : J) : ρ j ∈ relSub ρ :=
  Subgroup.subset_normalClosure ⟨j, rfl⟩

omit [Fintype α] [DecidableEq J] in
/-- The two-cycles of the chain complex of the universal cover are the Fox cycles. -/
theorem isFoxCycle_iff_bdry2_relSub (v : J → MonoidAlgebra ℤ (PresGroup ρ)) :
    IsFoxCycle ρ v ↔ bdry2 (relSub ρ) ρ v = 0 :=
  ⟨fun h => funext fun i => h i, fun h i => congrFun h i⟩

omit [Fintype α] in
/-- **Rule 2 preserves the Cockcroft property**, stated for the presentation complex: a Fox
cycle of the slid presentation, read in the group ring of the (unchanged) fundamental group,
has zero augmentation in every coordinate. -/
theorem slide_isCockcroft (hu : u ∈ Subgroup.normalClosure (Set.range (coreRel ρ j₀)))
    (hcock : IsCockcroft ρ) {v : J → MonoidAlgebra ℤ (PresGroup ρ)}
    (hv : bdry2 (relSub ρ) (slideRel ρ j₀ u) v = 0) (j : J) : augPres ρ (v j) = 0 := by
  obtain ⟨lam, hlam0, hlam⟩ := exists_slideCoeff (relSub ρ) ρ j₀ u (rel_mem_relSub ρ) hu
  refine slide_cockcroft (relSub ρ) (rel_mem_relSub ρ) hlam0 hlam ?_ hv j
  intro y hy
  exact hcock y ((isFoxCycle_iff_bdry2_relSub ρ y).2 hy)

end Presentation

end FiniteChains
