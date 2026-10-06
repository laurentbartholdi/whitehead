module

public import RequestProject.CellComplex
public import RequestProject.CoverAcyclic

@[expose] public section

/-!
# The presentation complex, its covers, and the dictionary with the Fox complex

For a finite presentation `⟨x_1, …, x_n | r_1, …, r_m⟩` this file builds, inside the
combinatorial world of `RequestProject/CellComplex.lean`:

* `FiniteChains.Comb.presComplex ρ` — the presentation complex `K`: one vertex, one edge
  per generator, one two-cell per relator, attached along the relator word;
* `FiniteChains.Comb.coverComplex ρ Nsub` — for a normal subgroup `Ñ ◁ F` containing the
  relators, the cover `K_N` with deck group `Q = F/Ñ`: vertices `Q`, edges `Q × {x_i}`,
  two-cells `Q × {r_j}` attached along the lift of the relator word;
* `FiniteChains.Comb.coverProj` — the covering map `K_N → K`, which is proved to be a
  combinatorial covering (`coverProj_isCovering`), regular with deck group `Q`
  (`coverProj_isRegular`), with `K_N` connected (`coverComplex_isConnected`).

The **dictionary between topology and algebra** is the content of
`FiniteChains.Comb.coords_pathChain_liftPath`: in the coordinates
`ℤ[cells of K_N] ≅ ℤ[Q]^{cells of K}`, the cellular chain carried by the lift at `q` of a
word `w` is `q · (∂w/∂x_i)_i`, the Fox vector of `w`.  Consequently the cellular chain
complex of `K_N` *is* the Fox complex of `RequestProject/CoverChainComplex.lean`
(`coverComplex_bdry1`, `coverComplex_bdry2`, `coverComplex_augC`), and the algebraic
acyclicity proved there becomes acyclicity of the cover as a two-complex
(`coverComplex_isAcyclic`).

The final statement, `FiniteChains.Comb.presComplex_hasAcyclicRegularCover`, is exactly the
topological input `cover` of Section 2, now a theorem: a perfect normal subgroup satisfying
the requirements (2.2) produces a connected acyclic regular cover of the presentation
complex.
-/

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains
namespace Comb

open MonoidAlgebra

universe u

variable {α : Type u} [Fintype α] [DecidableEq α]
variable {J : Type u} [Fintype J] [DecidableEq J]

/-! ### Paths in a complex with one vertex -/

theorem isPath_of_subsingleton {V E : Type*} [Subsingleton V] (src tgt : E → V)
    (p : List (E × Bool)) (a b : V) : IsPath src tgt p a b := by
  induction p generalizing a with
  | nil => exact Subsingleton.elim _ _
  | cons e p ih => exact ⟨Subsingleton.elim _ _, ih _⟩

/-! ### The presentation complex -/

/-- The two-complex of the presentation `⟨x_i | r_j⟩`: one vertex, an edge for every
generator and a two-cell for every relator, attached along the relator word. -/
abbrev presComplex (ρ : J → FreeGroup α) : Complex2.{u} where
  V := PUnit.{u + 1}
  E := α
  F := J
  src _ := PUnit.unit
  tgt _ := PUnit.unit
  base _ := PUnit.unit
  att j := FreeGroup.toWord (ρ j)
  att_isLoop _ := isPath_of_subsingleton _ _ _ _ _

/-! ### The cover attached to a normal subgroup of the free group -/

variable (Nsub : Subgroup (FreeGroup α)) [Nsub.Normal]

/-- The image of a generator in the deck group `Q = F/Ñ`. -/
def qof (i : α) : FreeGroup α ⧸ Nsub := QuotientGroup.mk (FreeGroup.of i)

variable {Nsub}

/-- The lift at the vertex `q` of the edge path spelled by a word. -/
def liftPath : List (α × Bool) → (FreeGroup α ⧸ Nsub) →
    List (((FreeGroup α ⧸ Nsub) × α) × Bool)
  | [], _ => []
  | (i, true) :: L, q => ((q, i), true) :: liftPath L (q * qof Nsub i)
  | (i, false) :: L, q => ((q * (qof Nsub i)⁻¹, i), false) :: liftPath L (q * (qof Nsub i)⁻¹)

omit [Fintype α] [DecidableEq α] in
@[simp] theorem liftPath_nil (q : FreeGroup α ⧸ Nsub) : liftPath [] q = [] := rfl

omit [Fintype α] [DecidableEq α] in
@[simp] theorem liftPath_cons_true (i : α) (L : List (α × Bool)) (q : FreeGroup α ⧸ Nsub) :
    liftPath ((i, true) :: L) q = ((q, i), true) :: liftPath L (q * qof Nsub i) := rfl

omit [Fintype α] [DecidableEq α] in
@[simp] theorem liftPath_cons_false (i : α) (L : List (α × Bool)) (q : FreeGroup α ⧸ Nsub) :
    liftPath ((i, false) :: L) q
      = ((q * (qof Nsub i)⁻¹, i), false) :: liftPath L (q * (qof Nsub i)⁻¹) := rfl

omit [Fintype α] in
theorem mk_cons_true (i : α) (L : List (α × Bool)) :
    FreeGroup.mk ((i, true) :: L) = FreeGroup.of i * FreeGroup.mk L :=
  FreeGroup.toWord_inj.mp rfl

omit [Fintype α] in
theorem mk_cons_false (i : α) (L : List (α × Bool)) :
    FreeGroup.mk ((i, false) :: L) = (FreeGroup.of i)⁻¹ * FreeGroup.mk L :=
  FreeGroup.toWord_inj.mp rfl

omit [Fintype α] [DecidableEq α] in
/-- The projection of the lift of a word is the word itself. -/
theorem map_liftPath (L : List (α × Bool)) (q : FreeGroup α ⧸ Nsub) :
    (liftPath L q).map (fun eb => (eb.1.2, eb.2)) = L := by
  induction L generalizing q with
  | nil => rfl
  | cons a L ih =>
      obtain ⟨i, b⟩ := a
      cases b
      · simpa using ih (q * (qof Nsub i)⁻¹)
      · simpa using ih (q * qof Nsub i)

omit [Fintype α] [DecidableEq α] in
/-- The lift of a word is equivariant for left translation. -/
theorem liftPath_translate (L : List (α × Bool)) (q₀ q : FreeGroup α ⧸ Nsub) :
    liftPath L (q₀ * q) = (liftPath L q).map (fun eb => ((q₀ * eb.1.1, eb.1.2), eb.2)) := by
  induction L generalizing q with
  | nil => rfl
  | cons a L ih =>
      obtain ⟨i, b⟩ := a
      cases b
      · simpa [mul_assoc] using ih (q * (qof Nsub i)⁻¹)
      · simpa [mul_assoc] using ih (q * qof Nsub i)

variable (Nsub)

omit [Fintype α] in
/-- The lift at `q` of the word `w` is an edge path from `q` to `q · w`. -/
theorem liftPath_isPath (L : List (α × Bool)) (q : FreeGroup α ⧸ Nsub) :
    IsPath (fun e : (FreeGroup α ⧸ Nsub) × α => e.1)
      (fun e : (FreeGroup α ⧸ Nsub) × α => e.1 * qof Nsub e.2) (liftPath L q) q
      (q * QuotientGroup.mk (FreeGroup.mk L)) := by
  induction L generalizing q with
  | nil =>
      show q = q * QuotientGroup.mk (FreeGroup.mk ([] : List (α × Bool)))
      rw [show FreeGroup.mk ([] : List (α × Bool)) = 1 from rfl]
      simp
  | cons a L ih =>
      obtain ⟨i, b⟩ := a
      cases b
      · have hmk : (QuotientGroup.mk (FreeGroup.mk ((i, false) :: L)) : FreeGroup α ⧸ Nsub)
            = (qof Nsub i)⁻¹ * QuotientGroup.mk (FreeGroup.mk L) := by
          rw [mk_cons_false, QuotientGroup.mk_mul, QuotientGroup.mk_inv]
          rfl
        refine ⟨?_, ?_⟩
        · show q = (q * (qof Nsub i)⁻¹) * qof Nsub i
          group
        · have h := ih (q * (qof Nsub i)⁻¹)
          rw [hmk, ← mul_assoc]
          exact h
      · have hmk : (QuotientGroup.mk (FreeGroup.mk ((i, true) :: L)) : FreeGroup α ⧸ Nsub)
            = qof Nsub i * QuotientGroup.mk (FreeGroup.mk L) := by
          rw [mk_cons_true, QuotientGroup.mk_mul]
          rfl
        refine ⟨rfl, ?_⟩
        have h := ih (q * qof Nsub i)
        rw [hmk, ← mul_assoc]
        exact h

variable (ρ : J → FreeGroup α)

/-- The cover `K_N` of the presentation complex attached to `Ñ ◁ F`: vertices the deck
group `Q = F/Ñ`, one edge `(q, x_i)` from `q` to `q x_i` for every `q` and every generator,
one two-cell `(q, r_j)` attached along the lift at `q` of the relator `r_j`. -/
abbrev coverComplex (hρ : ∀ j, ρ j ∈ Nsub) : Complex2.{u} where
  V := FreeGroup α ⧸ Nsub
  E := (FreeGroup α ⧸ Nsub) × α
  F := (FreeGroup α ⧸ Nsub) × J
  src e := e.1
  tgt e := e.1 * qof Nsub e.2
  base f := f.1
  att f := liftPath (FreeGroup.toWord (ρ f.2)) f.1
  att_isLoop f := by
    have h := liftPath_isPath Nsub (FreeGroup.toWord (ρ f.2)) f.1
    rw [FreeGroup.mk_toWord] at h
    rwa [(QuotientGroup.eq_one_iff (ρ f.2)).2 (hρ f.2), mul_one] at h

variable {Nsub ρ}

/-! ### Coordinates: the cellular chains of the cover as free `ℤ[Q]`-modules -/

variable (Nsub)

/-- The cellular chains on the cells `Q × β` of the cover, read as the free `ℤ[Q]`-module
on `β`. -/
noncomputable def coords (β : Type u) [Fintype β] [DecidableEq β] :
    (((FreeGroup α ⧸ Nsub) × β) →₀ ℤ) ≃ₗ[ℤ] (β → CoverRing Nsub) :=
  (Finsupp.domLCongr (Equiv.prodComm (FreeGroup α ⧸ Nsub) β)).trans
    ((Finsupp.curryLinearEquiv (R := ℤ)).trans
      ((Finsupp.linearEquivFunOnFinite ℤ ((FreeGroup α ⧸ Nsub) →₀ ℤ) β).trans
        (LinearEquiv.piCongrRight (fun _ => (MonoidAlgebra.coeffLinearEquiv ℤ).symm))))

variable {Nsub}

omit [Fintype α] [DecidableEq α] [Nsub.Normal] in
/-- The coordinates of a cellular chain: the coefficient of the cell `(q, i)`. -/
theorem coords_apply (β : Type u) [Fintype β] [DecidableEq β]
    (c : ((FreeGroup α ⧸ Nsub) × β) →₀ ℤ) (i : β) (q : FreeGroup α ⧸ Nsub) :
    ((coords Nsub β c) i).coeff q = c (q, i) := by
  show ((Finsupp.equivMapDomain (Equiv.prodComm _ β) c).curry i) q = c (q, i)
  rw [Finsupp.curry_apply, Finsupp.equivMapDomain_apply]
  rfl

omit [Fintype α] [DecidableEq α] in
theorem coords_single (β : Type u) [Fintype β] [DecidableEq β] (q : FreeGroup α ⧸ Nsub)
    (i : β) (n : ℤ) :
    coords Nsub β (Finsupp.single (q, i) n) = Pi.single i (MonoidAlgebra.single q n) := by
  classical
  funext k
  apply MonoidAlgebra.coeff_injective
  refine Finsupp.ext fun q' => ?_
  rw [coords_apply, Finsupp.single_apply]
  by_cases h : k = i
  · subst h
    rw [Pi.single_eq_same, MonoidAlgebra.coeff_single, Finsupp.single_apply]
    by_cases hq : q = q'
    · simp [hq]
    · simp [hq]
  · rw [Pi.single_eq_of_ne h]
    simp [Ne.symm h]

/-- **The dictionary between the cellular boundary and the Fox derivative.**  In the
coordinates above, the cellular chain carried by the lift at `q` of the word `w` is the
Fox vector `q · (∂w/∂x_i)_i`. -/
theorem coords_pathChain_liftPath (L : List (α × Bool)) (q : FreeGroup α ⧸ Nsub) :
    coords Nsub α (pathChain (liftPath L q))
      = fun i => (MonoidAlgebra.single q (1 : ℤ) : CoverRing Nsub) *
          proj Nsub (fox i (FreeGroup.mk L)) := by
  classical
  induction L generalizing q with
  | nil =>
      funext i
      rw [show FreeGroup.mk ([] : List (α × Bool)) = 1 from rfl]
      simp
  | cons a L ih =>
      obtain ⟨i₀, b⟩ := a
      cases b
      · -- the letter `x_{i₀}⁻¹`
        have hq : (MonoidAlgebra.single (q * (qof Nsub i₀)⁻¹) (1 : ℤ) : CoverRing Nsub)
            = (MonoidAlgebra.single q (1 : ℤ) : CoverRing Nsub) *
              proj Nsub (grp (FreeGroup.of i₀)⁻¹) := by
          rw [proj_grp, qgrp, QuotientGroup.mk_inv, MonoidAlgebra.single_mul_single, mul_one]
          rfl
        rw [liftPath_cons_false, pathChain_cons]
        simp only [Bool.false_eq_true, if_false, map_add, map_neg]
        rw [ih (q * (qof Nsub i₀)⁻¹)]
        funext i
        rw [Pi.add_apply, Pi.neg_apply, coords_single, mk_cons_false, fox_mul, fox_inv,
          map_add, map_neg, map_mul, map_mul, mul_add, mul_neg, ← mul_assoc, ← mul_assoc, ← hq]
        congr 1
        by_cases h : i = i₀
        · subst h
          rw [Pi.single_eq_same, fox_of, if_pos rfl, map_one, mul_one]
        · rw [Pi.single_eq_of_ne h, fox_of, if_neg h, map_zero, mul_zero, neg_zero]
      · -- the letter `x_{i₀}`
        have hq : (MonoidAlgebra.single (q * qof Nsub i₀) (1 : ℤ) : CoverRing Nsub)
            = (MonoidAlgebra.single q (1 : ℤ) : CoverRing Nsub) *
              proj Nsub (grp (FreeGroup.of i₀)) := by
          rw [proj_grp, qgrp, MonoidAlgebra.single_mul_single, mul_one]
          rfl
        rw [liftPath_cons_true, pathChain_cons]
        simp only [if_true, map_add]
        rw [ih (q * qof Nsub i₀)]
        funext i
        rw [Pi.add_apply, coords_single, mk_cons_true, fox_mul, map_add, map_mul, mul_add,
          ← mul_assoc, ← hq]
        congr 1
        by_cases h : i = i₀
        · subst h
          rw [Pi.single_eq_same, fox_of, if_pos rfl, map_one, mul_one]
        · rw [Pi.single_eq_of_ne h, fox_of, if_neg h, map_zero, mul_zero]

/-! ### The cellular chain complex of the cover is the Fox complex -/

variable (hρ : ∀ j, ρ j ∈ Nsub)

omit [Fintype J] [DecidableEq J] in
include hρ in
/-- `∂₁` of the cover complex is the Fox boundary `∂₁(e_i) = x_i - 1`. -/
theorem coverComplex_bdry1 (c : ((FreeGroup α ⧸ Nsub) × α) →₀ ℤ) :
    _root_.FiniteChains.bdry1 Nsub (coords Nsub α c) = MonoidAlgebra.ofCoeff (Comb.bdry1 (coverComplex Nsub ρ hρ) c) := by
  classical
  induction c using Finsupp.induction_linear with
  | zero => simp [_root_.FiniteChains.bdry1]
  | add c₁ c₂ h₁ h₂ =>
      rw [map_add, _root_.FiniteChains.bdry1_add, h₁, h₂, map_add, MonoidAlgebra.ofCoeff_add]
  | single e n =>
      obtain ⟨q, i⟩ := e
      rw [coords_single, bdry1_single]
      show ∑ i' : α, (Pi.single i (MonoidAlgebra.single q n) : α → CoverRing Nsub) i' *
          (qgrp Nsub (FreeGroup.of i') - 1)
        = n • (MonoidAlgebra.single (q * qof Nsub i) (1 : ℤ) - MonoidAlgebra.single q (1 : ℤ))
      rw [Finset.sum_eq_single i (fun i' _ h => by simp [Pi.single_eq_of_ne h])
        (fun h => absurd (Finset.mem_univ i) h)]
      simp only [Pi.single_eq_same, qgrp, mul_sub, mul_one, MonoidAlgebra.single_mul_single]
      simp [qof, smul_sub, MonoidAlgebra.smul_single]

include hρ in
/-- `∂₂` of the cover complex is the Fox boundary `∂₂(e_j) = (∂r_j/∂x_i)_i`. -/
theorem coverComplex_bdry2 (u : ((FreeGroup α ⧸ Nsub) × J) →₀ ℤ) :
    _root_.FiniteChains.bdry2 Nsub ρ (coords Nsub J u)
      = coords Nsub α (Comb.bdry2 (coverComplex Nsub ρ hρ) u) := by
  classical
  induction u using Finsupp.induction_linear with
  | zero => rw [map_zero, _root_.FiniteChains.bdry2_zero, map_zero, map_zero]
  | add u₁ u₂ h₁ h₂ =>
      rw [map_add, _root_.FiniteChains.bdry2_add, h₁, h₂, map_add, ← map_add]
  | single f n =>
      obtain ⟨q, j⟩ := f
      rw [coords_single, bdry2_single, map_smul, coords_pathChain_liftPath, FreeGroup.mk_toWord]
      funext i
      show ∑ j' : J, (Pi.single j (MonoidAlgebra.single q n) : J → CoverRing Nsub) j' *
          proj Nsub (fox i (ρ j')) = _
      rw [Finset.sum_eq_single j (fun j' _ h => by simp [Pi.single_eq_of_ne h])
        (fun h => absurd (Finset.mem_univ j) h)]
      simp only [Pi.single_eq_same, Pi.smul_apply]
      rw [show (MonoidAlgebra.single q n : CoverRing Nsub)
          = n • (MonoidAlgebra.single q (1 : ℤ) : CoverRing Nsub) by
        rw [MonoidAlgebra.smul_single, smul_eq_mul, mul_one], smul_mul_assoc]

omit [Fintype α] [Fintype J] [DecidableEq J] in
include hρ in
/-- The augmentation of the cover complex is the augmentation of `ℤ[Q]`. -/
theorem coverComplex_augC (c : (FreeGroup α ⧸ Nsub) →₀ ℤ) :
    Comb.augC (coverComplex Nsub ρ hρ) c = augQ Nsub (MonoidAlgebra.ofCoeff c) := by
  classical
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c₁ c₂ h₁ h₂ => rw [map_add, MonoidAlgebra.ofCoeff_add, map_add, h₁, h₂]
  | single q n =>
      rw [MonoidAlgebra.ofCoeff_single, augQ_single]
      exact augC_single (X := coverComplex Nsub ρ hρ) q n

/-! ### Acyclicity of the cover -/

include hρ in
/-- **The cover is acyclic** as soon as the Fox complex is: this is the algebraic
acyclicity of `RequestProject/CoverChainComplex.lean` read through the dictionary. -/
theorem coverComplex_isAcyclic
    (hperf : Nsub ≤ Subgroup.normalClosure (Set.range ρ) ⊔ ⁅Nsub, Nsub⁆)
    (hinj : ∀ u : J → CoverRing Nsub, _root_.FiniteChains.bdry2 Nsub ρ u = 0 → u = 0) :
    IsAcyclic (coverComplex Nsub ρ hρ) := by
  obtain ⟨-, h2, h1, h0, -⟩ := cover_acyclic Nsub ρ hρ hperf hinj
  refine ⟨?_, ?_, ?_⟩
  · intro u₁ u₂ h
    have h' : _root_.FiniteChains.bdry2 Nsub ρ (coords Nsub J u₁)
        = _root_.FiniteChains.bdry2 Nsub ρ (coords Nsub J u₂) := by
      rw [coverComplex_bdry2 hρ, coverComplex_bdry2 hρ, h]
    have hzero : _root_.FiniteChains.bdry2 Nsub ρ
        (coords Nsub J u₁ + (- coords Nsub J u₂)) = 0 := by
      rw [_root_.FiniteChains.bdry2_add, _root_.FiniteChains.bdry2_neg, h', add_neg_cancel]
    have hsub := h2 _ hzero
    have hcoords : coords Nsub J u₁ = coords Nsub J u₂ := by
      have := add_eq_zero_iff_eq_neg.mp hsub
      rw [this, neg_neg]
    exact (coords Nsub J).injective hcoords
  · intro c hc
    have hc' : _root_.FiniteChains.bdry1 Nsub (coords Nsub α c) = 0 := by
      rw [coverComplex_bdry1 hρ, hc, MonoidAlgebra.ofCoeff_zero]
    obtain ⟨u, hu⟩ := h1 _ hc'
    refine ⟨(coords Nsub J).symm u, ?_⟩
    apply (coords Nsub α).injective
    rw [← coverComplex_bdry2 hρ, LinearEquiv.apply_symm_apply, hu]
  · intro c hc
    have hc' : augQ Nsub (MonoidAlgebra.ofCoeff c) = 0 := by rw [← coverComplex_augC hρ c, hc]
    obtain ⟨d, hd⟩ := h0 _ hc'
    refine ⟨(coords Nsub α).symm d, ?_⟩
    apply MonoidAlgebra.ofCoeff_injective
    rw [← coverComplex_bdry1 hρ, LinearEquiv.apply_symm_apply, hd]

/-! ### The cover is connected -/

omit [Fintype α] [Fintype J] [DecidableEq J] in
include hρ in
/-- The cover is path connected: any two vertices are joined by an edge path. -/
theorem coverComplex_isConnected : IsConnected (coverComplex Nsub ρ hρ) := by
  intro a b
  obtain ⟨w, hw⟩ := QuotientGroup.mk_surjective (s := Nsub) (a⁻¹ * b)
  refine ⟨liftPath (FreeGroup.toWord w) a, ?_⟩
  have h := liftPath_isPath Nsub (FreeGroup.toWord w) a
  rw [FreeGroup.mk_toWord, hw, show a * (a⁻¹ * b) = b by group] at h
  exact h

/-! ### The covering map and the deck action -/

/-- The projection of the cover onto the presentation complex. -/
def coverProj : Hom (coverComplex Nsub ρ hρ) (presComplex ρ) where
  onV _ := PUnit.unit
  onE e := e.2
  onF f := f.2
  src_onE _ := rfl
  tgt_onE _ := rfl
  base_onF _ := rfl
  att_onF f := (map_liftPath (FreeGroup.toWord (ρ f.2)) f.1).symm

omit [Fintype α] [Fintype J] [DecidableEq J] in
include hρ in
/-- The projection is a combinatorial covering map. -/
theorem coverProj_isCovering : IsCovering (coverProj hρ) := by
  classical
  refine ⟨fun _ => ⟨(1 : FreeGroup α ⧸ Nsub), rfl⟩, fun q => ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · -- injectivity on germs
    rintro ⟨⟨⟨q₁, i₁⟩, b₁⟩, h₁⟩ ⟨⟨⟨q₂, i₂⟩, b₂⟩, h₂⟩ h
    have hval := congrArg Subtype.val h
    have hi : i₁ = i₂ := congrArg Prod.fst hval
    have hb : b₁ = b₂ := congrArg Prod.snd hval
    subst hi
    subst hb
    have hq : q₁ = q₂ := by
      cases b₁
      · have e₁ : q₁ * qof Nsub i₁ = q := h₁
        have e₂ : q₂ * qof Nsub i₁ = q := h₂
        exact mul_right_cancel (e₁.trans e₂.symm)
      · exact (h₁ : q₁ = q).trans (h₂ : q₂ = q).symm
    subst hq
    rfl
  · -- surjectivity on germs
    rintro ⟨⟨i, b⟩, -⟩
    cases b
    · refine ⟨⟨((q * (qof Nsub i)⁻¹, i), false), ?_⟩, rfl⟩
      show q * (qof Nsub i)⁻¹ * qof Nsub i = q
      group
    · exact ⟨⟨((q, i), true), rfl⟩, rfl⟩
  · -- injectivity on two-cells
    rintro ⟨q₁, j₁⟩ ⟨q₂, j₂⟩ h
    have hval := congrArg Subtype.val h
    have hj : j₁ = j₂ := congrArg (fun x => x.1) hval
    have hq : q₁ = q₂ := congrArg (fun x => x.2) hval
    rw [hj, hq]
  · -- surjectivity on two-cells
    rintro ⟨⟨j, q⟩, -⟩
    exact ⟨(q, j), rfl⟩

/-- The deck action of `Q = F/Ñ` on the cover, by left translation. -/
def coverDeck : DeckAction (coverComplex Nsub ρ hρ) (FreeGroup α ⧸ Nsub) where
  smulV q a := q * a
  smulE q e := (q * e.1, e.2)
  smulF q f := (q * f.1, f.2)
  one_smulV _ := one_mul _
  mul_smulV _ _ _ := mul_assoc ..
  one_smulE e := by simp
  mul_smulE _ _ e := by simp [mul_assoc]
  one_smulF f := by simp
  mul_smulF _ _ f := by simp [mul_assoc]
  src_smul _ _ := rfl
  tgt_smul _ e := mul_assoc ..
  base_smul _ _ := rfl
  att_smul q f := liftPath_translate (FreeGroup.toWord (ρ f.2)) q f.1

omit [Fintype α] [Fintype J] [DecidableEq J] in
include hρ in
/-- The covering is regular: the deck group acts simply transitively on the fibres. -/
theorem coverProj_isRegular : IsRegular (coverProj hρ) (coverDeck hρ) := by
  refine ⟨fun _ _ => rfl, fun a b _ => ⟨b * a⁻¹, ?_, ?_⟩⟩
  · show b * a⁻¹ * a = b
    group
  · intro q hq
    have hqa : q * a = b := hq
    rw [← hqa]
    group

/-! ### The topological input of Section 2, as a theorem -/

include hρ in
/-- **A perfect normal subgroup satisfying the requirements (2.2) yields a connected acyclic
regular cover of the presentation complex.**  This is the input `cover` of Section 2 of the
paper, here proved. -/
theorem presComplex_hasAcyclicRegularCover
    (hperf : Nsub ≤ Subgroup.normalClosure (Set.range ρ) ⊔ ⁅Nsub, Nsub⁆)
    (hsat : ∀ v : J →₀ FreeGroupRing α, FoxSat (foxMatrix ρ) v Nsub) :
    HasAcyclicRegularCover (presComplex ρ) :=
  ⟨coverComplex Nsub ρ hρ, FreeGroup α ⧸ Nsub, inferInstance, coverProj hρ, coverDeck hρ,
    coverProj_isCovering hρ, coverProj_isRegular hρ, coverComplex_isConnected hρ,
    coverComplex_isAcyclic hρ hperf (bdry2_injective_of_foxSat Nsub ρ hsat)⟩

end Comb
end FiniteChains
