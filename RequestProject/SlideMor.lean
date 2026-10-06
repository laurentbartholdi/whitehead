import RequestProject.SlideGeneration
import RequestProject.RuleOneMor

/-!
# Rule 2 as a structural map with the generation property

Rule 2 of the operation `T` of Lemma 3.9 replaces an extra relator `r*` by
`r⁰ = r* ∏_j r_j^{c_j}`, a product of `r*` with retained core relators.  The paper justifies
the generation equation (3.3) for this rule by the remark that the move is a finite sequence
of slides of the relator disk over core disks, hence a homotopy equivalence relative to `D`.

`RequestProject/SlideGeneration.lean` proves the combinatorial content of that remark: the
slide does not change the normal closure of the relators, and on two-cycles it acts as the
`ℤ[G]`-linear isomorphism `y ↦ (j ↦ y j - y_{j₀} λ j)`.  This file packages the move as a
**structural map** `PresMor` of `RequestProject/GenerationStep.lean` and proves that it
satisfies `FiniteChains.Generates`, so that rule 2 composes with rules 1 and 3.

* `FiniteChains.slideGroupHom` — the (iso)morphism of fundamental groups induced by the
  slide, together with its inverse and the induced isomorphism of group rings;
* `FiniteChains.slideMor` — rule 2 as a structural map;
* `FiniteChains.generates_slideMor` — **equation (3.3) for rule 2**, with no hypothesis
  beyond the defining property of the correcting word and its coefficient vector.
-/

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains

open MonoidAlgebra

universe u

variable {α : Type u} [Fintype α] [DecidableEq α] {J : Type u} [Fintype J] [DecidableEq J]
variable (ρ : J → FreeGroup α) (j₀ : J) (u : FreeGroup α)
  (hu : u ∈ Subgroup.normalClosure (Set.range (coreRel ρ j₀)))

/-! ### The identification of the two fundamental groups -/

omit [Fintype α] [DecidableEq α] [Fintype J] in
/-- The slide does not change the normal closure of the relators, so the identity of the free
group descends to the two presented groups. -/
def slideGroupHom : PresGroup ρ →* PresGroup (slideRel ρ j₀ u) :=
  QuotientGroup.map _ _ (MonoidHom.id _) (by
    rw [Subgroup.comap_id, relSub_slideRel ρ j₀ u hu])

omit [Fintype α] [DecidableEq α] [Fintype J] in
/-- The inverse identification. -/
def slideGroupHomInv : PresGroup (slideRel ρ j₀ u) →* PresGroup ρ :=
  QuotientGroup.map _ _ (MonoidHom.id _) (by
    rw [Subgroup.comap_id, relSub_slideRel ρ j₀ u hu])

omit [Fintype α] [DecidableEq α] [Fintype J] in
@[simp] theorem slideGroupHom_mk (w : FreeGroup α) :
    slideGroupHom ρ j₀ u hu (QuotientGroup.mk w) = QuotientGroup.mk w := rfl

omit [Fintype α] [DecidableEq α] [Fintype J] in
@[simp] theorem slideGroupHomInv_mk (w : FreeGroup α) :
    slideGroupHomInv ρ j₀ u hu (QuotientGroup.mk w) = QuotientGroup.mk w := rfl

omit [Fintype α] [DecidableEq α] [Fintype J] in
theorem slideGroupHom_injective : Function.Injective (slideGroupHom ρ j₀ u hu) := by
  intro a b hab
  induction a using QuotientGroup.induction_on with
  | H wa =>
      induction b using QuotientGroup.induction_on with
      | H wb =>
          rw [slideGroupHom_mk, slideGroupHom_mk] at hab
          have := congrArg (slideGroupHomInv ρ j₀ u hu) hab
          rwa [slideGroupHomInv_mk, slideGroupHomInv_mk] at this

omit [Fintype α] [DecidableEq α] [Fintype J] in
theorem slideGroupHom_slideGroupHomInv (q : PresGroup (slideRel ρ j₀ u)) :
    slideGroupHom ρ j₀ u hu (slideGroupHomInv ρ j₀ u hu q) = q := by
  induction q using QuotientGroup.induction_on with
  | H w => rw [slideGroupHomInv_mk, slideGroupHom_mk]

/-- The induced isomorphism of group rings. -/
noncomputable def slideRing :
    MonoidAlgebra ℤ (PresGroup ρ) →+* MonoidAlgebra ℤ (PresGroup (slideRel ρ j₀ u)) :=
  MonoidAlgebra.mapDomainRingHom ℤ (slideGroupHom ρ j₀ u hu)

/-- The inverse isomorphism of group rings. -/
noncomputable def slideRingInv :
    MonoidAlgebra ℤ (PresGroup (slideRel ρ j₀ u)) →+* MonoidAlgebra ℤ (PresGroup ρ) :=
  MonoidAlgebra.mapDomainRingHom ℤ (slideGroupHomInv ρ j₀ u hu)

omit [Fintype α] [DecidableEq α] [Fintype J] in
theorem slideRing_injective : Function.Injective (slideRing ρ j₀ u hu) :=
  fun _ _ h => MonoidAlgebra.coeff_injective (Finsupp.mapDomain_injective (slideGroupHom_injective ρ j₀ u hu) (congrArg MonoidAlgebra.coeff h))

omit [Fintype α] [DecidableEq α] [Fintype J] in
theorem slideRing_slideRingInv (x : MonoidAlgebra ℤ (PresGroup (slideRel ρ j₀ u))) :
    slideRing ρ j₀ u hu (slideRingInv ρ j₀ u hu x) = x := by
  show MonoidAlgebra.mapDomain (slideGroupHom ρ j₀ u hu)
      (MonoidAlgebra.mapDomain (slideGroupHomInv ρ j₀ u hu) x) = x
  rw [← MonoidAlgebra.mapDomain_comp]
  have h : (⇑(slideGroupHom ρ j₀ u hu) ∘ ⇑(slideGroupHomInv ρ j₀ u hu)) = id :=
    funext fun q => slideGroupHom_slideGroupHomInv ρ j₀ u hu q
  rw [h, MonoidAlgebra.mapDomain_id]

omit [Fintype α] [DecidableEq α] [Fintype J] in
/-- Reading a group-ring element of `ℤ[F]` in the two presented groups gives corresponding
elements. -/
theorem slideRing_quotRingHom (x : FreeGroupRing α) :
    slideRing ρ j₀ u hu (quotRingHom ℤ (relSub ρ) x)
      = quotRingHom ℤ (relSub (slideRel ρ j₀ u)) x := by
  induction x using MonoidAlgebra.induction_linear with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | single w m =>
      show MonoidAlgebra.mapDomain (slideGroupHom ρ j₀ u hu)
          (quotRingHom ℤ (relSub ρ) (MonoidAlgebra.single w m)) = _
      rw [quotRingHom_single, MonoidAlgebra.mapDomain_single, slideGroupHom_mk, quotRingHom_single]

omit [Fintype α] [Fintype J] in
/-- The Fox matrix of the slid presentation is the image of the Fox matrix computed in the
old group ring. -/
theorem foxMatrixPres_slide (i : α) (j : J) :
    foxMatrixPres (slideRel ρ j₀ u) i j
      = slideRing ρ j₀ u hu (proj (relSub ρ) (fox i (slideRel ρ j₀ u j))) :=
  (slideRing_quotRingHom ρ j₀ u hu (fox i (slideRel ρ j₀ u j))).symm

omit [Fintype α] in
/-- Fox cycles of the slid presentation are exactly the two-cycles of its boundary map read
in the old group ring. -/
theorem isFoxCycle_slide_iff (w : J → MonoidAlgebra ℤ (PresGroup ρ)) :
    IsFoxCycle (slideRel ρ j₀ u) (fun j => slideRing ρ j₀ u hu (w j))
      ↔ bdry2 (relSub ρ) (slideRel ρ j₀ u) w = 0 := by
  have hsum : ∀ i : α,
      ∑ j : J, slideRing ρ j₀ u hu (w j) * foxMatrixPres (slideRel ρ j₀ u) i j
        = slideRing ρ j₀ u hu (bdry2 (relSub ρ) (slideRel ρ j₀ u) w i) := by
    intro i
    rw [show bdry2 (relSub ρ) (slideRel ρ j₀ u) w i
      = ∑ j : J, w j * proj (relSub ρ) (fox i (slideRel ρ j₀ u j)) from rfl, map_sum]
    exact Finset.sum_congr rfl fun j _ => by
      rw [map_mul, foxMatrixPres_slide ρ j₀ u hu i j]
  constructor
  · intro h
    funext i
    have := h i
    rw [hsum i] at this
    have h0 : slideRing ρ j₀ u hu (bdry2 (relSub ρ) (slideRel ρ j₀ u) w i)
        = slideRing ρ j₀ u hu 0 := by rw [this, map_zero]
    exact slideRing_injective ρ j₀ u hu h0
  · intro h i
    rw [hsum i, show bdry2 (relSub ρ) (slideRel ρ j₀ u) w i = 0 from congrFun h i, map_zero]

/-! ### Rule 2 as a structural map -/

variable (lam : J → MonoidAlgebra ℤ (PresGroup ρ))

/-- The map on two-chains induced by the slide: `y ↦ (j ↦ y j - y_{j₀} λ j)`, read in the
group ring of the slid presentation. -/
noncomputable def slideCells (y : J → MonoidAlgebra ℤ (PresGroup ρ)) :
    J → MonoidAlgebra ℤ (PresGroup (slideRel ρ j₀ u)) :=
  fun j => slideRing ρ j₀ u hu (y j - y j₀ * lam j)

omit [Fintype α] in
theorem isFoxCycle_slideCells (hlam0 : lam j₀ = 0)
    (hlam : bdry2 (relSub ρ) ρ lam = foxVec (relSub ρ) u)
    {y : J → MonoidAlgebra ℤ (PresGroup ρ)} (hy : IsFoxCycle ρ y) :
    IsFoxCycle (slideRel ρ j₀ u) (slideCells ρ j₀ u hu lam y) := by
  refine (isFoxCycle_slide_iff ρ j₀ u hu (fun j => y j - y j₀ * lam j)).2 ?_
  exact slideCycle_image_isCycle (relSub ρ) (rel_mem_relSub ρ) hlam0 hlam
    ((isFoxCycle_iff_bdry2_relSub ρ y).1 hy)

omit [Fintype α] in
/-- **Rule 2 as a structural map.** -/
noncomputable def slideMor (hlam0 : lam j₀ = 0)
    (hlam : bdry2 (relSub ρ) ρ lam = foxVec (relSub ρ) u) : PresMor ρ (slideRel ρ j₀ u) where
  hom := slideGroupHom ρ j₀ u hu
  cells := slideCells ρ j₀ u hu lam
  cells_add := fun y z => by
    funext j
    show slideRing ρ j₀ u hu ((y j + z j) - (y j₀ + z j₀) * lam j) = _
    show _ = slideRing ρ j₀ u hu (y j - y j₀ * lam j) + slideRing ρ j₀ u hu (z j - z j₀ * lam j)
    rw [← map_add]
    congr 1
    noncomm_ring
  cells_smul := fun c y => by
    funext j
    show slideRing ρ j₀ u hu (c * y j - (c * y j₀) * lam j)
      = slideRing ρ j₀ u hu c * slideRing ρ j₀ u hu (y j - y j₀ * lam j)
    rw [← map_mul]
    congr 1
    noncomm_ring
  cells_cycle := fun _ hy => isFoxCycle_slideCells ρ j₀ u hu lam hlam0 hlam hy
  cells_aug := fun y hy j => by
    have haug : ∀ x : MonoidAlgebra ℤ (PresGroup ρ),
        augPres (slideRel ρ j₀ u) (slideRing ρ j₀ u hu x) = augPres ρ x :=
      fun x => augQ_mapDomain (slideGroupHom ρ j₀ u hu) x
    show augPres (slideRel ρ j₀ u) (slideRing ρ j₀ u hu (y j - y j₀ * lam j)) = 0
    rw [haug, map_sub, map_mul, hy j, hy j₀, zero_mul, sub_zero]

omit [Fintype α] in
/-- **Equation (3.3) for rule 2.**  Every Fox cycle of the slid presentation is already the
image of a Fox cycle of the old one: the slide is an isomorphism on second homotopy
groups. -/
theorem generates_slideMor (hlam0 : lam j₀ = 0)
    (hlam : bdry2 (relSub ρ) ρ lam = foxVec (relSub ρ) u) :
    Generates (slideMor ρ j₀ u hu lam hlam0 hlam) := by
  intro v hv
  have hv' : IsFoxCycle (slideRel ρ j₀ u)
      (fun j => slideRing ρ j₀ u hu (slideRingInv ρ j₀ u hu (v j))) := by
    have h : (fun j => slideRing ρ j₀ u hu (slideRingInv ρ j₀ u hu (v j))) = v :=
      funext fun j => slideRing_slideRingInv ρ j₀ u hu (v j)
    rw [h]
    exact hv
  obtain ⟨y, hy, hveq⟩ := slideCycle_image (relSub ρ) (rel_mem_relSub ρ) hlam0 hlam
    ((isFoxCycle_slide_iff ρ j₀ u hu _).1 hv')
  refine Submodule.subset_span ⟨y, (isFoxCycle_iff_bdry2_relSub ρ y).2 hy, ?_⟩
  funext j
  show v j = slideRing ρ j₀ u hu (y j - y j₀ * lam j)
  rw [← slideRing_slideRingInv ρ j₀ u hu (v j)]
  congr 1
  exact congrFun hveq j

end FiniteChains
