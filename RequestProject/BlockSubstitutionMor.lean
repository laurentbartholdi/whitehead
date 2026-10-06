module

public import RequestProject.GenerationStep
public import RequestProject.FoxNaturality
public import RequestProject.CockcroftExtStep

@[expose] public section

/-!
# Rule 3 as a structural map

`RequestProject/BlockSubstitutionPi1.lean` computes the fundamental group of the substituted
presentation (3.4) of rule 3.  This file produces the *structural map* of rule 3 in the sense
of `RequestProject/GenerationStep.lean`, i.e. it equips the substitution with its induced map
on the two-chains of the universal covers and proves that this map is semilinear, carries Fox
cycles to Fox cycles and preserves zero augmentations.  After that, rule 3 enters the
composite operation `T` on exactly the same footing as rules 1 and 2: `Generates.comp`,
`isCockcroft_of_generates` and `cells_eq_zero_of_generates` apply to it verbatim, and the
*only* thing that the block still has to supply is the generation property (B2) itself.

The set-up is the indexed form of (3.4).  The source presentation is
`ρ : Option J → FreeGroup α`, where `ρ none = r` is the replaced entry and the `ρ (some j)`
are the retained ones; the target is

  `substPres ρ bsub : J ⊕ M → FreeGroup (α ⊕ Z)`,
  `inl j ↦ r_j` (read in the larger free group),  `inr m ↦ β_m(u, v, Z)`.

Two things are assumed, and both are the algebraic shadow of the chosen filling of (B1):

* `hfill` — the replaced relator `r` dies in the group of (3.4).  This is proved from the
  filling in `FiniteChains.BlockSubst.mk_map_inl_relator_eq_one`;
* the two-chain `c : M → ℤ[G']` carried by the filling, whose cellular boundary is the
  boundary of the replaced two-cell (`hbdry_base`) and which involves no internal generator
  in a spurious way (`hbdry_int`).  In the pushout of the paper this chain is the image of
  the fundamental class of `Σ_q` under `b_q`.

Nothing here assumes anything about the block beyond these identities; in particular the
generation property (B2) is *not* proved, and by
`FiniteChains.BlockSubst.baseHom_not_injective` it cannot be, from presentations alone.
-/

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains
namespace BlockMor

open MonoidAlgebra

universe u

variable {α Z J M : Type u}

/-- The substituted presentation (3.4) in indexed form: the retained relators, read in the
free group on the old and the internal generators, together with the substituted block
relators. -/
def substPres (ρ : Option J → FreeGroup α) (bsub : M → FreeGroup (α ⊕ Z)) :
    J ⊕ M → FreeGroup (α ⊕ Z) :=
  Sum.elim (fun j => FreeGroup.map Sum.inl (ρ (some j))) bsub

@[simp] theorem substPres_inl (ρ : Option J → FreeGroup α) (bsub : M → FreeGroup (α ⊕ Z))
    (j : J) : substPres ρ bsub (Sum.inl j) = FreeGroup.map Sum.inl (ρ (some j)) := rfl

@[simp] theorem substPres_inr (ρ : Option J → FreeGroup α) (bsub : M → FreeGroup (α ⊕ Z))
    (m : M) : substPres ρ bsub (Sum.inr m) = bsub m := rfl

variable (ρ : Option J → FreeGroup α) (bsub : M → FreeGroup (α ⊕ Z))

/-- The hypothesis supplied by the filling of (B1): the replaced relator is a consequence of
the relators of (3.4). -/
abbrev Filled : Prop :=
  FreeGroup.map (Sum.inl (β := Z)) (ρ none) ∈ Subgroup.normalClosure (Set.range (substPres ρ bsub))

/-- **The structural map on fundamental groups.** -/
def substHom (hfill : Filled ρ bsub) : PresGroup ρ →* PresGroup (substPres ρ bsub) :=
  QuotientGroup.lift _
    ((QuotientGroup.mk' (relSub (substPres ρ bsub))).comp (FreeGroup.map (Sum.inl (β := Z))))
    (by
      refine Subgroup.normalClosure_le_normal ?_
      rintro _ ⟨k, rfl⟩
      show ((QuotientGroup.mk' (relSub (substPres ρ bsub))).comp
        (FreeGroup.map (Sum.inl (β := Z)))) (ρ k) = 1
      cases k with
      | none => exact (QuotientGroup.eq_one_iff _).2 hfill
      | some j =>
          exact (QuotientGroup.eq_one_iff _).2
            (Subgroup.subset_normalClosure ⟨Sum.inl j, rfl⟩))

variable (hfill : Filled ρ bsub)

@[simp] theorem substHom_mk (w : FreeGroup α) :
    substHom ρ bsub hfill (QuotientGroup.mk w) =
      QuotientGroup.mk (FreeGroup.map (Sum.inl (β := Z)) w) := rfl

/-- The coefficient map of the structural map: coefficients of the old presentation are pushed
along `substHom`. -/
noncomputable def coeff (hfill : Filled ρ bsub) : MonoidAlgebra ℤ (PresGroup ρ) →+*
    MonoidAlgebra ℤ (PresGroup (substPres ρ bsub)) :=
  MonoidAlgebra.mapDomainRingHom ℤ (substHom ρ bsub hfill)

section Fox

variable [Fintype α] [DecidableEq α] [Fintype Z] [DecidableEq Z]
  [Fintype J] [DecidableEq J] [Fintype M] [DecidableEq M]

/-! ### Naturality of the Fox matrix -/

theorem mapDomainRingHom_comp' {G H K : Type*} [Group G] [Group H] [Group K]
    (g : H →* K) (f : G →* H) (x : MonoidAlgebra ℤ G) :
    MonoidAlgebra.mapDomainRingHom ℤ g (MonoidAlgebra.mapDomainRingHom ℤ f x)
      = MonoidAlgebra.mapDomainRingHom ℤ (g.comp f) x := by
  change MonoidAlgebra.mapDomain g (MonoidAlgebra.mapDomain f x) = MonoidAlgebra.mapDomain (g.comp f) x
  rw [← MonoidAlgebra.mapDomain_comp]
  rfl

omit [Fintype α] [DecidableEq α] [Fintype Z] [DecidableEq Z] [Fintype J] [DecidableEq J]
  [Fintype M] [DecidableEq M] in
theorem coeff_quotRingHom (x : FreeGroupRing α) :
    coeff ρ bsub hfill (quotRingHom ℤ (relSub ρ) x)
      = quotRingHom ℤ (relSub (substPres ρ bsub)) (freeRingMap (Sum.inl (β := Z)) x) := by
  show MonoidAlgebra.mapDomainRingHom ℤ (substHom ρ bsub hfill)
      (MonoidAlgebra.mapDomainRingHom ℤ (QuotientGroup.mk' (relSub ρ)) x)
    = MonoidAlgebra.mapDomainRingHom ℤ (QuotientGroup.mk' (relSub (substPres ρ bsub)))
        (MonoidAlgebra.mapDomainRingHom ℤ (FreeGroup.map (Sum.inl (β := Z))) x)
  rw [mapDomainRingHom_comp', mapDomainRingHom_comp']
  congr 1

omit [Fintype α] [Fintype Z] [Fintype J] [DecidableEq J] [Fintype M] [DecidableEq M] in
/-- **The retained relators contribute the old Fox matrix.** -/
theorem foxMatrix_inl_inl (i : α) (j : J) :
    foxMatrixPres (substPres ρ bsub) (Sum.inl i) (Sum.inl j)
      = coeff ρ bsub hfill (foxMatrixPres ρ i (some j)) := by
  show quotRingHom ℤ (relSub (substPres ρ bsub)) (fox (Sum.inl i) (substPres ρ bsub (Sum.inl j)))
    = coeff ρ bsub hfill (quotRingHom ℤ (relSub ρ) (fox i (ρ (some j))))
  rw [coeff_quotRingHom, substPres_inl, fox_map Sum.inl Sum.inl_injective]

omit [Fintype α] [Fintype Z] [Fintype J] [DecidableEq J] [Fintype M] [DecidableEq M] in
/-- **A retained relator has no derivative in an internal generator.** -/
theorem foxMatrix_inr_inl (z : Z) (j : J) :
    foxMatrixPres (substPres ρ bsub) (Sum.inr z) (Sum.inl j) = 0 := by
  show quotRingHom ℤ (relSub (substPres ρ bsub)) (fox (Sum.inr z) (substPres ρ bsub (Sum.inl j)))
    = 0
  rw [substPres_inl, fox_map_of_not_mem_range Sum.inl (fun i => Sum.inr_ne_inl), map_zero]

/-! ### The structural map on two-chains -/

variable (c : M → MonoidAlgebra ℤ (PresGroup (substPres ρ bsub)))

/-- The map on two-chains induced by the substitution: a retained two-cell keeps its
coefficient, and the coefficient of the replaced two-cell is spread over the block along the
filling chain `c`. -/
noncomputable def substCells (y : Option J → MonoidAlgebra ℤ (PresGroup ρ)) :
    J ⊕ M → MonoidAlgebra ℤ (PresGroup (substPres ρ bsub)) :=
  Sum.elim (fun j => coeff ρ bsub hfill (y (some j)))
    (fun m => coeff ρ bsub hfill (y none) * c m)

omit [Fintype α] [DecidableEq α] [Fintype Z] [DecidableEq Z] [Fintype J] [DecidableEq J]
  [Fintype M] [DecidableEq M] in
theorem substCells_add (y y' : Option J → MonoidAlgebra ℤ (PresGroup ρ)) :
    substCells ρ bsub hfill c (y + y') = substCells ρ bsub hfill c y + substCells ρ bsub hfill c y'
    := by
  funext k
  cases k with
  | inl j =>
      show coeff ρ bsub hfill (y (some j) + y' (some j))
        = coeff ρ bsub hfill (y (some j)) + coeff ρ bsub hfill (y' (some j))
      rw [map_add]
  | inr m =>
      show coeff ρ bsub hfill (y none + y' none) * c m
        = coeff ρ bsub hfill (y none) * c m + coeff ρ bsub hfill (y' none) * c m
      rw [map_add, add_mul]

omit [Fintype α] [DecidableEq α] [Fintype Z] [DecidableEq Z] [Fintype J] [DecidableEq J]
  [Fintype M] [DecidableEq M] in
theorem substCells_smul (x : MonoidAlgebra ℤ (PresGroup ρ))
    (y : Option J → MonoidAlgebra ℤ (PresGroup ρ)) :
    substCells ρ bsub hfill c (x • y)
      = coeff ρ bsub hfill x • substCells ρ bsub hfill c y := by
  funext k
  cases k with
  | inl j =>
      show coeff ρ bsub hfill (x * y (some j))
        = coeff ρ bsub hfill x * coeff ρ bsub hfill (y (some j))
      rw [map_mul]
  | inr m =>
      show coeff ρ bsub hfill (x * y none) * c m
        = coeff ρ bsub hfill x * (coeff ρ bsub hfill (y none) * c m)
      rw [map_mul, mul_assoc]

/-- The boundary hypotheses on the filling chain: its cellular boundary is that of the
replaced two-cell. -/
structure IsFilling : Prop where
  /-- On an old generator the boundary of the filling chain is the Fox derivative of the
  replaced relator. -/
  base : ∀ i : α, ∑ m, c m * foxMatrixPres (substPres ρ bsub) (Sum.inl i) (Sum.inr m)
      = coeff ρ bsub hfill (foxMatrixPres ρ i none)
  /-- On an internal generator the boundary of the filling chain vanishes. -/
  internal : ∀ z : Z, ∑ m, c m * foxMatrixPres (substPres ρ bsub) (Sum.inr z) (Sum.inr m) = 0

variable {ρ bsub hfill c}

omit [Fintype α] [Fintype Z] [DecidableEq J] [DecidableEq M] in
/-- **The substitution carries Fox cycles to Fox cycles**, i.e. it is a map of second
homotopy modules. -/
theorem isFoxCycle_substCells (hc : IsFilling ρ bsub hfill c)
    {y : Option J → MonoidAlgebra ℤ (PresGroup ρ)} (hy : IsFoxCycle ρ y) :
    IsFoxCycle (substPres ρ bsub) (substCells ρ bsub hfill c y) := by
  intro i
  rw [Fintype.sum_sum_type]
  cases i with
  | inl i =>
      have hleft : ∑ j : J, substCells ρ bsub hfill c y (Sum.inl j)
            * foxMatrixPres (substPres ρ bsub) (Sum.inl i) (Sum.inl j)
          = coeff ρ bsub hfill (∑ j : J, y (some j) * foxMatrixPres ρ i (some j)) := by
        rw [map_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [foxMatrix_inl_inl, map_mul]
        rfl
      have hright : ∑ m : M, substCells ρ bsub hfill c y (Sum.inr m)
            * foxMatrixPres (substPres ρ bsub) (Sum.inl i) (Sum.inr m)
          = coeff ρ bsub hfill (y none * foxMatrixPres ρ i none) := by
        have : ∀ m : M, substCells ρ bsub hfill c y (Sum.inr m)
              * foxMatrixPres (substPres ρ bsub) (Sum.inl i) (Sum.inr m)
            = coeff ρ bsub hfill (y none)
              * (c m * foxMatrixPres (substPres ρ bsub) (Sum.inl i) (Sum.inr m)) := by
          intro m
          show coeff ρ bsub hfill (y none) * c m * _ = _
          rw [mul_assoc]
        rw [Finset.sum_congr rfl fun m _ => this m, ← Finset.mul_sum, hc.base i, map_mul]
      have hsum := hy i
      rw [Fintype.sum_option] at hsum
      rw [hleft, hright, ← map_add, add_comm, hsum, map_zero]
  | inr z =>
      have hleft : ∑ j : J, substCells ρ bsub hfill c y (Sum.inl j)
          * foxMatrixPres (substPres ρ bsub) (Sum.inr z) (Sum.inl j) = 0 := by
        refine Finset.sum_eq_zero fun j _ => ?_
        rw [foxMatrix_inr_inl, mul_zero]
      have hright : ∑ m : M, substCells ρ bsub hfill c y (Sum.inr m)
          * foxMatrixPres (substPres ρ bsub) (Sum.inr z) (Sum.inr m) = 0 := by
        have : ∀ m : M, substCells ρ bsub hfill c y (Sum.inr m)
              * foxMatrixPres (substPres ρ bsub) (Sum.inr z) (Sum.inr m)
            = coeff ρ bsub hfill (y none)
              * (c m * foxMatrixPres (substPres ρ bsub) (Sum.inr z) (Sum.inr m)) := by
          intro m
          show coeff ρ bsub hfill (y none) * c m * _ = _
          rw [mul_assoc]
        rw [Finset.sum_congr rfl fun m _ => this m, ← Finset.mul_sum, hc.internal z, mul_zero]
      rw [hleft, hright, add_zero]

omit [Fintype α] [DecidableEq α] [Fintype Z] [DecidableEq Z] [Fintype J] [DecidableEq J]
  [Fintype M] [DecidableEq M] in
/-- **The substitution preserves zero augmentations** (naturality of the Hurewicz map). -/
theorem augPres_substCells_eq_zero {y : Option J → MonoidAlgebra ℤ (PresGroup ρ)}
    (hy : ∀ k, augPres ρ (y k) = 0) (k : J ⊕ M) :
    augPres (substPres ρ bsub) (substCells ρ bsub hfill c y k) = 0 := by
  have haug : ∀ x : MonoidAlgebra ℤ (PresGroup ρ),
      augPres (substPres ρ bsub) (coeff ρ bsub hfill x) = augPres ρ x :=
    fun x => augQ_mapDomain (substHom ρ bsub hfill) x
  cases k with
  | inl j => rw [show substCells ρ bsub hfill c y (Sum.inl j)
        = coeff ρ bsub hfill (y (some j)) from rfl, haug, hy (some j)]
  | inr m =>
      rw [show substCells ρ bsub hfill c y (Sum.inr m)
        = coeff ρ bsub hfill (y none) * c m from rfl, map_mul, haug, hy none, zero_mul]

variable (ρ bsub hfill c)

/-- **Rule 3 as a structural map.**  The substitution of a block for the entry `r`, with its
induced maps on fundamental groups and on two-chains. -/
noncomputable def substMor (hc : IsFilling ρ bsub hfill c) : PresMor ρ (substPres ρ bsub) where
  hom := substHom ρ bsub hfill
  cells := substCells ρ bsub hfill c
  cells_add := substCells_add ρ bsub hfill c
  cells_smul := substCells_smul ρ bsub hfill c
  cells_cycle := fun _ hy => isFoxCycle_substCells hc hy
  cells_aug := fun _ hy => augPres_substCells_eq_zero hy

omit [Fintype α] [Fintype Z] [DecidableEq J] [DecidableEq M] in
@[simp] theorem substMor_cells (hc : IsFilling ρ bsub hfill c)
    (y : Option J → MonoidAlgebra ℤ (PresGroup ρ)) :
    (substMor ρ bsub hfill c hc).cells y = substCells ρ bsub hfill c y := rfl

omit [Fintype α] [Fintype Z] [DecidableEq J] [DecidableEq M] in
/-- **The two consequences of (B2) for rule 3.**  Once the block supplies the generation
property (3.3) for the structural map of the substitution — this is exactly property (B2),
and it is the only remaining geometric input — rule 3 preserves the Cockcroft property, just
like rules 1 and 2. -/
theorem isCockcroft_substPres (hc : IsFilling ρ bsub hfill c)
    (hgen : Generates (substMor ρ bsub hfill c hc)) (hP : IsCockcroft ρ) :
    IsCockcroft (substPres ρ bsub) :=
  isCockcroft_of_generates _ hgen hP

/-! ### The hypotheses are satisfiable

The data assumed above do occur: the *trivial block*, whose single relator is the replaced
one and whose filling chain is the corresponding single two-cell, satisfies them.  (It is of
course not a surface block: it has no internal generators and does not change the
presentation.  The point of the example is only that `IsFilling` is not vacuous.) -/

section Trivial

/-- The trivial block: one relator, equal to the replaced one. -/
def trivialBlock (ρ : Option J → FreeGroup α) : PUnit.{u + 1} → FreeGroup (α ⊕ Z) :=
  fun _ => FreeGroup.map Sum.inl (ρ none)

omit [Fintype α] [DecidableEq α] [Fintype Z] [DecidableEq Z] [Fintype J] [DecidableEq J]
  [Fintype M] [DecidableEq M] in
theorem filled_trivialBlock (ρ : Option J → FreeGroup α) :
    Filled ρ (trivialBlock (Z := Z) ρ) :=
  Subgroup.subset_normalClosure ⟨Sum.inr PUnit.unit, rfl⟩

omit [Fintype α] [Fintype Z] [Fintype J] [DecidableEq J] [Fintype M] [DecidableEq M] in
theorem isFilling_trivialBlock (ρ : Option J → FreeGroup α) :
    IsFilling ρ (trivialBlock (Z := Z) ρ) (filled_trivialBlock ρ) (fun _ => 1) where
  base i := by
    rw [Fintype.sum_unique, one_mul]
    show quotRingHom ℤ (relSub (substPres ρ (trivialBlock (Z := Z) ρ)))
        (fox (Sum.inl i) (substPres ρ (trivialBlock (Z := Z) ρ) (Sum.inr PUnit.unit)))
      = coeff ρ (trivialBlock ρ) (filled_trivialBlock ρ)
          (quotRingHom ℤ (relSub ρ) (fox i (ρ none)))
    rw [coeff_quotRingHom, substPres_inr, trivialBlock, fox_map Sum.inl Sum.inl_injective]
  internal z := by
    rw [Fintype.sum_unique, one_mul]
    show quotRingHom ℤ (relSub (substPres ρ (trivialBlock (Z := Z) ρ)))
        (fox (Sum.inr z) (substPres ρ (trivialBlock (Z := Z) ρ) (Sum.inr PUnit.unit))) = 0
    rw [substPres_inr, trivialBlock,
      fox_map_of_not_mem_range Sum.inl (fun i => Sum.inr_ne_inl), map_zero]

end Trivial

end Fox

end BlockMor
end FiniteChains
