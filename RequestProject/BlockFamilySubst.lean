import RequestProject.BlockSubstitutionMor

/-!
# Rule 3 for a family of simultaneously replaced entries

`RequestProject/BlockSubstitutionMor.lean` formalises the substitution of one block for one
labelled relator entry (`FiniteChains.BlockMor.substMor`).  The article's property (B2) is
stated for an **arbitrary family** of labelled entries replaced at the same time, each by its
own block with its own copy of the internal generators; the family form is what rule 3 uses,
because rule 3 replaces all extra entries of a presentation simultaneously.

This file carries out that generalisation.  The source presentation is written as

  `ρ : Jr ⊕ Sx → FreeGroup α`,

the entries indexed by `Sx` being the ones that are replaced and the entries indexed by `Jr`
the retained ones (every family of labelled entries of a presentation is of this shape after
reindexing).  For each `s : Sx` a block is given by its own set `Zt s` of internal generators
and its own set `Mt s` of relator entries,

  `bsub s : Mt s → FreeGroup (α ⊕ Zt s)`,

and the substituted presentation of the article, equation (3.4) in its simultaneous form, is

  `substPresF ρ bsub : Jr ⊕ (Σ s, Mt s) → FreeGroup (α ⊕ (Σ s, Zt s))`.

What is proved here is that this simultaneous substitution is a *structural map* in the sense
of `RequestProject/GenerationStep.lean`:

* `FiniteChains.BlockFamily.substHomF` — the induced homomorphism of fundamental groups,
  available as soon as every replaced relator dies in the substituted presentation
  (`FiniteChains.BlockFamily.FilledF`, the algebraic shadow of the chosen surface fillings
  of (B1));
* `FiniteChains.BlockFamily.cellsF` — the induced map on the two-chains of the universal
  covers: a retained two-cell keeps its coefficient, and the coefficient of a replaced
  two-cell is spread over its own block along that block's filling chain `c s`;
* `FiniteChains.BlockFamily.substMorF` — the two together form a `FiniteChains.PresMor`:
  the map is additive and semilinear, carries Fox cycles to Fox cycles and preserves zero
  augmentations.

As in the one-entry case, nothing here proves property (B2) itself: that is the subject of
`RequestProject/BlockFamilyChainModel.lean`, where the chain model of the double mapping
cylinder of the whole family is built over this structural map.

Since the ambient framework of the project is that of finite presentations (the Fox boundary
is a finite sum over the relator entries), `Sx` is a finite index type here; within a finite
presentation an arbitrary set of labelled entries is of this form.
-/

namespace FiniteChains

namespace BlockFamily

open MonoidAlgebra

universe u

variable {α Jr Sx : Type u} {Zt Mt : Sx → Type u}

/-- The generators used by the block substituted at the entry `s`: the old generators
together with the copy `Zt s` of the internal generators belonging to `s`. -/
def genEmb (s : Sx) : α ⊕ Zt s → α ⊕ (Σ s : Sx, Zt s) :=
  Sum.map id (fun z => ⟨s, z⟩)

@[simp] theorem genEmb_inl (s : Sx) (i : α) :
    genEmb (Zt := Zt) s (Sum.inl i) = Sum.inl i := rfl

@[simp] theorem genEmb_inr (s : Sx) (z : Zt s) :
    genEmb (α := α) s (Sum.inr z) = Sum.inr ⟨s, z⟩ := rfl

theorem genEmb_injective (s : Sx) : Function.Injective (genEmb (α := α) (Zt := Zt) s) := by
  rintro (i | z) (i' | z') h
  · exact congrArg Sum.inl (Sum.inl_injective h)
  · exact absurd h (by simp [genEmb])
  · exact absurd h (by simp [genEmb])
  · have h' : (⟨s, z⟩ : Σ s : Sx, Zt s) = ⟨s, z'⟩ := Sum.inr_injective h
    exact congrArg Sum.inr (eq_of_heq (Sigma.mk.inj h').2)

/-- A generator belonging to another block, or an internal generator of a different entry,
is outside the range of `genEmb s`. -/
theorem inr_ne_genEmb {s s' : Sx} (hs : s ≠ s') (z : Zt s') (x : α ⊕ Zt s) :
    (Sum.inr ⟨s', z⟩ : α ⊕ (Σ s : Sx, Zt s)) ≠ genEmb s x := by
  cases x with
  | inl i => simp [genEmb]
  | inr w =>
      simp only [genEmb_inr, ne_eq, Sum.inr.injEq]
      intro h
      exact hs (congrArg Sigma.fst h).symm

variable (ρ : Jr ⊕ Sx → FreeGroup α) (bsub : ∀ s : Sx, Mt s → FreeGroup (α ⊕ Zt s))

/-- **The simultaneous substitution (3.4).**  The retained relators, read in the free group
on the old generators and all the new internal generators, together with the relators of the
blocks substituted at the entries of `Sx`. -/
def substPresF : Jr ⊕ (Σ s : Sx, Mt s) → FreeGroup (α ⊕ (Σ s : Sx, Zt s)) :=
  Sum.elim (fun j => FreeGroup.map Sum.inl (ρ (Sum.inl j)))
    (fun p => FreeGroup.map (genEmb p.1) (bsub p.1 p.2))

@[simp] theorem substPresF_inl (j : Jr) :
    substPresF ρ bsub (Sum.inl j) = FreeGroup.map Sum.inl (ρ (Sum.inl j)) := rfl

@[simp] theorem substPresF_inr (p : Σ s : Sx, Mt s) :
    substPresF ρ bsub (Sum.inr p) = FreeGroup.map (genEmb p.1) (bsub p.1 p.2) := rfl

/-- The hypothesis supplied by the chosen fillings of (B1): every replaced relator is a
consequence of the relators of the substituted presentation. -/
abbrev FilledF : Prop := ∀ s : Sx,
  FreeGroup.map (Sum.inl (β := Σ s : Sx, Zt s)) (ρ (Sum.inr s))
    ∈ Subgroup.normalClosure (Set.range (substPresF ρ bsub))

/-- **The structural map on fundamental groups** of the simultaneous substitution. -/
def substHomF (hfill : FilledF ρ bsub) : PresGroup ρ →* PresGroup (substPresF ρ bsub) :=
  QuotientGroup.lift _
    ((QuotientGroup.mk' (relSub (substPresF ρ bsub))).comp
      (FreeGroup.map (Sum.inl (β := Σ s : Sx, Zt s))))
    (by
      refine Subgroup.normalClosure_le_normal ?_
      rintro _ ⟨k, rfl⟩
      show ((QuotientGroup.mk' (relSub (substPresF ρ bsub))).comp
        (FreeGroup.map (Sum.inl (β := Σ s : Sx, Zt s)))) (ρ k) = 1
      cases k with
      | inl j =>
          exact (QuotientGroup.eq_one_iff _).2
            (Subgroup.subset_normalClosure ⟨Sum.inl j, rfl⟩)
      | inr s => exact (QuotientGroup.eq_one_iff _).2 (hfill s))

variable (hfill : FilledF ρ bsub)

@[simp] theorem substHomF_mk (w : FreeGroup α) :
    substHomF ρ bsub hfill (QuotientGroup.mk w) =
      QuotientGroup.mk (FreeGroup.map (Sum.inl (β := Σ s : Sx, Zt s)) w) := rfl

/-- The coefficient homomorphism of the structural map. -/
noncomputable def coeffF : MonoidAlgebra ℤ (PresGroup ρ) →+*
    MonoidAlgebra ℤ (PresGroup (substPresF ρ bsub)) :=
  MonoidAlgebra.mapDomainRingHom ℤ (substHomF ρ bsub hfill)

section Fox

variable [Fintype α] [DecidableEq α] [Fintype Jr] [DecidableEq Jr]
  [Fintype Sx] [DecidableEq Sx]
  [∀ s, Fintype (Zt s)] [∀ s, DecidableEq (Zt s)] [∀ s, Fintype (Mt s)]

omit [Fintype α] [DecidableEq α] [Fintype Jr] [DecidableEq Jr] [Fintype Sx] [DecidableEq Sx]
  [∀ s, Fintype (Zt s)] [∀ s, DecidableEq (Zt s)] [∀ s, Fintype (Mt s)] in
theorem coeffF_quotRingHom (x : FreeGroupRing α) :
    coeffF ρ bsub hfill (quotRingHom ℤ (relSub ρ) x)
      = quotRingHom ℤ (relSub (substPresF ρ bsub))
          (freeRingMap (Sum.inl (β := Σ s : Sx, Zt s)) x) := by
  show MonoidAlgebra.mapDomainRingHom ℤ (substHomF ρ bsub hfill)
      (MonoidAlgebra.mapDomainRingHom ℤ (QuotientGroup.mk' (relSub ρ)) x)
    = MonoidAlgebra.mapDomainRingHom ℤ (QuotientGroup.mk' (relSub (substPresF ρ bsub)))
        (MonoidAlgebra.mapDomainRingHom ℤ
          (FreeGroup.map (Sum.inl (β := Σ s : Sx, Zt s))) x)
  rw [BlockMor.mapDomainRingHom_comp', BlockMor.mapDomainRingHom_comp']
  congr 1

omit [Fintype α] [Fintype Jr] [DecidableEq Jr] [Fintype Sx] [∀ s, Fintype (Zt s)]
  [∀ s, Fintype (Mt s)] in
/-- **A retained relator contributes the old Fox matrix.** -/
theorem foxMatrix_inl_inl (i : α) (j : Jr) :
    foxMatrixPres (substPresF ρ bsub) (Sum.inl i) (Sum.inl j)
      = coeffF ρ bsub hfill (foxMatrixPres ρ i (Sum.inl j)) := by
  show quotRingHom ℤ (relSub (substPresF ρ bsub))
      (fox (Sum.inl i) (substPresF ρ bsub (Sum.inl j)))
    = coeffF ρ bsub hfill (quotRingHom ℤ (relSub ρ) (fox i (ρ (Sum.inl j))))
  rw [coeffF_quotRingHom, substPresF_inl, fox_map Sum.inl Sum.inl_injective]

omit [Fintype α] [Fintype Jr] [DecidableEq Jr] [Fintype Sx] [∀ s, Fintype (Zt s)]
  [∀ s, Fintype (Mt s)] in
/-- **A retained relator has no derivative in an internal generator.** -/
theorem foxMatrix_inr_inl (w : Σ s : Sx, Zt s) (j : Jr) :
    foxMatrixPres (substPresF ρ bsub) (Sum.inr w) (Sum.inl j) = 0 := by
  show quotRingHom ℤ (relSub (substPresF ρ bsub))
      (fox (Sum.inr w) (substPresF ρ bsub (Sum.inl j))) = 0
  rw [substPresF_inl, fox_map_of_not_mem_range Sum.inl (fun i => Sum.inr_ne_inl), map_zero]

omit [Fintype α] [Fintype Jr] [DecidableEq Jr] [Fintype Sx] [∀ s, Fintype (Zt s)]
  [∀ s, Fintype (Mt s)] in
/-- **A block relator has no derivative in the internal generators of another block.**  This
is what makes the simultaneous replacement of a whole family behave like a single one: the
blocks do not interfere. -/
theorem foxMatrix_inr_inr_of_ne {s s' : Sx} (hs : s ≠ s') (z : Zt s') (m : Mt s) :
    foxMatrixPres (substPresF ρ bsub) (Sum.inr ⟨s', z⟩) (Sum.inr ⟨s, m⟩) = 0 := by
  show quotRingHom ℤ (relSub (substPresF ρ bsub))
      (fox (Sum.inr ⟨s', z⟩) (substPresF ρ bsub (Sum.inr ⟨s, m⟩))) = 0
  rw [substPresF_inr,
    fox_map_of_not_mem_range (genEmb s) (inr_ne_genEmb hs z), map_zero]

/-! ### The structural map on two-chains -/

variable (c : ∀ s : Sx, Mt s → MonoidAlgebra ℤ (PresGroup (substPresF ρ bsub)))

/-- The map on two-chains induced by the simultaneous substitution: a retained two-cell keeps
its coefficient, the coefficient of the two-cell replaced at `s` is spread over the block at
`s` along the filling chain `c s`. -/
noncomputable def cellsF (y : Jr ⊕ Sx → MonoidAlgebra ℤ (PresGroup ρ)) :
    Jr ⊕ (Σ s : Sx, Mt s) → MonoidAlgebra ℤ (PresGroup (substPresF ρ bsub)) :=
  Sum.elim (fun j => coeffF ρ bsub hfill (y (Sum.inl j)))
    (fun p => coeffF ρ bsub hfill (y (Sum.inr p.1)) * c p.1 p.2)

omit [Fintype α] [DecidableEq α] [Fintype Jr] [DecidableEq Jr] [Fintype Sx] [DecidableEq Sx]
  [∀ s, Fintype (Zt s)] [∀ s, DecidableEq (Zt s)] [∀ s, Fintype (Mt s)] in
@[simp] theorem cellsF_inl (y : Jr ⊕ Sx → MonoidAlgebra ℤ (PresGroup ρ)) (j : Jr) :
    cellsF ρ bsub hfill c y (Sum.inl j) = coeffF ρ bsub hfill (y (Sum.inl j)) := rfl

omit [Fintype α] [DecidableEq α] [Fintype Jr] [DecidableEq Jr] [Fintype Sx] [DecidableEq Sx]
  [∀ s, Fintype (Zt s)] [∀ s, DecidableEq (Zt s)] [∀ s, Fintype (Mt s)] in
@[simp] theorem cellsF_inr (y : Jr ⊕ Sx → MonoidAlgebra ℤ (PresGroup ρ))
    (p : Σ s : Sx, Mt s) :
    cellsF ρ bsub hfill c y (Sum.inr p)
      = coeffF ρ bsub hfill (y (Sum.inr p.1)) * c p.1 p.2 := rfl

omit [Fintype α] [DecidableEq α] [Fintype Jr] [DecidableEq Jr] [Fintype Sx] [DecidableEq Sx]
  [∀ s, Fintype (Zt s)] [∀ s, DecidableEq (Zt s)] [∀ s, Fintype (Mt s)] in
theorem cellsF_add (y y' : Jr ⊕ Sx → MonoidAlgebra ℤ (PresGroup ρ)) :
    cellsF ρ bsub hfill c (y + y') = cellsF ρ bsub hfill c y + cellsF ρ bsub hfill c y' := by
  funext k
  cases k with
  | inl j =>
      show coeffF ρ bsub hfill (y (Sum.inl j) + y' (Sum.inl j)) = _
      rw [map_add]; rfl
  | inr p =>
      show coeffF ρ bsub hfill (y (Sum.inr p.1) + y' (Sum.inr p.1)) * c p.1 p.2 = _
      rw [map_add, add_mul]; rfl

omit [Fintype α] [DecidableEq α] [Fintype Jr] [DecidableEq Jr] [Fintype Sx] [DecidableEq Sx]
  [∀ s, Fintype (Zt s)] [∀ s, DecidableEq (Zt s)] [∀ s, Fintype (Mt s)] in
theorem cellsF_smul (x : MonoidAlgebra ℤ (PresGroup ρ))
    (y : Jr ⊕ Sx → MonoidAlgebra ℤ (PresGroup ρ)) :
    cellsF ρ bsub hfill c (x • y)
      = coeffF ρ bsub hfill x • cellsF ρ bsub hfill c y := by
  funext k
  cases k with
  | inl j =>
      show coeffF ρ bsub hfill (x * y (Sum.inl j))
        = coeffF ρ bsub hfill x * coeffF ρ bsub hfill (y (Sum.inl j))
      rw [map_mul]
  | inr p =>
      show coeffF ρ bsub hfill (x * y (Sum.inr p.1)) * c p.1 p.2
        = coeffF ρ bsub hfill x * (coeffF ρ bsub hfill (y (Sum.inr p.1)) * c p.1 p.2)
      rw [map_mul, mul_assoc]

/-- The boundary conditions on the family of filling chains: for every replaced entry the
cellular boundary of its filling chain is the boundary of the replaced two-cell. -/
structure IsFillingF : Prop where
  /-- On an old generator the boundary of the filling chain at `s` is the Fox derivative of
  the relator replaced at `s`. -/
  base : ∀ (s : Sx) (i : α),
    ∑ m : Mt s, c s m * foxMatrixPres (substPresF ρ bsub) (Sum.inl i) (Sum.inr ⟨s, m⟩)
      = coeffF ρ bsub hfill (foxMatrixPres ρ i (Sum.inr s))
  /-- On an internal generator of its own block the boundary of the filling chain
  vanishes. -/
  internal : ∀ (s : Sx) (z : Zt s),
    ∑ m : Mt s, c s m * foxMatrixPres (substPresF ρ bsub) (Sum.inr ⟨s, z⟩) (Sum.inr ⟨s, m⟩)
      = 0

variable {ρ bsub hfill c}

omit [Fintype α] [Fintype Jr] [DecidableEq Jr] [∀ s, Fintype (Zt s)] in
/-- The contribution of the block cells to the Fox boundary, at an old generator. -/
theorem sum_cells_inr_inl (hc : IsFillingF ρ bsub hfill c)
    (y : Jr ⊕ Sx → MonoidAlgebra ℤ (PresGroup ρ)) (i : α) :
    ∑ p : Σ s : Sx, Mt s, cellsF ρ bsub hfill c y (Sum.inr p)
        * foxMatrixPres (substPresF ρ bsub) (Sum.inl i) (Sum.inr p)
      = ∑ s : Sx, coeffF ρ bsub hfill (y (Sum.inr s) * foxMatrixPres ρ i (Sum.inr s)) := by
  rw [Fintype.sum_sigma]
  refine Finset.sum_congr rfl fun s _ => ?_
  have h : ∀ m : Mt s, cellsF ρ bsub hfill c y (Sum.inr ⟨s, m⟩)
        * foxMatrixPres (substPresF ρ bsub) (Sum.inl i) (Sum.inr ⟨s, m⟩)
      = coeffF ρ bsub hfill (y (Sum.inr s))
        * (c s m * foxMatrixPres (substPresF ρ bsub) (Sum.inl i) (Sum.inr ⟨s, m⟩)) := by
    intro m
    rw [cellsF_inr, mul_assoc]
  rw [Finset.sum_congr rfl fun m _ => h m, ← Finset.mul_sum, hc.base s i, map_mul]

omit [Fintype α] [Fintype Jr] [DecidableEq Jr] [∀ s, Fintype (Zt s)] in
/-- The contribution of the block cells to the Fox boundary, at an internal generator. -/
theorem sum_cells_inr_inr (hc : IsFillingF ρ bsub hfill c)
    (y : Jr ⊕ Sx → MonoidAlgebra ℤ (PresGroup ρ)) (s' : Sx) (z : Zt s') :
    ∑ p : Σ s : Sx, Mt s, cellsF ρ bsub hfill c y (Sum.inr p)
        * foxMatrixPres (substPresF ρ bsub) (Sum.inr ⟨s', z⟩) (Sum.inr p) = 0 := by
  rw [Fintype.sum_sigma]
  refine Finset.sum_eq_zero fun s _ => ?_
  by_cases hs : s = s'
  · subst hs
    have h : ∀ m : Mt s, cellsF ρ bsub hfill c y (Sum.inr ⟨s, m⟩)
          * foxMatrixPres (substPresF ρ bsub) (Sum.inr ⟨s, z⟩) (Sum.inr ⟨s, m⟩)
        = coeffF ρ bsub hfill (y (Sum.inr s))
          * (c s m * foxMatrixPres (substPresF ρ bsub) (Sum.inr ⟨s, z⟩) (Sum.inr ⟨s, m⟩)) := by
      intro m
      rw [cellsF_inr, mul_assoc]
    rw [Finset.sum_congr rfl fun m _ => h m, ← Finset.mul_sum, hc.internal s z, mul_zero]
  · refine Finset.sum_eq_zero fun m _ => ?_
    rw [foxMatrix_inr_inr_of_ne ρ bsub hs z m, mul_zero]

omit [Fintype α] [DecidableEq Jr] [∀ s, Fintype (Zt s)] in
/-- **The simultaneous substitution carries Fox cycles to Fox cycles**: it is a map of second
homotopy modules. -/
theorem isFoxCycle_cellsF (hc : IsFillingF ρ bsub hfill c)
    {y : Jr ⊕ Sx → MonoidAlgebra ℤ (PresGroup ρ)} (hy : IsFoxCycle ρ y) :
    IsFoxCycle (substPresF ρ bsub) (cellsF ρ bsub hfill c y) := by
  intro i
  rw [Fintype.sum_sum_type]
  cases i with
  | inl i =>
      have hleft : ∑ j : Jr, cellsF ρ bsub hfill c y (Sum.inl j)
            * foxMatrixPres (substPresF ρ bsub) (Sum.inl i) (Sum.inl j)
          = ∑ j : Jr, coeffF ρ bsub hfill (y (Sum.inl j) * foxMatrixPres ρ i (Sum.inl j)) := by
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [cellsF_inl, foxMatrix_inl_inl ρ bsub hfill, ← map_mul]
      rw [hleft, sum_cells_inr_inl hc y i]
      have hsum := hy i
      rw [Fintype.sum_sum_type] at hsum
      rw [← map_sum, ← map_sum, ← map_add, hsum, map_zero]
  | inr w =>
      obtain ⟨s', z⟩ := w
      have hleft : ∑ j : Jr, cellsF ρ bsub hfill c y (Sum.inl j)
          * foxMatrixPres (substPresF ρ bsub) (Sum.inr ⟨s', z⟩) (Sum.inl j) = 0 := by
        refine Finset.sum_eq_zero fun j _ => ?_
        rw [foxMatrix_inr_inl ρ bsub, mul_zero]
      rw [hleft, sum_cells_inr_inr hc y s' z, add_zero]

omit [Fintype α] [DecidableEq α] [Fintype Jr] [DecidableEq Jr] [Fintype Sx] [DecidableEq Sx]
  [∀ s, Fintype (Zt s)] [∀ s, DecidableEq (Zt s)] [∀ s, Fintype (Mt s)] in
/-- **The simultaneous substitution preserves zero augmentations** (naturality of the
Hurewicz map). -/
theorem augPres_cellsF_eq_zero {y : Jr ⊕ Sx → MonoidAlgebra ℤ (PresGroup ρ)}
    (hy : ∀ k, augPres ρ (y k) = 0) (k : Jr ⊕ (Σ s : Sx, Mt s)) :
    augPres (substPresF ρ bsub) (cellsF ρ bsub hfill c y k) = 0 := by
  have haug : ∀ x : MonoidAlgebra ℤ (PresGroup ρ),
      augPres (substPresF ρ bsub) (coeffF ρ bsub hfill x) = augPres ρ x :=
    fun x => augQ_mapDomain (substHomF ρ bsub hfill) x
  cases k with
  | inl j => rw [cellsF_inl, haug, hy (Sum.inl j)]
  | inr p => rw [cellsF_inr, map_mul, haug, hy (Sum.inr p.1), zero_mul]

variable (ρ bsub hfill c)

/-- **Rule 3 for a family, as a structural map.**  The simultaneous substitution of a family
of blocks for a family of labelled entries, with its induced maps on fundamental groups and
on the two-chains of the universal covers. -/
noncomputable def substMorF (hc : IsFillingF ρ bsub hfill c) :
    PresMor ρ (substPresF ρ bsub) where
  hom := substHomF ρ bsub hfill
  cells := cellsF ρ bsub hfill c
  cells_add := cellsF_add ρ bsub hfill c
  cells_smul := cellsF_smul ρ bsub hfill c
  cells_cycle := fun _ hy => isFoxCycle_cellsF hc hy
  cells_aug := fun _ hy => augPres_cellsF_eq_zero hy

omit [Fintype α] [DecidableEq Jr] [∀ s, Fintype (Zt s)] in
@[simp] theorem substMorF_hom (hc : IsFillingF ρ bsub hfill c) :
    (substMorF ρ bsub hfill c hc).hom = substHomF ρ bsub hfill := rfl

omit [Fintype α] [DecidableEq Jr] [∀ s, Fintype (Zt s)] in
@[simp] theorem substMorF_cells (hc : IsFillingF ρ bsub hfill c)
    (y : Jr ⊕ Sx → MonoidAlgebra ℤ (PresGroup ρ)) :
    (substMorF ρ bsub hfill c hc).cells y = cellsF ρ bsub hfill c y := rfl

end Fox

end BlockFamily

end FiniteChains
