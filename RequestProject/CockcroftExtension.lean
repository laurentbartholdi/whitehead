module

public import RequestProject.Cockcroft
public import RequestProject.Pi2Dictionary

@[expose] public section

/-!
# Cockcroft complexes and two-dimensional extensions killing `π₂`

The introduction of the paper records the following characterization: a connected
two-complex `K` admits at least one two-dimensional extension inducing zero on `π₂` if and
only if `K` is Cockcroft.  The argument given there is:

* for an inclusion `i : K ⊂ L` of two-complexes the map `H₂(i)` is injective, since there
  are no three-cells; hence `π₂(i) = 0` forces the Hurewicz map of `K` to vanish;
* conversely, attaching disks along a generating set of `π₁(K)` produces a simply connected
  `L`, and the inclusion is then zero on `π₂`.

This file proves both halves in the combinatorial model of the project, for a complex of a
finite presentation: `π₂` is the module of Fox cycles, the Hurewicz map is the augmentation
(see `RequestProject/Cockcroft.lean`), and an extension is a presentation containing the
generators and the two-cells of `K`, with the old cells attached along the old words.

The result is `FiniteChains.isCockcroft_iff_nonempty_zeroPi2Ext`: the presentation complex
of `ρ` is Cockcroft if and only if it admits a two-dimensional extension which is zero on
`π₂`.  The extension produced in the proof is the one from the paper: adjoin one disk along
each generator.
-/

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains

open MonoidAlgebra

universe u

variable {α J : Type u} [Fintype α] [DecidableEq α] [Fintype J]

omit [Fintype α] [DecidableEq α] [Fintype J] in
/-- The relator subgroup of `K` maps into the relator subgroup of an extension. -/
theorem relSub_le_comap_ext {β C : Type u} (ρ : J → FreeGroup α) (σ : C → FreeGroup β)
    (g : α → β) (f : J → C) (hrel : ∀ j, σ (f j) = FreeGroup.map g (ρ j)) :
    relSub ρ ≤ (relSub σ).comap (FreeGroup.map g) := by
  refine Subgroup.normalClosure_le_normal ?_
  rintro _ ⟨j, rfl⟩
  refine Subgroup.mem_comap.2 ?_
  rw [← hrel j]
  exact Subgroup.subset_normalClosure (Set.mem_range_self _)

/-- A two-dimensional extension `K ⊂ L` of the presentation complex of `ρ` which is zero on
`π₂`.  The generators and the two-cells of `K` are generators and two-cells of `L`, an old
two-cell is attached along the old word, and every Fox cycle of `K` — that is, every element
of `π₂(K)` — has zero image in the chain module of `L`. -/
structure ZeroPi2Ext (ρ : J → FreeGroup α) where
  /-- The generators of the extension. -/
  gen : Type u
  /-- The two-cells of the extension. -/
  cell : Type u
  /-- The attaching words. -/
  rel : cell → FreeGroup gen
  /-- The generators of `K` are generators of `L`. -/
  genIncl : α → gen
  genIncl_injective : Function.Injective genIncl
  /-- The two-cells of `K` are two-cells of `L`. -/
  cellIncl : J → cell
  cellIncl_injective : Function.Injective cellIncl
  /-- An old two-cell is attached along the same word. -/
  rel_incl : ∀ j, rel (cellIncl j) = FreeGroup.map genIncl (ρ j)
  /-- The inclusion is zero on `π₂`: in Fox coordinates, every Fox cycle of `K` has zero
  image in `ℤ[π₁(L)]` in each coordinate. -/
  zero_pi2 : ∀ v : J → MonoidAlgebra ℤ (PresGroup ρ), IsFoxCycle ρ v → ∀ j,
    MonoidAlgebra.mapDomainRingHom ℤ
      (QuotientGroup.map (relSub ρ) (relSub rel) (FreeGroup.map genIncl)
        (relSub_le_comap_ext ρ rel genIncl cellIncl rel_incl)) (v j) = 0

omit [Fintype α] [DecidableEq α] [Fintype J] in
/-- Naturality of the augmentation: it is unchanged by the map of group rings induced by an
extension.  This is the algebraic form of "`H₂(i)` is injective because there are no
three-cells". -/
theorem augQ_mapDomainRingHom_quotientGroupMap {β : Type u} {C : Type u}
    {ρ : J → FreeGroup α} {σ : C → FreeGroup β} {g : α → β}
    (hle : relSub ρ ≤ (relSub σ).comap (FreeGroup.map g))
    (x : MonoidAlgebra ℤ (PresGroup ρ)) :
    augQ (relSub σ)
        (MonoidAlgebra.mapDomainRingHom ℤ
          (QuotientGroup.map (relSub ρ) (relSub σ) (FreeGroup.map g) hle) x)
      = augQ (relSub ρ) x := by
  induction x using MonoidAlgebra.induction_linear with
  | zero => simp
  | add x y hx hy => rw [map_add, map_add, hx, hy, map_add]
  | single q n =>
      rw [show MonoidAlgebra.mapDomainRingHom ℤ
            (QuotientGroup.map (relSub ρ) (relSub σ) (FreeGroup.map g) hle) (single q n)
          = single (QuotientGroup.map (relSub ρ) (relSub σ) (FreeGroup.map g) hle q) n from
        MonoidAlgebra.mapDomain_single, augQ_single, augQ_single]

omit [Fintype α] in
/-- **A complex with a two-dimensional extension killing `π₂` is Cockcroft.** -/
theorem isCockcroft_of_zeroPi2Ext {ρ : J → FreeGroup α} (E : ZeroPi2Ext ρ) :
    IsCockcroft ρ := by
  intro v hv j
  have h := E.zero_pi2 v hv j
  have := congrArg (augQ (relSub E.rel)) h
  rwa [augQ_mapDomainRingHom_quotientGroupMap _ (v j), map_zero] at this

/-! ### The condition "zero on `π₂`" in cellular form -/

/-- **The condition carried by `ZeroPi2Ext` is the topological one.**  For a presentation
complex `π₂` is the module of cellular two-cycles of the universal cover, and the inclusion
`K ⊂ L` lifts to the universal covers as `(q, c) ↦ (ψ q, cellIncl c)`.  The requirement that
this map kills every two-cycle is equivalent to the Fox-coordinate condition used in the
structure `FiniteChains.ZeroPi2Ext`. -/
theorem zeroPi2_cellular_iff [DecidableEq J] {β C : Type u} {ρ : J → FreeGroup α}
    {σ : C → FreeGroup β} {g : α → β} {f : J → C} (hf : Function.Injective f)
    (hle : relSub ρ ≤ (relSub σ).comap (FreeGroup.map g)) :
    (∀ u : ((FreeGroup α ⧸ relSub ρ) × J) →₀ ℤ, Comb.bdry2 (Comb.univCover ρ) u = 0 →
        Finsupp.mapDomain
          (Prod.map (⇑(QuotientGroup.map (relSub ρ) (relSub σ) (FreeGroup.map g) hle)) f) u = 0)
      ↔ (∀ v : J → MonoidAlgebra ℤ (PresGroup ρ), IsFoxCycle ρ v → ∀ j,
          MonoidAlgebra.mapDomainRingHom ℤ
            (QuotientGroup.map (relSub ρ) (relSub σ) (FreeGroup.map g) hle) (v j) = 0) := by
  classical
  set Φ := QuotientGroup.map (relSub ρ) (relSub σ) (FreeGroup.map g) hle with hΦ
  have hsum : ∀ (w : J →₀ MonoidAlgebra ℤ (PresGroup ρ)) (a : α),
      ∑ c ∈ w.support, w c * foxMatrixPres ρ a c = ∑ c, w c * foxMatrixPres ρ a c := by
    intro w a
    refine Finset.sum_subset (Finset.subset_univ _) ?_
    intro c _ hc
    rw [Finsupp.notMem_support_iff.1 hc, zero_mul]
  rw [Comb.univCover_zero_pi2_iff ρ Φ f hf]
  constructor
  · intro H v hv j
    have hv' : ∀ a : α, ∑ c ∈ (Finsupp.equivFunOnFinite.symm v).support,
        (Finsupp.equivFunOnFinite.symm v) c * foxMatrixPres ρ a c = 0 := by
      intro a
      rw [hsum]
      simpa using hv a
    have hH := H _ hv'
    rw [Comb.mapDomain_mapRange_eq_zero_iff Φ f hf] at hH
    simpa using hH j
  · intro H v hv
    rw [Comb.mapDomain_mapRange_eq_zero_iff Φ f hf]
    intro j
    refine H (fun j => v j) ?_ j
    intro a
    rw [← hsum v a]
    exact hv a

/-! ### The capped extension: adjoin a disk along every generator -/

/-- The presentation obtained from `ρ` by attaching a disk along each generator. -/
def capRel (ρ : J → FreeGroup α) : J ⊕ α → FreeGroup α :=
  Sum.elim ρ fun i => FreeGroup.of i

omit [Fintype α] [DecidableEq α] [Fintype J] in
theorem capRel_inl (ρ : J → FreeGroup α) (j : J) : capRel ρ (Sum.inl j) = ρ j := rfl

omit [Fintype α] [DecidableEq α] [Fintype J] in
theorem capRel_inr (ρ : J → FreeGroup α) (i : α) : capRel ρ (Sum.inr i) = FreeGroup.of i := rfl

omit [Fintype α] [DecidableEq α] [Fintype J] in
/-- The capped presentation presents the trivial group: its complex is simply connected. -/
theorem capRel_relSub_top (ρ : J → FreeGroup α) : relSub (capRel ρ) = ⊤ := by
  refine (Subgroup.eq_top_iff' _).2 fun w => ?_
  induction w using FreeGroup.induction_on with
  | one => exact one_mem _
  | of i => exact Subgroup.subset_normalClosure ⟨Sum.inr i, rfl⟩
  | inv_of i _ => exact inv_mem (Subgroup.subset_normalClosure ⟨Sum.inr i, rfl⟩)
  | mul x y hx hy => exact mul_mem hx hy

instance capPresGroup_subsingleton (ρ : J → FreeGroup α) :
    Subsingleton (PresGroup (capRel ρ)) := by
  constructor
  intro x y
  induction x using QuotientGroup.induction_on with
  | H x =>
    induction y using QuotientGroup.induction_on with
    | H y =>
      refine QuotientGroup.eq.2 ?_
      rw [capRel_relSub_top]
      trivial

omit [Fintype α] [DecidableEq α] in
/-- In the group ring of a trivial group every element is determined by its augmentation. -/
theorem eq_zero_of_augQ_eq_zero {N : Subgroup (FreeGroup α)} [N.Normal]
    [Subsingleton (FreeGroup α ⧸ N)] {x : MonoidAlgebra ℤ (FreeGroup α ⧸ N)}
    (hx : augQ N x = 0) : x = 0 := by
  have hsingle : ∀ y : MonoidAlgebra ℤ (FreeGroup α ⧸ N),
      y = single (1 : FreeGroup α ⧸ N) (augQ N y) := by
    intro y
    induction y using MonoidAlgebra.induction_linear with
    | zero => simp
    | add y z hy hz =>
        rw [map_add, single_add, ← hy, ← hz]
    | single q n =>
        rw [augQ_single, Subsingleton.elim q (1 : FreeGroup α ⧸ N)]
  rw [hsingle x, hx, single_zero]

/-- **A Cockcroft complex has a two-dimensional extension killing `π₂`**: adjoin one disk
along each generator. -/
noncomputable def cappedExt {ρ : J → FreeGroup α} (h : IsCockcroft ρ) : ZeroPi2Ext ρ where
  gen := α
  cell := J ⊕ α
  rel := capRel ρ
  genIncl := id
  genIncl_injective := Function.injective_id
  cellIncl := Sum.inl
  cellIncl_injective := Sum.inl_injective
  rel_incl := fun j => by simp [capRel_inl]
  zero_pi2 := by
    intro v hv j
    refine eq_zero_of_augQ_eq_zero ?_
    rw [augQ_mapDomainRingHom_quotientGroupMap _ (v j)]
    exact h v hv j

/-- The extension produced from a Cockcroft complex kills `π₂` in the cellular sense as
well: every cellular two-cycle of the universal cover of `K` dies in the extension. -/
theorem cappedExt_zero_pi2_cellular [DecidableEq J] {ρ : J → FreeGroup α}
    (h : IsCockcroft ρ) :
    ∀ u : ((FreeGroup α ⧸ relSub ρ) × J) →₀ ℤ, Comb.bdry2 (Comb.univCover ρ) u = 0 →
      Finsupp.mapDomain
        (Prod.map (⇑(QuotientGroup.map (relSub ρ) (relSub (capRel ρ)) (FreeGroup.map id)
          (relSub_le_comap_ext ρ (capRel ρ) id (Sum.inl : J → J ⊕ α)
            (fun j => by simp [capRel_inl]))))
          (Sum.inl : J → J ⊕ α)) u = 0 :=
  (zeroPi2_cellular_iff (f := (Sum.inl : J → J ⊕ α)) Sum.inl_injective _).2
    (cappedExt h).zero_pi2

omit [Fintype α] in
/-- **The characterization from the introduction.**  The presentation complex of `ρ` is
Cockcroft if and only if it admits a two-dimensional extension which is zero on `π₂`. -/
theorem isCockcroft_iff_nonempty_zeroPi2Ext (ρ : J → FreeGroup α) :
    IsCockcroft ρ ↔ Nonempty (ZeroPi2Ext ρ) :=
  ⟨fun h => ⟨cappedExt h⟩, fun ⟨E⟩ => isCockcroft_of_zeroPi2Ext E⟩

end FiniteChains
