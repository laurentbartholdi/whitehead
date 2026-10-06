module

public import RequestProject.RuleOneComposite
public import RequestProject.WedgeSigma

@[expose] public section

/-!
# Lemma 3.10: the terminal extension `Q`

Lemma 3.10 of the paper reads:

> Suppose `P` is Cockcroft and all core generators `x_i` are trivial in `G(P)`.  Then `Q(P)`
> is Cockcroft and `T(P) ⊂ Q(P)` is zero on `π₂`.  The core group remains trivial in both new
> groups.

Here `T` is the structural operation of Lemma 3.9 (`RequestProject/LemmaStructural.lean`) and
the *terminal extension* `Q(P)` of (3.6) is `T(P)` with the letters `a_z, b_z` added as
individual relators.

Its proof has two halves.

**First half** (the `π₂` statement).  "The structural map fixes the `x_i`, so they remain
trivial.  The composite `P → T(P) → Q(P)` kills all of `G(P)`: every extra generator maps to a
commutator of two capped loops.  A map from a Cockcroft complex that kills its fundamental
group is zero on `π₂`: lift to the simply connected target cover and use naturality of
Hurewicz.  This applies to the composite.  Equation (3.3) then makes the inclusion
`T(P) → Q(P)` zero on all of `π₂`."  This half is proved here **in full**, in the
presentation model of the project:

* `FiniteChains.addRels`, `FiniteChains.addRelsMor`, `FiniteChains.PresPoint.addRels` — the
  terminal extension: adjoining relators, with its structural map;
* `FiniteChains.cells_eq_zero_of_isCockcroft_of_hom_trivial` — **a map out of a Cockcroft
  complex which kills the fundamental group is zero on `π₂`** (the augmentation argument: on
  a trivial fundamental group the coefficient ring acts through the augmentation, so the
  image of a chain only depends on the Hurewicz image of that chain, which vanishes);
* `FiniteChains.cells_eq_zero_of_generates_comp` — the passage "equation (3.3) then makes the
  inclusion zero on *all* of `π₂`";
* `FiniteChains.terminal_cells_eq_zero` — **`T(P) ⊂ Q(P)` is zero on `π₂`**;
* `FiniteChains.terminal_core_trivial` — **the core group remains trivial in both new
  groups**;
* `FiniteChains.terminal_cells_eq_zero_ruleOne` — the same conclusion for rule 1 with one
  extra generator, with no hypothesis beyond Cockcroftness of `P` and the triviality of the
  core generators: there the composite kills `G(P)` because the stable-letter relator makes
  the extra generator equal to `[a,b]`, and `a` and `b` are killed by `Q`.

**Second half** (Cockcroftness of `Q(P)`).  The paper collapses the acyclic core `D`, so that
`H₂(Q(P)) ≅ H₂(Q(P)/D)`, identifies the quotient with a wedge of block complexes, and quotes
property **(B3)** of Theorem 3.2 for each factor.  The wedge step is proved in
`RequestProject/WedgeSigma.lean`; here it is combined with the two inputs the paper quotes —
(B3) and the isomorphism induced by the collapse on second homology — into

* `FiniteChains.isCockcroft_of_collapse_to_wedge` — **if the collapse is injective on
  Hurewicz images and every block factor is Cockcroft, then the complex is Cockcroft**.

The collapse isomorphism and (B3) are exactly the inputs that Lemma 3.10 imports from
Theorem 3.2, just as (B2) is the one input carried by the moves of Lemma 3.9.
-/

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains

open MonoidAlgebra

universe u

/-! ### A map which kills the fundamental group is zero on Hurewicz-trivial chains -/

section Trivial

variable {α J α' J' : Type u} [Fintype α] [DecidableEq α] [Fintype J]
  [Fintype α'] [DecidableEq α'] [Fintype J']
variable {ρ : J → FreeGroup α} {ρ' : J' → FreeGroup α'}

omit [Fintype α] [Fintype α'] in
/-- A structural map commutes with finite sums of two-chains. -/
theorem PresMor.cells_finset_sum {ι : Type u} (f : PresMor ρ ρ') (s : Finset ι)
    (y : ι → (J → MonoidAlgebra ℤ (PresGroup ρ))) :
    f.cells (∑ i ∈ s, y i) = ∑ i ∈ s, f.cells (y i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.sum_insert ha, f.cells_add, ih, Finset.sum_insert ha]

omit [Fintype α] [DecidableEq α] [Fintype J] [Fintype α'] [DecidableEq α'] [Fintype J'] in
/-- If a homomorphism of fundamental groups is trivial, then pushing coefficients along it is
the augmentation: the group ring acts on the target through `ℤ`. -/
theorem mapDomainRingHom_eq_single_augPres (h : PresGroup ρ →* PresGroup ρ')
    (htriv : ∀ g, h g = 1) (c : MonoidAlgebra ℤ (PresGroup ρ)) :
    MonoidAlgebra.mapDomainRingHom ℤ h c = MonoidAlgebra.single 1 (augPres ρ c) := by
  induction c using MonoidAlgebra.induction_linear with
  | zero => simp
  | add x y hx hy => rw [map_add, map_add, hx, hy, MonoidAlgebra.single_add]
  | single g m =>
      show MonoidAlgebra.mapDomain h (MonoidAlgebra.single g m) = _
      rw [MonoidAlgebra.mapDomain_single, htriv g]
      exact congrArg (MonoidAlgebra.single (1 : PresGroup ρ') ·) (augQ_single _ _ _).symm

omit [Fintype α] [Fintype α'] in
/-- **A map which kills the fundamental group is zero on chains with zero Hurewicz image.**
Because the fundamental group of the source acts trivially on the target, the image of a
two-chain is the integer combination, with the augmentations of its coordinates as
coefficients, of the images of the two-cells. -/
theorem cells_eq_zero_of_hom_trivial (f : PresMor ρ ρ') (htriv : ∀ g, f.hom g = 1)
    {y : J → MonoidAlgebra ℤ (PresGroup ρ)} (hy : ∀ j, augPres ρ (y j) = 0) : f.cells y = 0 := by
  classical
  have hdec : y = ∑ j : J, (y j) •
      (Pi.single j (1 : MonoidAlgebra ℤ (PresGroup ρ)) : J → MonoidAlgebra ℤ (PresGroup ρ)) := by
    funext k
    rw [Finset.sum_apply]
    refine Eq.symm ?_
    refine (Finset.sum_eq_single k ?_ ?_).trans ?_
    · intro j _ hjk
      show y j * (Pi.single j (1 : MonoidAlgebra ℤ (PresGroup ρ))
        : J → MonoidAlgebra ℤ (PresGroup ρ)) k = 0
      rw [Pi.single_apply, if_neg (fun h => hjk h.symm), mul_zero]
    · intro hk
      exact absurd (Finset.mem_univ k) hk
    · show y k * (Pi.single k (1 : MonoidAlgebra ℤ (PresGroup ρ))
        : J → MonoidAlgebra ℤ (PresGroup ρ)) k = y k
      rw [Pi.single_apply, if_pos rfl, mul_one]
  rw [hdec, f.cells_finset_sum]
  refine Finset.sum_eq_zero fun j _ => ?_
  rw [f.cells_smul, mapDomainRingHom_eq_single_augPres f.hom htriv, hy j]
  show MonoidAlgebra.single (1 : PresGroup ρ') (0 : ℤ) • _ = 0
  rw [MonoidAlgebra.single_zero, zero_smul]

omit [Fintype α] [Fintype α'] in
/-- **A map out of a Cockcroft complex which kills the fundamental group is zero on `π₂`**
(the observation the paper uses in the first paragraph of the proof of Lemma 3.10), in the
presentation model. -/
theorem cells_eq_zero_of_isCockcroft_of_hom_trivial (f : PresMor ρ ρ') (hP : IsCockcroft ρ)
    (htriv : ∀ g, f.hom g = 1) {v : J → MonoidAlgebra ℤ (PresGroup ρ)} (hv : IsFoxCycle ρ v) :
    f.cells v = 0 :=
  cells_eq_zero_of_hom_trivial f htriv (hP v hv)

omit [Fintype α] [Fintype α'] in
/-- **"Equation (3.3) then makes the inclusion zero on all of `π₂`".**  If the structural map
`η_P` has the generation property and a further map `g` kills the images of the Fox cycles of
`P`, then `g` is zero on the whole of `π₂` of the intermediate complex. -/
theorem cells_eq_zero_of_generates_comp {β K : Type u} [Fintype β] [DecidableEq β] [Fintype K]
    {τ : K → FreeGroup β} (etaP : PresMor ρ τ) (g : PresMor τ ρ') (hgen : Generates etaP)
    (hcomp : ∀ y, IsFoxCycle ρ y → g.cells (etaP.cells y) = 0)
    {v : K → MonoidAlgebra ℤ (PresGroup τ)} (hv : IsFoxCycle τ v) : g.cells v = 0 := by
  set N : Submodule (MonoidAlgebra ℤ (PresGroup τ)) (K → MonoidAlgebra ℤ (PresGroup τ)) :=
    { carrier := {w | g.cells w = 0}
      add_mem' := by
        intro a b ha hb
        simp only [Set.mem_setOf_eq] at ha hb ⊢
        rw [g.cells_add, ha, hb, add_zero]
      zero_mem' := by simp
      smul_mem' := by
        intro c a ha
        simp only [Set.mem_setOf_eq] at ha ⊢
        rw [g.cells_smul, ha, smul_zero] } with hN
  have hle : Submodule.span (MonoidAlgebra ℤ (PresGroup τ))
      {w : K → MonoidAlgebra ℤ (PresGroup τ) | ∃ y, IsFoxCycle ρ y ∧ w = etaP.cells y} ≤ N := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨y, hy, rfl⟩
    exact hcomp y hy
  exact hle (hgen v hv)

omit [Fintype α] [DecidableEq α] [Fintype J] [Fintype α'] [DecidableEq α'] [Fintype J'] in
/-- A homomorphism out of a presented group is trivial as soon as it kills the generators. -/
theorem hom_eq_one_of_gens {H : Type u} [Group H] (h : PresGroup ρ →* H)
    (hgen : ∀ a : α, h (QuotientGroup.mk (FreeGroup.of a)) = 1) (x : PresGroup ρ) : h x = 1 := by
  have hcomp : (h.comp (QuotientGroup.mk' (relSub ρ)) : FreeGroup α →* H) = 1 :=
    FreeGroup.ext_hom _ _ fun a => hgen a
  induction x using QuotientGroup.induction_on with
  | H w => exact congrArg (fun F : FreeGroup α →* H => F w) hcomp

end Trivial

/-! ### The terminal extension: adjoining individual relators -/

section AddRels

variable {α J L : Type u} [Fintype α] [DecidableEq α] [Fintype J] [DecidableEq J]
  [Fintype L] [DecidableEq L]
variable (ρ : J → FreeGroup α) (ν : L → FreeGroup α)

/-- **The terminal extension on presentations**: the relators `ν` (in the paper the letters
`a_z` and `b_z`) are adjoined as further individual relators, the generators being
unchanged. -/
def addRels : J ⊕ L → FreeGroup α := Sum.elim ρ ν

omit [Fintype α] [DecidableEq α] [Fintype J] [DecidableEq J] [Fintype L] [DecidableEq L] in
@[simp] theorem addRels_inl (j : J) : addRels ρ ν (Sum.inl j) = ρ j := rfl

omit [Fintype α] [DecidableEq α] [Fintype J] [DecidableEq J] [Fintype L] [DecidableEq L] in
@[simp] theorem addRels_inr (l : L) : addRels ρ ν (Sum.inr l) = ν l := rfl

omit [Fintype α] [DecidableEq α] [Fintype J] [DecidableEq J] [Fintype L] [DecidableEq L] in
theorem relSub_le_relSub_addRels : relSub ρ ≤ relSub (addRels ρ ν) := by
  refine Subgroup.normalClosure_le_normal ?_
  rintro _ ⟨j, rfl⟩
  exact Subgroup.subset_normalClosure ⟨Sum.inl j, rfl⟩

/-- The homomorphism of fundamental groups induced by the terminal extension. -/
def addRelsHom : PresGroup ρ →* PresGroup (addRels ρ ν) :=
  QuotientGroup.map _ _ (MonoidHom.id _) (by
    intro w hw
    exact Subgroup.mem_comap.2 (relSub_le_relSub_addRels ρ ν hw))

omit [Fintype α] [DecidableEq α] [Fintype J] [DecidableEq J] [Fintype L] [DecidableEq L] in
@[simp] theorem addRelsHom_mk (w : FreeGroup α) :
    addRelsHom ρ ν (QuotientGroup.mk w) = QuotientGroup.mk w := rfl

/-- The induced map of group rings. -/
noncomputable def addRelsRingHom :
    MonoidAlgebra ℤ (PresGroup ρ) →+* MonoidAlgebra ℤ (PresGroup (addRels ρ ν)) :=
  MonoidAlgebra.mapDomainRingHom ℤ (addRelsHom ρ ν)

omit [Fintype α] [DecidableEq α] [Fintype J] [DecidableEq J] [Fintype L] [DecidableEq L] in
/-- Reading an element of `ℤ[F]` in the group ring of the enlarged presentation agrees with
pushing it forward from the group ring of the old one. -/
theorem quot_addRelsRingHom (x : FreeGroupRing α) :
    quotRingHom ℤ (relSub (addRels ρ ν)) x = addRelsRingHom ρ ν (quotRingHom ℤ (relSub ρ) x) := by
  induction x using MonoidAlgebra.induction_linear with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | single w m =>
      rw [quotRingHom_single]
      show _ = MonoidAlgebra.mapDomain (addRelsHom ρ ν) (quotRingHom ℤ (relSub ρ) (single w m))
      rw [quotRingHom_single, MonoidAlgebra.mapDomain_single, addRelsHom_mk]

omit [Fintype α] [Fintype J] [DecidableEq J] [Fintype L] [DecidableEq L] in
/-- On the old two-cells the Fox matrix of the enlarged presentation is the image of the old
Fox matrix. -/
theorem foxMatrix_addRels_inl (i : α) (j : J) :
    foxMatrixPres (addRels ρ ν) i (Sum.inl j) = addRelsRingHom ρ ν (foxMatrixPres ρ i j) :=
  quot_addRelsRingHom ρ ν (fox i (ρ j))

omit [Fintype α] [DecidableEq α] [Fintype J] [DecidableEq J] [Fintype L] [DecidableEq L] in
/-- The augmentation is unchanged by the terminal extension. -/
theorem augPres_addRelsRingHom (z : MonoidAlgebra ℤ (PresGroup ρ)) :
    augPres (addRels ρ ν) (addRelsRingHom ρ ν z) = augPres ρ z :=
  augQ_mapDomain (addRelsHom ρ ν) z

/-- The map on two-chains induced by the terminal extension: the old coefficients are read in
the new group ring, and the new two-cells receive the coefficient `0`. -/
noncomputable def addRelsCells (y : J → MonoidAlgebra ℤ (PresGroup ρ)) :
    J ⊕ L → MonoidAlgebra ℤ (PresGroup (addRels ρ ν)) :=
  Sum.elim (fun j => addRelsRingHom ρ ν (y j)) (fun _ => 0)

omit [Fintype α] [DecidableEq J] [DecidableEq L] in
theorem isFoxCycle_addRelsCells {y : J → MonoidAlgebra ℤ (PresGroup ρ)} (hy : IsFoxCycle ρ y) :
    IsFoxCycle (addRels ρ ν) (addRelsCells ρ ν y) := by
  intro i
  rw [Fintype.sum_sum_type]
  have hL : ∑ l : L, addRelsCells ρ ν y (Sum.inr l) * foxMatrixPres (addRels ρ ν) i (Sum.inr l)
      = 0 := by
    refine Finset.sum_eq_zero fun l _ => ?_
    show (0 : MonoidAlgebra ℤ (PresGroup (addRels ρ ν))) * _ = 0
    rw [zero_mul]
  have hJ : ∀ j : J, addRelsCells ρ ν y (Sum.inl j) * foxMatrixPres (addRels ρ ν) i (Sum.inl j)
      = addRelsRingHom ρ ν (y j * foxMatrixPres ρ i j) := by
    intro j
    rw [foxMatrix_addRels_inl, map_mul]
    rfl
  rw [hL, add_zero, Finset.sum_congr rfl fun j _ => hJ j, ← map_sum, hy i, map_zero]

/-- **The terminal extension as a structural map.**  This is the inclusion `T(P) ⊂ Q(P)` of
Lemma 3.10 together with its effect on two-chains. -/
noncomputable def addRelsMor : PresMor ρ (addRels ρ ν) where
  hom := addRelsHom ρ ν
  cells := addRelsCells ρ ν
  cells_add := by
    intro y z
    funext p
    cases p with
    | inl j => exact map_add (addRelsRingHom ρ ν) _ _
    | inr l => show (0 : MonoidAlgebra ℤ (PresGroup (addRels ρ ν))) = 0 + 0; rw [add_zero]
  cells_smul := by
    intro c y
    funext p
    cases p with
    | inl j => exact map_mul (addRelsRingHom ρ ν) c (y j)
    | inr l => show (0 : MonoidAlgebra ℤ (PresGroup (addRels ρ ν))) = _ * 0; rw [mul_zero]
  cells_cycle := fun _ hy => isFoxCycle_addRelsCells ρ ν hy
  cells_aug := by
    intro y hy p
    cases p with
    | inl j =>
        show augPres (addRels ρ ν) (addRelsRingHom ρ ν (y j)) = 0
        rw [augPres_addRelsRingHom, hy j]
    | inr l => show augPres (addRels ρ ν) 0 = 0; rw [map_zero]

omit [Fintype α] [DecidableEq J] [DecidableEq L] in
@[simp] theorem addRelsMor_hom_mk (w : FreeGroup α) :
    (addRelsMor ρ ν).hom (QuotientGroup.mk w) = QuotientGroup.mk w := rfl

omit [Fintype α] [DecidableEq α] [Fintype J] [DecidableEq J] [Fintype L] [DecidableEq L] in
/-- The adjoined relators are trivial in the enlarged group. -/
theorem addRels_mk_eq_one (l : L) :
    (QuotientGroup.mk (ν l) : PresGroup (addRels ρ ν)) = 1 :=
  (QuotientGroup.eq_one_iff _).2 (Subgroup.subset_normalClosure ⟨Sum.inr l, rfl⟩)

omit [Fintype α] [DecidableEq α] [Fintype J] [DecidableEq J] [Fintype L] [DecidableEq L] in
/-- The old relators are trivial in the enlarged group. -/
theorem addRels_mk_rel_eq_one (j : J) :
    (QuotientGroup.mk (ρ j) : PresGroup (addRels ρ ν)) = 1 :=
  (QuotientGroup.eq_one_iff _).2 (Subgroup.subset_normalClosure ⟨Sum.inl j, rfl⟩)

end AddRels

/-! ### The terminal extension of a point of the space of presentations -/

namespace PresPoint

/-- **The terminal extension `Q(P)`**: the presentation `P` together with the further
individual relators `ν` (in the paper, the letters `a_z` and `b_z`). -/
def addRels (P : PresPoint.{u}) {L : Type u} [Fintype L] [DecidableEq L]
    (ν : L → FreeGroup P.gens) : PresPoint.{u} where
  gens := P.gens
  cells := P.cells ⊕ L
  rel := FiniteChains.addRels P.rel ν

end PresPoint

/-! ### Lemma 3.10 -/

section Terminal

variable {P Q : PresPoint.{u}} {L : Type u} [Fintype L] [DecidableEq L]

omit [DecidableEq L] in
/-- **The core group remains trivial in both new groups** (the first sentence of the proof of
Lemma 3.10): the structural map and the terminal extension fix the generators, so a generator
which is already trivial in `G(P)` stays trivial in `G(T(P))` and in `G(Q(P))`. -/
theorem terminal_core_trivial (t : TPath P Q) (ν : L → FreeGroup Q.gens) (x : P.gens)
    (hx : (QuotientGroup.mk (FreeGroup.of x) : PresGroup P.rel) = 1) :
    t.mor.hom (QuotientGroup.mk (FreeGroup.of x)) = 1 ∧
      (addRelsMor Q.rel ν).hom (t.mor.hom (QuotientGroup.mk (FreeGroup.of x))) = 1 := by
  have h : t.mor.hom (QuotientGroup.mk (FreeGroup.of x)) = 1 := by rw [hx, map_one]
  exact ⟨h, by rw [h, map_one]⟩

omit [DecidableEq L] in
/-- **`T(P) ⊂ Q(P)` is zero on `π₂`** — the main assertion of Lemma 3.10.

The hypotheses are exactly those of the paper: `P` is Cockcroft, and the composite
`P → T(P) → Q(P)` kills `G(P)`, which the paper checks on the generators (the core generators
`x_i` are trivial in `G(P)` by assumption, and every extra generator becomes a commutator of
two capped loops, hence dies in `Q(P)`).  The proof is the paper's: the composite is zero on
`π₂` because its source is Cockcroft and it kills the fundamental group, and equation (3.3)
for `T` then propagates this from the image of `π₂(P)` to the whole of `π₂(T(P))`. -/
theorem terminal_cells_eq_zero (t : TPath P Q) (ν : L → FreeGroup Q.gens)
    (hP : IsCockcroft P.rel)
    (hkill : ∀ a : P.gens,
      (addRelsMor Q.rel ν).hom (t.mor.hom (QuotientGroup.mk (FreeGroup.of a))) = 1)
    {v : Q.cells → MonoidAlgebra ℤ (PresGroup Q.rel)} (hv : IsFoxCycle Q.rel v) :
    (addRelsMor Q.rel ν).cells v = 0 := by
  have htriv : ∀ g : PresGroup P.rel, ((addRelsMor Q.rel ν).comp t.mor).hom g = 1 :=
    hom_eq_one_of_gens _ hkill
  refine cells_eq_zero_of_generates_comp t.mor (addRelsMor Q.rel ν) t.generates ?_ hv
  intro y hy
  exact cells_eq_zero_of_isCockcroft_of_hom_trivial ((addRelsMor Q.rel ν).comp t.mor) hP htriv hy

end Terminal

/-! ### Cockcroftness of the terminal extension -/

section Collapse

variable {γ M : Type u} [Fintype γ] [DecidableEq γ] [Fintype M] {σ : M → FreeGroup γ}
variable {S : Type u} [Fintype S] [DecidableEq S] {β K : S → Type u}
  [∀ s, Fintype (β s)] [∀ s, DecidableEq (β s)] [∀ s, Fintype (K s)]

omit [Fintype γ] [∀ s, Fintype (β s)] in
/-- **Cockcroftness of the terminal extension** (the second half of the proof of Lemma 3.10).

The paper collapses the acyclic core `D`, obtains an isomorphism `H₂(Q(P)) ≅ H₂(Q(P)/D)`,
identifies the quotient with the wedge `⋁_r K⟨Z_r | β_{q(r),j}(1,…,1,Z_r)⟩`, and quotes
property (B3) for each factor.  Formalized: `kappa` is the map induced by the collapse,
`hinj` says that it is injective on Hurewicz images (the isomorphism on `H₂`), and `hB3` is
property (B3) for the factors.  The wedge step — "a wedge of Cockcroft complexes is
Cockcroft" — is `FiniteChains.isCockcroft_sigmaWedgeRel`, proved in this development. -/
theorem isCockcroft_of_collapse_to_wedge (blk : ∀ s, K s → FreeGroup (β s))
    (hB3 : ∀ s, IsCockcroft (blk s)) (kappa : PresMor σ (sigmaWedgeRel blk))
    (hinj : ∀ v, IsFoxCycle σ v →
      (∀ p, augPres (sigmaWedgeRel blk) (kappa.cells v p) = 0) → ∀ m, augPres σ (v m) = 0) :
    IsCockcroft σ := fun v hv m =>
  hinj v hv
    (fun p => isCockcroft_sigmaWedgeRel blk hB3 (kappa.cells v) (kappa.cells_cycle v hv) p) m

end Collapse

/-! ### Lemma 3.10 -/

section Statement

variable {P Q : PresPoint.{u}} {L : Type u} [Fintype L] [DecidableEq L]
variable {S : Type u} [Fintype S] [DecidableEq S] {β K : S → Type u}
  [∀ s, Fintype (β s)] [∀ s, DecidableEq (β s)] [∀ s, Fintype (K s)]

omit [DecidableEq L] [∀ s, Fintype (β s)] in
/-- **Lemma 3.10.**  Let `P` be Cockcroft, let `T` be the structural operation of Lemma 3.9
(a finite sequence `t` of elementary moves) and let `Q(P)` be the terminal extension, which
adjoins the letters `ν` (the `a_z` and `b_z`) as individual relators.  Assume, as in the
paper, that the composite `P → T(P) → Q(P)` kills every generator of `P` (`hkill`: the core
generators are trivial in `G(P)` already, and each extra generator becomes a commutator of
two capped loops, which `Q` kills), and that the collapse of the acyclic core identifies the
Hurewicz images of `Q(P)` with those of a wedge of block complexes (`kappa`, `hinj`) each of
which is Cockcroft by property (B3) (`hB3`).  Then:

* `Q(P)` is Cockcroft;
* the inclusion `T(P) ⊂ Q(P)` is zero on the whole of `π₂(T(P))`;
* a core generator which is trivial in `G(P)` stays trivial in `G(T(P))` and in `G(Q(P))`. -/
theorem lemma_terminal (t : TPath P Q) (ν : L → FreeGroup Q.gens) (hP : IsCockcroft P.rel)
    (hkill : ∀ a : P.gens,
      (addRelsMor Q.rel ν).hom (t.mor.hom (QuotientGroup.mk (FreeGroup.of a))) = 1)
    (blk : ∀ s, K s → FreeGroup (β s)) (hB3 : ∀ s, IsCockcroft (blk s))
    (kappa : PresMor (addRels Q.rel ν) (sigmaWedgeRel blk))
    (hinj : ∀ v, IsFoxCycle (addRels Q.rel ν) v →
      (∀ p, augPres (sigmaWedgeRel blk) (kappa.cells v p) = 0) →
      ∀ m, augPres (addRels Q.rel ν) (v m) = 0) :
    IsCockcroft (addRels Q.rel ν) ∧
      (∀ v : Q.cells → MonoidAlgebra ℤ (PresGroup Q.rel), IsFoxCycle Q.rel v →
        (addRelsMor Q.rel ν).cells v = 0) ∧
      (∀ x : P.gens, (QuotientGroup.mk (FreeGroup.of x) : PresGroup P.rel) = 1 →
        t.mor.hom (QuotientGroup.mk (FreeGroup.of x)) = 1 ∧
          (addRelsMor Q.rel ν).hom (t.mor.hom (QuotientGroup.mk (FreeGroup.of x))) = 1) :=
  ⟨isCockcroft_of_collapse_to_wedge blk hB3 kappa hinj,
    fun _ hv => terminal_cells_eq_zero t ν hP hkill hv,
    fun x hx => terminal_core_trivial t ν x hx⟩

end Statement

/-! ### Rule 1 with one extra generator: the terminal extension without any hypothesis -/

section RuleOne

variable (P : PresPoint.{u}) (zg : P.gens)

/-- The two individual relators of the terminal extension after rule 1 for one extra
generator: the stable letter `a` and the freely adjoined letter `b`. -/
def ruleOneKill :
    ULift.{u} Bool → FreeGroup (P.free.ext (ruleOneRelator P (FreeGroup.of zg))).gens
  | ⟨false⟩ => FreeGroup.of none
  | ⟨true⟩ => FreeGroup.of (some none)

/-- In the terminal extension the stable letter `a` dies. -/
theorem ruleOneKill_a_eq_one :
    (QuotientGroup.mk (FreeGroup.of (none :
        (P.free.ext (ruleOneRelator P (FreeGroup.of zg))).gens)) :
      PresGroup (addRels (P.free.ext (ruleOneRelator P (FreeGroup.of zg))).rel
        (ruleOneKill P zg))) = 1 :=
  addRels_mk_eq_one _ (ruleOneKill P zg) ⟨false⟩

/-- In the terminal extension the freely adjoined letter `b` dies. -/
theorem ruleOneKill_b_eq_one :
    (QuotientGroup.mk (FreeGroup.of (some none :
        (P.free.ext (ruleOneRelator P (FreeGroup.of zg))).gens)) :
      PresGroup (addRels (P.free.ext (ruleOneRelator P (FreeGroup.of zg))).rel
        (ruleOneKill P zg))) = 1 :=
  addRels_mk_eq_one _ (ruleOneKill P zg) ⟨true⟩

/-- **The extra generator dies in the terminal extension.**  The stable-letter relator says
`a b a⁻¹ = z b`; since `a` and `b` are killed by `Q`, so is `z`.  This is the paper's "every
extra generator maps to a commutator of two capped loops". -/
theorem ruleOne_extra_eq_one :
    (QuotientGroup.mk (FreeGroup.of (some (some zg) :
        (P.free.ext (ruleOneRelator P (FreeGroup.of zg))).gens)) :
      PresGroup (addRels (P.free.ext (ruleOneRelator P (FreeGroup.of zg))).rel
        (ruleOneKill P zg))) = 1 := by
  set R := P.free.ext (ruleOneRelator P (FreeGroup.of zg)) with hR
  set ν := ruleOneKill P zg with hnu
  set pr := QuotientGroup.mk' (relSub (addRels R.rel ν)) with hpr
  have ha : pr (FreeGroup.of (none : R.gens)) = 1 := ruleOneKill_a_eq_one P zg
  have hb : pr (FreeGroup.of (some none : R.gens)) = 1 := ruleOneKill_b_eq_one P zg
  have hrel : pr (R.rel none) = 1 := addRels_mk_rel_eq_one R.rel ν none
  have hword : R.rel none = ruleOneRelator P (FreeGroup.of zg) := rfl
  rw [hword, ruleOneRelator, hnnWord] at hrel
  simp only [map_mul, map_inv, FreeGroup.map.of, ha, hb, one_mul, mul_one, inv_one] at hrel
  exact inv_eq_one.1 hrel

/-- **Lemma 3.10 for rule 1 with one extra generator, with no further hypothesis.**

`P` is Cockcroft and all its generators except the extra one `z` are trivial in `G(P)`; `T` is
rule 1 for `z` (freely adjoin `b`, adjoin the stable letter `a` with `a b a⁻¹ = z b`) and
`Q(P)` adjoins `a` and `b` as individual relators.  Then the inclusion `T(P) ⊂ Q(P)` is zero
on the whole of `π₂(T(P))`. -/
theorem terminal_cells_eq_zero_ruleOne (hP : IsCockcroft P.rel)
    (hcore : ∀ x : P.gens, x ≠ zg → (QuotientGroup.mk (FreeGroup.of x) : PresGroup P.rel) = 1)
    {v : (P.free.ext (ruleOneRelator P (FreeGroup.of zg))).cells →
      MonoidAlgebra ℤ (PresGroup (P.free.ext (ruleOneRelator P (FreeGroup.of zg))).rel)}
    (hv : IsFoxCycle (P.free.ext (ruleOneRelator P (FreeGroup.of zg))).rel v) :
    (addRelsMor (P.free.ext (ruleOneRelator P (FreeGroup.of zg))).rel (ruleOneKill P zg)).cells v
      = 0 := by
  refine terminal_cells_eq_zero (ruleOnePath P (FreeGroup.of zg)) (ruleOneKill P zg) hP ?_ hv
  intro a
  by_cases hazg : a = zg
  · subst hazg
    have h : (ruleOnePath P (FreeGroup.of a)).mor.hom
        (QuotientGroup.mk (FreeGroup.of a)) =
        QuotientGroup.mk (FreeGroup.of (some (some a) :
          (P.free.ext (ruleOneRelator P (FreeGroup.of a))).gens)) := rfl
    rw [h]
    exact ruleOne_extra_eq_one P a
  · rw [hcore a hazg, map_one, map_one]

end RuleOne

/-! ### The hypotheses are satisfiable -/

section Example

/-- The presentation `⟨z | ⟩` with one generator and no relator. -/
def freeOnePres : PresPoint.{u} where
  gens := PUnit.{u + 1}
  cells := PEmpty.{u + 1}
  rel := fun e => e.elim

/-- It is Cockcroft, there being no two-cells at all. -/
theorem isCockcroft_freeOnePres : IsCockcroft freeOnePres.{u}.rel := fun _ _ j => j.elim

/-- **The situation of Lemma 3.10 occurs**: for `P = ⟨z | ⟩`, rule 1 for the single extra
generator `z` and the terminal extension which kills `a` and `b`, the inclusion
`T(P) ⊂ Q(P)` is zero on the whole of `π₂(T(P))`, with no hypothesis at all. -/
theorem terminal_cells_eq_zero_freeOne
    {v : (freeOnePres.{u}.free.ext
        (ruleOneRelator freeOnePres.{u} (FreeGroup.of PUnit.unit))).cells →
      MonoidAlgebra ℤ (PresGroup (freeOnePres.{u}.free.ext
        (ruleOneRelator freeOnePres.{u} (FreeGroup.of PUnit.unit))).rel)}
    (hv : IsFoxCycle (freeOnePres.{u}.free.ext
      (ruleOneRelator freeOnePres.{u} (FreeGroup.of PUnit.unit))).rel v) :
    (addRelsMor (freeOnePres.{u}.free.ext
      (ruleOneRelator freeOnePres.{u} (FreeGroup.of PUnit.unit))).rel
        (ruleOneKill freeOnePres.{u} PUnit.unit)).cells v = 0 :=
  terminal_cells_eq_zero_ruleOne freeOnePres PUnit.unit isCockcroft_freeOnePres
    (fun x hx => absurd (rfl : (x : PUnit.{u + 1}) = PUnit.unit) hx) hv

end Example

end FiniteChains
