import RequestProject.BlockFamilySubst
import RequestProject.FoxFinsupp

/-!
Arbitrary-family assembly of the block-local surface-generation statement.

The block family, retained relators, and the relators of an individual block
may all be infinite. Every chain below is finitely supported in its cell
indices as well as in its group coefficients. In particular, the polygon
coefficients are chosen to be zero outside the blocks occupied by the input
chain. This is the support argument missing from the finite-family assembly.

The geometric block-local B2 statement remains an explicit hypothesis. The
results here construct its global chain preimage and the cancelling-cylinder
relative filling; they do not assume global generation or relative exactness.

This new source has not been compiled under the current no-checkpoint workflow.
-/

noncomputable section

namespace FiniteChains.BlockFamily

universe u

section Chains

variable {Jr Sx R : Type u} {Mt : Sx → Type u} [Ring R]

/-- The part of a two-chain supported on the substituted blocks. -/
def fsBlockPart (x : (Jr ⊕ (Σ s, Mt s)) →₀ R) : (Σ s, Mt s) →₀ R :=
  x.comapDomain Sum.inr Sum.inr_injective.injOn

/-- The actual finitely supported chain in one block. -/
def fsBlockSlice (x : (Jr ⊕ (Σ s, Mt s)) →₀ R) (s : Sx) : Mt s →₀ R :=
  (fsBlockPart x).split s

@[simp] theorem fsBlockSlice_apply (x : (Jr ⊕ (Σ s, Mt s)) →₀ R)
    (s : Sx) (m : Mt s) : fsBlockSlice x s m = x (Sum.inr ⟨s, m⟩) := rfl

/-- Only the finitely many occupied block labels are needed for coefficients. -/
def fsBlockSupport (x : (Jr ⊕ (Σ s, Mt s)) →₀ R) : Finset Sx :=
  (fsBlockPart x).splitSupport

theorem fsBlockSlice_eq_zero_of_not_mem (x : (Jr ⊕ (Σ s, Mt s)) →₀ R)
    {s : Sx} (hs : s ∉ fsBlockSupport x) : fsBlockSlice x s = 0 := by
  by_contra h
  exact hs ((Finsupp.mem_splitSupport_iff_nonzero (fsBlockPart x) s).mpr h)

/-- A finitely supported family of polygon coefficients expands along the
actual finitely supported surface chains. -/
def fsFillBlocks (c : ∀ s, Mt s →₀ R) (w : Sx →₀ R) : (Σ s, Mt s) →₀ R := by
  classical
  refine Finsupp.onFinset (w.support.sigma fun s => (c s).support)
    (fun p => w p.1 * c p.1 p.2) ?_
  intro p hp
  apply Finset.mem_sigma.mpr
  constructor
  · apply Finsupp.mem_support_iff.mpr
    intro hw
    exact hp (by change w p.1 * c p.1 p.2 = 0; rw [hw, zero_mul])
  · apply Finsupp.mem_support_iff.mpr
    intro hc
    exact hp (by change w p.1 * c p.1 p.2 = 0; rw [hc, mul_zero])

@[simp] theorem fsFillBlocks_apply (c : ∀ s, Mt s →₀ R) (w : Sx →₀ R)
    (p : Σ s, Mt s) : fsFillBlocks c w p = w p.1 * c p.1 p.2 := rfl

/-- The substituted two-chain map after extending coefficients to the target
ring: retain old cells and replace each polygon by its chosen surface chain. -/
def fsCellsBase (c : ∀ s, Mt s →₀ R) :
    ((Jr ⊕ Sx) →₀ R) →ₗ[R] ((Jr ⊕ (Σ s, Mt s)) →₀ R) where
  toFun y := Finsupp.sumElim
    (y.comapDomain Sum.inl Sum.inl_injective.injOn)
    (fsFillBlocks c (y.comapDomain Sum.inr Sum.inr_injective.injOn))
  map_add' y z := by
    ext k
    cases k with
    | inl j => rfl
    | inr p =>
        change (y (Sum.inr p.1) + z (Sum.inr p.1)) * c p.1 p.2 = _
        exact add_mul _ _ _
  map_smul' a y := by
    ext k
    cases k with
    | inl j => rfl
    | inr p =>
        change (a * y (Sum.inr p.1)) * c p.1 p.2 =
          a * (y (Sum.inr p.1) * c p.1 p.2)
        exact mul_assoc _ _ _

@[simp] theorem fsCellsBase_inl (c : ∀ s, Mt s →₀ R)
    (y : (Jr ⊕ Sx) →₀ R) (j : Jr) :
    fsCellsBase c y (Sum.inl j) = y (Sum.inl j) := rfl

@[simp] theorem fsCellsBase_inr (c : ∀ s, Mt s →₀ R)
    (y : (Jr ⊕ Sx) →₀ R) (s : Sx) (m : Mt s) :
    fsCellsBase c y (Sum.inr ⟨s, m⟩) = y (Sum.inr s) * c s m := rfl

/-- Local witnesses can be selected with finite support, even if zero blocks
admit nonzero scalar witnesses. Thus no injectivity of a surface chain is
needed to obtain finitely supported polygon coefficients. -/
theorem exists_fsBlockCoefficients (c : ∀ s, Mt s →₀ R)
    (x : (Jr ⊕ (Σ s, Mt s)) →₀ R)
    (h : ∀ s, ∃ a : R, ∀ m, x (Sum.inr ⟨s, m⟩) = a * c s m) :
    ∃ w : Sx →₀ R, w.support ⊆ fsBlockSupport x ∧
      ∀ s m, x (Sum.inr ⟨s, m⟩) = w s * c s m := by
  classical
  choose a ha using h
  let w : Sx →₀ R := Finsupp.onFinset (fsBlockSupport x)
    (fun s => if s ∈ fsBlockSupport x then a s else 0)
    (by intro s hs; by_contra hn; exact hs (if_neg hn))
  refine ⟨w, Finsupp.support_onFinset_subset, ?_⟩
  intro s m
  by_cases hs : s ∈ fsBlockSupport x
  · simpa only [w, Finsupp.onFinset_apply, if_pos hs] using ha s m
  · have hz := congrArg (fun b : Mt s →₀ R => b m)
      (fsBlockSlice_eq_zero_of_not_mem x hs)
    simpa only [fsBlockSlice_apply, Finsupp.zero_apply, w,
      Finsupp.onFinset_apply, if_neg hs, zero_mul] using hz

/-- Assemble the local surface coefficients and the retained coefficients into
an actual preimage of the full substituted two-chain. -/
theorem exists_fsCellsBase_preimage (c : ∀ s, Mt s →₀ R)
    (x : (Jr ⊕ (Σ s, Mt s)) →₀ R)
    (h : ∀ s, ∃ a : R, ∀ m, x (Sum.inr ⟨s, m⟩) = a * c s m) :
    ∃ y : (Jr ⊕ Sx) →₀ R, fsCellsBase c y = x ∧
      (∀ j, y (Sum.inl j) = x (Sum.inl j)) ∧
      (y.comapDomain Sum.inr Sum.inr_injective.injOn).support ⊆ fsBlockSupport x := by
  obtain ⟨w, hw, he⟩ := exists_fsBlockCoefficients c x h
  let y : (Jr ⊕ Sx) →₀ R :=
    Finsupp.sumElim (x.comapDomain Sum.inl Sum.inl_injective.injOn) w
  refine ⟨y, ?_, fun _ => rfl, ?_⟩
  · ext k
    cases k with
    | inl j => rfl
    | inr p => exact (he p.1 p.2).symm
  · have hy : y.comapDomain Sum.inr Sum.inr_injective.injOn = w := by
      ext s
      rfl
    rw [hy]
    exact hw

/-- Include the old two-chains into the double-cylinder two-chains. -/
def fsInclModel (c : ∀ s, Mt s →₀ R) :
    ((Jr ⊕ Sx) →₀ R) →ₗ[R]
      (((Jr ⊕ (Σ s, Mt s)) →₀ R) × (Sx →₀ R)) :=
  (fsCellsBase c).prod 0

/-- Each polygon-cylinder has boundary its actual block filling minus the
old polygon. The family of such three-chains is finitely supported. -/
def fsCylinderBoundary (c : ∀ s, Mt s →₀ R) (q : Sx →₀ R) :
    ((Jr ⊕ (Σ s, Mt s)) →₀ R) × (Sx →₀ R) :=
  (fsCellsBase c (Finsupp.sumElim 0 q), -q)

/-- Relative two-chains modulo the actual image of the old two-chains. -/
abbrev FSRelativeTwo (c : ∀ s, Mt s →₀ R) :=
  (((Jr ⊕ (Σ s, Mt s)) →₀ R) × (Sx →₀ R)) ⧸ (fsInclModel c).range

/-- A global preimage gives the exact cylinder filling in the relative
quotient. This is an equality of actual chain classes with its signs fixed. -/
theorem fsCylinderClass_eq_of_preimage (c : ∀ s, Mt s →₀ R)
    (x : (Jr ⊕ (Σ s, Mt s)) →₀ R) (q : Sx →₀ R)
    (h : ∃ a : (Jr ⊕ Sx) →₀ R, fsCellsBase c a = x) :
    (Submodule.Quotient.mk (fsCylinderBoundary c (-q)) : FSRelativeTwo (Jr := Jr) c) =
      Submodule.Quotient.mk (x, q) := by
  obtain ⟨a, ha⟩ := h
  rw [Submodule.Quotient.eq]
  refine ⟨Finsupp.sumElim 0 (-q) - a, ?_⟩
  apply Prod.ext
  · change fsCellsBase c (Finsupp.sumElim 0 (-q) - a) =
      fsCellsBase c (Finsupp.sumElim 0 (-q)) - x
    rw [map_sub, ha]
  · change 0 = -(-q) - q
    simp

end Chains

section Fox

variable {α Jr Sx : Type u} {Zt Mt : Sx → Type u}
  [DecidableEq α] [DecidableEq Sx] [∀ s, DecidableEq (Zt s)]
  (ρ : Jr ⊕ Sx → FreeGroup α)
  (bsub : ∀ s, Mt s → FreeGroup (α ⊕ Zt s))

local notation "R'" => MonoidAlgebra ℤ (PresGroup (substPresF ρ bsub))

/-- The existing genuine finitely supported Fox boundary, in matrix coordinates. -/
theorem fsCoverSecondBoundary_apply {A J : Type u} [DecidableEq A]
    (σ : J → FreeGroup A) (x : J →₀ MonoidAlgebra ℤ (PresGroup σ)) (i : A) :
    coverSecondBoundary (relSub σ) σ x i =
      x.sum (fun j a => a * foxMatrixPres σ i j) := by
  classical
  simp only [coverSecondBoundary, Finsupp.linearCombination_apply, Finsupp.sum,
    Finsupp.finset_sum_apply, Finsupp.smul_apply, smul_eq_mul]
  rfl

/-- Internal coordinates of the actual substituted Fox boundary see exactly
one block, with a finite sum even for an infinite block-relator set. -/
theorem fsCoverSecondBoundary_inr
    (x : (Jr ⊕ (Σ s, Mt s)) →₀ R') (s : Sx) (z : Zt s) :
    coverSecondBoundary (relSub (substPresF ρ bsub)) (substPresF ρ bsub) x
        (Sum.inr ⟨s, z⟩) =
      (fsBlockSlice x s).sum (fun m a => a *
        foxMatrixPres (substPresF ρ bsub) (Sum.inr ⟨s, z⟩) (Sum.inr ⟨s, m⟩)) := by
  classical
  rw [fsCoverSecondBoundary_apply]
  let old := x.comapDomain Sum.inl Sum.inl_injective.injOn
  let blocks := fsBlockPart x
  have hx : x = Finsupp.sumElim old blocks := by
    ext k
    cases k <;> rfl
  have ho : old.sum (fun j a => a *
      foxMatrixPres (substPresF ρ bsub) (Sum.inr ⟨s, z⟩) (Sum.inl j)) = 0 := by
    simp [foxMatrix_inr_inl ρ bsub]
  calc
    x.sum (fun k a => a * foxMatrixPres (substPresF ρ bsub) (Sum.inr ⟨s, z⟩) k) =
        old.sum (fun j a => a *
          foxMatrixPres (substPresF ρ bsub) (Sum.inr ⟨s, z⟩) (Sum.inl j)) +
        blocks.sum (fun p a => a *
          foxMatrixPres (substPresF ρ bsub) (Sum.inr ⟨s, z⟩) (Sum.inr p)) := by
      rw [hx, Finsupp.sum_sumElim]
      rfl
    _ = blocks.sum (fun p a => a *
        foxMatrixPres (substPresF ρ bsub) (Sum.inr ⟨s, z⟩) (Sum.inr p)) := by
      rw [ho, zero_add]
    _ = (fsBlockSlice x s).sum (fun m a => a *
        foxMatrixPres (substPresF ρ bsub) (Sum.inr ⟨s, z⟩) (Sum.inr ⟨s, m⟩)) := by
      rw [Finsupp.sigma_sum]
      change (∑ t ∈ blocks.splitSupport, (blocks.split t).sum (fun m a => a *
          foxMatrixPres (substPresF ρ bsub) (Sum.inr ⟨s, z⟩) (Sum.inr ⟨t, m⟩))) =
        (blocks.split s).sum (fun m a => a *
          foxMatrixPres (substPresF ρ bsub) (Sum.inr ⟨s, z⟩) (Sum.inr ⟨s, m⟩))
      apply Finset.sum_eq_single s
      · intro t _ hts
        simp [foxMatrix_inr_inr_of_ne ρ bsub hts z]
      · intro hs
        have hz : blocks.split s = 0 := by
          by_contra h
          exact hs ((Finsupp.mem_splitSupport_iff_nonzero blocks s).mpr h)
        simp [hz]

/-- The geometric block-local B2 input, with genuine finite support in the
block relators and coefficients in the whole substituted presentation group. -/
def BlockSurfaceGeneratesFS (c : ∀ s, Mt s →₀ R') : Prop :=
  ∀ (s : Sx) (β : Mt s →₀ R'),
    (∀ z : Zt s, β.sum (fun m a => a *
      foxMatrixPres (substPresF ρ bsub) (Sum.inr ⟨s, z⟩) (Sum.inr ⟨s, m⟩)) = 0) →
    ∃ w : R', ∀ m, β m = w * c s m

/-- A finite-block geometric B2 calculation feeds the arbitrary-family
assembly directly. Only each individual block's relator set is finite;
the ambient family and the retained presentation have no finiteness bound. -/
theorem blockSurfaceGeneratesFS_of_finite_blocks [∀ s, Fintype (Mt s)]
    (c : ∀ s, Mt s →₀ R')
    (hblock : ∀ (s : Sx) (β : Mt s → R'),
      (∀ z : Zt s, ∑ m : Mt s, β m *
        foxMatrixPres (substPresF ρ bsub) (Sum.inr ⟨s, z⟩) (Sum.inr ⟨s, m⟩) = 0) →
      ∃ w : R', ∀ m, β m = w * c s m) :
    BlockSurfaceGeneratesFS ρ bsub c := by
  intro s β hβ
  apply hblock s β
  intro z
  rw [← Finsupp.sum_fintype β
    (fun m a => a * foxMatrixPres (substPresF ρ bsub)
      (Sum.inr ⟨s, z⟩) (Sum.inr ⟨s, m⟩)) (fun _ => zero_mul _)]
  exact hβ z

/-- Block-local B2 supplies a finite global preimage for every chain whose
actual Fox boundary lies entirely on the old generators. No finite-family
assumption and no global generation hypothesis is used. -/
theorem fsCellsBase_preimage_of_internal_zero (c : ∀ s, Mt s →₀ R')
    (hblock : BlockSurfaceGeneratesFS ρ bsub c)
    (x : (Jr ⊕ (Σ s, Mt s)) →₀ R')
    (hx : ∀ (s : Sx) (z : Zt s),
      coverSecondBoundary (relSub (substPresF ρ bsub)) (substPresF ρ bsub) x
        (Sum.inr ⟨s, z⟩) = 0) :
    ∃ y : (Jr ⊕ Sx) →₀ R', fsCellsBase c y = x ∧
      (∀ j, y (Sum.inl j) = x (Sum.inl j)) ∧
      (y.comapDomain Sum.inr Sum.inr_injective.injOn).support ⊆ fsBlockSupport x := by
  apply exists_fsCellsBase_preimage c x
  intro s
  apply hblock s (fsBlockSlice x s)
  intro z
  rw [← fsCoverSecondBoundary_inr ρ bsub]
  exact hx s z

/-- The family relative-cycle filling follows from block-local B2. The
three-chain is the negative polygon part of the given representative, and
the residual old two-chain is constructed with finite support above. -/
theorem fsRelativeClass_fills_of_internal_zero (c : ∀ s, Mt s →₀ R')
    (hblock : BlockSurfaceGeneratesFS ρ bsub c)
    (x : ((Jr ⊕ (Σ s, Mt s)) →₀ R') × (Sx →₀ R'))
    (hx : ∀ (s : Sx) (z : Zt s),
      coverSecondBoundary (relSub (substPresF ρ bsub)) (substPresF ρ bsub) x.1
        (Sum.inr ⟨s, z⟩) = 0) :
    (Submodule.Quotient.mk (fsCylinderBoundary c (-x.2)) : FSRelativeTwo (Jr := Jr) c) =
      Submodule.Quotient.mk x := by
  obtain ⟨a, ha, _, _⟩ := fsCellsBase_preimage_of_internal_zero ρ bsub c hblock x.1 hx
  exact fsCylinderClass_eq_of_preimage c x.1 x.2 ⟨a, ha⟩

/-- The actual coefficient-changing structural map has finite support at both
levels; its coefficient map is the already constructed `coeffF`. -/
def fsCellsF (hfill : FilledF ρ bsub) (c : ∀ s, Mt s →₀ R')
    (y : (Jr ⊕ Sx) →₀ MonoidAlgebra ℤ (PresGroup ρ)) :
    (Jr ⊕ (Σ s, Mt s)) →₀ R' :=
  fsCellsBase c (y.mapRange (coeffF ρ bsub hfill) (map_zero _))

omit [DecidableEq α] [DecidableEq Sx] [∀ s, DecidableEq (Zt s)] in
@[simp] theorem fsCellsF_inl (hfill : FilledF ρ bsub) (c : ∀ s, Mt s →₀ R')
    (y : (Jr ⊕ Sx) →₀ MonoidAlgebra ℤ (PresGroup ρ)) (j : Jr) :
    fsCellsF ρ bsub hfill c y (Sum.inl j) = coeffF ρ bsub hfill (y (Sum.inl j)) := rfl

omit [DecidableEq α] [DecidableEq Sx] [∀ s, DecidableEq (Zt s)] in
@[simp] theorem fsCellsF_inr (hfill : FilledF ρ bsub) (c : ∀ s, Mt s →₀ R')
    (y : (Jr ⊕ Sx) →₀ MonoidAlgebra ℤ (PresGroup ρ)) (s : Sx) (m : Mt s) :
    fsCellsF ρ bsub hfill c y (Sum.inr ⟨s, m⟩) =
      coeffF ρ bsub hfill (y (Sum.inr s)) * c s m := rfl

omit [DecidableEq α] [DecidableEq Sx] [∀ s, DecidableEq (Zt s)] in
/-- The finite-support map has exactly the existing structural coefficient
formula, rather than a newly chosen or merely abstract comparison map. -/
theorem fsCellsF_coe (hfill : FilledF ρ bsub) (c : ∀ s, Mt s →₀ R')
    (y : (Jr ⊕ Sx) →₀ MonoidAlgebra ℤ (PresGroup ρ)) :
    (fsCellsF ρ bsub hfill c y : (Jr ⊕ (Σ s, Mt s)) → R') =
      cellsF ρ bsub hfill (fun s => c s) y := by
  funext k
  cases k <;> rfl

end Fox

end FiniteChains.BlockFamily
