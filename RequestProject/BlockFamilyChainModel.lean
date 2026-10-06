import RequestProject.BlockFamilySubst
import RequestProject.BlockRelativeQuotient

/-!
# The chain model of the double mapping cylinder of a whole family of blocks

`RequestProject/BlockFamilySubst.lean` builds the structural map of the article's
simultaneous substitution (3.4): a family `(s : Sx)` of labelled relator entries of

  `ρ : Jr ⊕ Sx → FreeGroup α`

is replaced at the same time, the entry `s` by its own block with its own internal generators
`Zt s` and its own relator entries `Mt s`.

This file instantiates the (B2) route of `RequestProject/BlockRelativeQuotient.lean` — the one
that goes through the *relative* complex of the pair `(W̃, U)` and the article's homological
input `H₂(W̃, U) = 0` — **at that concrete substitution**.  All the data that the general
statement `FiniteChains.BlockFox.generates_of_quotient_relative` takes as parameters are
*constructed* here from the substitution itself, and all its structural hypotheses are
*proved* here:

* `FiniteChains.BlockFamily.oneChainIncl` (`f₁`) — the one-chains of the preimage of `X` are
  the one-chains on the old generators, included into the one-chains on all generators by
  extension by zero.  Its injectivity is `oneChainIncl_injective`;
* `FiniteChains.BlockFamily.polyBdry` (`bq`) — the module `Sx → ℤ[G']` of the two-chains
  carried by the replaced polygons, with the boundary of the polygon at `s` equal to the
  base-changed Fox row of the replaced relator `ρ (Sum.inr s)`;
* `FiniteChains.BlockFamily.cylChain` (`a₃`) and the negation isomorphism (`b₃`) — the
  three-cells of the double mapping cylinder, one per replaced entry: the boundary of the
  three-cell at `s` is the filling chain `c s` of the block at `s` minus the replaced polygon.
  This is the cancelling pair of cells of the article ("in the double mapping cylinder of
  `a_s` the polygon-cylinder three-cell cancels that old two-cell; for distinct `s` these
  cancelling pairs are disjoint");
* `FiniteChains.BlockFamily.chainMap_incl` (`hchainF₂`) — the inclusion of the preimage of
  `X` is a chain map, i.e. the boundary of the cover restricts to the base-changed Fox
  boundary of `ρ`;
* `FiniteChains.BlockFamily.bdry_bdry_eq_zero` (`hdd`) — the boundary of the boundary of a
  three-cell vanishes.

The outcome is

  `FiniteChains.BlockFamily.generates_familySubst_of_relative_vanishing`,

property (B2) — equation (3.3) — for the article's simultaneous substitution, with exactly
two remaining inputs, both of them the geometric ones of the article's proof:

* `hinj`: the substitution is injective on fundamental groups (Step 1 of the article's
  "Generation in the pushout of a family", the radial retraction in the CAT(0) universal
  cover).  By `FiniteChains.BlockSubst.baseHom_not_injective` this cannot be replaced by any
  argument using presentations alone;
* `hrel`: `H₂(W̃, U) = 0` for this concrete relative complex (Steps 2 and 3, the collapsed
  space `V` and its cube structure).

No further dictionary, no cell-by-cell identification with a cube complex and no hypothesis
about `H₂(W̃)` (which is false for a nonaspherical `X`, see
`RequestProject/BlockSphereRegression.lean`) is used.

As everywhere in the project's Fox calculus, the presentations are finite, so the family `Sx`
of simultaneously replaced entries is a finite (but otherwise arbitrary) set of labelled
entries.
-/

namespace FiniteChains

namespace BlockFamily

open MonoidAlgebra

universe u

variable {α Jr Sx : Type u} {Zt Mt : Sx → Type u}
  [Fintype α] [DecidableEq α] [Fintype Jr] [DecidableEq Jr]
  [Fintype Sx] [DecidableEq Sx]
  [∀ s, Fintype (Zt s)] [∀ s, DecidableEq (Zt s)] [∀ s, Fintype (Mt s)]
  {ρ : Jr ⊕ Sx → FreeGroup α} {bsub : ∀ s : Sx, Mt s → FreeGroup (α ⊕ Zt s)}
  {hfill : FilledF ρ bsub}
  {c : ∀ s : Sx, Mt s → MonoidAlgebra ℤ (PresGroup (substPresF ρ bsub))}

/-! ### The one-chains of the preimage of `X` -/

/-- The inclusion of the one-chains of the preimage of `X` into the one-chains of the cover of
the double mapping cylinder: extension by zero from the old generators to all generators. -/
noncomputable def oneChainIncl (ρ : Jr ⊕ Sx → FreeGroup α)
    (bsub : ∀ s : Sx, Mt s → FreeGroup (α ⊕ Zt s)) :
    (α → MonoidAlgebra ℤ (PresGroup (substPresF ρ bsub)))
      →ₗ[MonoidAlgebra ℤ (PresGroup (substPresF ρ bsub))]
      ((α ⊕ (Σ s : Sx, Zt s)) → MonoidAlgebra ℤ (PresGroup (substPresF ρ bsub))) where
  toFun v := Sum.elim v 0
  map_add' v w := by
    funext i
    cases i <;> simp
  map_smul' x v := by
    funext i
    cases i <;> simp

omit [Fintype α] [DecidableEq α] [Fintype Jr] [DecidableEq Jr] [Fintype Sx] [DecidableEq Sx]
  [∀ s, Fintype (Zt s)] [∀ s, DecidableEq (Zt s)] [∀ s, Fintype (Mt s)] in
@[simp] theorem oneChainIncl_inl
    (v : α → MonoidAlgebra ℤ (PresGroup (substPresF ρ bsub))) (i : α) :
    oneChainIncl ρ bsub v (Sum.inl i) = v i := rfl

omit [Fintype α] [DecidableEq α] [Fintype Jr] [DecidableEq Jr] [Fintype Sx] [DecidableEq Sx]
  [∀ s, Fintype (Zt s)] [∀ s, DecidableEq (Zt s)] [∀ s, Fintype (Mt s)] in
@[simp] theorem oneChainIncl_inr
    (v : α → MonoidAlgebra ℤ (PresGroup (substPresF ρ bsub))) (w : Σ s : Sx, Zt s) :
    oneChainIncl ρ bsub v (Sum.inr w) = 0 := rfl

omit [Fintype α] [DecidableEq α] [Fintype Jr] [DecidableEq Jr] [Fintype Sx] [DecidableEq Sx]
  [∀ s, Fintype (Zt s)] [∀ s, DecidableEq (Zt s)] [∀ s, Fintype (Mt s)] in
theorem oneChainIncl_injective : Function.Injective (oneChainIncl ρ bsub) := by
  intro v w h
  funext i
  exact congrFun h (Sum.inl i)

/-! ### The replaced polygons and the cancelling three-cells -/

/-- The boundary of the replaced two-cells: the polygon of the entry `s` is attached along the
replaced relator, so its boundary is the base change of the Fox row of that relator. -/
noncomputable def polyBdry (ρ : Jr ⊕ Sx → FreeGroup α)
    (bsub : ∀ s : Sx, Mt s → FreeGroup (α ⊕ Zt s)) (hfill : FilledF ρ bsub) :
    (Sx → MonoidAlgebra ℤ (PresGroup (substPresF ρ bsub)))
      →ₗ[MonoidAlgebra ℤ (PresGroup (substPresF ρ bsub))]
      ((α ⊕ (Σ s : Sx, Zt s)) → MonoidAlgebra ℤ (PresGroup (substPresF ρ bsub))) where
  toFun q := Sum.elim
    (fun i => ∑ s : Sx, q s * coeffF ρ bsub hfill (foxMatrixPres ρ i (Sum.inr s))) 0
  map_add' q q' := by
    funext i
    cases i with
    | inl i => simp [Finset.sum_add_distrib, add_mul]
    | inr w => simp
  map_smul' x q := by
    funext i
    cases i with
    | inl i => simp [Finset.mul_sum, mul_assoc]
    | inr w => simp

omit [Fintype α] [Fintype Jr] [DecidableEq Jr] [DecidableEq Sx]
  [∀ s, Fintype (Zt s)] [∀ s, DecidableEq (Zt s)] [∀ s, Fintype (Mt s)] in
@[simp] theorem polyBdry_inl (q : Sx → MonoidAlgebra ℤ (PresGroup (substPresF ρ bsub)))
    (i : α) :
    polyBdry ρ bsub hfill q (Sum.inl i)
      = ∑ s : Sx, q s * coeffF ρ bsub hfill (foxMatrixPres ρ i (Sum.inr s)) := rfl

omit [Fintype α] [Fintype Jr] [DecidableEq Jr] [DecidableEq Sx]
  [∀ s, Fintype (Zt s)] [∀ s, DecidableEq (Zt s)] [∀ s, Fintype (Mt s)] in
@[simp] theorem polyBdry_inr (q : Sx → MonoidAlgebra ℤ (PresGroup (substPresF ρ bsub)))
    (w : Σ s : Sx, Zt s) : polyBdry ρ bsub hfill q (Sum.inr w) = 0 := rfl

/-- The part of the boundary of the three-cells which lies on the two-cells of the substituted
presentation: the three-cell at `s` is the cylinder over the polygon of `s`, so this part is
the filling chain `c s` of the block substituted at `s`. -/
noncomputable def cylChain (ρ : Jr ⊕ Sx → FreeGroup α)
    (bsub : ∀ s : Sx, Mt s → FreeGroup (α ⊕ Zt s))
    (c : ∀ s : Sx, Mt s → MonoidAlgebra ℤ (PresGroup (substPresF ρ bsub))) :
    (Sx → MonoidAlgebra ℤ (PresGroup (substPresF ρ bsub)))
      →ₗ[MonoidAlgebra ℤ (PresGroup (substPresF ρ bsub))]
      ((Jr ⊕ (Σ s : Sx, Mt s)) → MonoidAlgebra ℤ (PresGroup (substPresF ρ bsub))) where
  toFun y := Sum.elim 0 (fun p => y p.1 * c p.1 p.2)
  map_add' y y' := by
    funext k
    cases k with
    | inl j => simp
    | inr p => simp [add_mul]
  map_smul' x y := by
    funext k
    cases k with
    | inl j => simp
    | inr p => simp [mul_assoc]

omit [Fintype α] [DecidableEq α] [Fintype Jr] [DecidableEq Jr] [Fintype Sx] [DecidableEq Sx]
  [∀ s, Fintype (Zt s)] [∀ s, DecidableEq (Zt s)] [∀ s, Fintype (Mt s)] in
@[simp] theorem cylChain_inl (y : Sx → MonoidAlgebra ℤ (PresGroup (substPresF ρ bsub)))
    (j : Jr) : cylChain ρ bsub c y (Sum.inl j) = 0 := rfl

omit [Fintype α] [DecidableEq α] [Fintype Jr] [DecidableEq Jr] [Fintype Sx] [DecidableEq Sx]
  [∀ s, Fintype (Zt s)] [∀ s, DecidableEq (Zt s)] [∀ s, Fintype (Mt s)] in
@[simp] theorem cylChain_inr (y : Sx → MonoidAlgebra ℤ (PresGroup (substPresF ρ bsub)))
    (p : Σ s : Sx, Mt s) : cylChain ρ bsub c y (Sum.inr p) = y p.1 * c p.1 p.2 := rfl

/-- The identification of the three-cells with the replaced two-cells they cancel: the
three-cell at `s` has the polygon at `s` in its boundary with the coefficient `-1`. -/
noncomputable def cylCancel (ρ : Jr ⊕ Sx → FreeGroup α)
    (bsub : ∀ s : Sx, Mt s → FreeGroup (α ⊕ Zt s)) :
    (Sx → MonoidAlgebra ℤ (PresGroup (substPresF ρ bsub)))
      ≃ₗ[MonoidAlgebra ℤ (PresGroup (substPresF ρ bsub))]
      (Sx → MonoidAlgebra ℤ (PresGroup (substPresF ρ bsub))) :=
  LinearEquiv.neg _

omit [Fintype α] [DecidableEq α] [Fintype Jr] [DecidableEq Jr] [Fintype Sx] [DecidableEq Sx]
  [∀ s, Fintype (Zt s)] [∀ s, DecidableEq (Zt s)] [∀ s, Fintype (Mt s)] in
@[simp] theorem cylCancel_apply (y : Sx → MonoidAlgebra ℤ (PresGroup (substPresF ρ bsub))) :
    cylCancel ρ bsub y = -y := rfl

/-! ### The two sums over the cells of the blocks -/

variable (hc : IsFillingF ρ bsub hfill c)

include hc

omit [Fintype α] [Fintype Jr] [DecidableEq Jr] [∀ s, Fintype (Zt s)] in
/-- The block cells of a chain spread along the filling chains contribute, at an old
generator, the boundary of the replaced polygons. -/
theorem sum_filling_inl (w : Sx → MonoidAlgebra ℤ (PresGroup (substPresF ρ bsub))) (i : α) :
    ∑ p : Σ s : Sx, Mt s, w p.1 * c p.1 p.2
        * foxMatrixPres (substPresF ρ bsub) (Sum.inl i) (Sum.inr p)
      = ∑ s : Sx, w s * coeffF ρ bsub hfill (foxMatrixPres ρ i (Sum.inr s)) := by
  rw [Fintype.sum_sigma]
  refine Finset.sum_congr rfl fun s _ => ?_
  have h : ∀ m : Mt s, w s * c s m
        * foxMatrixPres (substPresF ρ bsub) (Sum.inl i) (Sum.inr ⟨s, m⟩)
      = w s * (c s m * foxMatrixPres (substPresF ρ bsub) (Sum.inl i) (Sum.inr ⟨s, m⟩)) := by
    intro m
    rw [mul_assoc]
  rw [Finset.sum_congr rfl fun m _ => h m, ← Finset.mul_sum, hc.base s i]

omit [Fintype α] [Fintype Jr] [DecidableEq Jr] [∀ s, Fintype (Zt s)] in
/-- The block cells of a chain spread along the filling chains contribute nothing at an
internal generator. -/
theorem sum_filling_inr (w : Sx → MonoidAlgebra ℤ (PresGroup (substPresF ρ bsub)))
    (s' : Sx) (z : Zt s') :
    ∑ p : Σ s : Sx, Mt s, w p.1 * c p.1 p.2
        * foxMatrixPres (substPresF ρ bsub) (Sum.inr ⟨s', z⟩) (Sum.inr p) = 0 := by
  rw [Fintype.sum_sigma]
  refine Finset.sum_eq_zero fun s _ => ?_
  by_cases hs : s = s'
  · subst hs
    have h : ∀ m : Mt s, w s * c s m
          * foxMatrixPres (substPresF ρ bsub) (Sum.inr ⟨s, z⟩) (Sum.inr ⟨s, m⟩)
        = w s * (c s m
            * foxMatrixPres (substPresF ρ bsub) (Sum.inr ⟨s, z⟩) (Sum.inr ⟨s, m⟩)) := by
      intro m
      rw [mul_assoc]
    rw [Finset.sum_congr rfl fun m _ => h m, ← Finset.mul_sum, hc.internal s z, mul_zero]
  · refine Finset.sum_eq_zero fun m _ => ?_
    rw [foxMatrix_inr_inr_of_ne ρ bsub hs z m, mul_zero]

/-! ### The inclusion of the preimage of `X`, in the coordinates of the model -/

omit [Fintype α] [∀ s, Fintype (Zt s)] in
/-- The base-changed chain map of the structural map, computed on a retained two-cell. -/
theorem cellsBase_inl (a : (Jr ⊕ Sx) → MonoidAlgebra ℤ (PresGroup (substPresF ρ bsub)))
    (j : Jr) :
    (substMorF ρ bsub hfill c hc).cellsBase a (Sum.inl j) = a (Sum.inl j) := by
  classical
  show (∑ k : Jr ⊕ Sx, a k • (substMorF ρ bsub hfill c hc).cells
    (Pi.single k 1)) (Sum.inl j) = a (Sum.inl j)
  rw [Finset.sum_apply]
  rw [Finset.sum_eq_single (Sum.inl j)]
  · show a (Sum.inl j) * coeffF ρ bsub hfill ((Pi.single (Sum.inl j) 1 :
      (Jr ⊕ Sx) → MonoidAlgebra ℤ (PresGroup ρ)) (Sum.inl j)) = a (Sum.inl j)
    rw [Pi.single_eq_same, map_one, mul_one]
  · intro k _ hk
    show a k * coeffF ρ bsub hfill ((Pi.single k 1 :
      (Jr ⊕ Sx) → MonoidAlgebra ℤ (PresGroup ρ)) (Sum.inl j)) = 0
    rw [Pi.single_eq_of_ne (Ne.symm hk), map_zero, mul_zero]
  · intro hk
    exact absurd (Finset.mem_univ _) hk

omit [Fintype α] [∀ s, Fintype (Zt s)] in
/-- The base-changed chain map of the structural map, computed on a cell of a block. -/
theorem cellsBase_inr (a : (Jr ⊕ Sx) → MonoidAlgebra ℤ (PresGroup (substPresF ρ bsub)))
    (p : Σ s : Sx, Mt s) :
    (substMorF ρ bsub hfill c hc).cellsBase a (Sum.inr p) = a (Sum.inr p.1) * c p.1 p.2 := by
  classical
  show (∑ k : Jr ⊕ Sx, a k • (substMorF ρ bsub hfill c hc).cells
    (Pi.single k 1)) (Sum.inr p) = a (Sum.inr p.1) * c p.1 p.2
  rw [Finset.sum_apply]
  rw [Finset.sum_eq_single (Sum.inr p.1)]
  · show a (Sum.inr p.1) * (coeffF ρ bsub hfill ((Pi.single (Sum.inr p.1) 1 :
      (Jr ⊕ Sx) → MonoidAlgebra ℤ (PresGroup ρ)) (Sum.inr p.1)) * c p.1 p.2) = _
    rw [Pi.single_eq_same, map_one, one_mul]
  · intro k _ hk
    show a k * (coeffF ρ bsub hfill ((Pi.single k 1 :
      (Jr ⊕ Sx) → MonoidAlgebra ℤ (PresGroup ρ)) (Sum.inr p.1)) * c p.1 p.2) = 0
    rw [Pi.single_eq_of_ne (Ne.symm hk), map_zero, zero_mul, mul_zero]
  · intro hk
    exact absurd (Finset.mem_univ _) hk

omit [Fintype α] [∀ s, Fintype (Zt s)] in
/-- **The inclusion of the preimage of `X` is a chain map.**  The boundary of the cover of the
double mapping cylinder, restricted to the chains of the preimage of `X`, is the base change
of the Fox boundary of the original presentation.  This is the hypothesis `hchainF₂` of
`FiniteChains.BlockFox.generates_of_quotient_relative`, proved here for the article's
substitution. -/
theorem chainMap_incl (a : (Jr ⊕ Sx) → MonoidAlgebra ℤ (PresGroup (substPresF ρ bsub))) :
    BlockFox.bdry₂model (polyBdry ρ bsub hfill)
        (BlockFox.inclModel (substMorF ρ bsub hfill c hc) a)
      = oneChainIncl ρ bsub (BlockFox.foxBdryPush (substMorF ρ bsub hfill c hc) a) := by
  funext i
  have hzero : (polyBdry ρ bsub hfill) 0 = 0 := map_zero _
  show foxBdry (substPresF ρ bsub) ((substMorF ρ bsub hfill c hc).cellsBase a) i
      + (polyBdry ρ bsub hfill) 0 i = _
  rw [hzero]
  cases i with
  | inl i =>
      show (∑ k : Jr ⊕ (Σ s : Sx, Mt s),
            (substMorF ρ bsub hfill c hc).cellsBase a k
              * foxMatrixPres (substPresF ρ bsub) (Sum.inl i) k) + 0
          = ∑ k : Jr ⊕ Sx, a k
              * coeffF ρ bsub hfill (foxMatrixPres ρ i k)
      rw [add_zero, Fintype.sum_sum_type, Fintype.sum_sum_type]
      congr 1
      · refine Finset.sum_congr rfl fun j _ => ?_
        rw [cellsBase_inl hc a j, foxMatrix_inl_inl ρ bsub hfill]
      · rw [← sum_filling_inl hc (fun s => a (Sum.inr s)) i]
        refine Finset.sum_congr rfl fun p _ => ?_
        rw [cellsBase_inr hc a p]
  | inr w =>
      obtain ⟨s', z⟩ := w
      show (∑ k : Jr ⊕ (Σ s : Sx, Mt s),
            (substMorF ρ bsub hfill c hc).cellsBase a k
              * foxMatrixPres (substPresF ρ bsub) (Sum.inr ⟨s', z⟩) k) + 0 = 0
      rw [add_zero, Fintype.sum_sum_type]
      have h1 : ∑ j : Jr, (substMorF ρ bsub hfill c hc).cellsBase a (Sum.inl j)
          * foxMatrixPres (substPresF ρ bsub) (Sum.inr ⟨s', z⟩) (Sum.inl j) = 0 := by
        refine Finset.sum_eq_zero fun j _ => ?_
        rw [foxMatrix_inr_inl ρ bsub, mul_zero]
      have h2 : ∑ p : Σ s : Sx, Mt s, (substMorF ρ bsub hfill c hc).cellsBase a (Sum.inr p)
          * foxMatrixPres (substPresF ρ bsub) (Sum.inr ⟨s', z⟩) (Sum.inr p) = 0 := by
        rw [← sum_filling_inr hc (fun s => a (Sum.inr s)) s' z]
        refine Finset.sum_congr rfl fun p _ => ?_
        rw [cellsBase_inr hc a p]
      rw [h1, h2, add_zero]

omit [Fintype α] [DecidableEq Jr] [∀ s, Fintype (Zt s)] in
/-- **The boundary of the boundary of a three-cell vanishes.**  The three-cell at `s` has in
its boundary the filling chain of the block at `s` and, with the opposite sign, the replaced
polygon; the two have the same boundary, by the filling conditions.  This is the hypothesis
`hdd` of `FiniteChains.BlockFox.generates_of_quotient_relative`, proved here for the article's
substitution. -/
theorem bdry_bdry_eq_zero (y : Sx → MonoidAlgebra ℤ (PresGroup (substPresF ρ bsub))) :
    BlockFox.bdry₂model (polyBdry ρ bsub hfill)
      (Cancel.bdry₃ (cylChain ρ bsub c) (cylCancel ρ bsub) y) = 0 := by
  funext i
  show foxBdry (substPresF ρ bsub) (cylChain ρ bsub c y) i
      + (polyBdry ρ bsub hfill) (-y) i = 0
  cases i with
  | inl i =>
      have h1 : foxBdry (substPresF ρ bsub) (cylChain ρ bsub c y) (Sum.inl i)
          = ∑ s : Sx, y s * coeffF ρ bsub hfill (foxMatrixPres ρ i (Sum.inr s)) := by
        show (∑ k : Jr ⊕ (Σ s : Sx, Mt s), cylChain ρ bsub c y k
            * foxMatrixPres (substPresF ρ bsub) (Sum.inl i) k) = _
        rw [Fintype.sum_sum_type]
        have hl : ∑ j : Jr, cylChain ρ bsub c y (Sum.inl j)
            * foxMatrixPres (substPresF ρ bsub) (Sum.inl i) (Sum.inl j) = 0 := by
          refine Finset.sum_eq_zero fun j _ => ?_
          rw [cylChain_inl, zero_mul]
        rw [hl, zero_add, ← sum_filling_inl hc y i]
        rfl
      have h2 : (polyBdry ρ bsub hfill) (-y) (Sum.inl i)
          = -∑ s : Sx, y s * coeffF ρ bsub hfill (foxMatrixPres ρ i (Sum.inr s)) := by
        rw [polyBdry_inl, ← Finset.sum_neg_distrib]
        refine Finset.sum_congr rfl fun s _ => ?_
        rw [Pi.neg_apply, neg_mul]
      rw [h1, h2, add_neg_cancel]
  | inr w =>
      obtain ⟨s', z⟩ := w
      have h1 : foxBdry (substPresF ρ bsub) (cylChain ρ bsub c y) (Sum.inr ⟨s', z⟩) = 0 := by
        show (∑ k : Jr ⊕ (Σ s : Sx, Mt s), cylChain ρ bsub c y k
            * foxMatrixPres (substPresF ρ bsub) (Sum.inr ⟨s', z⟩) k) = 0
        rw [Fintype.sum_sum_type]
        have hl : ∑ j : Jr, cylChain ρ bsub c y (Sum.inl j)
            * foxMatrixPres (substPresF ρ bsub) (Sum.inr ⟨s', z⟩) (Sum.inl j) = 0 := by
          refine Finset.sum_eq_zero fun j _ => ?_
          rw [cylChain_inl, zero_mul]
        rw [hl, zero_add, ← sum_filling_inr hc y s' z]
        rfl
      rw [h1, polyBdry_inr, add_zero]

/-! ### Property (B2) for the article's simultaneous substitution -/

omit [Fintype α] [∀ s, Fintype (Zt s)] in
/-- **Property (B2) — equation (3.3) — for the article's simultaneous substitution of a family
of blocks**, with every structural input discharged.

The relative chain complex of the pair `(W̃, U)` is the constructed quotient of
`RequestProject/BlockQuotientModel.lean` for the data built in this file; the chain-map and
`∂∂ = 0` conditions are the theorems `chainMap_incl` and `bdry_bdry_eq_zero`, and the
injectivity of the inclusion of one-chains is `oneChainIncl_injective`.

Exactly the two geometric inputs of the article's Lemma "Generation in the pushout of a
family" remain:

* `hinj` — Step 1: the substitution is injective on fundamental groups;
* `hrel` — Steps 2 and 3: `H₂(W̃, U) = 0`, i.e. every relative two-cycle is the relative
  boundary of a three-chain. -/
theorem generates_familySubst_of_relative_vanishing
    (hinj : Function.Injective (substHomF ρ bsub hfill))
    (hrel : ∀ q : BlockFox.RelTwo
        (Q := Sx → MonoidAlgebra ℤ (PresGroup (substPresF ρ bsub)))
        (substMorF ρ bsub hfill c hc),
      BlockFox.relBdry₂ (bq := polyBdry ρ bsub hfill) (chainMap_incl hc) q = 0 →
        ∃ y : Sx → MonoidAlgebra ℤ (PresGroup (substPresF ρ bsub)),
          BlockFox.relBdry₃ (Q := Sx → MonoidAlgebra ℤ (PresGroup (substPresF ρ bsub)))
            (f := substMorF ρ bsub hfill c hc) (cylChain ρ bsub c) (cylCancel ρ bsub) y = q) :
    Generates (substMorF ρ bsub hfill c hc) :=
  BlockFox.generates_of_quotient_relative (f := substMorF ρ bsub hfill c hc)
    (bq := polyBdry ρ bsub hfill) (f₁ := oneChainIncl ρ bsub) hinj
    (cylChain ρ bsub c) (cylCancel ρ bsub) oneChainIncl_injective (chainMap_incl hc)
    (bdry_bdry_eq_zero hc) hrel

end BlockFamily

end FiniteChains
