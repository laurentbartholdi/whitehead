import RequestProject.BlockGenerates
import RequestProject.BaseChangeCycles

/-!
# The chain model of the block substitution, built over the Fox complex

This is the (B2) half of the last link of the block argument.  `RequestProject/BlockGenerates.lean`
derives equation (3.3) — property (B2) — from the equivariant chain model of the double
mapping cylinder `W`, but through two hypotheses of dictionary type: that the boundary of the
cancelled two-complex *is* the Fox boundary of the substituted presentation (`hbdry`), and
that the cycles of the chosen copy of `X` *are* the images of the Fox cycles of `ρ`
(`himage`).

Here those two are built in instead of assumed.

* the two-chains of `W̃` are `(J' → ℤ[G']) × Q`, the first factor being the two-chains of the
  universal cover of the presentation complex of `ρ'` in the Fox coordinates, and the
  boundary is by construction the Fox boundary of `ρ'` on that factor
  (`FiniteChains.BlockFox.bdry₂`);
* the chains of the full preimage `U` of `X` are the free `ℤ[G']`-module on the two-cells of
  `X`, that is the base change `ℤ[G'] ⊗_{ℤ[G]} C₂(X̃)`, and its boundary is the base-changed
  Fox boundary of `ρ` (`FiniteChains.BlockFox.foxBdryPush`); the inclusion of the chosen copy
  of `X̃` is the base change `FiniteChains.PresMor.cellsBase` of the chain map of the
  structural map, which restricts to that map on the image of `C₂(X̃)`
  (`FiniteChains.PresMor.cellsBase_pushChain`);
* the chosen component is the `ℤ[G']`-span of the images of the Fox cycles of `ρ`, and the
  hypothesis "every cycle of `U` decomposes over the components" is a theorem
  (`FiniteChains.BlockFox.cycle_mem_span_pushCycles`): when the structural map is injective on
  fundamental groups — which is the `π₁`-injectivity of the substitution — the base-changed
  Fox matrix has its entries in the subring `ℤ[f(G)]`, so
  `FiniteChains.cycle_mem_span_subgroup_cycles` applies.

The result is `FiniteChains.BlockFox.generates_of_fox_chain_model`: **property (B2) with the
dictionary discharged**, its remaining hypotheses being the geometric ones — the exactness of
the pair `(W̃, U)` in the degrees used, and the vanishing `H₂(W̃, U) = 0` which the paper gets
from the curvature criterion.
-/

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains

open MonoidAlgebra

universe u

namespace PresMor

variable {α J α' J' : Type u}
  [DecidableEq α] [Fintype J] [DecidableEq J] [DecidableEq α'] [Fintype J']
  {ρ : J → FreeGroup α} {ρ' : J' → FreeGroup α'}

/-- The coefficient homomorphism `ℤ[G] → ℤ[G']` of a structural map. -/
noncomputable def pushRing (f : PresMor ρ ρ') :
    MonoidAlgebra ℤ (PresGroup ρ) →+* MonoidAlgebra ℤ (PresGroup ρ') :=
  MonoidAlgebra.mapDomainRingHom ℤ f.hom

/-- The base change of a two-chain of the universal cover of the presentation complex of `ρ`
to a chain of the preimage of `X` in the universal cover of `W`. -/
noncomputable def pushChain (f : PresMor ρ ρ') (y : J → MonoidAlgebra ℤ (PresGroup ρ)) :
    J → MonoidAlgebra ℤ (PresGroup ρ') :=
  fun j => f.pushRing (y j)

omit [DecidableEq α] in
/-- A two-chain is the combination of the two-cells with its own coefficients. -/
theorem chain_eq_sum_single (y : J → MonoidAlgebra ℤ (PresGroup ρ)) :
    y = ∑ j, y j • (Pi.single j 1 : J → MonoidAlgebra ℤ (PresGroup ρ)) := by
  funext k
  rw [Finset.sum_apply]
  rw [Finset.sum_eq_single k]
  · simp
  · intro j _ hjk
    simp [Ne.symm hjk]
  · intro hk
    exact absurd (Finset.mem_univ k) hk

omit [DecidableEq J] in
theorem cells_sum (f : PresMor ρ ρ') {ι : Type*} (s : Finset ι)
    (g : ι → (J → MonoidAlgebra ℤ (PresGroup ρ))) :
    f.cells (∑ i ∈ s, g i) = ∑ i ∈ s, f.cells (g i) := by
  classical
  induction s using Finset.induction with
  | empty => simp [f.cells_zero]
  | insert i s hi ih => rw [Finset.sum_insert hi, f.cells_add, ih, Finset.sum_insert hi]

/-- **The base change of the chain map of a structural map**: the `ℤ[G']`-linear map on the
chains of the preimage of `X` determined by the images of the two-cells. -/
noncomputable def cellsBase (f : PresMor ρ ρ') (y : J → MonoidAlgebra ℤ (PresGroup ρ')) :
    J' → MonoidAlgebra ℤ (PresGroup ρ') :=
  ∑ j, y j • f.cells (Pi.single j 1)

theorem cellsBase_add (f : PresMor ρ ρ') (y z : J → MonoidAlgebra ℤ (PresGroup ρ')) :
    f.cellsBase (y + z) = f.cellsBase y + f.cellsBase z := by
  simp only [cellsBase, Pi.add_apply, add_smul]
  rw [Finset.sum_add_distrib]

theorem cellsBase_smul (f : PresMor ρ ρ') (c : MonoidAlgebra ℤ (PresGroup ρ'))
    (y : J → MonoidAlgebra ℤ (PresGroup ρ')) :
    f.cellsBase (c • y) = c • f.cellsBase y := by
  simp only [cellsBase, Pi.smul_apply, smul_eq_mul, mul_smul]
  rw [Finset.smul_sum]

/-- The base-changed chain map, as a map of `ℤ[G']`-modules. -/
noncomputable def cellsBaseL (f : PresMor ρ ρ') :
    (J → MonoidAlgebra ℤ (PresGroup ρ')) →ₗ[MonoidAlgebra ℤ (PresGroup ρ')]
      (J' → MonoidAlgebra ℤ (PresGroup ρ')) where
  toFun := f.cellsBase
  map_add' := f.cellsBase_add
  map_smul' := f.cellsBase_smul

@[simp] theorem cellsBaseL_apply (f : PresMor ρ ρ') (y : J → MonoidAlgebra ℤ (PresGroup ρ')) :
    f.cellsBaseL y = f.cellsBase y := rfl

/-- **The base change restricts to the chain map itself**: on the image of the chains of the
universal cover of `X` the base-changed map is the map of the structural map. -/
theorem cellsBase_pushChain (f : PresMor ρ ρ') (y : J → MonoidAlgebra ℤ (PresGroup ρ)) :
    f.cellsBase (f.pushChain y) = f.cells y := by
  conv_rhs => rw [chain_eq_sum_single y]
  rw [f.cells_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [f.cells_smul]
  rfl

end PresMor

namespace BlockFox

variable {α J α' J' : Type u}
  [DecidableEq α] [Fintype J] [DecidableEq J] [DecidableEq α'] [Fintype J']
  {ρ : J → FreeGroup α} {ρ' : J' → FreeGroup α'}

/-- The boundary of the chains of the preimage of `X`: the base change of the Fox boundary of
`ρ`. -/
noncomputable def foxBdryPush (f : PresMor ρ ρ') :
    (J → MonoidAlgebra ℤ (PresGroup ρ')) →ₗ[MonoidAlgebra ℤ (PresGroup ρ')]
      (α → MonoidAlgebra ℤ (PresGroup ρ')) where
  toFun y := fun i => ∑ j, y j * f.pushRing (foxMatrixPres ρ i j)
  map_add' y z := by
    funext i
    simp [Finset.sum_add_distrib, add_mul]
  map_smul' c y := by
    funext i
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum, mul_assoc]

omit [DecidableEq J] in
@[simp] theorem foxBdryPush_apply (f : PresMor ρ ρ')
    (y : J → MonoidAlgebra ℤ (PresGroup ρ')) (i : α) :
    foxBdryPush f y i = ∑ j, y j * f.pushRing (foxMatrixPres ρ i j) := rfl

/-- The images of the Fox cycles of `ρ` in the chains of the preimage of `X`: the cycles of
the chosen copy of the universal cover of `X`. -/
def pushCycles (f : PresMor ρ ρ') : Set (J → MonoidAlgebra ℤ (PresGroup ρ')) :=
  {w | ∃ y, IsFoxCycle ρ y ∧ w = f.pushChain y}

omit [DecidableEq J] in
/-- The image of a Fox cycle is a cycle of the preimage. -/
theorem foxBdryPush_pushChain (f : PresMor ρ ρ') {y : J → MonoidAlgebra ℤ (PresGroup ρ)}
    (hy : IsFoxCycle ρ y) : foxBdryPush f (f.pushChain y) = 0 := by
  funext i
  show ∑ j, f.pushRing (y j) * f.pushRing (foxMatrixPres ρ i j) = 0
  have h := congrArg f.pushRing (hy i)
  rw [map_sum, map_zero] at h
  rw [← h]
  exact Finset.sum_congr rfl fun j _ => (map_mul f.pushRing (y j) (foxMatrixPres ρ i j)).symm

/-! ### Every cycle of the preimage comes from the chosen copy -/

section BaseChange

variable (f : PresMor ρ ρ') (hinj : Function.Injective f.hom)

/-- The isomorphism of `G` onto the image subgroup `f(G) ≤ G'`. -/
noncomputable def imEquiv : PresGroup ρ ≃* f.hom.range := MonoidHom.ofInjective hinj

/-- The isomorphism of group rings `ℤ[G] ≅ ℤ[f(G)]`. -/
noncomputable def imRing :
    MonoidAlgebra ℤ (PresGroup ρ) →+* MonoidAlgebra ℤ f.hom.range :=
  MonoidAlgebra.mapDomainRingHom ℤ (imEquiv f hinj).toMonoidHom

/-- The inverse isomorphism `ℤ[f(G)] ≅ ℤ[G]`. -/
noncomputable def imRingInv :
    MonoidAlgebra ℤ f.hom.range →+* MonoidAlgebra ℤ (PresGroup ρ) :=
  MonoidAlgebra.mapDomainRingHom ℤ (imEquiv f hinj).symm.toMonoidHom

omit [DecidableEq J] in
theorem subRingHom_imRing (x : MonoidAlgebra ℤ (PresGroup ρ)) :
    subRingHom f.hom.range (imRing f hinj x) = f.pushRing x := by
  change MonoidAlgebra.mapDomain _ (MonoidAlgebra.mapDomain _ x) = MonoidAlgebra.mapDomain _ x
  rw [← MonoidAlgebra.mapDomain_comp]
  rfl

omit [DecidableEq J] in
theorem imRing_injective : Function.Injective (imRing f hinj) :=
  fun _ _ h => MonoidAlgebra.coeff_injective (Finsupp.mapDomain_injective (imEquiv f hinj).injective (congrArg MonoidAlgebra.coeff h))

omit [DecidableEq J] in
theorem imRing_imRingInv (x : MonoidAlgebra ℤ f.hom.range) :
    imRing f hinj (imRingInv f hinj x) = x := by
  change MonoidAlgebra.mapDomain _ (MonoidAlgebra.mapDomain _ x) = x
  rw [← MonoidAlgebra.mapDomain_comp]
  have h : ((imEquiv f hinj).toMonoidHom : PresGroup ρ → f.hom.range) ∘
      ((imEquiv f hinj).symm.toMonoidHom : f.hom.range → PresGroup ρ) = id := by
    funext g
    exact (imEquiv f hinj).apply_symm_apply g
  rw [h, MonoidAlgebra.mapDomain_id]

omit [DecidableEq J] in
include hinj in
/-- **Every cycle of the preimage of `X` is a combination of images of Fox cycles of `ρ`.**
The base-changed Fox matrix has its entries in the subring `ℤ[f(G)]`, so this is the base
change statement `FiniteChains.cycle_mem_span_subgroup_cycles`: `ℤ[G']` is free over that
subring on the cosets, and a cycle splits into its pieces on the individual cosets.  This is
the algebraic form of the paper's step "the components of the preimage of `X` are permuted
transitively by the deck group". -/
theorem cycle_mem_span_pushCycles (v : J → MonoidAlgebra ℤ (PresGroup ρ'))
    (hv : foxBdryPush f v = 0) :
    v ∈ Submodule.span (MonoidAlgebra ℤ (PresGroup ρ')) (pushCycles f) := by
  classical
  set H := f.hom.range with hH
  set A : α → J → MonoidAlgebra ℤ H := fun i j => imRing f hinj (foxMatrixPres ρ i j) with hA
  have hv' : ∀ i, ∑ j, v j * subRingHom H (A i j) = 0 := by
    intro i
    have hi : ∑ j, v j * f.pushRing (foxMatrixPres ρ i j) = 0 := congrFun hv i
    rw [← hi]
    exact Finset.sum_congr rfl fun j _ => by rw [hA, subRingHom_imRing]
  have hmem := cycle_mem_span_subgroup_cycles H A v hv'
  refine Submodule.span_mono ?_ hmem
  rintro w ⟨y, hy, rfl⟩
  refine ⟨fun j => imRingInv f hinj (y j), ?_, ?_⟩
  · intro i
    refine imRing_injective f hinj ?_
    rw [map_sum, map_zero]
    have hyi := hy i
    rw [← hyi]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_mul, imRing_imRingInv, hA]
  · funext j
    show subRingHom H (y j) = f.pushRing (imRingInv f hinj (y j))
    rw [← subRingHom_imRing f hinj, imRing_imRingInv]

end BaseChange

/-! ### Property (B2) from the constructed chain model -/

section Model

variable (f : PresMor ρ ρ') (hinj : Function.Injective f.hom)

variable {Q B₃ Q₃ Q₂ Q₁ : Type*}
  [AddCommGroup Q] [Module (MonoidAlgebra ℤ (PresGroup ρ')) Q]
  [AddCommGroup B₃] [Module (MonoidAlgebra ℤ (PresGroup ρ')) B₃]
  [AddCommGroup Q₃] [Module (MonoidAlgebra ℤ (PresGroup ρ')) Q₃]
  [AddCommGroup Q₂] [Module (MonoidAlgebra ℤ (PresGroup ρ')) Q₂]
  [AddCommGroup Q₁] [Module (MonoidAlgebra ℤ (PresGroup ρ')) Q₁]

/-- The boundary of the two-chains of the universal cover of the double mapping cylinder:
on the two-cells of the substituted presentation complex it is, by construction, the Fox
boundary of `ρ'`; on the replaced two-cell it is given by `bq`. -/
noncomputable def bdry₂model
    (bq : Q →ₗ[MonoidAlgebra ℤ (PresGroup ρ')] (α' → MonoidAlgebra ℤ (PresGroup ρ'))) :
    ((J' → MonoidAlgebra ℤ (PresGroup ρ')) × Q) →ₗ[MonoidAlgebra ℤ (PresGroup ρ')]
      (α' → MonoidAlgebra ℤ (PresGroup ρ')) :=
  (foxBdry ρ').comp (LinearMap.fst _ _ _) + bq.comp (LinearMap.snd _ _ _)

@[simp] theorem bdry₂model_inl
    (bq : Q →ₗ[MonoidAlgebra ℤ (PresGroup ρ')] (α' → MonoidAlgebra ℤ (PresGroup ρ')))
    (p : J' → MonoidAlgebra ℤ (PresGroup ρ')) :
    bdry₂model (Q := Q) bq (p, 0) = foxBdry ρ' p := by
  simp [bdry₂model]

/-- The inclusion of the chains of the preimage of `X` into the two-chains of the universal
cover of the double mapping cylinder: the base change of the chain map of the structural
map, with zero coefficient on the replaced two-cell. -/
noncomputable def inclModel :
    (J → MonoidAlgebra ℤ (PresGroup ρ')) →ₗ[MonoidAlgebra ℤ (PresGroup ρ')]
      ((J' → MonoidAlgebra ℤ (PresGroup ρ')) × Q) :=
  (f.cellsBaseL).prod 0

@[simp] theorem inclModel_apply (y : J → MonoidAlgebra ℤ (PresGroup ρ')) :
    inclModel (Q := Q) f y = (f.cellsBase y, 0) := rfl

include hinj in
/-- **Property (B2) with the dictionary discharged.**  The chain model of the double mapping
cylinder is built over the Fox complex: its two-chains are the Fox coordinates of the
substituted presentation with the replaced two-cell adjoined, the chains of the preimage of
`X` are the base change of the Fox chains of `ρ`, and the chosen copy of the universal cover
of `X` is included by the base change of the structural chain map.  With the exactness of the
pair and the vanishing `H₂(W̃, U) = 0`, equation (3.3) — property (B2) — holds for the
structural map.  Neither the identification of the boundary with the Fox boundary nor the
identification of the cycles of the chosen copy with the images of the Fox cycles of `ρ` is
assumed: both are part of the construction, the second one resting on
`FiniteChains.BlockFox.cycle_mem_span_pushCycles`. -/
theorem generates_of_fox_chain_model
    (bq : Q →ₗ[MonoidAlgebra ℤ (PresGroup ρ')] (α' → MonoidAlgebra ℤ (PresGroup ρ')))
    (a₃ : B₃ →ₗ[MonoidAlgebra ℤ (PresGroup ρ')] (J' → MonoidAlgebra ℤ (PresGroup ρ')))
    (b₃ : B₃ ≃ₗ[MonoidAlgebra ℤ (PresGroup ρ')] Q)
    (dQ₃ : Q₃ →ₗ[MonoidAlgebra ℤ (PresGroup ρ')] Q₂)
    (dQ₂ : Q₂ →ₗ[MonoidAlgebra ℤ (PresGroup ρ')] Q₁)
    (f₁ : (α → MonoidAlgebra ℤ (PresGroup ρ')) →ₗ[MonoidAlgebra ℤ (PresGroup ρ')]
      (α' → MonoidAlgebra ℤ (PresGroup ρ')))
    (g₃ : B₃ →ₗ[MonoidAlgebra ℤ (PresGroup ρ')] Q₃)
    (g₂ : ((J' → MonoidAlgebra ℤ (PresGroup ρ')) × Q) →ₗ[MonoidAlgebra ℤ (PresGroup ρ')] Q₂)
    (g₁ : (α' → MonoidAlgebra ℤ (PresGroup ρ')) →ₗ[MonoidAlgebra ℤ (PresGroup ρ')] Q₁)
    (hf₁ : Function.Injective f₁)
    (hexB₂ : ∀ z, g₂ z = 0 → ∃ a, inclModel f a = z)
    (hg₃ : Function.Surjective g₃)
    (hchainF₂ : ∀ a, bdry₂model bq (inclModel f a) = f₁ (foxBdryPush f a))
    (hchainG₃ : ∀ y, g₂ (Cancel.bdry₃ a₃ b₃ y) = dQ₃ (g₃ y))
    (hchainG₂ : ∀ z, g₁ (bdry₂model bq z) = dQ₂ (g₂ z))
    (hdd : ∀ y, bdry₂model bq (Cancel.bdry₃ a₃ b₃ y) = 0)
    (hQvanish : ∀ q, dQ₂ q = 0 → ∃ q₃, dQ₃ q₃ = q) :
    Generates f := by
  classical
  intro v hv
  set T : Set (J' → MonoidAlgebra ℤ (PresGroup ρ')) :=
    {w | ∃ y, IsFoxCycle ρ y ∧ w = f.cells y} with hT
  set A₀ : AddSubgroup (J → MonoidAlgebra ℤ (PresGroup ρ')) :=
    (Submodule.span (MonoidAlgebra ℤ (PresGroup ρ')) (pushCycles f)).toAddSubgroup with hA₀
  have hvz : bdry₂model (Q := Q) bq (v, 0) = 0 := by
    rw [bdry₂model_inl, ← isFoxCycle_iff_foxBdry_eq_zero ρ' v]
    exact hv
  have hdecomp : ∀ a : J → MonoidAlgebra ℤ (PresGroup ρ'), foxBdryPush f a = 0 →
      ∃ (s : Finset Unit) (fc : Unit → (J → MonoidAlgebra ℤ (PresGroup ρ'))),
        (∀ i ∈ s, fc i ∈ A₀) ∧ a = ∑ i ∈ s, fc i := by
    intro a ha
    refine ⟨{()}, fun _ => a, ?_, by simp⟩
    intro i _
    exact cycle_mem_span_pushCycles f hinj a ha
  have htrans : ∀ _i : Unit, ∃ g : PresGroup ρ', ∀ x ∈ A₀, ∃ y ∈ A₀,
      x = (MonoidAlgebra.single g (1 : ℤ) : MonoidAlgebra ℤ (PresGroup ρ')) • y := by
    intro _
    refine ⟨1, fun x hx => ⟨x, hx, ?_⟩⟩
    rw [show (MonoidAlgebra.single (1 : PresGroup ρ') (1 : ℤ) :
      MonoidAlgebra ℤ (PresGroup ρ')) = 1 from rfl, one_smul]
  have hmem := block_generation_of_relative_vanishing (bdry₂model (Q := Q) bq) a₃ b₃
    (foxBdryPush f) dQ₃ dQ₂ (inclModel f) f₁ g₃ g₂ g₁ hf₁ hexB₂ hg₃ hchainF₂ hchainG₃
    hchainG₂ hdd hQvanish (fun _ : Unit => A₀) () hdecomp htrans v hvz
  -- the cancelled images of the chosen copy are the images of the Fox cycles of `ρ`
  set L := (Cancel.cancelMap a₃ b₃).comp (inclModel (Q := Q) f) with hL
  have hLpush : ∀ y : J → MonoidAlgebra ℤ (PresGroup ρ),
      L (f.pushChain y) = (f.cells y, 0) := by
    intro y
    show Cancel.cancelMap a₃ b₃ (f.cellsBase (f.pushChain y), 0) = (f.cells y, 0)
    rw [Cancel.cancelMap_of_snd_zero, f.cellsBase_pushChain]
  have hgen : ∀ w ∈ pushCycles f, L w ∈ Submodule.span (MonoidAlgebra ℤ (PresGroup ρ'))
      ((LinearMap.inl (MonoidAlgebra ℤ (PresGroup ρ')) (J' → MonoidAlgebra ℤ (PresGroup ρ'))
        Q) '' T) := by
    rintro w ⟨y, hy, rfl⟩
    refine Submodule.subset_span ⟨f.cells y, ⟨y, hy, rfl⟩, ?_⟩
    rw [hLpush y]
    rfl
  have hspan : Submodule.span (MonoidAlgebra ℤ (PresGroup ρ'))
      (Cancel.cancelMap a₃ b₃ '' (inclModel (Q := Q) f ''
        (A₀ : Set (J → MonoidAlgebra ℤ (PresGroup ρ')))))
      ≤ Submodule.span (MonoidAlgebra ℤ (PresGroup ρ'))
        ((LinearMap.inl (MonoidAlgebra ℤ (PresGroup ρ'))
          (J' → MonoidAlgebra ℤ (PresGroup ρ')) Q) '' T) := by
    refine Submodule.span_le.2 ?_
    rintro z ⟨_, ⟨a, ha, rfl⟩, rfl⟩
    have hmap : Submodule.map L (Submodule.span (MonoidAlgebra ℤ (PresGroup ρ'))
        (pushCycles f))
        ≤ Submodule.span (MonoidAlgebra ℤ (PresGroup ρ')) (L '' pushCycles f) := by
      rw [Submodule.map_span]
    have h1 : L a ∈ Submodule.span (MonoidAlgebra ℤ (PresGroup ρ')) (L '' pushCycles f) :=
      hmap ⟨a, ha, rfl⟩
    have h2 : Submodule.span (MonoidAlgebra ℤ (PresGroup ρ')) (L '' pushCycles f)
        ≤ Submodule.span (MonoidAlgebra ℤ (PresGroup ρ'))
          ((LinearMap.inl (MonoidAlgebra ℤ (PresGroup ρ'))
            (J' → MonoidAlgebra ℤ (PresGroup ρ')) Q) '' T) :=
      Submodule.span_le.2 (by rintro _ ⟨w, hw, rfl⟩; exact hgen w hw)
    exact h2 h1
  have hvin := hspan hmem
  have hfst : Submodule.map (LinearMap.fst (MonoidAlgebra ℤ (PresGroup ρ'))
      (J' → MonoidAlgebra ℤ (PresGroup ρ')) Q)
      (Submodule.span (MonoidAlgebra ℤ (PresGroup ρ'))
        ((LinearMap.inl (MonoidAlgebra ℤ (PresGroup ρ'))
          (J' → MonoidAlgebra ℤ (PresGroup ρ')) Q) '' T))
      ≤ Submodule.span (MonoidAlgebra ℤ (PresGroup ρ')) T := by
    rw [Submodule.map_span]
    refine Submodule.span_le.2 ?_
    rintro _ ⟨_, ⟨w, hw, rfl⟩, rfl⟩
    exact Submodule.subset_span hw
  exact hfst ⟨(v, 0), hvin, rfl⟩

end Model

end BlockFox

end FiniteChains
