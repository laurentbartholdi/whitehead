import RequestProject.BlockFamilyB1Finsupp
import RequestProject.CrowellFinsupp
import RequestProject.GenusSpineFactorComparison
import RequestProject.GenusSpineSubstitutedBoundary
import RequestProject.PrincipalCycleBaseChange
import RequestProject.GenusNormalizedSpineReference

/-!
Finite-support generation for the actual arbitrary family of genus spines.
The surface filling is chosen in the marked spine before substituting any old
words, with the old geometric class of the explicit degree-one polygon.
B1 is proved by Fox naturality. The actual individual factors embed in
the simultaneous group, so principal generation in those factors implies the
family B2 by group-ring base change. The sole remaining geometric input is the
explicit individual B2 for this marked surface filling.

Written proof terms; this source has not been compiled under the current workflow.
-/

noncomputable section
open scoped Classical

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains

/-- Fox chain rule for a finite source alphabet and an arbitrary target alphabet. -/
theorem fox_wordHom_chainRule {A B : Type*} [Fintype A] [DecidableEq A]
    [DecidableEq B] (φ : FreeGroup A →* FreeGroup B) (b : B) (w : FreeGroup A) :
    fox b (φ w) = ∑ i : A,
      MonoidAlgebra.mapDomainRingHom ℤ φ (fox i w) * fox b (φ (FreeGroup.of i)) := by
  induction w using FreeGroup.induction_on with
  | one => simp
  | of j => simp [fox_of]
  | inv_of j ih =>
      rw [map_inv, fox_inv, ih]
      simp only [fox_inv, map_neg, map_mul, groupRingMap_grp]
      rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro i hi
      rw [map_inv]
      simp only [neg_mul, mul_assoc]
  | mul v w hv hw =>
      rw [map_mul, fox_mul, hv, hw]
      simp only [fox_mul, map_add, map_mul, groupRingMap_grp, add_mul]
      rw [Finset.sum_add_distrib, Finset.mul_sum]
      congr 1
      exact Finset.sum_congr rfl (fun i _ => (mul_assoc _ _ _).symm)

/-- Transport a genuine filling through a word homomorphism and its induced
quotient homomorphism. No injectivity of the word substitution is required. -/
theorem fox_filling_wordHom {A B J : Type*} [Fintype A] [DecidableEq A]
    [DecidableEq B] [Fintype J] (σ : J → FreeGroup A)
    (N : Subgroup (FreeGroup B)) [N.Normal]
    (φ : FreeGroup A →* FreeGroup B) (ψ : PresGroup σ →* (FreeGroup B ⧸ N))
    (hψ : ∀ w, ψ (QuotientGroup.mk w) = QuotientGroup.mk (φ w))
    (c : J → MonoidAlgebra ℤ (PresGroup σ)) (w : FreeGroup A)
    (hc : ∀ i, ∑ j, c j * foxMatrixPres σ i j =
      quotRingHom ℤ (relSub σ) (fox i w)) (b : B) :
    (∑ j, MonoidAlgebra.mapDomainRingHom ℤ ψ (c j) *
      quotRingHom ℤ N (fox b (φ (σ j)))) = quotRingHom ℤ N (fox b (φ w)) := by
  let C := MonoidAlgebra.mapDomainRingHom ℤ ψ
  have hcoeff (x : FreeGroupRing A) :
      C (quotRingHom ℤ (relSub σ) x) =
        quotRingHom ℤ N (MonoidAlgebra.mapDomainRingHom ℤ φ x) := by
    change MonoidAlgebra.mapDomainRingHom ℤ ψ
        (MonoidAlgebra.mapDomainRingHom ℤ (QuotientGroup.mk' (relSub σ)) x) =
      MonoidAlgebra.mapDomainRingHom ℤ (QuotientGroup.mk' N)
        (MonoidAlgebra.mapDomainRingHom ℤ φ x)
    have hh : ψ.comp (QuotientGroup.mk' (relSub σ)) =
        (QuotientGroup.mk' N).comp φ := MonoidHom.ext hψ
    rw [BlockMor.mapDomainRingHom_comp', BlockMor.mapDomainRingHom_comp', hh]
  have hfox (v : FreeGroup A) : quotRingHom ℤ N (fox b (φ v)) =
      ∑ i : A, C (quotRingHom ℤ (relSub σ) (fox i v)) *
        quotRingHom ℤ N (fox b (φ (FreeGroup.of i))) := by
    rw [fox_wordHom_chainRule, map_sum]
    exact Finset.sum_congr rfl (fun i _ => by rw [map_mul, hcoeff])
  have hcol (j : J) := hfox (σ j)
  rw [hfox w]
  simp_rw [hcol, Finset.mul_sum, ← mul_assoc]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  rw [← Finset.sum_mul]
  congr 1
  simpa only [map_mul, map_sum, MonoidHom.comp_apply, C, foxMatrixPres] using congrArg C (hc i)

end FiniteChains

namespace FiniteChains.Davis.Genus

open RACG Mirror Comb PresModel BlockFamily

/-- The genuine marked surface word, prior to any substitution in a core. -/
def markedSpineSurfaceWord (n : ℕ) [NeZero n] : FreeGroup (MarkedSpineGen n) :=
  commWord (fun x : Fin n × Bool => FreeGroup.of (Sum.inl x)) (finitePairs n)

theorem markedSpineFilling_exists (n : ℕ) [NeZero n] :
    ∃ c : NamedSpineRel n →₀ MonoidAlgebra ℤ (PresGroup (markedSpineBeta n)),
      coverSecondBoundary (relSub (markedSpineBeta n)) (markedSpineBeta n) c =
        coverFoxGradient (relSub (markedSpineBeta n)) (markedSpineSurfaceWord n) := by
  refine ⟨normalizedMarkedSpineFilling n (normalizedSpineReference n), ?_⟩
  apply Finsupp.ext
  intro i
  rw [fsCoverSecondBoundary_apply,
    Finsupp.sum_fintype _ _ (fun _ => zero_mul _)]
  exact normalizedMarkedSpineFilling_boundary n (normalizedSpineReference n)
    (normalizedSpineReference_boundary n) i

/-- Choose the degree-one geometric surface class once in the genuine marked
spine. This choice is independent of the core and all substituted words. -/
def markedSpineFilling (n : ℕ) [NeZero n] :
    NamedSpineRel n →₀ MonoidAlgebra ℤ (PresGroup (markedSpineBeta n)) :=
  normalizedMarkedSpineFilling n (normalizedSpineReference n)

theorem markedSpineFilling_boundary (n : ℕ) [NeZero n] (i : MarkedSpineGen n) :
    (∑ m, markedSpineFilling n m * foxMatrixPres (markedSpineBeta n) i m) =
      quotRingHom ℤ (relSub (markedSpineBeta n)) (fox i (markedSpineSurfaceWord n)) := by
  exact normalizedMarkedSpineFilling_boundary n (normalizedSpineReference n)
    (normalizedSpineReference_boundary n) i

@[simp] theorem markedSpineFilling_named_coeff (n : ℕ) [NeZero n] (m : NamedSpineRel n) :
    markedSpineFilling n m =
      MonoidAlgebra.mapDomainRingHom ℤ (spineReorderHom n)
        (normalizedNamedSpineVector n (normalizedSpineReference n) m) :=
  normalizedMarkedSpineFilling_apply n (normalizedSpineReference n) m

variable {α Jr Sx : Type} (ρ : Jr ⊕ Sx → FreeGroup α)
  (q : Sx → ℕ) [∀ s, NeZero (q s)]
  (u : ∀ s, Fin (q s) × Bool → FreeGroup α)
  (hrho : ∀ s, ρ (Sum.inr s) = commWord (u s) (finitePairs (q s)))

/-- The actual marked receiver in an individual substituted factor. -/
def finiteSpineIndividualMarkedHom (s : Sx) :
    PresGroup (markedSpineBeta (q s)) →*
      IndividualGroup ρ (familyFiniteSpineWordBlock q u) s :=
  markedBlockHom (oneRel ρ s) (fun _ : PUnit.{1} => u s)
    (fun _ : PUnit.{1} => markedSpineBeta (q s)) PUnit.unit

/-- The actual marked receiver in the simultaneous substituted group. -/
def finiteSpineFamilyMarkedHom (s : Sx) :
    PresGroup (markedSpineBeta (q s)) →*
      PresGroup (substPresF ρ (familyFiniteSpineWordBlock q u)) :=
  markedBlockHom ρ u (fun s => markedSpineBeta (q s)) s

def finiteSpineIndividualFilling (s : Sx) : NamedSpineRel (q s) →₀
    MonoidAlgebra ℤ (IndividualGroup ρ (familyFiniteSpineWordBlock q u) s) :=
  (markedSpineFilling (q s)).mapRange
    (MonoidAlgebra.mapDomainRingHom ℤ (finiteSpineIndividualMarkedHom ρ q u s))
    (map_zero _)

def finiteSpineFamilyFilling (s : Sx) : NamedSpineRel (q s) →₀
    MonoidAlgebra ℤ (PresGroup (substPresF ρ (familyFiniteSpineWordBlock q u))) :=
  (markedSpineFilling (q s)).mapRange
    (MonoidAlgebra.mapDomainRingHom ℤ (finiteSpineFamilyMarkedHom ρ q u s))
    (map_zero _)

include hrho in
theorem finiteSpineFamily_surfaceWord (s : Sx) :
    FreeGroup.map (genEmb (Zt := fun s => SpinePresentationGen (q s)) s)
      (blockSubst (Zt := fun s => SpinePresentationGen (q s)) u s
        (markedSpineSurfaceWord (q s))) =
    FreeGroup.map (Sum.inl (β := Σ s, SpinePresentationGen (q s))) (ρ (Sum.inr s)) := by
  have hm : (FreeGroup.map (genEmb (Zt := fun s => SpinePresentationGen (q s)) s)).comp
      (FreeGroup.map (Sum.inl (β := SpinePresentationGen (q s)))) =
      FreeGroup.map (Sum.inl (α := α) (β := Σ s, SpinePresentationGen (q s))) := by
    apply FreeGroup.ext_hom
    intro a
    simp
  rw [markedSpineSurfaceWord, map_commWord, map_commWord]
  simp only [blockSubst_of_inl]
  simp_rw [← MonoidHom.comp_apply, hm]
  rw [← map_commWord, hrho s]

/-- Actual B1 for the arbitrary genus family, with no geometric hypothesis left. -/
theorem finiteSpineFamilyFilling_isFilling :
    IsFillingFS ρ (familyFiniteSpineWordBlock q u)
      (familyFiniteSpineWordBlock_filled ρ q u hrho)
      (finiteSpineFamilyFilling ρ q u) := by
  have hboundary (s : Sx) (i : α ⊕ (Σ s, SpinePresentationGen (q s))) :=
    fox_filling_wordHom (markedSpineBeta (q s))
      (relSub (substPresF ρ (familyFiniteSpineWordBlock q u)))
      ((FreeGroup.map (genEmb (Zt := fun s => SpinePresentationGen (q s)) s)).comp
        (blockSubst (Zt := fun s => SpinePresentationGen (q s)) u s))
      (finiteSpineFamilyMarkedHom ρ q u s) (fun _ => rfl)
      (markedSpineFilling (q s)) (markedSpineSurfaceWord (q s))
      (markedSpineFilling_boundary (q s)) i
  apply isFillingFS_of_finite_blocks
  · intro s i
    have h := hboundary s (Sum.inl i)
    change (∑ m, finiteSpineFamilyFilling ρ q u s m *
      foxMatrixPres (substPresF ρ (familyFiniteSpineWordBlock q u))
        (Sum.inl i) (Sum.inr ⟨s, m⟩)) =
      quotRingHom ℤ _ (fox (Sum.inl i)
        (FreeGroup.map (genEmb s) (blockSubst u s (markedSpineSurfaceWord (q s))))) at h
    rw [finiteSpineFamily_surfaceWord ρ q u hrho,
      fox_map Sum.inl Sum.inl_injective, ← coeffF_quotRingHom ρ
        (familyFiniteSpineWordBlock q u) (familyFiniteSpineWordBlock_filled ρ q u hrho)] at h
    exact h
  · intro s z
    have h := hboundary s (Sum.inr ⟨s, z⟩)
    change (∑ m, finiteSpineFamilyFilling ρ q u s m *
      foxMatrixPres (substPresF ρ (familyFiniteSpineWordBlock q u))
        (Sum.inr ⟨s, z⟩) (Sum.inr ⟨s, m⟩)) =
      quotRingHom ℤ _ (fox (Sum.inr ⟨s, z⟩)
        (FreeGroup.map (genEmb s) (blockSubst u s (markedSpineSurfaceWord (q s))))) at h
    rw [finiteSpineFamily_surfaceWord ρ q u hrho,
      fox_map_of_not_mem_range Sum.inl (fun _ => Sum.inr_ne_inl), map_zero] at h
    exact h

theorem finiteSpineFactor_marked (s : Sx) :
    (finiteSpineFactorToFamily ρ q u hrho s).comp
      (finiteSpineIndividualMarkedHom ρ q u s) = finiteSpineFamilyMarkedHom ρ q u s := by
  apply MonoidHom.ext
  intro x
  induction x using QuotientGroup.induction_on with
  | _ w =>
      change QuotientGroup.mk (FreeGroup.map
        (individualGenEmb (α := α) (Zt := fun s => SpinePresentationGen (q s)) s)
        (FreeGroup.map (genEmb (Zt := fun _ : PUnit.{1} => SpinePresentationGen (q s))
          PUnit.unit) (blockSubst (Zt := fun s => SpinePresentationGen (q s)) u s w))) = _
      rw [individualGenEmb_block]
      rfl

/-- The reference family filling is the coefficient image of the individual one. -/
theorem finiteSpineFamilyFilling_coeff (s : Sx) (m : NamedSpineRel (q s)) :
    finiteSpineFamilyFilling ρ q u s m =
      finiteSpineFactorRingHom ρ q u hrho s (finiteSpineIndividualFilling ρ q u s m) := by
  change MonoidAlgebra.mapDomainRingHom ℤ (finiteSpineFamilyMarkedHom ρ q u s)
      (markedSpineFilling (q s) m) =
    MonoidAlgebra.mapDomainRingHom ℤ (finiteSpineFactorToFamily ρ q u hrho s)
      (MonoidAlgebra.mapDomainRingHom ℤ (finiteSpineIndividualMarkedHom ρ q u s)
        (markedSpineFilling (q s) m))
  rw [BlockMor.mapDomainRingHom_comp', finiteSpineFactor_marked]

/-- The actual internal Fox matrix commutes with the individual factor inclusion. -/
theorem finiteSpineFactor_internalMatrix (s : Sx) (z : SpinePresentationGen (q s))
    (m : NamedSpineRel (q s)) :
    foxMatrixPres (substPresF ρ (familyFiniteSpineWordBlock q u))
      (Sum.inr ⟨s, z⟩) (Sum.inr ⟨s, m⟩) =
    finiteSpineFactorRingHom ρ q u hrho s
      (foxMatrixPres (substPresF (oneRel ρ s)
        (fun _ : PUnit.{1} => familyFiniteSpineWordBlock q u s))
        (Sum.inr ⟨PUnit.unit, z⟩) (Sum.inr ⟨PUnit.unit, m⟩)) := by
  have hf : foxMatrixPres (substPresF ρ (familyFiniteSpineWordBlock q u))
      (Sum.inr ⟨s, z⟩) (Sum.inr ⟨s, m⟩) =
      MonoidAlgebra.mapDomainRingHom ℤ (finiteSpineFamilyMarkedHom ρ q u s)
        (foxMatrixPres (markedSpineBeta (q s)) (Sum.inr z) m) := by
    convert foxMatrix_markedBlock_internal ρ u (fun t => markedSpineBeta (q t)) s z m using 1 <;> rfl
  have hi : foxMatrixPres (substPresF (oneRel ρ s)
      (fun _ : PUnit.{1} => familyFiniteSpineWordBlock q u s))
      (Sum.inr ⟨PUnit.unit, z⟩) (Sum.inr ⟨PUnit.unit, m⟩) =
      MonoidAlgebra.mapDomainRingHom ℤ (finiteSpineIndividualMarkedHom ρ q u s)
        (foxMatrixPres (markedSpineBeta (q s)) (Sum.inr z) m) := by
    convert foxMatrix_markedBlock_internal (oneRel ρ s)
        (fun _ : PUnit.{1} => u s) (fun _ : PUnit.{1} => markedSpineBeta (q s))
        PUnit.unit z m using 1 <;> rfl
  rw [hf, hi]
  change _ = MonoidAlgebra.mapDomainRingHom ℤ (finiteSpineFactorToFamily ρ q u hrho s)
    (MonoidAlgebra.mapDomainRingHom ℤ (finiteSpineIndividualMarkedHom ρ q u s) _)
  rw [BlockMor.mapDomainRingHom_comp', finiteSpineFactor_marked]

/-- The remaining geometric statement, over each actual individual substituted
group and with the fixed genuine marked-surface coefficients. -/
def FiniteSpineIndividualB2 : Prop :=
  ∀ (s : Sx) (v : NamedSpineRel (q s) →
    MonoidAlgebra ℤ (IndividualGroup ρ (familyFiniteSpineWordBlock q u) s)),
    (∀ z : SpinePresentationGen (q s), ∑ m, v m *
      foxMatrixPres (substPresF (oneRel ρ s)
        (fun _ : PUnit.{1} => familyFiniteSpineWordBlock q u s))
        (Sum.inr ⟨PUnit.unit, z⟩) (Sum.inr ⟨PUnit.unit, m⟩) = 0) →
    ∃ r, ∀ m, v m = r * finiteSpineIndividualFilling ρ q u s m

include hrho in
/-- Individual B2 implies family B2 through the proved injective factor maps.
No finiteness of the old presentation or of the replaced family is imposed. -/
theorem finiteSpineFamilyB2_of_individual (hB2 : FiniteSpineIndividualB2 ρ q u) :
    BlockSurfaceGeneratesFS ρ (familyFiniteSpineWordBlock q u)
      (finiteSpineFamilyFilling ρ q u) := by
  apply blockSurfaceGeneratesFS_of_finite_blocks
  intro s v hv
  obtain ⟨r, hr⟩ := principal_cycles_baseChange
    (finiteSpineFactorToFamily ρ q u hrho s)
    (finiteSpineFactorToFamily_injective ρ q u hrho s)
    (fun z m => foxMatrixPres (substPresF (oneRel ρ s)
      (fun _ : PUnit.{1} => familyFiniteSpineWordBlock q u s))
      (Sum.inr ⟨PUnit.unit, z⟩) (Sum.inr ⟨PUnit.unit, m⟩))
    (finiteSpineIndividualFilling ρ q u s) (hB2 s) v (by
      intro z
      simpa only [finiteSpineFactor_internalMatrix ρ q u hrho,
        finiteSpineFactorRingHom] using hv z)
  refine ⟨r, fun m => ?_⟩
  rw [finiteSpineFamilyFilling_coeff ρ q u hrho]
  exact hr m

/-- Actual arbitrary-family finite-support generation, with B1 and injection
fully discharged. Only the concrete individual B2 remains as an input. -/
theorem finiteSpineFamily_fsGenerates (hB2 : FiniteSpineIndividualB2 ρ q u)
    (x : (Jr ⊕ (Σ s, NamedSpineRel (q s))) →₀
      MonoidAlgebra ℤ (PresGroup (substPresF ρ (familyFiniteSpineWordBlock q u))))
    (hx : coverSecondBoundary (relSub (substPresF ρ (familyFiniteSpineWordBlock q u)))
      (substPresF ρ (familyFiniteSpineWordBlock q u)) x = 0) :
    x ∈ Submodule.span
      (MonoidAlgebra ℤ (PresGroup (substPresF ρ (familyFiniteSpineWordBlock q u))))
      {v | ∃ y : (Jr ⊕ Sx) →₀ MonoidAlgebra ℤ (PresGroup ρ),
        coverSecondBoundary (relSub ρ) ρ y = 0 ∧
        v = fsCellsF ρ (familyFiniteSpineWordBlock q u)
          (familyFiniteSpineWordBlock_filled ρ q u hrho)
          (finiteSpineFamilyFilling ρ q u) y} :=
  fsGenerates_familySubst ρ (familyFiniteSpineWordBlock q u)
    (familyFiniteSpineWordBlock_filled ρ q u hrho) (finiteSpineFamilyFilling ρ q u)
    (finiteSpineFamilyFilling_isFilling ρ q u hrho)
    (finiteSpineFamilyB2_of_individual ρ q u hrho hB2)
    (familyFiniteSpineWordBlock_injective ρ q u hrho) x hx

end FiniteChains.Davis.Genus
