module

public import RequestProject.GenusUniversalCoveredSpine
public import RequestProject.GenusSpineSubstitutedBoundary
public import RequestProject.ReceivedTreeMarkedChains
public import RequestProject.CrowellFinsupp
public import RequestProject.BlockFamilyBlockwiseFinsupp

@[expose] public section

/-! Convert a geometrically normalized pre-substitution spine filling to the
full named Fox filling, preserving the marked coefficients and the original
face coordinates. The geometric choice is made by the surface construction;
this file supplies its exact algebraic interface. Awaiting Lean verification. -/
noncomputable section
open scoped Classical
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains.Davis.Genus
open RACG Mirror Comb BlockFamily
variable (q : ℕ) [NeZero q]

theorem sum_namedSpineRel {M : Type*} [AddCommMonoid M]
    (f : NamedSpineRel q → M) :
    (∑ m, f m) = (∑ j : SpinePresentationRel q, f (Sum.inl j)) +
      ∑ i : Fin q × Bool, f (Sum.inr i) := by
  have hu : (Finset.univ : Finset (NamedSpineRel q)) =
      @Finset.univ (NamedSpineRel q)
        (instFintypeSum (SpinePresentationRel q) (Fin q × Bool)) :=
    congrArg (@Finset.univ (NamedSpineRel q)) (Subsingleton.elim _ _)
  exact (congrArg (fun s : Finset (NamedSpineRel q) => ∑ m ∈ s, f m) hu).trans
    (Fintype.sum_sum_type f)

def namedSpineSurfaceWord : FreeGroup (NamedSpineGen q) :=
  commWord (fun i : Fin q × Bool => FreeGroup.of (Sum.inr i)) (finitePairs q)

def namedSpineSurfaceMarkingCoefficient (i : Fin q × Bool) :
    MonoidAlgebra ℤ (PresGroup (namedSpinePresentation q)) :=
  quotRingHom ℤ (relSub (namedSpinePresentation q))
    (fox (Sum.inr i) (namedSpineSurfaceWord q))

def normalizedNamedSpineVector (d : (universalNamedSpineCover q).F →₀ ℤ) :
    NamedSpineRel q → MonoidAlgebra ℤ (PresGroup (namedSpinePresentation q)) :=
  Sum.elim (fun j => ReceivedTree.cellCoefficient j d) (namedSpineSurfaceMarkingCoefficient q)

theorem universalSpineWordCoefficient (x : FreeGroupRing (SpinePresentationGen q)) :
    ReceivedTree.coefficientMap (markedSpineTree q) (universalSpineWordReceiver q) x =
      NamedPresentation.wordCoefficientMap (spinePresentation q) (spinePresentationMarkedWord q) x := by
  change MonoidAlgebra.mapDomainRingHom ℤ (universalSpineWordReceiver q)
      (MonoidAlgebra.mapDomainRingHom ℤ (QuotientGroup.mk' (relSub (spinePresentation q))) x) =
    MonoidAlgebra.mapDomainRingHom ℤ (QuotientGroup.mk' (relSub (namedSpinePresentation q)))
      (MonoidAlgebra.mapDomainRingHom ℤ (FreeGroup.map Sum.inl) x)
  simp only [BlockMor.mapDomainRingHom_comp']
  congr 1

theorem namedSpineSurfaceWord_fox_internal (z : SpinePresentationGen q) :
    fox (Sum.inl z) (namedSpineSurfaceWord q) = 0 := by
  have hw : namedSpineSurfaceWord q = FreeGroup.map Sum.inr
      (commWord (fun i : Fin q × Bool => FreeGroup.of i) (finitePairs q)) := by
    simp only [namedSpineSurfaceWord, map_commWord, FreeGroup.map.of]
  rw (config := { transparency := .default }) [hw]
  exact fox_map_of_not_mem_range Sum.inr (fun _ => Sum.inl_ne_inr) _

/-- An initial filling with this exact boundary exists before geometric
normalization. Its arbitrary homology class will subsequently be adjusted to
the explicitly constructed degree-one polygon. -/
theorem exists_universalNamedSpine_markedFilling :
    ∃ d : (universalNamedSpineCover q).F →₀ ℤ,
      Comb.bdry2 (universalNamedSpineCover q) d =
        ReceivedTree.markedChain (markedSpineTree q) (universalSpineWordReceiver q)
          (treeMarkedSpineLoop q) (namedSpineSurfaceMarkingCoefficient q) := by
  have hw : namedSpineSurfaceWord q ∈ relSub (namedSpinePresentation q) := by
    apply (QuotientGroup.eq_one_iff _).mp
    change (QuotientGroup.mk' (relSub (namedSpinePresentation q))) (namedSpineSurfaceWord q) = 1
    rw (config := { transparency := .default }) [namedSpineSurfaceWord, map_commWord]
    exact namedSpine_surface_filling q
  obtain ⟨c, hc⟩ := exists_coverSecondBoundary_of_mem_normalClosure
    (N := relSub (namedSpinePresentation q)) (ρ := namedSpinePresentation q)
    (fun m => Subgroup.subset_normalClosure ⟨m, rfl⟩) hw
  have hrow (a : NamedSpineGen q) :
      (∑ m, c m * foxMatrixPres (namedSpinePresentation q) a m) =
        quotRingHom ℤ (relSub (namedSpinePresentation q)) (fox a (namedSpineSurfaceWord q)) := by
    have h := congrArg (fun x => x a) hc
    rw (config := { transparency := .default }) [fsCoverSecondBoundary_apply, Finsupp.sum_fintype _ _ (fun _ => zero_mul _)] at h
    exact h
  have hm (i : Fin q × Bool) : c (Sum.inr i) = namedSpineSurfaceMarkingCoefficient q i := by
    have h := hrow (Sum.inr i)
    rw (config := { transparency := .default }) [sum_namedSpineRel] at h
    simpa [namedSpinePresentation,
      NamedPresentation.matrix_marked_relator, NamedPresentation.matrix_marked_name,
      namedSpineSurfaceMarkingCoefficient] using h
  let d : (universalNamedSpineCover q).F →₀ ℤ :=
    (ReceivedTree.cellCoordinates (SpinePresentationRel q)).symm (fun j => c (Sum.inl j))
  refine ⟨d, ?_⟩
  apply ReceivedTree.bdry2_eq_markedChain_of_coordinates
    (markedSpineTree q) (universalSpineWordReceiver q)
    (treeMarkedSpineLoop q) (namedSpineSurfaceMarkingCoefficient q) d
  intro z
  rw (config := { transparency := .default }) [ReceivedTree.cellCoefficient_bdry2]
  simp only [d, ReceivedTree.cellCoefficient_coordinates_symm,
    universalSpineWordCoefficient, treeMarkedSpineLoop]
  have hz := hrow (Sum.inl z)
  rw (config := { transparency := .default }) [namedSpineSurfaceWord_fox_internal, map_zero] at hz
  rw (config := { transparency := .default }) [sum_namedSpineRel] at hz
  simp only [namedSpinePresentation, NamedPresentation.matrix_internal_relator,
    NamedPresentation.matrix_internal_name, mul_neg, Finset.sum_neg_distrib,
    ← sub_eq_add_neg] at hz
  refine (sub_eq_zero.mp hz).trans ?_
  apply Finset.sum_congr rfl
  intro i _
  exact congrArg (fun x => x * NamedPresentation.wordCoefficientMap
    (spinePresentation q) (spinePresentationMarkedWord q)
    (fox z (spinePresentationMarkedWord q i))) (hm i)

/-- Every actual filling with the prescribed marked boundary gives all Fox
coordinates, including the name-relator coordinates, with their exact signs. -/
theorem normalizedNamedSpineVector_boundary
    (d : (universalNamedSpineCover q).F →₀ ℤ)
    (hd : Comb.bdry2 (universalNamedSpineCover q) d =
      ReceivedTree.markedChain (markedSpineTree q) (universalSpineWordReceiver q)
        (treeMarkedSpineLoop q) (namedSpineSurfaceMarkingCoefficient q))
    (a : NamedSpineGen q) :
    (∑ m, normalizedNamedSpineVector q d m * foxMatrixPres (namedSpinePresentation q) a m) =
      quotRingHom ℤ (relSub (namedSpinePresentation q)) (fox a (namedSpineSurfaceWord q)) := by
  cases a with
  | inl z =>
      have h := congrArg (ReceivedTree.cellCoefficient z.1) hd
      rw (config := { transparency := .default }) [ReceivedTree.cellCoefficient_bdry2, ReceivedTree.cellCoefficient_markedChain] at h
      simp only [universalSpineWordCoefficient, treeMarkedSpineLoop] at h
      rw (config := { transparency := .default }) [namedSpineSurfaceWord_fox_internal, map_zero]
      rw (config := { transparency := .default }) [sum_namedSpineRel]
      simp only [namedSpinePresentation, NamedPresentation.matrix_internal_relator,
        NamedPresentation.matrix_internal_name, normalizedNamedSpineVector,
        Sum.elim_inl, Sum.elim_inr, mul_neg, Finset.sum_neg_distrib]
      convert sub_eq_zero.mpr h using 1 <;>
        simp only [sub_eq_add_neg, spinePresentation, spinePresentationMarkedWord] <;> rfl
  | inr i =>
      rw (config := { transparency := .default }) [sum_namedSpineRel]
      simp [namedSpinePresentation, NamedPresentation.matrix_marked_relator,
        NamedPresentation.matrix_marked_name, normalizedNamedSpineVector,
        namedSpineSurfaceMarkingCoefficient]

theorem spineReorderHom_fox (a : NamedSpineGen q) (w : FreeGroup (NamedSpineGen q)) :
    MonoidAlgebra.mapDomainRingHom ℤ (spineReorderHom q)
      (quotRingHom ℤ (relSub (namedSpinePresentation q)) (fox a w)) =
    quotRingHom ℤ (relSub (markedSpineBeta q))
      (fox (Sum.swap a) (FreeGroup.map Sum.swap w)) := by
  simpa only [fox_map Sum.swap (Equiv.sumComm _ _).injective] using
    spineReorderHom_coeff q (fox a w)

theorem spineReorderHom_matrix (a : NamedSpineGen q) (m : NamedSpineRel q) :
    MonoidAlgebra.mapDomainRingHom ℤ (spineReorderHom q)
      (foxMatrixPres (namedSpinePresentation q) a m) =
    foxMatrixPres (markedSpineBeta q) (Sum.swap a) m :=
  spineReorderHom_fox q a (namedSpinePresentation q m)

def normalizedMarkedSpineFilling (d : (universalNamedSpineCover q).F →₀ ℤ) :
    NamedSpineRel q →₀ MonoidAlgebra ℤ (PresGroup (markedSpineBeta q)) :=
  Finsupp.equivFunOnFinite.symm (fun m =>
    MonoidAlgebra.mapDomainRingHom ℤ (spineReorderHom q) (normalizedNamedSpineVector q d m))

@[simp] theorem normalizedMarkedSpineFilling_apply
    (d : (universalNamedSpineCover q).F →₀ ℤ) (m : NamedSpineRel q) :
    normalizedMarkedSpineFilling q d m =
      MonoidAlgebra.mapDomainRingHom ℤ (spineReorderHom q) (normalizedNamedSpineVector q d m) := by
  simp [normalizedMarkedSpineFilling]

/-- This is the full pre-substitution B1 certificate for the normalized
reference; it can replace the arbitrary Crowell choice without changing any
of the later substitution or family arguments. -/
theorem normalizedMarkedSpineFilling_boundary
    (d : (universalNamedSpineCover q).F →₀ ℤ)
    (hd : Comb.bdry2 (universalNamedSpineCover q) d =
      ReceivedTree.markedChain (markedSpineTree q) (universalSpineWordReceiver q)
        (treeMarkedSpineLoop q) (namedSpineSurfaceMarkingCoefficient q))
    (a : MarkedSpineGen q) :
    (∑ m, normalizedMarkedSpineFilling q d m * foxMatrixPres (markedSpineBeta q) a m) =
      quotRingHom ℤ (relSub (markedSpineBeta q))
        (fox a (commWord (fun i : Fin q × Bool => FreeGroup.of (Sum.inl i)) (finitePairs q))) := by
  have h := congrArg (MonoidAlgebra.mapDomainRingHom ℤ (spineReorderHom q))
    (normalizedNamedSpineVector_boundary q d hd (Sum.swap a))
  simp only [map_sum, map_mul, spineReorderHom_matrix, spineReorderHom_fox,
    Sum.swap_swap] at h
  have hw : FreeGroup.map Sum.swap (namedSpineSurfaceWord q) =
      commWord (fun i : Fin q × Bool => FreeGroup.of (Sum.inl i)) (finitePairs q) := by
    simp only [namedSpineSurfaceWord, map_commWord, FreeGroup.map.of, Sum.swap_inr]
  simpa only [normalizedMarkedSpineFilling_apply, hw] using h

end FiniteChains.Davis.Genus
