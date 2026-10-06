import RequestProject.GenusSpineSubstitutedBoundary
import RequestProject.ReceivedTreeComparison
import RequestProject.ReceivedTreeFoxCoordinates

/-! A genuine spine cover with the actual substituted group as its sheet set. -/
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains.Davis.Genus
open RACG Mirror Comb BlockFamily
open scoped Classical
variable {A Jr S : Type} (ρ : Jr ⊕ S → FreeGroup A)
  (q : S → ℕ) [∀ s, NeZero (q s)] (u : ∀ s, Fin (q s) × Bool → FreeGroup A)

noncomputable def receivedSpineWordReceiver (s : S) : PresGroup (spinePresentation (q s)) →*
    PresGroup (substPresF ρ (familyFiniteSpineWordBlock q u)) :=
  (familySpineHom ρ q u s).comp
    (NamedPresentation.inclusion (spinePresentation (q s)) (spinePresentationMarkedWord (q s)))

noncomputable abbrev receivedSpineCover (s : S) : Complex2 :=
  ReceivedTree.cover (markedSpineTree (q s)) (receivedSpineWordReceiver ρ q u s)

noncomputable def receivedSpineProjection (s : S) :
    Hom (receivedSpineCover ρ q u s) (markedSpineCx (q s)) :=
  ReceivedTree.projection (markedSpineTree (q s)) (receivedSpineWordReceiver ρ q u s)

theorem receivedSpineProjection_isCovering (s : S) : IsCovering (receivedSpineProjection ρ q u s) :=
  ReceivedTree.projection_isCovering _ _

theorem receivedSpineProjection_isRegular (s : S) :
    IsRegular (receivedSpineProjection ρ q u s)
      (ReceivedTree.deck (markedSpineTree (q s)) (receivedSpineWordReceiver ρ q u s)) :=
  ReceivedTree.projection_isRegular _ _

/-- Its word coefficients are exactly the coefficient map in the relative Fox
boundary already proved for the substituted family. -/
theorem receivedSpineWordReceiver_coeff (s : S) (x : FreeGroupRing (SpinePresentationGen (q s))) :
    MonoidAlgebra.mapDomainRingHom ℤ (receivedSpineWordReceiver ρ q u s)
      (quotRingHom ℤ (relSub (spinePresentation (q s))) x) =
    NamedPresentation.receivedWordCoefficientMap (spinePresentation (q s))
      (spinePresentationMarkedWord (q s)) (familySpineHom ρ q u s) x := by
  unfold NamedPresentation.receivedWordCoefficientMap NamedPresentation.wordCoefficientMap
  change MonoidAlgebra.mapDomainRingHom ℤ (receivedSpineWordReceiver ρ q u s)
      (MonoidAlgebra.mapDomainRingHom ℤ
        (QuotientGroup.mk' (relSub (spinePresentation (q s)))) x) =
    MonoidAlgebra.mapDomainRingHom ℤ (familySpineHom ρ q u s)
      (MonoidAlgebra.mapDomainRingHom ℤ
        (QuotientGroup.mk' (relSub (namedSpinePresentation (q s))))
        (MonoidAlgebra.mapDomainRingHom ℤ (FreeGroup.map Sum.inl) x))
  simp only [BlockMor.mapDomainRingHom_comp']
  congr 1

set_option maxHeartbeats 500000 in
theorem familySpineHom_marked (s : S) (i : Fin (q s) × Bool) :
    familySpineHom ρ q u s (QuotientGroup.mk (FreeGroup.of (Sum.inr i))) =
      QuotientGroup.mk (FreeGroup.map (Sum.inl (β := Σ s, SpinePresentationGen (q s))) (u s i)) := by
  change QuotientGroup.mk (FreeGroup.map (genEmb s)
      (blockSubst u s (FreeGroup.map Sum.swap (FreeGroup.of (Sum.inr i))))) = _
  rw (config := { transparency := .default }) [FreeGroup.map.of, Sum.swap_inr, blockSubst_of_inl]
  have h : (FreeGroup.map (genEmb (α := A) (Zt := fun s => SpinePresentationGen (q s)) s)).comp
      (FreeGroup.map (Sum.inl (β := SpinePresentationGen (q s)))) =
      FreeGroup.map (Sum.inl (β := Σ s, SpinePresentationGen (q s))) := by
    apply FreeGroup.ext_hom
    intro a
    simp
  exact congrArg QuotientGroup.mk (DFunLike.congr_fun h (u s i))

/-- Traversing the actual marked spine loop changes the sheet by the prescribed
old word in the actual substituted group. -/
theorem receivedSpine_marked_wordValue (s : S) (i : Fin (q s) × Bool) :
    ReceivedTree.wordValue (markedSpineTree (q s)) (receivedSpineWordReceiver ρ q u s)
      (markedSpineLoop (q s) i).1 =
      QuotientGroup.mk (FreeGroup.map (Sum.inl (β := Σ s, SpinePresentationGen (q s))) (u s i)) := by
  change familySpineHom ρ q u s
      (QuotientGroup.mk (FreeGroup.map Sum.inl (spinePresentationMarkedWord (q s) i))) = _
  have hn := NamedPresentation.name_eq_word (spinePresentation (q s))
    (spinePresentationMarkedWord (q s)) i
  exact (congrArg (familySpineHom ρ q u s) hn.symm).trans
    (familySpineHom_marked ρ q u s i)

/-- The old-face part of a named coefficient vector as an actual finite chain
in the constructed cover, with every group coefficient retained. -/
noncomputable def receivedSpineFaceChain (s : S)
    (β : NamedSpineRel (q s) → MonoidAlgebra ℤ
      (PresGroup (substPresF ρ (familyFiniteSpineWordBlock q u)))) :
    (receivedSpineCover ρ q u s).F →₀ ℤ :=
  (ReceivedTree.cellCoordinates (SpinePresentationRel (q s))).symm (fun j => β (Sum.inl j))

theorem receivedSpineFaceChain_coefficient (s : S)
    (β : NamedSpineRel (q s) → MonoidAlgebra ℤ
      (PresGroup (substPresF ρ (familyFiniteSpineWordBlock q u)))) (j : SpinePresentationRel (q s)) :
    ReceivedTree.cellCoefficient j (receivedSpineFaceChain ρ q u s β) = β (Sum.inl j) :=
  ReceivedTree.cellCoefficient_coordinates_symm _ _ _

/-- The actual two-boundary of the old face chain has the prescribed marked-word
coordinates whenever the genuine B2 internal-coordinate condition holds. -/
theorem receivedSpineFaceChain_relative_boundary (s : S)
    (β : NamedSpineRel (q s) → MonoidAlgebra ℤ
      (PresGroup (substPresF ρ (familyFiniteSpineWordBlock q u))))
    (hβ : ∀ z : SpinePresentationGen (q s),
      (∑ m, β m * foxMatrixPres (substPresF ρ (familyFiniteSpineWordBlock q u))
        (Sum.inr ⟨s, z⟩) (Sum.inr ⟨s, m⟩)) = 0)
    (z : SpinePresentationGen (q s)) :
    ReceivedTree.cellCoefficient z.1
      (Comb.bdry2 (receivedSpineCover ρ q u s) (receivedSpineFaceChain ρ q u s β)) =
      ∑ i, β (Sum.inr i) * NamedPresentation.receivedWordCoefficientMap
        (spinePresentation (q s)) (spinePresentationMarkedWord (q s))
        (familySpineHom ρ q u s) (fox z (spinePresentationMarkedWord (q s) i)) := by
  rw (config := { transparency := .default }) [ReceivedTree.cellCoefficient_bdry2]
  simp only [receivedSpineFaceChain_coefficient, ReceivedTree.coefficientMap,
    RingHom.comp_apply]
  change (∑ j, β (Sum.inl j) * MonoidAlgebra.mapDomainRingHom ℤ
    (receivedSpineWordReceiver ρ q u s)
    (quotRingHom ℤ (relSub (spinePresentation (q s)))
      (fox z (spinePresentation (q s) j)))) = _
  simp only [receivedSpineWordReceiver_coeff]
  exact (familySpine_internal_zero_iff ρ q u s β).mp hβ z

end FiniteChains.Davis.Genus
