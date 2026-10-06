module

public import RequestProject.GenusSquareCoefficientSupport
public import RequestProject.GenusOldCoordinateCollapse

@[expose] public section

/-! Actual recovered coordinate chains are supported on the surviving genus spine. -/
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains.Davis.Genus
open RACG Mirror Comb
variable (q : ℕ) [NeZero q]

noncomputable def markedSpineSquareCoefficients : ((markedSpineCx q).F →₀ ℤ) →ₗ[ℤ]
    (QSquare (cmpRel (GenusVertex q)) →₀ ℤ) :=
  qSquareCycleCoefficients.comp (normalizeOrdChain2.comp (chain2 (markedSpineToFullCube q)))

noncomputable def markedSpineCoordinateChain : ((markedSpineCx q).F →₀ ℤ) →ₗ[ℤ]
    (Cube (GenusVertex q) →₀ ℤ) :=
  (Finsupp.lmapDomain ℤ ℤ
    (fun s : QSquare (cmpRel (GenusVertex q)) => qCubeToCoordinate s.1)).comp
      (markedSpineSquareCoefficients q)

noncomputable def markedSpineExtendedCoordinateChain : ((markedSpineCx q).F →₀ ℤ) →ₗ[ℤ]
    ((Cube (GenusVertex q) ⊕ Finset (GenusVertex q)) →₀ ℤ) :=
  (Finsupp.lmapDomain ℤ ℤ Sum.inl).comp (markedSpineCoordinateChain q)

theorem markedSpineCoordinateChain_zero_on_removed_square
    (d : (markedSpineCx q).F →₀ ℤ) (g : Cube (GenusVertex q))
    (hg : Sum.inl g ∈ (genusChainCollapse q).map Prod.snd) :
    markedSpineCoordinateChain q d g = 0 := by
  classical
  by_contra hn
  have hmem := Finsupp.mem_support_iff.mpr hn
  change g ∈ (Finsupp.mapDomain
    (fun s : QSquare (cmpRel (GenusVertex q)) => qCubeToCoordinate s.1)
    (markedSpineSquareCoefficients q d)).support at hmem
  obtain ⟨s, hs, he⟩ := Finset.mem_image.mp (Finsupp.mapDomain_support hmem)
  obtain ⟨a, ha, hae⟩ := markedSpine_square_coefficient_support q d s
    (Finsupp.mem_support_iff.mp hs)
  have hnot := ha.2
  change Sum.inl (qCubeToCoordinate a.1) ∉ (genusChainCollapse q).map Prod.snd at hnot
  rw [hae, he] at hnot
  exact hnot hg

theorem markedSpineExtendedCoordinateChain_zero_on_removed_face
    (d : (markedSpineCx q).F →₀ ℤ) (f : Cube (GenusVertex q) ⊕ Finset (GenusVertex q))
    (hf : f ∈ (genusChainCollapse q).map Prod.snd) :
    markedSpineExtendedCoordinateChain q d f = 0 := by
  classical
  cases f with
  | inl g =>
      change Finsupp.mapDomain
        (Sum.inl : Cube (GenusVertex q) → Cube (GenusVertex q) ⊕ Finset (GenusVertex q))
        (markedSpineCoordinateChain q d) (Sum.inl g) = 0
      rw [Finsupp.mapDomain_apply_of_injective Sum.inl_injective]
      exact markedSpineCoordinateChain_zero_on_removed_square q d g hf
  | inr σ =>
      exact Finsupp.mapDomain_notin_range _ _ (by rintro ⟨g, he⟩; cases he)

/-- The actual recovered coordinate chain of every old-spine two-chain is fixed by the
chosen geometric collapse because it has no coefficient on a removed face. -/
theorem markedSpineExtendedCoordinateChain_fixed (d : (markedSpineCx q).F →₀ ℤ) :
    CollapseChain.cmap (cubeBdry (V := GenusVertex q)) (genusChainCollapse q)
      (markedSpineExtendedCoordinateChain q d) = markedSpineExtendedCoordinateChain q d := by
  apply CollapseChain.cmap_of_forall_eq_zero
  intro p hp
  exact markedSpineExtendedCoordinateChain_zero_on_removed_face q d p.2
    (List.mem_map.mpr ⟨p, hp, rfl⟩)

end FiniteChains.Davis.Genus
