module

public import RequestProject.GenusQuotientRelativeSupport

@[expose] public section

/-! Lift the actual surface markings to the genuine attaching cover and apply
the relative old-chain filling theorem. Pending final Lean verification.
-/

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains.Comb
universe u
variable {P : Type u} [PartialOrder P] {a : P}

theorem universalNerveChain1_uOrderHom (c : OrdEdge (UOrder P a) →₀ ℤ) :
    universalNerveChain1 (chain1 uOrderHom c) = ordNerveChain1 c := by
  change ordNerveChain1
    (Finsupp.mapDomain uOrderHomInv.onE (Finsupp.mapDomain uOrderHom.onE c)) = _
  rw (config := { transparency := .default }) [← Finsupp.mapDomain_comp]
  have h : (uOrderHomInv (P := P) (a := a)).onE ∘ uOrderHom.onE = id := by
    funext e
    exact homInv_onE_comp uOrderHom Function.bijective_id
      ⟨uOrderEdge_injective, uOrderEdge_surjective⟩
      ⟨uOrderFace_injective, uOrderFace_surjective⟩ e
  rw (config := { transparency := .default }) [h, Finsupp.mapDomain_id]

end FiniteChains.Comb

namespace FiniteChains.Davis
open RACG Mirror Comb
universe u
variable {V : Type u} [DecidableEq V] {A : CommRel V}
  {X : Type u} [PartialOrder X] {att : NeSpx A →o X}

/-- The attaching-cover projection reconstructs its actual endpoint in the quotient. -/
theorem qAttachingCoverEnd_spec (a : Qpos A X att) (p : QLiftedAttaching a) :
    qOldIncl (att := att) (posQCube (qAttachingCoverEnd a p)) = uOrderEnd p.1 := by
  exact congrArg Subtype.val
    ((qPositiveOldOrderIso (att := att)).symm_apply_apply ⟨uOrderEnd p.1, p.2⟩)

end FiniteChains.Davis

namespace FiniteChains.Davis.Genus
open RACG Mirror Comb PresModel BlockFamily Nerve
open scoped Classical
variable (q : ℕ) [NeZero q] {α Jr : Type}
  (ρ : Jr ⊕ PUnit.{1} → FreeGroup α) (u : Fin q × Bool → FreeGroup α)
  (hrho : ρ (Sum.inr PUnit.unit) = commWord u (finitePairs q))

noncomputable abbrev namedAttachingCover := QLiftedAttaching (namedQuotientBase ρ q u)

theorem namedAttachingEnd_isPosetCover :
    IsPosetCover (qAttachingCoverEnd (namedQuotientBase ρ q u)) :=
  qAttachingCoverEnd_isPosetCover (namedAtt ρ q u (gBase q))
    (namedBasePos_isConnected ρ q u)

noncomputable def namedAttachingProjection :
    Hom (orderCx (namedAttachingCover q ρ u))
      (orderCx (NeSpx (cmpRel (GenusVertex q)))) :=
  orderCxMap (qAttachingCoverEnd (namedQuotientBase ρ q u))
    (namedAttachingEnd_isPosetCover q ρ u).mono

theorem namedAttachingProjection_isCovering :
    IsCovering (namedAttachingProjection q ρ u) :=
  isCovering_orderCxMap (namedAttachingEnd_isPosetCover q ρ u)

noncomputable def namedAttachingIntoUniversal :
    Hom (orderCx (namedAttachingCover q ρ u))
      (uCover (orderCx (namedQuotientPos ρ q u)) (namedQuotientBase ρ q u)) :=
  uOrderHom.comp (orderCxMap Subtype.val (fun _ _ h => h))

noncomputable def namedSurfaceIntoQuotient :
    Hom (orderCx (NeSpx (cmpRel (GenusVertex q)))) (orderCx (namedQuotientPos ρ q u)) :=
  (oldIntoNamedQuotient q ρ u).comp (surfCx (cmpRel (GenusVertex q)))

theorem namedAttachingIntoUniversal_projects :
    (univProj (orderCx (namedQuotientPos ρ q u)) (namedQuotientBase ρ q u)).comp
      (namedAttachingIntoUniversal q ρ u) =
      (namedSurfaceIntoQuotient q ρ u).comp (namedAttachingProjection q ρ u) := by
  apply Hom.ext'
  · funext p
    exact (qAttachingCoverEnd_spec (namedQuotientBase ρ q u) p).symm
  · funext e
    apply Subtype.ext
    exact Prod.ext
      (qAttachingCoverEnd_spec (namedQuotientBase ρ q u) e.1.1).symm
      (qAttachingCoverEnd_spec (namedQuotientBase ρ q u) e.1.2).symm
  · funext t
    apply Subtype.ext
    exact Prod.ext
      (qAttachingCoverEnd_spec (namedQuotientBase ρ q u) t.1.1).symm
      (Prod.ext
        (qAttachingCoverEnd_spec (namedQuotientBase ρ q u) t.1.2.1).symm
        (qAttachingCoverEnd_spec (namedQuotientBase ρ q u) t.1.2.2).symm)

noncomputable def namedAttachingReference
    (g : PresGroup (substPresF ρ (finiteSpineWordBlock q u))) :
    namedAttachingCover q ρ u :=
  ⟨deckV (finiteSpineToQuotient ρ q u hrho g) (quotientCylinderVertex q ρ u), by
    change InQOld (endV (deckV (finiteSpineToQuotient ρ q u hrho g)
        (quotientCylinderVertex q ρ u))) ∧
      InQBaseStar (endV (deckV (finiteSpineToQuotient ρ q u hrho g)
        (quotientCylinderVertex q ρ u)))
    simp only [endV_deckV, quotientCylinderVertex_end]
    exact ⟨trivial, rfl⟩⟩

theorem namedAttachingReference_projects
    (g : PresGroup (substPresF ρ (finiteSpineWordBlock q u))) :
    (namedAttachingProjection q ρ u).onV (namedAttachingReference q ρ u hrho g) =
      gBase q := by
  apply (qPositiveOldOrderIso (att := namedAtt ρ q u)).symm.injective
  apply Subtype.ext
  change qOldIncl (att := namedAtt ρ q u)
    (posQCube (qAttachingCoverEnd (namedQuotientBase ρ q u)
      (namedAttachingReference q ρ u hrho g))) =
    qOldIncl (att := namedAtt ρ q u) (posQCube (gBase q))
  rw (config := { transparency := .default }) [qAttachingCoverEnd_spec]
  change endV (deckV _ (quotientCylinderVertex q ρ u)) = _
  rw (config := { transparency := .default }) [endV_deckV, quotientCylinderVertex_end]
  rfl

theorem exists_namedAttachingMarkingPath
    (g : PresGroup (substPresF ρ (finiteSpineWordBlock q u))) (i : Fin q × Bool) :
    ∃ p : List ((orderCx (namedAttachingCover q ρ u)).E × Bool),
      ∃ b : namedAttachingCover q ρ u,
        IsPath (orderCx (namedAttachingCover q ρ u)).src
          (orderCx (namedAttachingCover q ρ u)).tgt p
          (namedAttachingReference q ρ u hrho g) b ∧
        mapPath (namedAttachingProjection q ρ u) p = gSig q (i.1.val, i.2) := by
  apply exists_liftPathAt (namedAttachingProjection_isCovering q ρ u)
    (gSig q (i.1.val, i.2)) (namedAttachingReference q ρ u hrho g) (gBase q)
  rw (config := { transparency := .default }) [namedAttachingReference_projects]
  exact isPath_gSig q (i.1.val, i.2)

noncomputable def namedAttachingMarkingPath
    (g : PresGroup (substPresF ρ (finiteSpineWordBlock q u))) (i : Fin q × Bool) :
    List ((orderCx (namedAttachingCover q ρ u)).E × Bool) :=
  Classical.choose (exists_namedAttachingMarkingPath q ρ u hrho g i)

noncomputable def namedAttachingMarkingEnd
    (g : PresGroup (substPresF ρ (finiteSpineWordBlock q u))) (i : Fin q × Bool) :
    namedAttachingCover q ρ u :=
  Classical.choose (Classical.choose_spec (exists_namedAttachingMarkingPath q ρ u hrho g i))

theorem namedAttachingMarkingPath_spec
    (g : PresGroup (substPresF ρ (finiteSpineWordBlock q u))) (i : Fin q × Bool) :
    IsPath (orderCx (namedAttachingCover q ρ u)).src
      (orderCx (namedAttachingCover q ρ u)).tgt (namedAttachingMarkingPath q ρ u hrho g i)
      (namedAttachingReference q ρ u hrho g) (namedAttachingMarkingEnd q ρ u hrho g i) ∧
    mapPath (namedAttachingProjection q ρ u) (namedAttachingMarkingPath q ρ u hrho g i) =
      gSig q (i.1.val, i.2) :=
  Classical.choose_spec (Classical.choose_spec (exists_namedAttachingMarkingPath q ρ u hrho g i))

/-- The image of the path lifted in the attaching cover is the actual universal-cover lift. -/
theorem namedAttachingMarkingPath_image
    (g : PresGroup (substPresF ρ (finiteSpineWordBlock q u))) (i : Fin q × Bool) :
    mapPath (namedAttachingIntoUniversal q ρ u) (namedAttachingMarkingPath q ρ u hrho g i) =
      uLiftPath (mapPath (oldIntoNamedQuotient q ρ u) (surfaceOldMarking q i))
        (deckV (finiteSpineToQuotient ρ q u hrho g) (quotientCylinderVertex q ρ u)) := by
  have hp := isPath_mapPath (namedAttachingIntoUniversal q ρ u)
    (namedAttachingMarkingPath_spec q ρ u hrho g i).1
  have he := eq_uLiftPath_of_isPath _ _ _ hp
  have hproj : mapPath
      (univProj (orderCx (namedQuotientPos ρ q u)) (namedQuotientBase ρ q u))
      (mapPath (namedAttachingIntoUniversal q ρ u)
        (namedAttachingMarkingPath q ρ u hrho g i)) =
      mapPath (namedSurfaceIntoQuotient q ρ u) (gSig q (i.1.val, i.2)) := by
    calc
      _ = mapPath
          ((univProj (orderCx (namedQuotientPos ρ q u)) (namedQuotientBase ρ q u)).comp
            (namedAttachingIntoUniversal q ρ u))
          (namedAttachingMarkingPath q ρ u hrho g i) := mapPath_comp _ _ _
      _ = mapPath ((namedSurfaceIntoQuotient q ρ u).comp (namedAttachingProjection q ρ u))
          (namedAttachingMarkingPath q ρ u hrho g i) :=
        congrArg (fun f => mapPath f (namedAttachingMarkingPath q ρ u hrho g i))
          (namedAttachingIntoUniversal_projects q ρ u)
      _ = mapPath (namedSurfaceIntoQuotient q ρ u)
          (mapPath (namedAttachingProjection q ρ u)
            (namedAttachingMarkingPath q ρ u hrho g i)) := (mapPath_comp _ _ _).symm
      _ = _ := congrArg (mapPath (namedSurfaceIntoQuotient q ρ u))
        (namedAttachingMarkingPath_spec q ρ u hrho g i).2
  have hsurf : mapPath (namedSurfaceIntoQuotient q ρ u) (gSig q (i.1.val, i.2)) =
      mapPath (oldIntoNamedQuotient q ρ u) (surfaceOldMarking q i) :=
    (mapPath_comp (oldIntoNamedQuotient q ρ u) (surfCx _) (gSig q (i.1.val, i.2))).symm
  rw (config := { transparency := .default }) [hproj, hsurf] at he
  exact he

noncomputable def namedAttachingMarkingChains :
    ((PresGroup (substPresF ρ (finiteSpineWordBlock q u)) × (Fin q × Bool)) →₀ ℤ) →ₗ[ℤ]
      (OrdEdge (namedAttachingCover q ρ u) →₀ ℤ) :=
  Finsupp.linearCombination ℤ
    (fun x => pathChain (namedAttachingMarkingPath q ρ u hrho x.1 x.2))

theorem namedAttachingMarkingChains_image
    (c : (PresGroup (substPresF ρ (finiteSpineWordBlock q u)) × (Fin q × Bool)) →₀ ℤ) :
    chain1 (namedAttachingIntoUniversal q ρ u) (namedAttachingMarkingChains q ρ u hrho c) =
      quotientSurfaceMarkingChains q ρ u hrho c := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd => rw (config := { transparency := .default }) [map_add, map_add, hc, hd, map_add]
  | single x n =>
      rw (config := { transparency := .default }) [namedAttachingMarkingChains, quotientSurfaceMarkingChains,
        Finsupp.linearCombination_single, Finsupp.linearCombination_single, map_smul]
      apply congrArg (fun z => n • z)
      change Finsupp.mapDomain (namedAttachingIntoUniversal q ρ u).onE
        (pathChain (namedAttachingMarkingPath q ρ u hrho x.1 x.2)) = _
      rw (config := { transparency := .default }) [← pathChain_map]
      exact congrArg pathChain (namedAttachingMarkingPath_image q ρ u hrho x.1 x.2)

noncomputable def namedAttachingNerveBoundary :
    ((PresGroup (substPresF ρ (finiteSpineWordBlock q u)) × (Fin q × Bool)) →₀ ℤ) →ₗ[ℤ]
      Ch (namedAttachingCover q ρ u) :=
  ordNerveChain1.comp (namedAttachingMarkingChains q ρ u hrho)

theorem namedAttachingNerveBoundary_mem_inc
    (c : (PresGroup (substPresF ρ (finiteSpineWordBlock q u)) × (Fin q × Bool)) →₀ ℤ) :
    namedAttachingNerveBoundary q ρ u hrho c ∈ Inc (namedAttachingCover q ρ u) :=
  ordNerveChain1_mem_inc _

theorem namedAttachingNerveBoundary_image
    (c : (PresGroup (substPresF ρ (finiteSpineWordBlock q u)) × (Fin q × Bool)) →₀ ℤ) :
    universalNerveChain1 (quotientSurfaceMarkingChains q ρ u hrho c) =
      cmap Subtype.val (namedAttachingNerveBoundary q ρ u hrho c) := by
  rw (config := { transparency := .default }) [← namedAttachingMarkingChains_image q ρ u hrho c]
  change universalNerveChain1 (chain1
      (uOrderHom.comp (orderCxMap Subtype.val (fun _ _ h => h)))
      (namedAttachingMarkingChains q ρ u hrho c)) =
    cmap Subtype.val (ordNerveChain1 (namedAttachingMarkingChains q ρ u hrho c))
  rw (config := { transparency := .default }) [chain1_comp_apply, universalNerveChain1_uOrderHom, ordNerveChain1_chain1]

/-- The actual B2 coordinate equation supplies an actual attaching-cover two-chain
with the original marked boundary, and an old three-chain correcting its image. -/
theorem quotientCorrectedRelative_attaching_filling
    (β : NamedSpineRel q → MonoidAlgebra ℤ
      (PresGroup (substPresF ρ (finiteSpineWordBlock q u))))
    (hβ : ∀ z : SpinePresentationGen q,
      (∑ m, β m * foxMatrixPres (substPresF ρ (finiteSpineWordBlock q u))
        (Sum.inr ⟨PUnit.unit, z⟩) (Sum.inr ⟨PUnit.unit, m⟩)) = 0) :
    ∃ c : Ch (namedAttachingCover q ρ u),
      c ∈ Inc _ ∧ lengthProjection 3 c = c ∧
      Nerve.bdry c = namedAttachingNerveBoundary q ρ u hrho
        ((ReceivedTree.cellCoordinates (Fin q × Bool)).symm (fun i => β (Sum.inr i))) ∧
      ∃ y ∈ IncOn (fun p => InQOld (uOrderEnd p)),
        lengthProjection 4 y = y ∧
        quotientCorrectedRelativeNerveChain q ρ u hrho β =
          cmap Subtype.val c + Nerve.bdry y := by
  apply qUniversal_old_cellular_relative_chain_from_attaching
    (namedAtt ρ q u (gBase q)) (namedBasePos_isConnected ρ q u) (gBase q)
    (quotientCorrectedRelativeChain q ρ u hrho β)
    (quotientCorrectedRelativeChain_face_support q ρ u hrho β)
    (namedAttachingNerveBoundary q ρ u hrho
      ((ReceivedTree.cellCoordinates (Fin q × Bool)).symm (fun i => β (Sum.inr i))))
    (namedAttachingNerveBoundary_mem_inc q ρ u hrho _)
  rw (config := { transparency := .default }) [quotientCorrectedRelativeChain_boundary q ρ u hrho β hβ,
    namedAttachingNerveBoundary_image]

end FiniteChains.Davis.Genus
