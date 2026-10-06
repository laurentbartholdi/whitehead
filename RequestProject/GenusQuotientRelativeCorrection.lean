module

public import RequestProject.GenusReceivedQuotientComparison
public import RequestProject.LiftedHomotopyChains
public import RequestProject.DeckChainTransport

@[expose] public section

/-! The actual old-cell correction from spine markings to attaching-surface
markings. 
-/

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains.Comb
variable {K Y : Complex2}

theorem univLift_pathChain (a : K.V) (f : Hom K Y) (v : UV K a)
    {p : List (K.E × Bool)} {b : K.V}
    (hp : IsPath K.src K.tgt p (endV v) b) :
    chain1 (univLift K f a) (pathChain (uLiftPath p v)) =
      pathChain (uLiftPath (mapPath f p) (univLiftV a f v)) := by
  change Finsupp.mapDomain (univLift K f a).onE (pathChain _) = _
  rw (config := { transparency := .default }) [← pathChain_map]
  exact congrArg pathChain (uLiftPath_univLiftV a f p v b hp).symm

theorem uCoverPathTransport_pathChain {a b : K.V} {c : List (K.E × Bool)}
    (hc : IsPath K.src K.tgt c a b) (v : UV K b)
    {p : List (K.E × Bool)} {d : K.V}
    (hp : IsPath K.src K.tgt p (endV v) d) :
    chain1 (uCoverPathTransport hc) (pathChain (uLiftPath p v)) =
      pathChain (uLiftPath p ((uCoverPathTransport hc).onV v)) := by
  change Finsupp.mapDomain (uCoverPathTransport hc).onE (pathChain _) = _
  rw (config := { transparency := .default }) [← pathChain_map]
  exact congrArg pathChain (uLiftPath_pathTransportV hc p v d hp).symm

theorem univDeck_pathChain (a : K.V) (g : Pi1 K a) (v : UV K a)
    {p : List (K.E × Bool)} {b : K.V}
    (hp : IsPath K.src K.tgt p (endV v) b) :
    chain1 ((univDeck K a).cellHom g) (pathChain (uLiftPath p v)) =
      pathChain (uLiftPath p (deckV g v)) := by
  change Finsupp.mapDomain ((univDeck K a).cellHom g).onE (pathChain (uLiftPath p v)) = _
  rw (config := { transparency := .default }) [← pathChain_map ((univDeck K a).cellHom g)]
  exact congrArg pathChain (uLiftPath_deckV g p v b hp).symm

end FiniteChains.Comb

namespace FiniteChains.Davis.Genus
open RACG Mirror Comb PresModel BlockFamily
open scoped Classical
variable (q : ℕ) [NeZero q]

noncomputable abbrev spineOldBase := posQCube (gBase q)
noncomputable abbrev spineOldCx := orderCx (QOld (cmpRel (GenusVertex q)))

noncomputable def spineOldMarking (i : Fin q × Bool) : List ((spineOldCx q).E × Bool) :=
  mapPath (genusSpineToOld q) (spineMarkedLoop q i).1

noncomputable def surfaceOldMarking (i : Fin q × Bool) : List ((spineOldCx q).E × Bool) :=
  mapPath (surfCx (cmpRel (GenusVertex q))) (gSig q (i.1.val, i.2))

theorem spineOldMarking_isPath (i : Fin q × Bool) :
    IsPath (spineOldCx q).src (spineOldCx q).tgt (spineOldMarking q i)
      (spineOldBase q) (spineOldBase q) :=
  isPath_mapPath (genusSpineToOld q) (spineMarkedLoop q i).2

theorem surfaceOldMarking_isPath (i : Fin q × Bool) :
    IsPath (spineOldCx q).src (spineOldCx q).tgt (surfaceOldMarking q i)
      (spineOldBase q) (spineOldBase q) :=
  isPath_mapPath (surfCx _) (isPath_gSig q (i.1.val, i.2))

theorem exists_spineOldMarkingCorrection (i : Fin q × Bool) :
    ∃ d : (uCover (spineOldCx q) (spineOldBase q)).F →₀ ℤ,
      Comb.bdry2 _ d =
        pathChain (uLiftPath (spineOldMarking q i) (UV.base _ (spineOldBase q))) -
          pathChain (uLiftPath (surfaceOldMarking q i) (UV.base _ (spineOldBase q))) := by
  exact (htpy_uLiftPath (c := UV.base (spineOldCx q) (spineOldBase q))
    (spineOldMarking_isPath q i) (spineMarkedLoop_toOld_htpy q i)).exists_boundary

noncomputable def spineOldMarkingCorrection (i : Fin q × Bool) :
    (uCover (spineOldCx q) (spineOldBase q)).F →₀ ℤ :=
  Classical.choose (exists_spineOldMarkingCorrection q i)

theorem spineOldMarkingCorrection_boundary (i : Fin q × Bool) :
    Comb.bdry2 _ (spineOldMarkingCorrection q i) =
      pathChain (uLiftPath (spineOldMarking q i) (UV.base _ (spineOldBase q))) -
        pathChain (uLiftPath (surfaceOldMarking q i) (UV.base _ (spineOldBase q))) :=
  Classical.choose_spec (exists_spineOldMarkingCorrection q i)

variable {α Jr : Type} (ρ : Jr ⊕ PUnit.{1} → FreeGroup α)
  (u : Fin q × Bool → FreeGroup α)
  (hrho : ρ (Sum.inr PUnit.unit) = commWord u (finitePairs q))

noncomputable def oldIntoNamedQuotient :
    Hom (spineOldCx q) (orderCx (namedQuotientPos ρ q u)) :=
  orderCxMap (qOldIncl (att := namedAtt ρ q u)) qOldIncl_monotone

theorem oldCylinderPath_isPath :
    IsPath (orderCx (namedQuotientPos ρ q u)).src
      (orderCx (namedQuotientPos ρ q u)).tgt (spineQuotientCylinderPath q ρ u)
      (namedQuotientBase ρ q u) ((oldIntoNamedQuotient q ρ u).onV (spineOldBase q)) :=
  isPath_ordPos (qNew_att_le_qOldIncl (att := namedAtt ρ q u) (gBase q))

noncomputable def quotientCylinderVertex :
    UV (orderCx (namedQuotientPos ρ q u)) (namedQuotientBase ρ q u) :=
  UV.mk ⟨spineQuotientCylinderPath q ρ u, by
    rw (config := { transparency := .default }) [endpt_eq_of_isPath (oldCylinderPath_isPath q ρ u)]
    exact oldCylinderPath_isPath q ρ u⟩

theorem quotientCylinderVertex_end :
    endV (quotientCylinderVertex q ρ u) =
      (oldIntoNamedQuotient q ρ u).onV (spineOldBase q) :=
  endpt_eq_of_isPath (oldCylinderPath_isPath q ρ u)

/-- Every face of this lift is an actual old face of the quotient. -/
noncomputable def oldCoverToNamedQuotient :
    Hom (uCover (spineOldCx q) (spineOldBase q))
      (uCover (orderCx (namedQuotientPos ρ q u)) (namedQuotientBase ρ q u)) :=
  (uCoverPathTransport (oldCylinderPath_isPath q ρ u)).comp
    (univLift (spineOldCx q) (oldIntoNamedQuotient q ρ u) (spineOldBase q))

theorem oldCoverToNamedQuotient_pathChain
    {p : List ((spineOldCx q).E × Bool)} (b : (spineOldCx q).V)
    (hp : IsPath (spineOldCx q).src (spineOldCx q).tgt p (spineOldBase q) b) :
    chain1 (oldCoverToNamedQuotient q ρ u)
      (pathChain (uLiftPath p (UV.base (spineOldCx q) (spineOldBase q)))) =
      pathChain (uLiftPath (mapPath (oldIntoNamedQuotient q ρ u) p)
        (quotientCylinderVertex q ρ u)) := by
  rw (config := { transparency := .default }) [oldCoverToNamedQuotient, chain1_comp_apply, univLift_pathChain _ _ _ hp]
  rw (config := { transparency := .default }) [uCoverPathTransport_pathChain _ _ (isPath_mapPath (oldIntoNamedQuotient q ρ u) hp)]
  congr 2

theorem receivedSpineToQuotient_root
    (g : PresGroup (substPresF ρ (finiteSpineWordBlock q u))) :
    (receivedSpineToQuotient q ρ u hrho).onV (g, (markedSpineTree q).root) =
      deckV (finiteSpineToQuotient ρ q u hrho g) (quotientCylinderVertex q ρ u) := by
  change (uCoverPathTransport (spineQuotientCylinderPath_isPath q ρ u)).onV
    (deckV (finiteSpineOldRootReceiver q ρ u hrho g)
      (SpanningTree.mappedTreeReference (markedSpineTree q)
        (markedSpineToNamedQuotient q ρ u) (markedSpineTree q).root)) = _
  simp only [SpanningTree.mappedTreeReference, SpanningTree.treePath_root,
    mapPath, List.map_nil, extendList_nil]
  rw (config := { transparency := .default }) [uCoverPathTransport_deckV, uCoverPathTransport_base]
  change deckV (pi1Conj (spineQuotientCylinderPath_isPath q ρ u)
    (pi1Conj (isPath_revPath (spineQuotientCylinderPath_isPath q ρ u))
      (finiteSpineToQuotient ρ q u hrho g))) (quotientCylinderVertex q ρ u) = _
  rw (config := { transparency := .default }) [pi1Conj_cancel_reverse]

noncomputable def quotientMarkingCorrection
    (g : PresGroup (substPresF ρ (finiteSpineWordBlock q u))) (i : Fin q × Bool) :
    (uCover (orderCx (namedQuotientPos ρ q u)) (namedQuotientBase ρ q u)).F →₀ ℤ :=
  (univDeck (orderCx (namedQuotientPos ρ q u)) (namedQuotientBase ρ q u)).faceChains
    (finiteSpineToQuotient ρ q u hrho g)
    (chain2 (oldCoverToNamedQuotient q ρ u) (spineOldMarkingCorrection q i))

/-- The correction is lifted in the old subcomplex before translation;
its boundary changes exactly the two chosen marking paths. -/
theorem quotientMarkingCorrection_boundary
    (g : PresGroup (substPresF ρ (finiteSpineWordBlock q u))) (i : Fin q × Bool) :
    Comb.bdry2 _ (quotientMarkingCorrection q ρ u hrho g i) =
      pathChain (uLiftPath
        (mapPath (oldIntoNamedQuotient q ρ u) (spineOldMarking q i))
        (deckV (finiteSpineToQuotient ρ q u hrho g) (quotientCylinderVertex q ρ u))) -
      pathChain (uLiftPath
        (mapPath (oldIntoNamedQuotient q ρ u) (surfaceOldMarking q i))
        (deckV (finiteSpineToQuotient ρ q u hrho g) (quotientCylinderVertex q ρ u))) := by
  rw (config := { transparency := .default }) [quotientMarkingCorrection, DeckAction.faceChains_boundary, bdry2_chain2,
    spineOldMarkingCorrection_boundary, map_sub, map_sub]
  rw (config := { transparency := .default }) [oldCoverToNamedQuotient_pathChain q ρ u _ (spineOldMarking_isPath q i),
    oldCoverToNamedQuotient_pathChain q ρ u _ (surfaceOldMarking_isPath q i)]
  have hp : IsPath (orderCx (namedQuotientPos ρ q u)).src
      (orderCx (namedQuotientPos ρ q u)).tgt
      (mapPath (oldIntoNamedQuotient q ρ u) (spineOldMarking q i))
      (endV (quotientCylinderVertex q ρ u))
      ((oldIntoNamedQuotient q ρ u).onV (spineOldBase q)) := by
    rw (config := { transparency := .default }) [quotientCylinderVertex_end]
    exact isPath_mapPath _ (spineOldMarking_isPath q i)
  have hs : IsPath (orderCx (namedQuotientPos ρ q u)).src
      (orderCx (namedQuotientPos ρ q u)).tgt
      (mapPath (oldIntoNamedQuotient q ρ u) (surfaceOldMarking q i))
      (endV (quotientCylinderVertex q ρ u))
      ((oldIntoNamedQuotient q ρ u).onV (spineOldBase q)) := by
    rw (config := { transparency := .default }) [quotientCylinderVertex_end]
    exact isPath_mapPath _ (surfaceOldMarking_isPath q i)
  rw (config := { transparency := .default }) [univDeck_pathChain _ _ _ hp, univDeck_pathChain _ _ _ hs]

noncomputable def quotientMarkingCorrections :
    ((PresGroup (substPresF ρ (finiteSpineWordBlock q u)) × (Fin q × Bool)) →₀ ℤ) →ₗ[ℤ]
      ((uCover (orderCx (namedQuotientPos ρ q u)) (namedQuotientBase ρ q u)).F →₀ ℤ) :=
  Finsupp.linearCombination ℤ (fun x => quotientMarkingCorrection q ρ u hrho x.1 x.2)

noncomputable def quotientSpineMarkingChains :
    ((PresGroup (substPresF ρ (finiteSpineWordBlock q u)) × (Fin q × Bool)) →₀ ℤ) →ₗ[ℤ]
      ((uCover (orderCx (namedQuotientPos ρ q u)) (namedQuotientBase ρ q u)).E →₀ ℤ) :=
  Finsupp.linearCombination ℤ (fun x => pathChain (uLiftPath
    (mapPath (oldIntoNamedQuotient q ρ u) (spineOldMarking q x.2))
    (deckV (finiteSpineToQuotient ρ q u hrho x.1) (quotientCylinderVertex q ρ u))))

noncomputable def quotientSurfaceMarkingChains :
    ((PresGroup (substPresF ρ (finiteSpineWordBlock q u)) × (Fin q × Bool)) →₀ ℤ) →ₗ[ℤ]
      ((uCover (orderCx (namedQuotientPos ρ q u)) (namedQuotientBase ρ q u)).E →₀ ℤ) :=
  Finsupp.linearCombination ℤ (fun x => pathChain (uLiftPath
    (mapPath (oldIntoNamedQuotient q ρ u) (surfaceOldMarking q x.2))
    (deckV (finiteSpineToQuotient ρ q u hrho x.1) (quotientCylinderVertex q ρ u))))

theorem quotientMarkingCorrections_boundary
    (c : (PresGroup (substPresF ρ (finiteSpineWordBlock q u)) × (Fin q × Bool)) →₀ ℤ) :
    Comb.bdry2 _ (quotientMarkingCorrections q ρ u hrho c) =
      quotientSpineMarkingChains q ρ u hrho c - quotientSurfaceMarkingChains q ρ u hrho c := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd =>
      rw (config := { transparency := .default }) [map_add, map_add, hc, hd, map_add, map_add]
      abel
  | single x n =>
      simp only [quotientMarkingCorrections, quotientSpineMarkingChains,
        quotientSurfaceMarkingChains, Finsupp.linearCombination_single, map_smul,
        quotientMarkingCorrection_boundary, smul_sub]

theorem markedSpineToNamedQuotient_marking_path (i : Fin q × Bool) :
    mapPath (markedSpineToNamedQuotient q ρ u) (treeMarkedSpineLoop q i).1 =
      mapPath (oldIntoNamedQuotient q ρ u) (spineOldMarking q i) := by
  change mapPath ((oldIntoNamedQuotient q ρ u).comp
      ((genusSpineToOld q).comp (componentIncl (genusSpineCx q) (spineBase q))))
    (markedSpineLoop q i).1 = _
  rw (config := { transparency := .default }) [← mapPath_comp, ← mapPath_comp, markedSpineLoop_inclusion]
  rfl

/-- The abstractly indexed marked chain map agrees exactly with the actual
translated lifted marking paths at the cylinder endpoint. -/
theorem quotientSpineMarkingChains_eq
    (c : (PresGroup (substPresF ρ (finiteSpineWordBlock q u)) × (Fin q × Bool)) →₀ ℤ) :
    chain1 (uCoverPathTransport (spineQuotientCylinderPath_isPath q ρ u))
      (ReceivedTree.geometricMarkedChainMap (markedSpineTree q)
        (markedSpineToNamedQuotient q ρ u) (finiteSpineOldRootReceiver q ρ u hrho)
        (treeMarkedSpineLoop q) c) = quotientSpineMarkingChains q ρ u hrho c := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd => rw (config := { transparency := .default }) [map_add, map_add, hc, hd, map_add]
  | single x n =>
      obtain ⟨g, i⟩ := x
      rw (config := { transparency := .default }) [ReceivedTree.geometricMarkedChainMap, Finsupp.linearCombination_single,
        map_smul, quotientSpineMarkingChains, Finsupp.linearCombination_single]
      apply congrArg (fun z => n • z)
      have hp : IsPath (orderCx (namedQuotientPos ρ q u)).src
          (orderCx (namedQuotientPos ρ q u)).tgt
          (mapPath (markedSpineToNamedQuotient q ρ u) (treeMarkedSpineLoop q i).1)
          (endV (ReceivedTree.receiverVertex (markedSpineTree q)
            (markedSpineToNamedQuotient q ρ u)
            (finiteSpineOldRootReceiver q ρ u hrho) g (markedSpineTree q).root))
          ((markedSpineToNamedQuotient q ρ u).onV (markedSpineTree q).root) := by
        rw (config := { transparency := .default }) [ReceivedTree.receiverVertex_end]
        exact isPath_mapPath _ (treeMarkedSpineLoop q i).2
      rw (config := { transparency := .default }) [uCoverPathTransport_pathChain _ _ hp, markedSpineToNamedQuotient_marking_path]
      change pathChain (uLiftPath _
        ((receivedSpineToQuotient q ρ u hrho).onV (g, (markedSpineTree q).root))) = _
      rw (config := { transparency := .default }) [receivedSpineToQuotient_root]

noncomputable def quotientCorrectedRelativeChain
    (β : NamedSpineRel q → MonoidAlgebra ℤ
      (PresGroup (substPresF ρ (finiteSpineWordBlock q u)))) :
    (uCover (orderCx (namedQuotientPos ρ q u)) (namedQuotientBase ρ q u)).F →₀ ℤ :=
  chain2 (receivedSpineToQuotient q ρ u hrho)
    (receivedSpineFaceChain ρ (fun _ : PUnit.{1} => q) (fun _ => u) PUnit.unit β) -
      quotientMarkingCorrections q ρ u hrho
        ((ReceivedTree.cellCoordinates (Fin q × Bool)).symm (fun i => β (Sum.inr i)))

/-- Starting with the actual B2 coordinate equation now gives an actual
old two-chain whose boundary lies on the attaching surface with exactly the
original marked coefficients. No absolute-cycle assumption is added. -/
theorem quotientCorrectedRelativeChain_boundary
    (β : NamedSpineRel q → MonoidAlgebra ℤ
      (PresGroup (substPresF ρ (finiteSpineWordBlock q u))))
    (hβ : ∀ z : SpinePresentationGen q,
      (∑ m, β m * foxMatrixPres (substPresF ρ (finiteSpineWordBlock q u))
        (Sum.inr ⟨PUnit.unit, z⟩) (Sum.inr ⟨PUnit.unit, m⟩)) = 0) :
    Comb.bdry2 _ (quotientCorrectedRelativeChain q ρ u hrho β) =
      quotientSurfaceMarkingChains q ρ u hrho
        ((ReceivedTree.cellCoordinates (Fin q × Bool)).symm (fun i => β (Sum.inr i))) := by
  rw (config := { transparency := .default }) [quotientCorrectedRelativeChain, map_sub,
    receivedSpineToQuotient_relative_boundary q ρ u hrho β hβ,
    quotientSpineMarkingChains_eq, quotientMarkingCorrections_boundary]
  abel

end FiniteChains.Davis.Genus
