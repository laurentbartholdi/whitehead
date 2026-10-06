import RequestProject.GenusFaithfulComparison
import RequestProject.ReceivedTreeMarkedComparison
import RequestProject.UniversalCoverPathTransport

/-! The received spine cover mapped to the actual named quotient.

-/

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains.Comb
variable {K Y Z : Complex2}

theorem pi1Map_comp_apply (f : Hom K Y) (g : Hom Y Z) (a : K.V)
    (z : Pi1 K a) :
    pi1Map (g.comp f) a z = pi1Map g (f.onV a) (pi1Map f a z) := by
  refine Quotient.inductionOn z ?_
  intro p
  apply congrArg Pi1.mk
  apply Subtype.ext
  simp only [mapPath, Hom.comp, List.map_map, Function.comp_def]

theorem pi1Map_baseEq_apply (f : Hom K Y) {a b : K.V} (h : a = b)
    (z : Pi1 K a) :
    pi1Map f b (pi1BaseEqEquiv h z) =
      pi1BaseEqEquiv (congrArg f.onV h) (pi1Map f a z) := by
  subst b
  rfl

theorem pi1Conj_baseEq_end {a b c : K.V} {p : List (K.E × Bool)}
    (hp : IsPath K.src K.tgt p a c) (h : b = c)
    (hp' : IsPath K.src K.tgt p a b) (z : Pi1 K b) :
    pi1Conj hp (pi1BaseEqEquiv h z) = pi1Conj hp' z := by
  subst c
  rfl

theorem pi1Conj_reverse_cancel {a b : K.V} {p : List (K.E × Bool)}
    (hp : IsPath K.src K.tgt p a b) (z : Pi1 K b) :
    pi1Conj (isPath_revPath hp) (pi1Conj hp z) = z := by
  rw (config := { transparency := .default }) [pi1Conj_pi1Conj]
  exact (pi1Conj_congr _ (show IsPath K.src K.tgt [] b b from rfl)
    (htpy_revPath_append hp) z).trans
    (pi1Conj_empty_apply b z)

theorem pi1Conj_cancel_reverse {a b : K.V} {p : List (K.E × Bool)}
    (hp : IsPath K.src K.tgt p a b) (z : Pi1 K a) :
    pi1Conj hp (pi1Conj (isPath_revPath hp) z) = z := by
  rw (config := { transparency := .default }) [pi1Conj_pi1Conj]
  exact (pi1Conj_congr _ (show IsPath K.src K.tgt [] a a from rfl)
    (htpy_append_revPath hp) z).trans
    (pi1Conj_empty_apply a z)

theorem chain1_comp_apply (f : Hom K Y) (g : Hom Y Z) (c : K.E →₀ ℤ) :
    chain1 (g.comp f) c = chain1 g (chain1 f c) := by
  change Finsupp.mapDomain (g.onE ∘ f.onE) c =
    Finsupp.mapDomain g.onE (Finsupp.mapDomain f.onE c)
  rw (config := { transparency := .default }) [Finsupp.mapDomain_comp]

theorem chain2_comp_apply (f : Hom K Y) (g : Hom Y Z) (c : K.F →₀ ℤ) :
    chain2 (g.comp f) c = chain2 g (chain2 f c) := by
  change Finsupp.mapDomain (g.onF ∘ f.onF) c =
    Finsupp.mapDomain g.onF (Finsupp.mapDomain f.onF c)
  rw (config := { transparency := .default }) [Finsupp.mapDomain_comp]

end FiniteChains.Comb

namespace FiniteChains.Davis.Genus
open RACG Mirror Comb PresModel BlockFamily
open scoped Classical

variable (q : ℕ) [NeZero q]

noncomputable def markedSpineToOld : Hom (markedSpineCx q)
    (orderCx (QOld (cmpRel (GenusVertex q)))) :=
  (genusSpineToOld q).comp (componentIncl (genusSpineCx q) (spineBase q))

theorem markedSpineToOld_root :
    (markedSpineToOld q).onV (markedSpineTree q).root = posQCube (gBase q) := by
  rw (config := { transparency := .default }) [markedSpineTree_root]
  rfl

/-- Naming the marked words does not change the geometric map from the
tree presentation of the connected spine. This identity holds on every word. -/
theorem namedSpineToOld_inclusion (z : PresGroup (spinePresentation q)) :
    namedSpineToOldEquiv q
      (NamedPresentation.inclusion (spinePresentation q) (spinePresentationMarkedWord q) z) =
    pi1BaseEqEquiv (markedSpineToOld_root q)
      (pi1Map (markedSpineToOld q) (markedSpineTree q).root
        (SpanningTree.presToPi1 (markedSpineTree q) z)) := by
  have hnamed : (namedSpinePi1Equiv q).symm
      (NamedPresentation.inclusion (spinePresentation q) (spinePresentationMarkedWord q) z) =
      SpanningTree.presToPi1 (markedSpineTree q) z := by
    change (spinePresentationPi1Equiv q).symm
      ((namedSpineGroupEquiv q).symm ((namedSpineGroupEquiv q) z)) = _
    rw (config := { transparency := .default }) [MulEquiv.symm_apply_apply]
    rfl
  change pi1Map (genusSpineToOld q) (spineBase q)
    (pi1Map (componentIncl (genusSpineCx q) (spineBase q)) (markedSpineBase q)
      (pi1BaseEqEquiv (markedSpineTree_root q)
        ((namedSpinePi1Equiv q).symm
          (NamedPresentation.inclusion (spinePresentation q)
            (spinePresentationMarkedWord q) z)))) = _
  rw (config := { transparency := .default }) [hnamed]
  erw [← pi1Map_comp_apply (componentIncl (genusSpineCx q) (spineBase q))
    (genusSpineToOld q) (markedSpineBase q)]
  exact pi1Map_baseEq_apply (markedSpineToOld q) (markedSpineTree_root q) _

variable {α Jr : Type} (ρ : Jr ⊕ PUnit.{1} → FreeGroup α)
  (u : Fin q × Bool → FreeGroup α)
  (hrho : ρ (Sum.inr PUnit.unit) = commWord u (finitePairs q))

noncomputable def markedSpineToNamedQuotient : Hom (markedSpineCx q)
    (orderCx (namedQuotientPos ρ q u)) :=
  (orderCxMap (qOldIncl (att := namedAtt ρ q u)) qOldIncl_monotone).comp
    (markedSpineToOld q)

theorem markedSpineToNamedQuotient_root :
    (markedSpineToNamedQuotient q ρ u).onV (markedSpineTree q).root =
      qOldIncl (att := namedAtt ρ q u) (posQCube (gBase q)) :=
  congrArg (qOldIncl (att := namedAtt ρ q u)) (markedSpineToOld_root q)

noncomputable def spineQuotientCylinderPath :
    List ((orderCx (namedQuotientPos ρ q u)).E × Bool) :=
  [ordPos (qNew_att_le_qOldIncl (att := namedAtt ρ q u) (gBase q))]

theorem spineQuotientCylinderPath_isPath :
    IsPath (orderCx (namedQuotientPos ρ q u)).src
      (orderCx (namedQuotientPos ρ q u)).tgt (spineQuotientCylinderPath q ρ u)
      (namedQuotientBase ρ q u)
      ((markedSpineToNamedQuotient q ρ u).onV (markedSpineTree q).root) := by
  rw (config := { transparency := .default }) [markedSpineToNamedQuotient_root]
  exact isPath_ordPos (qNew_att_le_qOldIncl (att := namedAtt ρ q u) (gBase q))

/-- The geometric map on all spine words, with the actual cylinder path
accounting for the two different base vertices. -/
theorem namedSpineIntoQuotient_inclusion (z : PresGroup (spinePresentation q)) :
    namedSpineIntoQuotient ρ q u
      (NamedPresentation.inclusion (spinePresentation q) (spinePresentationMarkedWord q) z) =
      pi1Conj (spineQuotientCylinderPath_isPath q ρ u)
        (pi1Map (markedSpineToNamedQuotient q ρ u) (markedSpineTree q).root
          (SpanningTree.presToPi1 (markedSpineTree q) z)) := by
  change pi1Conj (isPath_ordPos
      (qNew_att_le_qOldIncl (att := namedAtt ρ q u) (gBase q)))
    (pi1Map (orderCxMap (qOldIncl (att := namedAtt ρ q u)) qOldIncl_monotone)
      (posQCube (gBase q))
      (namedSpineToOldEquiv q
        (NamedPresentation.inclusion (spinePresentation q)
          (spinePresentationMarkedWord q) z))) = _
  rw (config := { transparency := .default }) [namedSpineToOld_inclusion, pi1Map_baseEq_apply]
  erw [pi1Conj_baseEq_end
    (isPath_ordPos (qNew_att_le_qOldIncl (att := namedAtt ρ q u) (gBase q)))
    (markedSpineToNamedQuotient_root q ρ u)
    (spineQuotientCylinderPath_isPath q ρ u)]
  rw (config := { transparency := .default }) [← pi1Map_comp_apply]
  rfl

noncomputable abbrev singleReceivedSpineCover : Complex2 :=
  receivedSpineCover ρ (fun _ : PUnit.{1} => q) (fun _ => u) PUnit.unit

/-- The proved faithful comparison expressed at the old spine base vertex. -/
noncomputable def finiteSpineOldRootReceiver :
    PresGroup (substPresF ρ (finiteSpineWordBlock q u)) →*
      Pi1 (orderCx (namedQuotientPos ρ q u))
        ((markedSpineToNamedQuotient q ρ u).onV (markedSpineTree q).root) :=
  (pi1Conj (isPath_revPath (spineQuotientCylinderPath_isPath q ρ u))).comp
    (finiteSpineToQuotient ρ q u hrho)

theorem finiteSpineOldRootReceiver_compatible :
    (finiteSpineOldRootReceiver q ρ u hrho).comp
      (receivedSpineWordReceiver ρ (fun _ : PUnit.{1} => q) (fun _ => u) PUnit.unit) =
      (pi1Map (markedSpineToNamedQuotient q ρ u) (markedSpineTree q).root).comp
        (SpanningTree.presToPi1 (markedSpineTree q)) := by
  apply MonoidHom.ext
  intro z
  change pi1Conj (isPath_revPath (spineQuotientCylinderPath_isPath q ρ u))
    (finiteSpineToQuotient ρ q u hrho
      (singleSpineNamedReceiver ρ q u
        (NamedPresentation.inclusion (spinePresentation q)
          (spinePresentationMarkedWord q) z))) = _
  have h := DFunLike.congr_fun (finiteSpineToQuotient_spine ρ q u hrho)
    (NamedPresentation.inclusion (spinePresentation q) (spinePresentationMarkedWord q) z)
  rw (config := { transparency := .default }) [show finiteSpineToQuotient ρ q u hrho
      (singleSpineNamedReceiver ρ q u
        (NamedPresentation.inclusion (spinePresentation q) (spinePresentationMarkedWord q) z)) =
      namedSpineIntoQuotient ρ q u
        (NamedPresentation.inclusion (spinePresentation q) (spinePresentationMarkedWord q) z)
      from h]
  rw (config := { transparency := .default }) [namedSpineIntoQuotient_inclusion, pi1Conj_reverse_cancel]
  rfl

/-- A genuine cellular comparison, with compatibility now proved from the
actual substituted presentation instead of required as an extra hypothesis. -/
noncomputable def receivedSpineToQuotientOldRoot :
    Hom (singleReceivedSpineCover q ρ u)
      (uCover (orderCx (namedQuotientPos ρ q u))
        ((markedSpineToNamedQuotient q ρ u).onV (markedSpineTree q).root)) :=
  ReceivedTree.comparison (markedSpineTree q) (markedSpineToNamedQuotient q ρ u)
    (receivedSpineWordReceiver ρ (fun _ : PUnit.{1} => q) (fun _ => u) PUnit.unit)
    (finiteSpineOldRootReceiver q ρ u hrho)
    (finiteSpineOldRootReceiver_compatible q ρ u hrho)

theorem receivedSpineToQuotientOldRoot_projects :
    (univProj (orderCx (namedQuotientPos ρ q u))
      ((markedSpineToNamedQuotient q ρ u).onV (markedSpineTree q).root)).comp
      (receivedSpineToQuotientOldRoot q ρ u hrho) =
      (markedSpineToNamedQuotient q ρ u).comp
        (receivedSpineProjection ρ (fun _ : PUnit.{1} => q) (fun _ => u) PUnit.unit) :=
  ReceivedTree.comparison_projects _ _ _ _ _

theorem receivedSpineToQuotientOldRoot_boundary
    (c : (singleReceivedSpineCover q ρ u).F →₀ ℤ) :
    Comb.bdry2 _ (chain2 (receivedSpineToQuotientOldRoot q ρ u hrho) c) =
      chain1 (receivedSpineToQuotientOldRoot q ρ u hrho)
        (Comb.bdry2 (singleReceivedSpineCover q ρ u) c) :=
  bdry2_chain2 _ _

/-- The comparison now lands at the base vertex used by the old/star
relative filling theorem. The change of base is the actual cylinder path. -/
noncomputable def receivedSpineToQuotient :
    Hom (singleReceivedSpineCover q ρ u)
      (uCover (orderCx (namedQuotientPos ρ q u)) (namedQuotientBase ρ q u)) :=
  (uCoverPathTransport (spineQuotientCylinderPath_isPath q ρ u)).comp
    (receivedSpineToQuotientOldRoot q ρ u hrho)

theorem receivedSpineToQuotient_projects :
    (univProj (orderCx (namedQuotientPos ρ q u)) (namedQuotientBase ρ q u)).comp
      (receivedSpineToQuotient q ρ u hrho) =
      (markedSpineToNamedQuotient q ρ u).comp
        (receivedSpineProjection ρ (fun _ : PUnit.{1} => q) (fun _ => u) PUnit.unit) := by
  apply Hom.ext'
  · funext x
    change endV (pathTransportV (spineQuotientCylinderPath_isPath q ρ u)
      (ReceivedTree.receiverVertex (markedSpineTree q) (markedSpineToNamedQuotient q ρ u)
        (finiteSpineOldRootReceiver q ρ u hrho) x.1 x.2)) = _
    rw (config := { transparency := .default }) [endV_pathTransportV, ReceivedTree.receiverVertex_end]
    rfl
  · rfl
  · rfl

theorem receivedSpineToQuotient_boundary
    (c : (singleReceivedSpineCover q ρ u).F →₀ ℤ) :
    Comb.bdry2 _ (chain2 (receivedSpineToQuotient q ρ u hrho) c) =
      chain1 (receivedSpineToQuotient q ρ u hrho)
        (Comb.bdry2 (singleReceivedSpineCover q ρ u) c) :=
  bdry2_chain2 _ _

/-- The original substituted group acts through its proved faithful map;
the change of base does not replace or identify any sheet coefficients. -/
theorem receivedSpineToQuotient_deckV
    (g h : PresGroup (substPresF ρ (finiteSpineWordBlock q u)))
    (a : (markedSpineCx q).V) :
    (receivedSpineToQuotient q ρ u hrho).onV (g * h, a) =
      deckV (finiteSpineToQuotient ρ q u hrho g)
        ((receivedSpineToQuotient q ρ u hrho).onV (h, a)) := by
  have hs : ReceivedTree.receiverVertex (markedSpineTree q)
      (markedSpineToNamedQuotient q ρ u) (finiteSpineOldRootReceiver q ρ u hrho) (g * h) a =
      deckV (finiteSpineOldRootReceiver q ρ u hrho g)
        (ReceivedTree.receiverVertex (markedSpineTree q)
          (markedSpineToNamedQuotient q ρ u) (finiteSpineOldRootReceiver q ρ u hrho) h a) := by
    simp only [ReceivedTree.receiverVertex, map_mul, deckV_mul]
  change (uCoverPathTransport (spineQuotientCylinderPath_isPath q ρ u)).onV
    (ReceivedTree.receiverVertex (markedSpineTree q) (markedSpineToNamedQuotient q ρ u)
      (finiteSpineOldRootReceiver q ρ u hrho) (g * h) a) = _
  rw (config := { transparency := .default }) [hs, uCoverPathTransport_deckV]
  change deckV (pi1Conj (spineQuotientCylinderPath_isPath q ρ u)
    (pi1Conj (isPath_revPath (spineQuotientCylinderPath_isPath q ρ u))
      (finiteSpineToQuotient ρ q u hrho g))) _ = _
  rw (config := { transparency := .default }) [pi1Conj_cancel_reverse]
  rfl

theorem receivedSpineToQuotient_deckE
    (g h : PresGroup (substPresF ρ (finiteSpineWordBlock q u)))
    (e : (markedSpineCx q).E) :
    (receivedSpineToQuotient q ρ u hrho).onE (g * h, e) =
      deckE (finiteSpineToQuotient ρ q u hrho g)
        ((receivedSpineToQuotient q ρ u hrho).onE (h, e)) := by
  apply Subtype.ext
  exact Prod.ext (receivedSpineToQuotient_deckV q ρ u hrho g h _) rfl

theorem receivedSpineToQuotient_deckF
    (g h : PresGroup (substPresF ρ (finiteSpineWordBlock q u)))
    (f : (markedSpineCx q).F) :
    (receivedSpineToQuotient q ρ u hrho).onF (g * h, f) =
      deckF (finiteSpineToQuotient ρ q u hrho g)
        ((receivedSpineToQuotient q ρ u hrho).onF (h, f)) := by
  apply Subtype.ext
  exact Prod.ext (receivedSpineToQuotient_deckV q ρ u hrho g h _) rfl

/-- Exact geometric marked boundary, retaining every coefficient of the
actual single-block ring. Only the B2 coordinate equation is assumed. -/
theorem receivedSpineToQuotient_relative_boundary
    (β : NamedSpineRel q → MonoidAlgebra ℤ
      (PresGroup (substPresF ρ (finiteSpineWordBlock q u))))
    (hβ : ∀ z : SpinePresentationGen q,
      (∑ m, β m * foxMatrixPres (substPresF ρ (finiteSpineWordBlock q u))
        (Sum.inr ⟨PUnit.unit, z⟩) (Sum.inr ⟨PUnit.unit, m⟩)) = 0) :
    Comb.bdry2 (uCover (orderCx (namedQuotientPos ρ q u)) (namedQuotientBase ρ q u))
      (chain2 (receivedSpineToQuotient q ρ u hrho)
      (receivedSpineFaceChain ρ (fun _ : PUnit.{1} => q) (fun _ => u) PUnit.unit β)) =
      chain1 (uCoverPathTransport (spineQuotientCylinderPath_isPath q ρ u))
        (ReceivedTree.geometricMarkedChainMap (markedSpineTree q)
          (markedSpineToNamedQuotient q ρ u) (finiteSpineOldRootReceiver q ρ u hrho)
          (treeMarkedSpineLoop q)
          ((ReceivedTree.cellCoordinates (Fin q × Bool)).symm (fun i => β (Sum.inr i)))) := by
  rw (config := { transparency := .default }) [receivedSpineToQuotient, chain2_comp_apply, bdry2_chain2]
  apply congrArg (chain1 (uCoverPathTransport (spineQuotientCylinderPath_isPath q ρ u)))
  apply ReceivedTree.comparison_relative_boundary
    (markedSpineTree q) (markedSpineToNamedQuotient q ρ u)
    (receivedSpineWordReceiver ρ (fun _ : PUnit.{1} => q) (fun _ => u) PUnit.unit)
    (finiteSpineOldRootReceiver q ρ u hrho)
    (finiteSpineOldRootReceiver_compatible q ρ u hrho)
    (treeMarkedSpineLoop q) (fun i => β (Sum.inr i))
    (receivedSpineFaceChain ρ (fun _ : PUnit.{1} => q) (fun _ => u) PUnit.unit β)
  intro z
  let βF : NamedSpineRel q → MonoidAlgebra ℤ
      (PresGroup (substPresF ρ
        (familyFiniteSpineWordBlock (fun _ : PUnit.{1} => q) (fun _ => u)))) := β
  have hz0 := receivedSpineFaceChain_relative_boundary ρ (fun _ : PUnit.{1} => q)
    (fun _ => u) PUnit.unit βF
  have hz := hz0 (by
      intro t
      with_reducible
        convert hβ t using 1
        congr
      all_goals first
        | exact Subsingleton.elim _ _
        | (funext m
           with_reducible congr 2
           all_goals first | exact Subsingleton.elim _ _ | rfl)) z
  refine hz.trans ?_
  apply Finset.sum_congr rfl
  intro i _
  apply congrArg (fun x => βF (Sum.inr i) * x)
  exact (receivedSpineWordReceiver_coeff ρ (fun _ : PUnit.{1} => q)
    (fun _ => u) PUnit.unit (fox z (spinePresentationMarkedWord q i))).symm

end FiniteChains.Davis.Genus
