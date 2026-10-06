import RequestProject.GenusQuotientRelativeSupport
import RequestProject.GenusOldCoverSpineFaithfulness
import RequestProject.ChamberQuotientOldCover
import RequestProject.StrictOrderPullbackHom
import RequestProject.OrderCxRestriction
import RequestProject.UniversalCoverPi1Injection

/-! The received spine is mapped into the genuine pulled-back old-cover spine.

-/
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains.Comb
variable {K Y Z : Complex2}

theorem Hom.comp_left_cancel_of_injective (f : Hom Y Z)
    (hv : Function.Injective f.onV) (he : Function.Injective f.onE)
    (hf : Function.Injective f.onF) (r s : Hom K Y)
    (h : f.comp r = f.comp s) : r = s := by
  apply Hom.ext'
  · funext a
    exact hv (congrArg (fun k : Hom K Z => k.onV a) h)
  · funext e
    exact he (congrArg (fun k : Hom K Z => k.onE e) h)
  · funext t
    exact hf (congrArg (fun k : Hom K Z => k.onF t) h)

theorem uOrderHomInv_projection_square {P : Type} [PartialOrder P] (a : P) :
    (orderCxMap uOrderEnd (uOrderEnd_monotone (P := P) (a := a))).comp uOrderHomInv =
      univProj (orderCx P) a := by
  apply Hom.ext'
  · funext x
    change uOrderEnd (uOrderHomInv.onV x) = endV x
    rw (config := { transparency := .default }) [uOrderHomInv_vertex]
    rfl
  · funext e
    exact uOrderHomInv_edge_projection e
  · funext t
    exact uOrderHomInv_face_projection t

theorem deckV_injective_in_group {X : Complex2} (a : X.V) (v : UV X a) :
    Function.Injective (fun g : Pi1 X a => deckV g v) := by
  intro g h he
  obtain ⟨d, _, hu⟩ := (isRegular_univProj (X := X) (x₀ := a)).simply_transitive
    v (deckV g v) (endV_deckV g v).symm
  exact (hu g rfl).trans (hu h he.symm).symm

end FiniteChains.Comb

namespace FiniteChains.Davis
open RACG Mirror Comb
variable {V : Type} [DecidableEq V] {A : CommRel V}
  {X : Type} [PartialOrder X] {att : NeSpx A →o X}

theorem qOldCover_projection_square (a : Qpos A X att)
    (hf : Monotone (qOldCoverEnd a)) :
    (orderCxMap (qOldIncl (att := att)) qOldIncl_monotone).comp
      (orderCxMap (qOldCoverEnd a) hf) =
      (orderCxMap uOrderEnd uOrderEnd_monotone).comp
        (orderCxMap (Subtype.val : QLiftedOld a → UOrder (Qpos A X att) a)
          (fun _ _ h => h)) := by
  apply Hom.ext'
  · funext p
    exact qOldCoverEnd_spec a p
  · funext e
    apply Subtype.ext
    exact Prod.ext (qOldCoverEnd_spec a e.1.1) (qOldCoverEnd_spec a e.1.2)
  · funext t
    apply Subtype.ext
    exact Prod.ext (qOldCoverEnd_spec a t.1.1)
      (Prod.ext (qOldCoverEnd_spec a t.1.2.1) (qOldCoverEnd_spec a t.1.2.2))

end FiniteChains.Davis

namespace FiniteChains.Davis.Genus
open RACG Mirror Comb PresModel BlockFamily Nerve
open scoped Classical
variable (q : ℕ) [NeZero q] {α Jr : Type}
  (ρ : Jr ⊕ PUnit.{1} → FreeGroup α) (u : Fin q × Bool → FreeGroup α)
  (hrho : ρ (Sum.inr PUnit.unit) = commWord u (finitePairs q))

noncomputable abbrev namedOldCover := QLiftedOld (namedQuotientBase ρ q u)

noncomputable def namedOldCoverProjection :
    namedOldCover q ρ u → QOld (cmpRel (GenusVertex q)) :=
  qOldCoverEnd (namedQuotientBase ρ q u)

theorem namedOldCoverProjection_isPosetCover : IsPosetCover (namedOldCoverProjection q ρ u) :=
  qOldCoverEnd_isPosetCover (namedAtt ρ q u (gBase q)) (namedBasePos_isConnected ρ q u)

noncomputable def receivedSpineOrderMap :
    Hom (singleReceivedSpineCover q ρ u)
      (orderCx (UOrder (namedQuotientPos ρ q u) (namedQuotientBase ρ q u))) :=
  uOrderHomInv.comp (receivedSpineToQuotient q ρ u hrho)

theorem receivedSpineOrderMap_old (a : (singleReceivedSpineCover q ρ u).V) :
    InQOld (uOrderEnd ((receivedSpineOrderMap q ρ u hrho).onV a)) := by
  change InQOld (endV (uOrderHomInv.onV ((receivedSpineToQuotient q ρ u hrho).onV a)))
  rw (config := { transparency := .default }) [uOrderHomInv_vertex]
  have h := congrArg
    (fun k : Hom (singleReceivedSpineCover q ρ u) (orderCx (namedQuotientPos ρ q u)) => k.onV a)
    (receivedSpineToQuotient_projects q ρ u hrho)
  change endV ((receivedSpineToQuotient q ρ u hrho).onV a) =
    (markedSpineToNamedQuotient q ρ u).onV a.2 at h
  rw (config := { transparency := .default }) [h]
  trivial

noncomputable def receivedSpineToOldCover :
    Hom (singleReceivedSpineCover q ρ u) (orderCx (namedOldCover q ρ u)) :=
  orderCxRestrict (receivedSpineOrderMap q ρ u hrho)
    (fun p => InQOld (uOrderEnd p)) (receivedSpineOrderMap_old q ρ u hrho)

noncomputable def receivedSpineToStrictSpine :
    Hom (singleReceivedSpineCover q ρ u) (strictOrderCx (GenusSpineCell q)) :=
  (componentIncl (genusSpineCx q) (spineBase q)).comp
    (receivedSpineProjection ρ (fun _ : PUnit.{1} => q) (fun _ => u) PUnit.unit)

theorem receivedSpine_old_square :
    (orderCxMap (namedOldCoverProjection q ρ u)
      (namedOldCoverProjection_isPosetCover q ρ u).mono).comp
      (receivedSpineToOldCover q ρ u hrho) =
      (orderCxMap (genusSpineCellToOld q) (genusSpineCellToOld_monotone q)).comp
        ((strictOrderIncl (GenusSpineCell q)).comp (receivedSpineToStrictSpine q ρ u)) := by
  let j := orderCxMap (qOldIncl (att := namedAtt ρ q u)) qOldIncl_monotone
  have hv : Function.Injective j.onV := fun _ _ h => Sum.inl.inj h
  have he : Function.Injective j.onE := by
    intro e f h
    apply Subtype.ext
    exact Prod.ext (Sum.inl.inj (congrArg (fun t : OrdEdge (namedQuotientPos ρ q u) => t.1.1) h))
      (Sum.inl.inj (congrArg (fun t : OrdEdge (namedQuotientPos ρ q u) => t.1.2) h))
  have ht : Function.Injective j.onF := by
    intro e f h
    apply Subtype.ext
    exact Prod.ext (Sum.inl.inj (congrArg (fun t : OrdTri (namedQuotientPos ρ q u) => t.1.1) h))
      (Prod.ext (Sum.inl.inj (congrArg (fun t : OrdTri (namedQuotientPos ρ q u) => t.1.2.1) h))
        (Sum.inl.inj (congrArg (fun t : OrdTri (namedQuotientPos ρ q u) => t.1.2.2) h)))
  apply Hom.comp_left_cancel_of_injective j hv he ht
  calc
    _ = (orderCxMap uOrderEnd uOrderEnd_monotone).comp
        ((orderCxMap Subtype.val (fun _ _ h => h)).comp
          (receivedSpineToOldCover q ρ u hrho)) := by
      change (j.comp (orderCxMap (namedOldCoverProjection q ρ u)
        (namedOldCoverProjection_isPosetCover q ρ u).mono)).comp _ = _
      dsimp only [j, namedOldCoverProjection]
      rw (config := { transparency := .default }) [qOldCover_projection_square]
      rfl
    _ = (orderCxMap uOrderEnd uOrderEnd_monotone).comp
        (receivedSpineOrderMap q ρ u hrho) := by
      rw (config := { transparency := .default }) [receivedSpineToOldCover, orderCxRestrict_projects]
    _ = (univProj (orderCx (namedQuotientPos ρ q u)) (namedQuotientBase ρ q u)).comp
        (receivedSpineToQuotient q ρ u hrho) := by
      change ((orderCxMap uOrderEnd uOrderEnd_monotone).comp uOrderHomInv).comp _ = _
      rw (config := { transparency := .default }) [uOrderHomInv_projection_square]
    _ = _ := receivedSpineToQuotient_projects q ρ u hrho

noncomputable def receivedSpineToPullback :
    Hom (singleReceivedSpineCover q ρ u)
      (strictOrderCx (PosetCoverPullback (namedOldCoverProjection q ρ u) (genusSpineCellToOld q))) :=
  strictOrderPullbackHom (namedOldCoverProjection q ρ u)
    (namedOldCoverProjection_isPosetCover q ρ u) (genusSpineCellToOld q)
    (genusSpineCellToOld_monotone q) (receivedSpineToOldCover q ρ u hrho)
    (receivedSpineToStrictSpine q ρ u) (receivedSpine_old_square q ρ u hrho)

variable {P : Type} [PartialOrder P] (f : P → QOld (cmpRel (GenusVertex q)))

/-- The fibre product over the surviving spine is precisely the old-cover
spine used by the proved chain-faithfulness theorem. -/
def spinePullbackOldCoverOrderIso :
    PosetCoverPullback f (genusSpineCellToOld q) ≃o OldCoveredSpine q f where
  toFun x := ⟨⟨(x.1.1, x.1.2.1), x.2⟩, x.1.2.2⟩
  invFun x := ⟨(x.1.1.1, ⟨x.1.1.2, x.2⟩), x.1.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_rel_iff' := Iff.rfl

noncomputable def receivedSpineToCoveredSpine :
    Hom (singleReceivedSpineCover q ρ u)
      (strictOrderCx (OldCoveredSpine q (namedOldCoverProjection q ρ u))) :=
  (strictOrderCxMap (spinePullbackOldCoverOrderIso q (namedOldCoverProjection q ρ u))
    (spinePullbackOldCoverOrderIso q (namedOldCoverProjection q ρ u)).strictMono).comp
      (receivedSpineToPullback q ρ u hrho)

end FiniteChains.Davis.Genus

namespace FiniteChains.Davis.Genus
open RACG Mirror Comb PresModel BlockFamily Nerve
open scoped Classical
variable (q : ℕ) [NeZero q] {α Jr : Type}
  (ρ : Jr ⊕ PUnit.{1} → FreeGroup α) (u : Fin q × Bool → FreeGroup α)
  (hrho : ρ (Sum.inr PUnit.unit) = commWord u (finitePairs q))

noncomputable def coveredSpineToStrictSpine :
    Hom (strictOrderCx (OldCoveredSpine q (namedOldCoverProjection q ρ u)))
      (strictOrderCx (GenusSpineCell q)) :=
  (strictPullbackProjection (namedOldCoverProjection q ρ u)
    (namedOldCoverProjection_isPosetCover q ρ u) (genusSpineCellToOld q)
    (genusSpineCellToOld_monotone q)).comp
      (strictOrderCxMap (spinePullbackOldCoverOrderIso q (namedOldCoverProjection q ρ u)).symm
        (spinePullbackOldCoverOrderIso q (namedOldCoverProjection q ρ u)).symm.strictMono)

theorem receivedSpineToCoveredSpine_second :
    (coveredSpineToStrictSpine q ρ u).comp (receivedSpineToCoveredSpine q ρ u hrho) =
      receivedSpineToStrictSpine q ρ u := by
  apply Hom.ext' <;> rfl

theorem receivedSpineToCoveredSpine_first :
    (orderCxMap (oldCoveredSpineToOld q (namedOldCoverProjection q ρ u))
      (oldCoveredSpineToOld_monotone q (namedOldCoverProjection q ρ u))).comp
      ((strictOrderIncl _).comp (receivedSpineToCoveredSpine q ρ u hrho)) =
      receivedSpineToOldCover q ρ u hrho := by
  apply Hom.ext' <;> rfl

theorem receivedSpineToCoveredSpine_vertex_old (a : (singleReceivedSpineCover q ρ u).V) :
    (oldCoveredSpineToOld q (namedOldCoverProjection q ρ u)
      ((receivedSpineToCoveredSpine q ρ u hrho).onV a)).1 =
      (receivedSpineToQuotient q ρ u hrho).onV a := by
  change uOrderHomInv.onV ((receivedSpineToQuotient q ρ u hrho).onV a) = _
  exact uOrderHomInv_vertex _

/-- Faithfulness of the group receiver preserves the individual sheets over
every spine vertex, including vertices away from the chosen root. -/
theorem receivedSpineToQuotient_sheet_injective (a : (markedSpineCx q).V) :
    Function.Injective (fun g : PresGroup (substPresF ρ (finiteSpineWordBlock q u)) =>
      (receivedSpineToQuotient q ρ u hrho).onV (g, a)) := by
  intro g h hgh
  apply finiteSpineToQuotient_injective ρ q u hrho
  apply deckV_injective_in_group (X := orderCx (namedQuotientPos ρ q u))
    (namedQuotientBase ρ q u)
    ((receivedSpineToQuotient q ρ u hrho).onV (1, a))
  have hg := receivedSpineToQuotient_deckV q ρ u hrho g 1 a
  have hh := receivedSpineToQuotient_deckV q ρ u hrho h 1 a
  rw (config := { transparency := .default }) [mul_one] at hg hh
  exact hg.symm.trans (hgh.trans hh)

/-- The actual map into the pullback spine is injective on faces: its
spine projection retains the original face, and its old-cover projection
retains the sheet through the proved faithful receiver. -/
theorem receivedSpineToCoveredSpine_onF_injective :
    Function.Injective (receivedSpineToCoveredSpine q ρ u hrho).onF := by
  rintro ⟨g, t⟩ ⟨h, s⟩ he
  have hs := congrArg (coveredSpineToStrictSpine q ρ u).onF he
  change (receivedSpineToStrictSpine q ρ u).onF (g, t) =
    (receivedSpineToStrictSpine q ρ u).onF (h, s) at hs
  have hts : t = s := Subtype.ext hs
  subst s
  have hv : (receivedSpineToCoveredSpine q ρ u hrho).onV
      ((singleReceivedSpineCover q ρ u).base (g, t)) =
      (receivedSpineToCoveredSpine q ρ u hrho).onV
        ((singleReceivedSpineCover q ρ u).base (h, t)) := by
    rw (config := { transparency := .default }) [← (receivedSpineToCoveredSpine q ρ u hrho).base_onF,
      ← (receivedSpineToCoveredSpine q ρ u hrho).base_onF, he]
  have hv' := congrArg (fun a =>
    (oldCoveredSpineToOld q (namedOldCoverProjection q ρ u) a).1) hv
  dsimp only at hv'
  rw (config := { transparency := .default }) [receivedSpineToCoveredSpine_vertex_old, receivedSpineToCoveredSpine_vertex_old] at hv'
  have hg : g = h := receivedSpineToQuotient_sheet_injective q ρ u hrho
    ((markedSpineCx q).base t) hv'
  exact Prod.ext hg rfl

theorem receivedSpineToCoveredSpine_chain2_injective :
    Function.Injective (chain2 (receivedSpineToCoveredSpine q ρ u hrho)) :=
  Finsupp.mapDomain_injective (receivedSpineToCoveredSpine_onF_injective q ρ u hrho)

/-- A received spine cycle which bounds in the actual old cover is zero
already in the original group-indexed face chain. No abstract identification
of covered chains or extra injectivity hypothesis is used. -/
theorem receivedSpine_cycle_zero_of_old_boundary
    (c : (singleReceivedSpineCover q ρ u).F →₀ ℤ)
    (hc : Comb.bdry2 (singleReceivedSpineCover q ρ u) c = 0)
    (hbound : ∃ y ∈ Inc (namedOldCover q ρ u), Nerve.bdry y =
      cmap (oldCoveredSpineToOld q (namedOldCoverProjection q ρ u))
        (ordNerveChain2 (ordStrictInclusion2
          (chain2 (receivedSpineToCoveredSpine q ρ u hrho) c)))) : c = 0 := by
  have hz : chain2 (receivedSpineToCoveredSpine q ρ u hrho) c = 0 := by
    apply genus_old_cover_spine_chain_zero_of_boundary q (namedOldCoverProjection q ρ u)
      (namedOldCoverProjection_isPosetCover q ρ u) _ _ hbound
    rw (config := { transparency := .default }) [bdry2_chain2, hc, map_zero]
  apply receivedSpineToCoveredSpine_chain2_injective q ρ u hrho
  simpa only [map_zero] using hz

theorem receivedSpineCoveredChain_nerve_image
    (c : (singleReceivedSpineCover q ρ u).F →₀ ℤ) :
    cmap (Subtype.val : namedOldCover q ρ u →
      UOrder (namedQuotientPos ρ q u) (namedQuotientBase ρ q u))
      (cmap (oldCoveredSpineToOld q (namedOldCoverProjection q ρ u))
        (ordNerveChain2 (ordStrictInclusion2
          (chain2 (receivedSpineToCoveredSpine q ρ u hrho) c)))) =
      universalNerveChain2 (chain2 (receivedSpineToQuotient q ρ u hrho) c) := by
  change cmap Subtype.val
    (cmap (oldCoveredSpineToOld q (namedOldCoverProjection q ρ u))
      (ordNerveChain2 (chain2 (strictOrderIncl _)
        (chain2 (receivedSpineToCoveredSpine q ρ u hrho) c)))) =
    ordNerveChain2 (chain2 uOrderHomInv
      (chain2 (receivedSpineToQuotient q ρ u hrho) c))
  rw (config := { transparency := .default }) [← ordNerveChain2_chain2 _ (oldCoveredSpineToOld_monotone q
    (namedOldCoverProjection q ρ u))]
  rw (config := { transparency := .default }) [← ordNerveChain2_chain2
    (Subtype.val : namedOldCover q ρ u →
      UOrder (namedQuotientPos ρ q u) (namedQuotientBase ρ q u))
    (fun _ _ h => h)]
  apply congrArg ordNerveChain2
  have hfirst := congrArg (fun k => chain2 k c)
    (receivedSpineToCoveredSpine_first q ρ u hrho)
  simp only [chain2_comp_apply] at hfirst
  rw (config := { transparency := .default }) [hfirst]
  have hrestrict := congrArg (fun k => chain2 k c)
    (orderCxRestrict_projects (receivedSpineOrderMap q ρ u hrho)
      (fun p => InQOld (uOrderEnd p)) (receivedSpineOrderMap_old q ρ u hrho))
  simp only [receivedSpineOrderMap, chain2_comp_apply] at hrestrict
  exact hrestrict

/-- This is the precise reflection needed after the old/star relative
filling: a three-boundary supported on actual old cells forces the original
received two-cycle, with its individual sheet coefficients, to vanish. -/
theorem receivedSpine_cycle_zero_of_quotient_old_boundary
    (c : (singleReceivedSpineCover q ρ u).F →₀ ℤ)
    (hc : Comb.bdry2 (singleReceivedSpineCover q ρ u) c = 0)
    (hbound : ∃ y ∈ IncOn (fun p : UOrder (namedQuotientPos ρ q u)
        (namedQuotientBase ρ q u) => InQOld (uOrderEnd p)),
      Nerve.bdry y = universalNerveChain2 (chain2 (receivedSpineToQuotient q ρ u hrho) c)) :
    c = 0 := by
  obtain ⟨y, hy, hdy⟩ := hbound
  obtain ⟨b, hb, hby⟩ := exists_preimage_of_mem_incOn
    (fun p : UOrder (namedQuotientPos ρ q u) (namedQuotientBase ρ q u) =>
      InQOld (uOrderEnd p)) hy
  apply receivedSpine_cycle_zero_of_old_boundary q ρ u hrho c hc
  refine ⟨b, hb, ?_⟩
  have hne : ∃ p : UOrder (namedQuotientPos ρ q u) (namedQuotientBase ρ q u),
      InQOld (uOrderEnd p) :=
    ⟨(receivedSpineOrderMap q ρ u hrho).onV (1, (markedSpineTree q).root),
      receivedSpineOrderMap_old q ρ u hrho _⟩
  apply cmap_val_injective _ hne
  rw (config := { transparency := .default }) [cmap_bdry, hby, hdy]
  exact (receivedSpineCoveredChain_nerve_image q ρ u hrho c).symm

end FiniteChains.Davis.Genus
