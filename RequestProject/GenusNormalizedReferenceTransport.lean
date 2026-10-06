module

public import RequestProject.GenusUniversalPolygonTransport
public import RequestProject.GenusSingleSpineReference

@[expose] public section

/-! The chosen source spine filling and its exact marking corrections map
to the actual substituted reference. This supplies its geometric reference
class, not an additional B2 hypothesis. Awaiting final Lean verification. -/
noncomputable section
open scoped Classical

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains.Comb
universe u
variable {K X Y : Complex2.{u}}

theorem univLiftV_extendList (f : Hom X Y) (a : X.V)
    (v : UV X a) {p : List (X.E × Bool)} {b : X.V}
    (hp : IsPath X.src X.tgt p (endV v) b) :
    univLiftV a f (extendList p v) =
      extendList (mapPath f p) (univLiftV a f v) := by
  induction p generalizing v with
  | nil => rfl
  | cons e p ih =>
      have htail : IsPath X.src X.tgt p (endV (extend e v)) b := by
        rw [endV_extend hp.1]
        exact hp.2
      change univLiftV a f (extendList p (extend e v)) =
        extendList (mapPath f p) (extend (f.onE e.1, e.2) (univLiftV a f v))
      rw [ih (extend e v) htail, univLiftV_extend a f hp.1]

theorem SpanningTree.univLiftV_mappedTreeReference (T : SpanningTree K)
    (f : Hom K X) (j : Hom X Y) (a : K.V) :
    univLiftV (f.onV T.root) j (T.mappedTreeReference f a) =
      T.mappedTreeReference (j.comp f) a := by
  rw [SpanningTree.mappedTreeReference,
    univLiftV_extendList j (f.onV T.root) (UV.base X (f.onV T.root))
      (isPath_mapPath f (T.treePath_isPath a))]
  change extendList (mapPath j (mapPath f (T.treePath a))) (UV.base _ _) =
    extendList (mapPath (j.comp f) (T.treePath a)) (UV.base _ _)
  rw [mapPath_comp]

end FiniteChains.Comb

namespace FiniteChains.Davis.Genus
open RACG Mirror Comb PresModel BlockFamily Nerve
variable {α Jr : Type} (ρ : Jr ⊕ PUnit.{1} → FreeGroup α)
  (q : ℕ) [NeZero q] (u : Fin q × Bool → FreeGroup α)
  (hrho : ρ (Sum.inr PUnit.unit) = commWord u (finitePairs q))

/-- Equality on the entire named source group follows from the already
proved compatibility on the surjective tree-presentation inclusion. -/
theorem universalSpineOldReceiver_to_single_old
    (g : PresGroup (namedSpinePresentation q)) :
    finiteSpineOldRootReceiver q ρ u hrho (singleSpineNamedReceiver ρ q u g) =
      pi1Map (oldIntoNamedQuotient q ρ u) (universalSpineOldBase q)
        (universalSpineOldReceiver q g) := by
  obtain ⟨z, rfl⟩ := (namedSpineGroupEquiv q).surjective g
  have h₁ := DFunLike.congr_fun (finiteSpineOldRootReceiver_compatible q ρ u hrho) z
  have h₂ := DFunLike.congr_fun (universalSpineOldReceiver_compatible q) z
  calc
    _ = pi1Map (markedSpineToNamedQuotient q ρ u) (markedSpineTree q).root
        (SpanningTree.presToPi1 (markedSpineTree q) z) := h₁
    _ = pi1Map (oldIntoNamedQuotient q ρ u) (universalSpineOldBase q)
        (pi1Map (universalSpineToOld q) (markedSpineTree q).root
          (SpanningTree.presToPi1 (markedSpineTree q) z)) :=
      pi1Map_comp_apply (universalSpineToOld q) (oldIntoNamedQuotient q ρ u)
        (markedSpineTree q).root _
    _ = _ := congrArg (pi1Map (oldIntoNamedQuotient q ρ u) (universalSpineOldBase q)) h₂.symm

def universalReceivedSpineToSingle :
    Hom (universalNamedSpineCover q) (singleReceivedSpineCover q ρ u) :=
  ReceivedTree.changeGroup (markedSpineTree q) (universalSpineWordReceiver q)
    (singleSpineNamedReceiver ρ q u)

theorem universalNamedSpineComparison_vertex_factor
    (g : PresGroup (namedSpinePresentation q)) (a : (markedSpineCx q).V) :
    (receivedSpineToQuotient q ρ u hrho).onV (singleSpineNamedReceiver ρ q u g, a) =
      (universalOldToNamedQuotient ρ q u).onV
        ((universalNamedSpineComparison q).onV (g, a)) := by
  have he : univLiftV (universalSpineOldBase q) (oldIntoNamedQuotient q ρ u)
      (ReceivedTree.receiverVertex (markedSpineTree q) (universalSpineToOld q)
        (universalSpineOldReceiver q) g a) =
      ReceivedTree.receiverVertex (markedSpineTree q) (markedSpineToNamedQuotient q ρ u)
        (finiteSpineOldRootReceiver q ρ u hrho) (singleSpineNamedReceiver ρ q u g) a := by
    rw [ReceivedTree.receiverVertex, univLiftV_deckV,
      SpanningTree.univLiftV_mappedTreeReference,
      ← universalSpineOldReceiver_to_single_old ρ q u hrho g]
    rfl
  exact congrArg (pathTransportV (spineQuotientCylinderPath_isPath q ρ u)) he.symm

/-- The square consists of actual cellular maps, before taking chains. -/
theorem universalNamedSpineComparison_square :
    (receivedSpineToQuotient q ρ u hrho).comp (universalReceivedSpineToSingle ρ q u) =
      (universalOldToNamedQuotient ρ q u).comp (universalNamedSpineComparison q) := by
  apply Hom.ext'
  · funext x
    exact universalNamedSpineComparison_vertex_factor ρ q u hrho x.1 x.2
  · funext e
    apply Subtype.ext
    exact Prod.ext (universalNamedSpineComparison_vertex_factor ρ q u hrho e.1 _ ) rfl
  · funext t
    apply Subtype.ext
    exact Prod.ext (universalNamedSpineComparison_vertex_factor ρ q u hrho t.1 _ ) rfl

theorem universalNamedSpineComparison_chain2_factor
    (c : (universalNamedSpineCover q).F →₀ ℤ) :
    chain2 (receivedSpineToQuotient q ρ u hrho)
      (Finsupp.mapDomain (fun x : PresGroup (namedSpinePresentation q) × SpinePresentationRel q =>
        (singleSpineNamedReceiver ρ q u x.1, x.2)) c) =
      chain2 (universalOldToNamedQuotient ρ q u) (chain2 (universalNamedSpineComparison q) c) := by
  change chain2 (receivedSpineToQuotient q ρ u hrho)
    (chain2 (universalReceivedSpineToSingle ρ q u) c) = _
  rw [← chain2_comp_apply, universalNamedSpineComparison_square, chain2_comp_apply]

theorem universalOldToNamedQuotient_deckV
    (g : PresGroup (namedSpinePresentation q))
    (v : UV (spineOldCx q) (universalSpineOldBase q)) :
    (universalOldToNamedQuotient ρ q u).onV (deckV (universalSpineOldReceiver q g) v) =
      deckV (finiteSpineToQuotient ρ q u hrho (singleSpineNamedReceiver ρ q u g))
        ((universalOldToNamedQuotient ρ q u).onV v) := by
  change (uCoverPathTransport (spineQuotientCylinderPath_isPath q ρ u)).onV
    (univLiftV (universalSpineOldBase q) (oldIntoNamedQuotient q ρ u)
      (deckV (universalSpineOldReceiver q g) v)) = _
  rw [univLiftV_deckV, uCoverPathTransport_deckV,
    ← universalSpineOldReceiver_to_single_old ρ q u hrho g]
  change deckV (pi1Conj (spineQuotientCylinderPath_isPath q ρ u)
    (pi1Conj (isPath_revPath (spineQuotientCylinderPath_isPath q ρ u))
      (finiteSpineToQuotient ρ q u hrho (singleSpineNamedReceiver ρ q u g)))) _ = _
  rw [pi1Conj_cancel_reverse]
  rfl

theorem universalOldToNamedQuotient_deckF
    (g : PresGroup (namedSpinePresentation q))
    (t : (uCover (spineOldCx q) (universalSpineOldBase q)).F) :
    (universalOldToNamedQuotient ρ q u).onF (deckF (universalSpineOldReceiver q g) t) =
      deckF (finiteSpineToQuotient ρ q u hrho (singleSpineNamedReceiver ρ q u g))
        ((universalOldToNamedQuotient ρ q u).onF t) := by
  apply Subtype.ext
  exact Prod.ext (universalOldToNamedQuotient_deckV ρ q u hrho g t.1.1) rfl

theorem universalOldToNamedQuotient_chain2_deck
    (g : PresGroup (namedSpinePresentation q))
    (c : (uCover (spineOldCx q) (universalSpineOldBase q)).F →₀ ℤ) :
    chain2 (universalOldToNamedQuotient ρ q u)
      ((univDeck (spineOldCx q) (universalSpineOldBase q)).faceChains
        (universalSpineOldReceiver q g) c) =
      (univDeck (orderCx (namedQuotientPos ρ q u)) (namedQuotientBase ρ q u)).faceChains
        (finiteSpineToQuotient ρ q u hrho (singleSpineNamedReceiver ρ q u g))
        (chain2 (universalOldToNamedQuotient ρ q u) c) := by
  change Finsupp.mapDomain (universalOldToNamedQuotient ρ q u).onF
      (Finsupp.mapDomain (deckF (universalSpineOldReceiver q g)) c) =
    Finsupp.mapDomain _ (Finsupp.mapDomain (universalOldToNamedQuotient ρ q u).onF c)
  rw [← Finsupp.mapDomain_comp, ← Finsupp.mapDomain_comp]
  congr 1
  funext t
  exact universalOldToNamedQuotient_deckF ρ q u hrho g t

theorem universalOldToNamedQuotient_baseTransport_vertex
    (v : UV (spineOldCx q) (spineOldBase q)) :
    (universalOldToNamedQuotient ρ q u).onV ((universalOldBaseTransport q).onV v) =
      (oldCoverToNamedQuotient q ρ u).onV v := by
  induction v using UV.ind with
  | h p =>
      change UV.mk (pathTransportP (spineQuotientCylinderPath_isPath q ρ u)
        (mapPathFrom (universalSpineOldBase q) (oldIntoNamedQuotient q ρ u)
          (pathTransportP (universalOldBasePath q) p))) =
        UV.mk (pathTransportP (oldCylinderPath_isPath q ρ u)
          (mapPathFrom (spineOldBase q) (oldIntoNamedQuotient q ρ u) p))
      apply congrArg UV.mk
      exact Subtype.ext rfl

theorem universalOldToNamedQuotient_baseTransport_square :
    (universalOldToNamedQuotient ρ q u).comp (universalOldBaseTransport q) =
      oldCoverToNamedQuotient q ρ u := by
  apply Hom.ext'
  · funext v
    exact universalOldToNamedQuotient_baseTransport_vertex ρ q u v
  · funext e
    apply Subtype.ext
    exact Prod.ext (universalOldToNamedQuotient_baseTransport_vertex ρ q u e.1.1) rfl
  · funext t
    apply Subtype.ext
    exact Prod.ext (universalOldToNamedQuotient_baseTransport_vertex ρ q u t.1.1) rfl

/-- The correction uses exactly the same old-cell filling after substitution. -/
theorem universalOldMarkingCorrection_factor
    (g : PresGroup (namedSpinePresentation q)) (i : Fin q × Bool) :
    chain2 (universalOldToNamedQuotient ρ q u) (universalOldMarkingCorrection q g i) =
      quotientMarkingCorrection q ρ u hrho (singleSpineNamedReceiver ρ q u g) i := by
  rw [universalOldMarkingCorrection, universalOldToNamedQuotient_chain2_deck,
    ← chain2_comp_apply, universalOldToNamedQuotient_baseTransport_square]
  rfl

theorem universalOldMarkingCorrections_factor
    (c : (PresGroup (namedSpinePresentation q) × (Fin q × Bool)) →₀ ℤ) :
    chain2 (universalOldToNamedQuotient ρ q u) (universalOldMarkingCorrections q c) =
      quotientMarkingCorrections q ρ u hrho
        (Finsupp.mapDomain (fun x : PresGroup (namedSpinePresentation q) × (Fin q × Bool) =>
          (singleSpineNamedReceiver ρ q u x.1, x.2)) c) := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd => simp only [map_add, Finsupp.mapDomain_add, hc, hd]
  | single x n =>
      rw [universalOldMarkingCorrections, Finsupp.linearCombination_single, map_smul,
        universalOldMarkingCorrection_factor, Finsupp.mapDomain_single,
        quotientMarkingCorrections, Finsupp.linearCombination_single]

theorem singleFiniteSpineReference_corrected_chain :
    quotientCorrectedRelativeChain q ρ u hrho (singleFiniteSpineReference ρ q u) =
      chain2 (universalOldToNamedQuotient ρ q u)
        (chain2 (universalNamedSpineComparison q) (normalizedSpineReference q) -
          universalOldMarkingCorrections q (universalReferenceMarkingCoefficients q)) := by
  rw [quotientCorrectedRelativeChain, singleFiniteSpineReference_faceChain,
    singleFiniteSpineReference_markingChain, map_sub]
  rw [show chain2 (receivedSpineToQuotient q ρ u hrho)
      (Finsupp.mapDomain (fun x : PresGroup (namedSpinePresentation q) × SpinePresentationRel q =>
        (familySpineHom ρ (fun _ : PUnit.{1} => q) (fun _ => u) PUnit.unit x.1, x.2))
        (normalizedSpineReference q)) =
      chain2 (universalOldToNamedQuotient ρ q u)
        (chain2 (universalNamedSpineComparison q) (normalizedSpineReference q)) from
      universalNamedSpineComparison_chain2_factor ρ q u hrho _]
  rw [universalOldMarkingCorrections_factor]
  rfl

/-- The actual canonical coefficient vector has the actual degree-one
attaching reference modulo a genuine old three-boundary. -/
theorem singleFiniteSpineReference_corrected_geometry :
    ∃ y ∈ IncOn (fun p => InQOld (uOrderEnd p)),
      quotientCorrectedRelativeNerveChain q ρ u hrho (singleFiniteSpineReference ρ q u) =
        cmap Subtype.val (transportedUniversalPolygonAttachingChain ρ q u) + Nerve.bdry y := by
  have h := universalOldToNamedQuotient_polygon_reference ρ q u
    (chain2 (universalNamedSpineComparison q) (normalizedSpineReference q) -
      universalOldMarkingCorrections q (universalReferenceMarkingCoefficients q))
    (normalizedSpineReference_corrected_geometry q)
  simpa only [quotientCorrectedRelativeNerveChain, singleFiniteSpineReference_corrected_chain]
    using h

end FiniteChains.Davis.Genus
