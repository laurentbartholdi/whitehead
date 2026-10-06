import RequestProject.GenusFaithfulComparison
import RequestProject.ChamberQuotientAttachingCover
import RequestProject.PosetCoverPullback
import RequestProject.PosetCoverComparableLifts
import RequestProject.OrderNormalizationNaturality
import RequestProject.GenusReceivedPolygonCoefficient
import RequestProject.NerveDegree

/-!
The genuine surface cover under the lifted attaching locus of the named
quotient. Since its attaching map is `gHom ∘ chainMax`, the surface cover is
an actual pullback of the quotient's universal order cover. A unique lower
interval lift gives the sheet-preserving map from the subdivided attaching
locus. Its normalized finite-chain map commutes with the boundary and
preserves the required support on the polygon marking.

Written proof terms; not compiled under the current workflow. This constructs
the forward chain transfer, not an unproved inverse subdivision equivalence.
-/

noncomputable section
open scoped Classical

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains.Comb

universe u
variable {P Q : Type u} [PartialOrder P] [PartialOrder Q]

/-- The normalized one-chain map of a monotone map between different posets. -/
def normalizedChain1To (f : P → Q) (hf : Monotone f) :
    (StrictOrdEdge P →₀ ℤ) →ₗ[ℤ] (StrictOrdEdge Q →₀ ℤ) :=
  normalizeOrdChain1.comp ((chain1 (orderCxMap f hf)).comp (chain1 (strictOrderIncl P)))

theorem normalizedChain2To_boundary (f : P → Q) (hf : Monotone f)
    (c : StrictOrdTri P →₀ ℤ) :
    Comb.bdry2 (strictOrderCx Q) (normalizedStrictChain2 f hf c) =
      normalizedChain1To f hf (Comb.bdry2 (strictOrderCx P) c) := by
  change Comb.bdry2 (strictOrderCx Q)
      (normalizeOrdChain2 (chain2 (orderCxMap f hf) (chain2 (strictOrderIncl P) c))) =
    normalizeOrdChain1 (chain1 (orderCxMap f hf)
      (chain1 (strictOrderIncl P) (Comb.bdry2 (strictOrderCx P) c)))
  rw (config := { transparency := .default }) [bdry2_normalizeOrdChain2, bdry2_chain2, bdry2_chain2]

theorem normalizedChain1To_support (f : P → Q) (hf : Monotone f)
    (c : StrictOrdEdge P →₀ ℤ) (e : StrictOrdEdge Q)
    (he : e ∈ (normalizedChain1To f hf c).support) :
    ∃ d ∈ c.support, e.1 = (f d.1.1, f d.1.2) := by
  have hsingle (d : StrictOrdEdge P) (n : ℤ) :
      normalizedChain1To f hf (Finsupp.single d n) =
        n • normalizeOrdEdge ⟨(f d.1.1, f d.1.2), hf d.2.le⟩ := by
    change normalizeOrdChain1 (Finsupp.mapDomain (orderCxMap f hf).onE
      (Finsupp.mapDomain (strictOrderIncl P).onE (Finsupp.single d n))) = _
    rw (config := { transparency := .default }) [Finsupp.mapDomain_single, Finsupp.mapDomain_single, normalizeOrdChain1_single]
    rfl
  have hsum : normalizedChain1To f hf c =
      ∑ d ∈ c.support, c d • normalizeOrdEdge ⟨(f d.1.1, f d.1.2), hf d.2.le⟩ := by
    conv_lhs => rw (config := { transparency := .default }) [← Finsupp.sum_single c]
    rw (config := { transparency := .default }) [map_finsuppSum]
    simp only [hsingle]
    rfl
  rw (config := { transparency := .default }) [hsum] at he
  obtain ⟨d, hd, hde⟩ := Finsupp.mem_support_finset_sum e he
  have hn : normalizeOrdEdge ⟨(f d.1.1, f d.1.2), hf d.2.le⟩ e ≠ 0 := by
    intro hz
    have h := Finsupp.mem_support_iff.mp hde
    rw (config := { transparency := .default }) [Finsupp.smul_apply, hz, smul_zero] at h
    exact h rfl
  unfold normalizeOrdEdge at hn
  split_ifs at hn with h
  · simp at hn
  · have heq : (⟨(f d.1.1, f d.1.2), lt_of_le_of_ne (hf d.2.le) h⟩ :
        StrictOrdEdge Q) = e := by
      by_contra hh
      exact hn (by simp [hh])
    exact ⟨d, hd, (congrArg Subtype.val heq).symm⟩

end FiniteChains.Comb

namespace FiniteChains.Davis
open RACG Mirror Comb

universe u
variable {P X : Type u} [PartialOrder P] [DecidableEq P]
  [PartialOrder X] (g : P →o X)
  (a : Qpos (cmpRel P) X (nerveAtt g))
  (hc : IsConnected (orderCx (Qpos (cmpRel P) X (nerveAtt g))))

/-- The cover of the original cell poset retains actual universal-cover sheets. -/
abbrev AttachingSurfaceCover := PosetCoverPullback
  (uOrderEnd (P := Qpos (cmpRel P) X (nerveAtt g)) (a := a))
  (fun p : P => qNew (att := nerveAtt g) (g p))

abbrev attachingSurfaceProjection : AttachingSurfaceCover g a → P :=
  posetPullbackProjection _ _

include hc in
theorem attachingSurfaceProjection_isPosetCover :
    IsPosetCover (attachingSurfaceProjection g a) :=
  (uOrderEnd_isPosetCover hc).pullback _ (qNew_monotone.comp g.monotone)

theorem qAttachingCoverEnd_monotone :
    Monotone (qAttachingCoverEnd a) := by
  intro p r hpr
  change qPositiveOldOrderIso ⟨uOrderEnd p.1, p.2⟩ ≤
    qPositiveOldOrderIso ⟨uOrderEnd r.1, r.2⟩
  exact qPositiveOldOrderIso.monotone
    (show (⟨uOrderEnd p.1, p.2⟩ : QPositiveOld) ≤ ⟨uOrderEnd r.1, r.2⟩ from
      uOrderEnd_monotone hpr)

theorem qAttachingCoverEnd_oldPoint (p : QLiftedAttaching a) :
    qOldIncl (att := nerveAtt g) (posQCube (qAttachingCoverEnd a p)) = uOrderEnd p.1 := by
  exact congrArg Subtype.val
    (qPositiveOldOrderIso.symm_apply_apply ⟨uOrderEnd p.1, p.2⟩)

theorem attachingSurface_lower_comparison (p : QLiftedAttaching a) :
    qNew (att := nerveAtt g) (nerveAtt g (qAttachingCoverEnd a p)) ≤ uOrderEnd p.1 := by
  rw (config := { transparency := .default }) [← qAttachingCoverEnd_oldPoint g a p]
  exact qNew_att_le_qOldIncl (qAttachingCoverEnd a p)

/-- Move to the actual lower base lift in the same universal-cover sheet. -/
def attachingSurfaceLowerLift (p : QLiftedAttaching a) :
    UOrder (Qpos (cmpRel P) X (nerveAtt g)) a :=
  (uOrderEnd_isPosetCover hc).lowerMapLift Subtype.val
    (fun p => qNew (att := nerveAtt g) (nerveAtt g (qAttachingCoverEnd a p)))
    (attachingSurface_lower_comparison g a) p

theorem attachingSurfaceLowerLift_spec (p : QLiftedAttaching a) :
    attachingSurfaceLowerLift g a hc p ≤ p.1 ∧
      uOrderEnd (attachingSurfaceLowerLift g a hc p) =
        qNew (att := nerveAtt g) (nerveAtt g (qAttachingCoverEnd a p)) :=
  (uOrderEnd_isPosetCover hc).lowerMapLift_spec _ _ _ p

theorem attachingSurfaceLowerLift_monotone :
    Monotone (attachingSurfaceLowerLift g a hc) :=
  (uOrderEnd_isPosetCover hc).lowerMapLift_monotone
    (Subtype.val : QLiftedAttaching a → UOrder (Qpos (cmpRel P) X (nerveAtt g)) a)
    (fun p => qNew (att := nerveAtt g) (nerveAtt g (qAttachingCoverEnd a p)))
    (fun _ _ h => h)
    (qNew_monotone.comp ((nerveAtt g).monotone.comp (qAttachingCoverEnd_monotone g a)))
    (attachingSurface_lower_comparison g a)

/-- The actual lifted last-vertex map from the subdivided attaching locus. -/
def attachingToSurfaceCover (p : QLiftedAttaching a) : AttachingSurfaceCover g a :=
  ⟨(attachingSurfaceLowerLift g a hc p, chainMax (qAttachingCoverEnd a p)),
    (attachingSurfaceLowerLift_spec g a hc p).2⟩

theorem attachingToSurfaceCover_monotone :
    Monotone (attachingToSurfaceCover g a hc) := by
  intro p r hpr
  exact ⟨attachingSurfaceLowerLift_monotone g a hc hpr,
    chainMax_monotone (qAttachingCoverEnd_monotone g a hpr)⟩

@[simp] theorem attachingToSurfaceCover_projection (p : QLiftedAttaching a) :
    attachingSurfaceProjection g a (attachingToSurfaceCover g a hc p) =
      chainMax (qAttachingCoverEnd a p) := rfl

def attachingSurfaceChain2 : (StrictOrdTri (QLiftedAttaching a) →₀ ℤ) →ₗ[ℤ]
    (StrictOrdTri (AttachingSurfaceCover g a) →₀ ℤ) :=
  normalizedStrictChain2 (attachingToSurfaceCover g a hc)
    (attachingToSurfaceCover_monotone g a hc)

def attachingSurfaceChain1 : (StrictOrdEdge (QLiftedAttaching a) →₀ ℤ) →ₗ[ℤ]
    (StrictOrdEdge (AttachingSurfaceCover g a) →₀ ℤ) :=
  normalizedChain1To (attachingToSurfaceCover g a hc)
    (attachingToSurfaceCover_monotone g a hc)

theorem attachingSurfaceChain2_boundary (c : StrictOrdTri (QLiftedAttaching a) →₀ ℤ) :
    Comb.bdry2 (strictOrderCx (AttachingSurfaceCover g a)) (attachingSurfaceChain2 g a hc c) =
      attachingSurfaceChain1 g a hc (Comb.bdry2 (strictOrderCx (QLiftedAttaching a)) c) :=
  normalizedChain2To_boundary _ _ c

theorem attachingSurfaceChain2_cycle (c : StrictOrdTri (QLiftedAttaching a) →₀ ℤ)
    (hcycle : Comb.bdry2 (strictOrderCx (QLiftedAttaching a)) c = 0) :
    Comb.bdry2 (strictOrderCx (AttachingSurfaceCover g a)) (attachingSurfaceChain2 g a hc c) = 0 := by
  rw (config := { transparency := .default }) [attachingSurfaceChain2_boundary, hcycle, map_zero]

/-- Actual boundary support survives the sheet-preserving chain transfer. -/
theorem attachingSurfaceChain2_boundary_support (S : Set P)
    (c : StrictOrdTri (QLiftedAttaching a) →₀ ℤ)
    (hs : ∀ e ∈ (Comb.bdry2 (strictOrderCx (QLiftedAttaching a)) c).support,
      chainMax (qAttachingCoverEnd a e.1.1) ∈ S) :
    ∀ e ∈ (Comb.bdry2 (strictOrderCx (AttachingSurfaceCover g a))
      (attachingSurfaceChain2 g a hc c)).support,
      attachingSurfaceProjection g a e.1.1 ∈ S := by
  intro e he
  rw (config := { transparency := .default }) [attachingSurfaceChain2_boundary] at he
  obtain ⟨d, hd, heq⟩ := normalizedChain1To_support
    (attachingToSurfaceCover g a hc) (attachingToSurfaceCover_monotone g a hc)
    (Comb.bdry2 (strictOrderCx (QLiftedAttaching a)) c) e he
  have hfst := congrArg Prod.fst heq
  rw (config := { transparency := .default }) [hfst, attachingToSurfaceCover_projection]
  exact hs d hd

/-- Both endpoints of every boundary edge are retained; this is the relative
chain condition for a genuine graph subcomplex. -/
theorem attachingSurfaceChain2_boundary_endpoints (S : Set P)
    (c : StrictOrdTri (QLiftedAttaching a) →₀ ℤ)
    (hs : ∀ e ∈ (Comb.bdry2 (strictOrderCx (QLiftedAttaching a)) c).support,
      chainMax (qAttachingCoverEnd a e.1.1) ∈ S ∧
      chainMax (qAttachingCoverEnd a e.1.2) ∈ S) :
    ∀ e ∈ (Comb.bdry2 (strictOrderCx (AttachingSurfaceCover g a))
      (attachingSurfaceChain2 g a hc c)).support,
      attachingSurfaceProjection g a e.1.1 ∈ S ∧
      attachingSurfaceProjection g a e.1.2 ∈ S := by
  intro e he
  rw (config := { transparency := .default }) [attachingSurfaceChain2_boundary] at he
  obtain ⟨d, hd, heq⟩ := normalizedChain1To_support
    (attachingToSurfaceCover g a hc) (attachingToSurfaceCover_monotone g a hc)
    (Comb.bdry2 (strictOrderCx (QLiftedAttaching a)) c) e he
  have hfst := congrArg Prod.fst heq
  have hsnd := congrArg Prod.snd heq
  rw (config := { transparency := .default }) [hfst, hsnd, attachingToSurfaceCover_projection, attachingToSurfaceCover_projection]
  exact hs d hd

/-- The barycentric pullback cover, before applying its last-vertex map. -/
abbrev AttachingSurfaceSubdivision := PosetCoverPullback
  (uOrderEnd (P := Qpos (cmpRel P) X (nerveAtt g)) (a := a))
  (fun σ : NeSpx (cmpRel P) => qNew (att := nerveAtt g) (nerveAtt g σ))

def attachingToSurfaceSubdivision (p : QLiftedAttaching a) :
    AttachingSurfaceSubdivision g a :=
  ⟨(attachingSurfaceLowerLift g a hc p, qAttachingCoverEnd a p),
    (attachingSurfaceLowerLift_spec g a hc p).2⟩

theorem attachingToSurfaceSubdivision_monotone :
    Monotone (attachingToSurfaceSubdivision g a hc) := by
  intro p r hpr
  exact ⟨attachingSurfaceLowerLift_monotone g a hc hpr,
    qAttachingCoverEnd_monotone g a hpr⟩

def surfaceSubdivisionLastVertex (p : AttachingSurfaceSubdivision g a) :
    AttachingSurfaceCover g a := ⟨(p.1.1, chainMax p.1.2), p.2⟩

theorem surfaceSubdivisionLastVertex_monotone :
    Monotone (surfaceSubdivisionLastVertex g a) := by
  intro p r hpr
  exact ⟨hpr.1, chainMax_monotone hpr.2⟩

@[simp] theorem surfaceSubdivisionLastVertex_attaching (p : QLiftedAttaching a) :
    surfaceSubdivisionLastVertex g a (attachingToSurfaceSubdivision g a hc p) =
      attachingToSurfaceCover g a hc p := rfl

theorem surfaceSubdivision_upper_comparison (p : AttachingSurfaceSubdivision g a) :
    uOrderEnd p.1.1 ≤ qOldIncl (att := nerveAtt g) (posQCube p.1.2) := by
  rw (config := { transparency := .default }) [p.2]
  exact qNew_att_le_qOldIncl p.1.2

/-- The inverse cover comparison is an actual upper interval lift in the
same sheet, rather than a selected homotopy equivalence of presentations. -/
def surfaceSubdivisionUpperLift (p : AttachingSurfaceSubdivision g a) :
    UOrder (Qpos (cmpRel P) X (nerveAtt g)) a :=
  (uOrderEnd_isPosetCover hc).upperMapLift (fun p => p.1.1)
    (fun p => qOldIncl (att := nerveAtt g) (posQCube p.1.2))
    (surfaceSubdivision_upper_comparison g a) p

theorem surfaceSubdivisionUpperLift_spec (p : AttachingSurfaceSubdivision g a) :
    p.1.1 ≤ surfaceSubdivisionUpperLift g a hc p ∧
      uOrderEnd (surfaceSubdivisionUpperLift g a hc p) =
        qOldIncl (att := nerveAtt g) (posQCube p.1.2) :=
  (uOrderEnd_isPosetCover hc).upperMapLift_spec
    (fun p : AttachingSurfaceSubdivision g a => p.1.1)
    (fun p => qOldIncl (att := nerveAtt g) (posQCube p.1.2))
    (surfaceSubdivision_upper_comparison g a) p

theorem surfaceSubdivisionUpperLift_monotone :
    Monotone (surfaceSubdivisionUpperLift g a hc) := by
  apply (uOrderEnd_isPosetCover hc).upperMapLift_monotone
    (fun p : AttachingSurfaceSubdivision g a => p.1.1)
    (fun p => qOldIncl (att := nerveAtt g) (posQCube p.1.2))
    ?_ ?_ (surfaceSubdivision_upper_comparison g a)
  · exact fun _ _ h => h.1
  · intro p r hpr
    exact qOldIncl_monotone (show posQCube p.1.2 ≤ posQCube r.1.2 from
      ⟨hpr.2, fun _ _ => rfl⟩)

def surfaceSubdivisionToAttaching (p : AttachingSurfaceSubdivision g a) :
    QLiftedAttaching a :=
  ⟨surfaceSubdivisionUpperLift g a hc p, by
    rw (config := { transparency := .default }) [(surfaceSubdivisionUpperLift_spec g a hc p).2]
    exact ⟨trivial, rfl⟩⟩

theorem surfaceSubdivisionToAttaching_monotone :
    Monotone (surfaceSubdivisionToAttaching g a hc) :=
  surfaceSubdivisionUpperLift_monotone g a hc

@[simp] theorem surfaceSubdivisionToAttaching_endpoint (p : AttachingSurfaceSubdivision g a) :
    qAttachingCoverEnd a (surfaceSubdivisionToAttaching g a hc p) = p.1.2 := by
  apply (qPositiveOldOrderIso (att := nerveAtt g)).symm.injective
  apply Subtype.ext
  change qOldIncl (att := nerveAtt g)
      (posQCube (qAttachingCoverEnd a (surfaceSubdivisionToAttaching g a hc p))) =
    qOldIncl (att := nerveAtt g) (posQCube p.1.2)
  rw (config := { transparency := .default }) [qAttachingCoverEnd_oldPoint]
  exact (surfaceSubdivisionUpperLift_spec g a hc p).2

theorem surfaceSubdivisionToAttaching_leftInverse :
    Function.LeftInverse (surfaceSubdivisionToAttaching g a hc)
      (attachingToSurfaceSubdivision g a hc) := by
  intro p
  apply Subtype.ext
  have hu := surfaceSubdivisionUpperLift_spec g a hc
    (attachingToSurfaceSubdivision g a hc p)
  have hl := attachingSurfaceLowerLift_spec g a hc p
  exact (uOrderEnd_isPosetCover hc).up_inj hu.1 hl.1
    (hu.2.trans (qAttachingCoverEnd_oldPoint g a p))

theorem surfaceSubdivisionToAttaching_rightInverse :
    Function.RightInverse (surfaceSubdivisionToAttaching g a hc)
      (attachingToSurfaceSubdivision g a hc) := by
  intro p
  apply Subtype.ext
  apply Prod.ext
  · have hl := attachingSurfaceLowerLift_spec g a hc
      (surfaceSubdivisionToAttaching g a hc p)
    have hu := surfaceSubdivisionUpperLift_spec g a hc p
    apply (uOrderEnd_isPosetCover hc).down_inj hl.1 hu.1
    rw (config := { transparency := .default }) [hl.2, surfaceSubdivisionToAttaching_endpoint, p.2]
  · exact surfaceSubdivisionToAttaching_endpoint g a hc p

/-- Exact cover identification with the pullback of the subdivided surface. -/
def attachingSurfaceSubdivisionOrderIso : QLiftedAttaching a ≃o
    AttachingSurfaceSubdivision g a where
  toFun := attachingToSurfaceSubdivision g a hc
  invFun := surfaceSubdivisionToAttaching g a hc
  left_inv := surfaceSubdivisionToAttaching_leftInverse g a hc
  right_inv := surfaceSubdivisionToAttaching_rightInverse g a hc
  map_rel_iff' := by
    intro p r
    change attachingToSurfaceSubdivision g a hc p ≤
      attachingToSurfaceSubdivision g a hc r ↔ p ≤ r
    constructor
    · intro h
      have hh := surfaceSubdivisionToAttaching_monotone g a hc h
      simpa only [surfaceSubdivisionToAttaching_leftInverse g a hc p,
        surfaceSubdivisionToAttaching_leftInverse g a hc r] using hh
    · intro h
      exact attachingToSurfaceSubdivision_monotone g a hc h

/-- Actual reverse subdivision-cover identification on the full augmented
nerve, retaining homogeneous degree, finite support, and every coefficient. -/
theorem attachingSurfaceSubdivision_chain_inverse (c : Nerve.Ch (QLiftedAttaching a)) :
    Nerve.cmap (surfaceSubdivisionToAttaching g a hc)
      (Nerve.cmap (attachingToSurfaceSubdivision g a hc) c) = c := by
  rw (config := { transparency := .default }) [Nerve.cmap_comp]
  have he : (surfaceSubdivisionToAttaching g a hc) ∘
      (attachingToSurfaceSubdivision g a hc) = id :=
    funext (surfaceSubdivisionToAttaching_leftInverse g a hc)
  rw (config := { transparency := .default }) [he, Nerve.cmap_id]

theorem attachingSurfaceSubdivision_chain_inc (c : Nerve.Ch (QLiftedAttaching a))
    (hinc : c ∈ Nerve.Inc (QLiftedAttaching a)) :
    Nerve.cmap (attachingToSurfaceSubdivision g a hc) c ∈
      Nerve.Inc (AttachingSurfaceSubdivision g a) :=
  Nerve.cmap_mem_inc_of_monotone (attachingToSurfaceSubdivision_monotone g a hc) hinc

theorem attachingSurfaceSubdivision_chain_degree (n : ℕ)
    (c : Nerve.Ch (QLiftedAttaching a)) (hdegree : Nerve.lengthProjection n c = c) :
    Nerve.lengthProjection n (Nerve.cmap (attachingToSurfaceSubdivision g a hc) c) =
      Nerve.cmap (attachingToSurfaceSubdivision g a hc) c := by
  rw (config := { transparency := .default }) [Nerve.lengthProjection_cmap, hdegree]

end FiniteChains.Davis

namespace FiniteChains.Davis.Genus
open RACG Mirror Comb PresModel BlockFamily

variable {α Jr : Type} (ρ : Jr ⊕ PUnit.{1} → FreeGroup α)
  (q : ℕ) [NeZero q] (u : Fin q × Bool → FreeGroup α)

def namedSurfaceLabel : GenusVertex q →o namedBasePos ρ q u :=
  gHom (w := genusNonemptyW (namedPres ρ q u)
      (namedA (α := α) q) (namedB (α := α) q) q) (j₀ := Sum.inr PUnit.unit)
    (genus_hM (namedA (α := α) q) (namedB (α := α) q) q)
    (genus_hvlab (namedA (α := α) q) (namedB (α := α) q) q)
    (genus_helb (namedA (α := α) q) (namedB (α := α) q) q) (gc q)

@[simp] theorem namedAtt_eq_nerveAtt :
    namedAtt ρ q u = nerveAtt (namedSurfaceLabel ρ q u) := rfl

theorem namedQuotientPos_isConnected : IsConnected (orderCx (namedQuotientPos ρ q u)) := by
  letI : Nonempty (namedBasePos ρ q u) := ⟨namedAtt ρ q u (gBase q)⟩
  exact qpos_isConnected_of_zpos (zpos_isConnected (namedBasePos_isConnected ρ q u))

abbrev NamedSurfaceCover :=
  AttachingSurfaceCover (namedSurfaceLabel ρ q u) (namedQuotientBase ρ q u)

abbrev namedSurfaceProjection : NamedSurfaceCover ρ q u → GenusVertex q :=
  attachingSurfaceProjection (namedSurfaceLabel ρ q u) (namedQuotientBase ρ q u)

theorem namedSurfaceProjection_isPosetCover : IsPosetCover (namedSurfaceProjection ρ q u) :=
  attachingSurfaceProjection_isPosetCover (namedSurfaceLabel ρ q u)
    (namedQuotientBase ρ q u) (namedQuotientPos_isConnected ρ q u)

abbrev namedAttachingSurfaceChain2 :=
  attachingSurfaceChain2 (namedSurfaceLabel ρ q u) (namedQuotientBase ρ q u)
    (namedQuotientPos_isConnected ρ q u)

/-- The precise hypothesis needed by the polygon rigidity theorem, transported
from the actual attaching-intersection chain with every cover sheet retained. -/
theorem namedAttachingSurfaceChain2_polygon_boundary
    (c : StrictOrdTri (QLiftedAttaching (namedQuotientBase ρ q u)) →₀ ℤ)
    (hboundary : ∀ e ∈ (Comb.bdry2 (strictOrderCx
      (QLiftedAttaching (namedQuotientBase ρ q u))) c).support,
      InPolygonBoundary (gc q) (chainMax (qAttachingCoverEnd
        (namedQuotientBase ρ q u) e.1.1))) :
    ∀ e ∈ (Comb.bdry2 (strictOrderCx (NamedSurfaceCover ρ q u))
      (namedAttachingSurfaceChain2 ρ q u c)).support,
      InPolygonBoundary (gc q) (namedSurfaceProjection ρ q u e.1.1) :=
  attachingSurfaceChain2_boundary_support (namedSurfaceLabel ρ q u)
    (namedQuotientBase ρ q u) (namedQuotientPos_isConnected ρ q u)
    {p | InPolygonBoundary (gc q) p} c hboundary

theorem namedAttachingSurfaceChain2_polygon_endpoints
    (c : StrictOrdTri (QLiftedAttaching (namedQuotientBase ρ q u)) →₀ ℤ)
    (hboundary : ∀ e ∈ (Comb.bdry2 (strictOrderCx
      (QLiftedAttaching (namedQuotientBase ρ q u))) c).support,
      InPolygonBoundary (gc q) (chainMax (qAttachingCoverEnd
        (namedQuotientBase ρ q u) e.1.1)) ∧
      InPolygonBoundary (gc q) (chainMax (qAttachingCoverEnd
        (namedQuotientBase ρ q u) e.1.2))) :
    ∀ e ∈ (Comb.bdry2 (strictOrderCx (NamedSurfaceCover ρ q u))
      (namedAttachingSurfaceChain2 ρ q u c)).support,
      InPolygonBoundary (gc q) (namedSurfaceProjection ρ q u e.1.1) ∧
      InPolygonBoundary (gc q) (namedSurfaceProjection ρ q u e.1.2) :=
  attachingSurfaceChain2_boundary_endpoints (namedSurfaceLabel ρ q u)
    (namedQuotientBase ρ q u) (namedQuotientPos_isConnected ρ q u)
    {p | InPolygonBoundary (gc q) p} c hboundary

end FiniteChains.Davis.Genus
