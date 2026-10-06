import RequestProject.GenusNamedSurfaceSubdivision
import RequestProject.GenusNamedPolygonCoefficients
import RequestProject.GenusQuotientAttachingFilling
import RequestProject.StrictOrderNormalizationMaps
import RequestProject.OrderUniversalDeckChains
import RequestProject.GenusAllQuotientRelativeRigidity

/-! Polygon reconstruction yields a boundary supported on actual old cells.
All deck coefficients are retained in the actual quotient group.
 -/
noncomputable section
open scoped Classical

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false


namespace FiniteChains.Comb
open Nerve
universe u
variable {P Q : Type u} [PartialOrder P] [PartialOrder Q]

theorem decodeOrdNerve2_cmap_homogeneous (f : P → Q) (hf : Monotone f)
    (c : Ch P) (hc : c ∈ Inc P) (hd : lengthProjection 3 c = c) :
    decodeOrdNerve2 (cmap f c) = chain2 (orderCxMap f hf) (decodeOrdNerve2 c) := by
  have he : ordNerveChain2 (decodeOrdNerve2 c) = c := (ordNerveChain2_decode hc).trans hd
  calc
    _ = decodeOrdNerve2 (cmap f (ordNerveChain2 (decodeOrdNerve2 c))) := by rw [he]
    _ = _ := by rw [← ordNerveChain2_chain2 f hf, decodeOrdNerve2_encode]

variable {a : P}

theorem uOrderEdge_deck (g : Pi1 (orderCx P) a) (e : OrdEdge (UOrder P a)) :
    uOrderEdge ((orderCxMap (uOrderDeckOrderIso g) (uOrderDeckOrderIso g).monotone).onE e) =
      deckE g (uOrderEdge e) := by
  apply Subtype.ext
  apply Prod.ext
  · rfl
  · apply Subtype.ext
    change (endV (deckV g e.1.1), endV (deckV g e.1.2)) = (endV e.1.1, endV e.1.2)
    simp only [endV_deckV]

theorem uOrderHomInv_deckE (g : Pi1 (orderCx P) a) (e : UE (orderCx P) a) :
    uOrderHomInv.onE (deckE g e) =
      (orderCxMap (uOrderDeckOrderIso g) (uOrderDeckOrderIso g).monotone).onE
        (uOrderHomInv.onE e) := by
  have hinv (e : UE (orderCx P) a) : uOrderEdge (uOrderHomInv.onE e) = e :=
    homInv_onE_apply uOrderHom Function.bijective_id
      ⟨uOrderEdge_injective, uOrderEdge_surjective⟩
      ⟨uOrderFace_injective, uOrderFace_surjective⟩ e
  apply uOrderEdge_injective
  rw [hinv, uOrderEdge_deck, hinv]

theorem uOrderHomInv_deckF (g : Pi1 (orderCx P) a) (t : UF (orderCx P) a) :
    uOrderHomInv.onF (deckF g t) =
      (orderCxMap (uOrderDeckOrderIso g) (uOrderDeckOrderIso g).monotone).onF
        (uOrderHomInv.onF t) := by
  have hinv (t : UF (orderCx P) a) : uOrderFace (uOrderHomInv.onF t) = t :=
    homInv_onF_apply uOrderHom Function.bijective_id
      ⟨uOrderEdge_injective, uOrderEdge_surjective⟩
      ⟨uOrderFace_injective, uOrderFace_surjective⟩ t
  apply uOrderFace_injective
  rw [hinv, uOrderFace_deck, hinv]

theorem universalNerveChain1_deck (g : Pi1 (orderCx P) a)
    (c : UE (orderCx P) a →₀ ℤ) :
    universalNerveChain1 (chain1 ((univDeck (orderCx P) a).cellHom g) c) =
      cmap (uOrderDeck g) (universalNerveChain1 c) := by
  have he : chain1 uOrderHomInv (chain1 ((univDeck (orderCx P) a).cellHom g) c) =
      chain1 (orderCxMap (uOrderDeckOrderIso g) (uOrderDeckOrderIso g).monotone)
        (chain1 uOrderHomInv c) := by
    change Finsupp.mapDomain uOrderHomInv.onE (Finsupp.mapDomain (deckE g) c) =
      Finsupp.mapDomain _ (Finsupp.mapDomain uOrderHomInv.onE c)
    rw [← Finsupp.mapDomain_comp, ← Finsupp.mapDomain_comp]
    congr 1
    funext e
    exact uOrderHomInv_deckE g e
  change ordNerveChain1 (chain1 uOrderHomInv
    (chain1 ((univDeck (orderCx P) a).cellHom g) c)) = _
  rw [he, ordNerveChain1_chain1]
  rfl

theorem universalNerveChain2_deck (g : Pi1 (orderCx P) a)
    (c : UF (orderCx P) a →₀ ℤ) :
    universalNerveChain2 ((univDeck (orderCx P) a).faceChains g c) =
      cmap (uOrderDeck g) (universalNerveChain2 c) := by
  have he : chain2 uOrderHomInv ((univDeck (orderCx P) a).faceChains g c) =
      chain2 (orderCxMap (uOrderDeckOrderIso g) (uOrderDeckOrderIso g).monotone)
        (chain2 uOrderHomInv c) := by
    change Finsupp.mapDomain uOrderHomInv.onF (Finsupp.mapDomain (deckF g) c) =
      Finsupp.mapDomain _ (Finsupp.mapDomain uOrderHomInv.onF c)
    rw [← Finsupp.mapDomain_comp, ← Finsupp.mapDomain_comp]
    congr 1
    funext t
    exact uOrderHomInv_deckF g t
  change ordNerveChain2 (chain2 uOrderHomInv
    ((univDeck (orderCx P) a).faceChains g c)) = _
  rw [he, ordNerveChain2_chain2]
  rfl

end FiniteChains.Comb

namespace FiniteChains.Davis.Genus
open RACG Mirror Comb PresModel BlockFamily Nerve
variable {α Jr : Type} (ρ : Jr ⊕ PUnit.{1} → FreeGroup α)
  (q : ℕ) [NeZero q] (u : Fin q × Bool → FreeGroup α)

def namedAttachingDeck (g : NamedPolygonDeckGroup ρ q u) :
    namedAttachingCover q ρ u ≃o namedAttachingCover q ρ u where
  toFun p := ⟨uOrderDeck g p.1, by rw [uOrderDeck_end]; exact p.2⟩
  invFun p := ⟨uOrderDeck g⁻¹ p.1, by rw [uOrderDeck_end]; exact p.2⟩
  left_inv p := by
    apply Subtype.ext
    change deckV g⁻¹ (deckV g p.1) = p.1
    rw [← deckV_mul, inv_mul_cancel, deckV_one]
  right_inv p := by
    apply Subtype.ext
    change deckV g (deckV g⁻¹ p.1) = p.1
    rw [← deckV_mul, mul_inv_cancel, deckV_one]
  map_rel_iff' := (uOrderDeckOrderIso g).map_rel_iff

theorem namedAttachingIntoUniversal_deck_square (g : NamedPolygonDeckGroup ρ q u) :
    (namedAttachingIntoUniversal q ρ u).comp
      (orderCxMap (namedAttachingDeck ρ q u g) (namedAttachingDeck ρ q u g).monotone) =
      ((univDeck (orderCx (namedQuotientPos ρ q u))
        (namedQuotientBase ρ q u)).cellHom g).comp (namedAttachingIntoUniversal q ρ u) := by
  apply Hom.ext'
  · funext p; rfl
  · funext e
    exact uOrderEdge_deck g ((orderCxMap (Subtype.val : namedAttachingCover q ρ u → _)
      (fun _ _ h => h)).onE e)
  · funext t
    exact uOrderFace_deck g ((orderCxMap (Subtype.val : namedAttachingCover q ρ u → _)
      (fun _ _ h => h)).onF t)

theorem namedAttachingIntoUniversal_chain1_deck (g : NamedPolygonDeckGroup ρ q u)
    (c : OrdEdge (namedAttachingCover q ρ u) →₀ ℤ) :
    chain1 (namedAttachingIntoUniversal q ρ u)
      (chain1 (orderCxMap (namedAttachingDeck ρ q u g)
        (namedAttachingDeck ρ q u g).monotone) c) =
      chain1 ((univDeck (orderCx (namedQuotientPos ρ q u))
        (namedQuotientBase ρ q u)).cellHom g)
          (chain1 (namedAttachingIntoUniversal q ρ u) c) := by
  rw [← chain1_comp_apply, namedAttachingIntoUniversal_deck_square, chain1_comp_apply]

theorem namedAttachingDeck_projection (g : NamedPolygonDeckGroup ρ q u)
    (p : namedAttachingCover q ρ u) :
    qAttachingCoverEnd (namedQuotientBase ρ q u) (namedAttachingDeck ρ q u g p) =
      qAttachingCoverEnd (namedQuotientBase ρ q u) p := by
  change qPositiveOldOrderIso ⟨uOrderEnd (uOrderDeck g p.1), _⟩ =
    qPositiveOldOrderIso ⟨uOrderEnd p.1, _⟩
  congr 1
  exact Subtype.ext (uOrderDeck_end g p.1)

theorem namedAttachingSurfaceLowerLift_deck (g : NamedPolygonDeckGroup ρ q u)
    (p : namedAttachingCover q ρ u) :
    attachingSurfaceLowerLift (namedSurfaceLabel ρ q u) (namedQuotientBase ρ q u)
      (namedQuotientPos_isConnected ρ q u) (namedAttachingDeck ρ q u g p) =
      uOrderDeck g (attachingSurfaceLowerLift (namedSurfaceLabel ρ q u)
        (namedQuotientBase ρ q u) (namedQuotientPos_isConnected ρ q u) p) := by
  have h₁ := attachingSurfaceLowerLift_spec (namedSurfaceLabel ρ q u)
    (namedQuotientBase ρ q u) (namedQuotientPos_isConnected ρ q u)
    (namedAttachingDeck ρ q u g p)
  have h₂ := attachingSurfaceLowerLift_spec (namedSurfaceLabel ρ q u)
    (namedQuotientBase ρ q u) (namedQuotientPos_isConnected ρ q u) p
  apply (uOrderEnd_isPosetCover (namedQuotientPos_isConnected ρ q u)).down_inj
    h₁.1 ((uOrderDeckOrderIso g).monotone h₂.1)
  change uOrderEnd (attachingSurfaceLowerLift (namedSurfaceLabel ρ q u)
    (namedQuotientBase ρ q u) (namedQuotientPos_isConnected ρ q u)
    (namedAttachingDeck ρ q u g p)) =
    uOrderEnd (uOrderDeck g (attachingSurfaceLowerLift (namedSurfaceLabel ρ q u)
      (namedQuotientBase ρ q u) (namedQuotientPos_isConnected ρ q u) p))
  rw [h₁.2, uOrderDeck_end, h₂.2, namedAttachingDeck_projection]

theorem namedAttachingToSurface_deck (g : NamedPolygonDeckGroup ρ q u)
    (p : namedAttachingCover q ρ u) :
    attachingToSurfaceCover (namedSurfaceLabel ρ q u) (namedQuotientBase ρ q u)
      (namedQuotientPos_isConnected ρ q u) (namedAttachingDeck ρ q u g p) =
      namedSurfaceDeck ρ q u g
        (attachingToSurfaceCover (namedSurfaceLabel ρ q u) (namedQuotientBase ρ q u)
          (namedQuotientPos_isConnected ρ q u) p) := by
  apply Subtype.ext
  exact Prod.ext (namedAttachingSurfaceLowerLift_deck ρ q u g p)
    (congrArg chainMax (namedAttachingDeck_projection ρ q u g p))

def namedAttachingNerveSurfaceChain :
    Ch (namedAttachingCover q ρ u) →+
      (StrictOrdTri (NamedSurfaceCover ρ q u) →₀ ℤ) :=
  normalizeOrdChain2.toAddMonoidHom.comp
    ((chain2 (orderCxMap
      (attachingToSurfaceCover (namedSurfaceLabel ρ q u) (namedQuotientBase ρ q u)
        (namedQuotientPos_isConnected ρ q u))
      (attachingToSurfaceCover_monotone (namedSurfaceLabel ρ q u)
        (namedQuotientBase ρ q u) (namedQuotientPos_isConnected ρ q u)))).toAddMonoidHom.comp
      decodeOrdNerve2)

theorem namedAttachingNerveSurfaceChain_deck (g : NamedPolygonDeckGroup ρ q u)
    (c : Ch (namedAttachingCover q ρ u)) (hc : c ∈ Inc _)
    (hd : lengthProjection 3 c = c) :
    namedAttachingNerveSurfaceChain ρ q u (cmap (namedAttachingDeck ρ q u g) c) =
      chain2 (strictOrderCxMap (namedSurfaceDeck ρ q u g)
        (namedSurfaceDeck ρ q u g).strictMono) (namedAttachingNerveSurfaceChain ρ q u c) := by
  let F : namedAttachingCover q ρ u → NamedSurfaceCover ρ q u :=
    attachingToSurfaceCover (namedSurfaceLabel ρ q u) (namedQuotientBase ρ q u)
    (namedQuotientPos_isConnected ρ q u)
  have hF : Monotone F := attachingToSurfaceCover_monotone (namedSurfaceLabel ρ q u)
    (namedQuotientBase ρ q u) (namedQuotientPos_isConnected ρ q u)
  have hs : (orderCxMap F hF).comp
      (orderCxMap (namedAttachingDeck ρ q u g) (namedAttachingDeck ρ q u g).monotone) =
      (orderCxMap (namedSurfaceDeck ρ q u g) (namedSurfaceDeck ρ q u g).monotone).comp
        (orderCxMap F hF) := by
    apply Hom.ext'
    · funext p; exact namedAttachingToSurface_deck ρ q u g p
    · funext e
      apply Subtype.ext
      exact Prod.ext (namedAttachingToSurface_deck ρ q u g _)
        (namedAttachingToSurface_deck ρ q u g _)
    · funext t
      apply Subtype.ext
      exact Prod.ext (namedAttachingToSurface_deck ρ q u g _)
        (Prod.ext (namedAttachingToSurface_deck ρ q u g _)
          (namedAttachingToSurface_deck ρ q u g _))
  change normalizeOrdChain2 (chain2 (orderCxMap F hF)
    (decodeOrdNerve2 (cmap (namedAttachingDeck ρ q u g) c))) = _
  rw [decodeOrdNerve2_cmap_homogeneous _ (namedAttachingDeck ρ q u g).monotone c hc hd,
    ← chain2_comp_apply, hs, chain2_comp_apply, normalizeOrdChain2_strict_map]
  rfl

def namedAttachingNerveMultiple (c : Ch (namedAttachingCover q ρ u)) :
    MonoidAlgebra ℤ (NamedPolygonDeckGroup ρ q u) →ₗ[ℤ]
      Ch (namedAttachingCover q ρ u) :=
  (Finsupp.linearCombination ℤ (fun g => cmap (namedAttachingDeck ρ q u g) c)).comp
    (MonoidAlgebra.coeffLinearEquiv ℤ).toLinearMap

def namedQuotientNerveMultiple
    (c : Ch (UOrder (namedQuotientPos ρ q u) (namedQuotientBase ρ q u))) :
    MonoidAlgebra ℤ (NamedPolygonDeckGroup ρ q u) →ₗ[ℤ]
      Ch (UOrder (namedQuotientPos ρ q u) (namedQuotientBase ρ q u)) :=
  (Finsupp.linearCombination ℤ (fun g => cmap (uOrderDeck g) c)).comp
    (MonoidAlgebra.coeffLinearEquiv ℤ).toLinearMap

@[simp] theorem namedAttachingNerveMultiple_single (c : Ch (namedAttachingCover q ρ u))
    (g : NamedPolygonDeckGroup ρ q u) (n : ℤ) :
    namedAttachingNerveMultiple ρ q u c (MonoidAlgebra.single g n) =
      n • cmap (namedAttachingDeck ρ q u g) c := by
  unfold namedAttachingNerveMultiple
  simp only [LinearMap.comp_apply, LinearEquiv.coe_toLinearMap,
    MonoidAlgebra.coeffLinearEquiv_apply, MonoidAlgebra.coeff_single,
    Finsupp.linearCombination_single]

@[simp] theorem namedQuotientNerveMultiple_single
    (c : Ch (UOrder (namedQuotientPos ρ q u) (namedQuotientBase ρ q u)))
    (g : NamedPolygonDeckGroup ρ q u) (n : ℤ) :
    namedQuotientNerveMultiple ρ q u c (MonoidAlgebra.single g n) =
      n • cmap (uOrderDeck g) c := by
  unfold namedQuotientNerveMultiple
  simp only [LinearMap.comp_apply, LinearEquiv.coe_toLinearMap,
    MonoidAlgebra.coeffLinearEquiv_apply, MonoidAlgebra.coeff_single,
    Finsupp.linearCombination_single]

theorem namedAttachingNerveMultiple_mem_inc (c : Ch (namedAttachingCover q ρ u))
    (hc : c ∈ Inc _) (w : MonoidAlgebra ℤ (NamedPolygonDeckGroup ρ q u)) :
    namedAttachingNerveMultiple ρ q u c w ∈ Inc _ := by
  induction w using MonoidAlgebra.induction_linear with
  | zero => simp
  | add w z hw hz => simpa only [map_add] using AddSubgroup.add_mem _ hw hz
  | single g n =>
      rw [namedAttachingNerveMultiple_single]
      exact AddSubgroup.zsmul_mem _
        (cmap_mem_inc_of_monotone (namedAttachingDeck ρ q u g).monotone hc) n

theorem namedAttachingNerveMultiple_degree (c : Ch (namedAttachingCover q ρ u))
    (k : ℕ) (hc : lengthProjection k c = c)
    (w : MonoidAlgebra ℤ (NamedPolygonDeckGroup ρ q u)) :
    lengthProjection k (namedAttachingNerveMultiple ρ q u c w) =
      namedAttachingNerveMultiple ρ q u c w := by
  induction w using MonoidAlgebra.induction_linear with
  | zero => simp
  | add w z hw hz => simp only [map_add, MonoidAlgebra.coeff_add, hw, hz]
  | single g n =>
      simp only [namedAttachingNerveMultiple_single,
        map_zsmul, lengthProjection_cmap, hc]

theorem namedAttachingNerveSurfaceChain_multiple
    (c : Ch (namedAttachingCover q ρ u)) (hc : c ∈ Inc _)
    (hd : lengthProjection 3 c = c) (v : NamedPolygonPole ρ q u)
    (hv : namedAttachingNerveSurfaceChain ρ q u c = namedPolygonFillingAt ρ q u v)
    (w : MonoidAlgebra ℤ (NamedPolygonDeckGroup ρ q u)) :
    namedAttachingNerveSurfaceChain ρ q u (namedAttachingNerveMultiple ρ q u c w) =
      namedPolygonMultipleAt ρ q u v w := by
  induction w using MonoidAlgebra.induction_linear with
  | zero => simp
  | add w z hw hz => simp only [map_add, MonoidAlgebra.coeff_add, hw, hz]
  | single g n =>
      rw [namedAttachingNerveMultiple_single, map_zsmul,
        namedAttachingNerveSurfaceChain_deck ρ q u g c hc hd, hv,
        namedPolygonMultipleAt]
      let f := fun g => chain2
        (strictOrderCxMap (namedSurfaceDeck ρ q u g) (namedSurfaceDeck ρ q u g).strictMono)
        (namedPolygonFillingAt ρ q u v)
      change n • f g = Finsupp.linearCombination ℤ f (Finsupp.single g n)
      exact (Finsupp.linearCombination_single ℤ n g).symm


theorem namedQuotientNerveMultiple_add (c d)
    (w : MonoidAlgebra ℤ (NamedPolygonDeckGroup ρ q u)) :
    namedQuotientNerveMultiple ρ q u (c + d) w =
      namedQuotientNerveMultiple ρ q u c w + namedQuotientNerveMultiple ρ q u d w := by
  induction w using MonoidAlgebra.induction_linear with
  | zero => simp
  | add w z hw hz => simp only [map_add, MonoidAlgebra.coeff_add, hw, hz]; abel
  | single g n =>
      simp only [namedQuotientNerveMultiple_single,
        map_add, smul_add]

theorem namedQuotientNerveMultiple_bdry (c)
    (w : MonoidAlgebra ℤ (NamedPolygonDeckGroup ρ q u)) :
    namedQuotientNerveMultiple ρ q u (Nerve.bdry c) w =
      Nerve.bdry (namedQuotientNerveMultiple ρ q u c w) := by
  induction w using MonoidAlgebra.induction_linear with
  | zero => simp
  | add w z hw hz => simp only [map_add, MonoidAlgebra.coeff_add, hw, hz]
  | single g n =>
      simp only [namedQuotientNerveMultiple_single,
        map_zsmul, cmap_bdry]

theorem namedQuotientNerveMultiple_attaching (c : Ch (namedAttachingCover q ρ u))
    (w : MonoidAlgebra ℤ (NamedPolygonDeckGroup ρ q u)) :
    namedQuotientNerveMultiple ρ q u (cmap Subtype.val c) w =
      cmap Subtype.val (namedAttachingNerveMultiple ρ q u c w) := by
  induction w using MonoidAlgebra.induction_linear with
  | zero =>
      rw [map_zero, map_zero]
      exact (cmap Subtype.val).map_zero.symm
  | add w z hw hz => simp only [map_add, MonoidAlgebra.coeff_add, hw, hz]
  | single g n =>
      simp only [namedQuotientNerveMultiple_single, namedAttachingNerveMultiple_single,
        map_zsmul, cmap_comp]
      rfl

theorem namedQuotientNerveMultiple_old (c)
    (hc : c ∈ IncOn (fun p => InQOld (uOrderEnd p)))
    (w : MonoidAlgebra ℤ (NamedPolygonDeckGroup ρ q u)) :
    namedQuotientNerveMultiple ρ q u c w ∈ IncOn (fun p => InQOld (uOrderEnd p)) := by
  obtain ⟨d, hd, hdc⟩ := exists_preimage_of_mem_incOn
    (fun p : UOrder (namedQuotientPos ρ q u) (namedQuotientBase ρ q u) =>
      InQOld (uOrderEnd p)) hc
  induction w using MonoidAlgebra.induction_linear with
  | zero => simp
  | add w z hw hz => simpa only [map_add] using AddSubgroup.add_mem _ hw hz
  | single g n =>
      rw [namedQuotientNerveMultiple_single]
      apply AddSubgroup.zsmul_mem
      rw [← hdc, cmap_comp]
      exact cmap_mem_incOn_of_maps
        (f := fun p : {p : UOrder (namedQuotientPos ρ q u) (namedQuotientBase ρ q u) //
          InQOld (uOrderEnd p)} => uOrderDeck g p.1)
        ((uOrderDeckOrderIso g).monotone.comp (fun _ _ h => h))
        (fun p => by change InQOld (uOrderEnd (uOrderDeck g p.1)); rw [uOrderDeck_end]; exact p.2)
        hd

theorem namedQuotientNerveMultiple_universal1
    (c : (uCover (orderCx (namedQuotientPos ρ q u)) (namedQuotientBase ρ q u)).E →₀ ℤ)
    (w : MonoidAlgebra ℤ (NamedPolygonDeckGroup ρ q u)) :
    namedQuotientNerveMultiple ρ q u (universalNerveChain1 c) w =
      universalNerveChain1 (Finsupp.linearCombination ℤ (fun g => chain1
        ((univDeck (orderCx (namedQuotientPos ρ q u)) (namedQuotientBase ρ q u)).cellHom g)
          c) w.coeff) := by
  induction w using MonoidAlgebra.induction_linear with
  | zero => simp
  | add w z hw hz => simp only [map_add, MonoidAlgebra.coeff_add, hw, hz]
  | single g n =>
      rw [namedQuotientNerveMultiple_single,
        MonoidAlgebra.coeff_single, Finsupp.linearCombination_single, map_smul, universalNerveChain1_deck]

theorem namedQuotientNerveMultiple_universal2
    (c : (uCover (orderCx (namedQuotientPos ρ q u)) (namedQuotientBase ρ q u)).F →₀ ℤ)
    (w : MonoidAlgebra ℤ (NamedPolygonDeckGroup ρ q u)) :
    namedQuotientNerveMultiple ρ q u (universalNerveChain2 c) w =
      universalNerveChain2 (Finsupp.linearCombination ℤ (fun g =>
        (univDeck (orderCx (namedQuotientPos ρ q u)) (namedQuotientBase ρ q u)).faceChains g
          c) w.coeff) := by
  induction w using MonoidAlgebra.induction_linear with
  | zero => simp
  | add w z hw hz => simp only [map_add, MonoidAlgebra.coeff_add, hw, hz]
  | single g n =>
      rw [namedQuotientNerveMultiple_single,
        MonoidAlgebra.coeff_single, Finsupp.linearCombination_single, map_smul, universalNerveChain2_deck]

/-- The reverse subdivision comparison supplies the missing old three-chain.
The reference is required to be the actual degree-one polygon filling. -/
theorem namedAttaching_polygon_multiple_old_boundary
    (hrho : ρ (Sum.inr PUnit.unit) = commWord u (finitePairs q))
    (C D : Ch (UOrder (namedQuotientPos ρ q u) (namedQuotientBase ρ q u)))
    (c d : Ch (namedAttachingCover q ρ u))
    (hc : c ∈ Inc _) (hd : d ∈ Inc _)
    (hcdegree : lengthProjection 3 c = c) (hddegree : lengthProjection 3 d = d)
    (yC yD : Ch (UOrder (namedQuotientPos ρ q u) (namedQuotientBase ρ q u)))
    (hyC : yC ∈ IncOn (fun p => InQOld (uOrderEnd p)))
    (hyD : yD ∈ IncOn (fun p => InQOld (uOrderEnd p)))
    (hC : C = cmap Subtype.val c + Nerve.bdry yC)
    (hD : D = cmap Subtype.val d + Nerve.bdry yD)
    (v : NamedPolygonPole ρ q u)
    (hreference : namedAttachingNerveSurfaceChain ρ q u d = namedPolygonFillingAt ρ q u v)
    (w : MonoidAlgebra ℤ (NamedPolygonDeckGroup ρ q u))
    (hpolygon : namedAttachingNerveSurfaceChain ρ q u c = namedPolygonMultipleAt ρ q u v w)
    (hboundary : Nerve.bdry C = namedQuotientNerveMultiple ρ q u (Nerve.bdry D) w) :
    ∃ y ∈ IncOn (fun p => InQOld (uOrderEnd p)),
      Nerve.bdry y = C - namedQuotientNerveMultiple ρ q u D w := by
  let dw := namedAttachingNerveMultiple ρ q u d w
  have hdw : dw ∈ Inc _ := namedAttachingNerveMultiple_mem_inc ρ q u d hd w
  have hdwdegree : lengthProjection 3 dw = dw :=
    namedAttachingNerveMultiple_degree ρ q u d 3 hddegree w
  have hD' : namedQuotientNerveMultiple ρ q u D w =
      cmap Subtype.val dw + Nerve.bdry (namedQuotientNerveMultiple ρ q u yD w) := by
    rw [hD, namedQuotientNerveMultiple_add, namedQuotientNerveMultiple_attaching,
      namedQuotientNerveMultiple_bdry]
  have hb : Nerve.bdry c = Nerve.bdry dw := by
    apply cmap_val_injective _
      ⟨(namedAttachingReference q ρ u hrho 1).1, (namedAttachingReference q ρ u hrho 1).2⟩
    have h := hboundary
    rw [namedQuotientNerveMultiple_bdry, hC, hD', map_add, map_add,
      Nerve.bdry_bdry, Nerve.bdry_bdry, add_zero, add_zero, ← cmap_bdry, ← cmap_bdry] at h
    exact h
  have himage : namedAttachingNerveSurfaceChain ρ q u c =
      namedAttachingNerveSurfaceChain ρ q u dw := by
    rw [hpolygon, namedAttachingNerveSurfaceChain_multiple ρ q u d hd hddegree v hreference w]
  obtain ⟨b, hbi, _, hbcd⟩ := attachingSurface_nerve_relative_comparison
    (namedSurfaceLabel ρ q u) (namedQuotientBase ρ q u)
    (namedQuotientPos_isConnected ρ q u) c dw hc hdw hcdegree hdwdegree hb himage
  have hbOld : cmap (Subtype.val : namedAttachingCover q ρ u → _) b ∈
      IncOn (fun p => InQOld (uOrderEnd p)) :=
    cmap_mem_incOn_of_maps
      (f := (Subtype.val : namedAttachingCover q ρ u →
        UOrder (namedQuotientPos ρ q u) (namedQuotientBase ρ q u)))
      (fun _ _ h => h) (fun p => p.2.1) hbi
  refine ⟨(cmap Subtype.val b :
      Ch (UOrder (namedQuotientPos ρ q u) (namedQuotientBase ρ q u))) +
      yC - namedQuotientNerveMultiple ρ q u yD w,
    AddSubgroup.sub_mem _ (AddSubgroup.add_mem _ hbOld hyC)
      (namedQuotientNerveMultiple_old ρ q u yD hyD w), ?_⟩
  rw [map_sub, map_add, ← cmap_bdry, ← hbcd, map_sub, hC, hD']
  let inc : namedAttachingCover q ρ u →
      UOrder (namedQuotientPos ρ q u) (namedQuotientBase ρ q u) := Subtype.val
  change (cmap inc c - cmap inc dw) + Nerve.bdry yC -
      Nerve.bdry (namedQuotientNerveMultiple ρ q u yD w) =
    (cmap inc c + Nerve.bdry yC) -
      (cmap inc dw + Nerve.bdry (namedQuotientNerveMultiple ρ q u yD w))
  abel

/-- The geometric comparison feeds the full coefficient-rigidity theorem.
Its scalar is the actual polygon coefficient at the specified reference pole. -/
theorem finiteSpine_polygon_reference_principal
    (hrho : ρ (Sum.inr PUnit.unit) = commWord u (finitePairs q))
    (β γ : NamedSpineRel q → MonoidAlgebra ℤ
      (PresGroup (substPresF ρ (finiteSpineWordBlock q u))))
    (hβ : ∀ z : SpinePresentationGen q,
      (∑ m, β m * foxMatrixPres (substPresF ρ (finiteSpineWordBlock q u))
        (Sum.inr ⟨PUnit.unit, z⟩) (Sum.inr ⟨PUnit.unit, m⟩)) = 0)
    (hγ : ∀ z : SpinePresentationGen q,
      (∑ m, γ m * foxMatrixPres (substPresF ρ (finiteSpineWordBlock q u))
        (Sum.inr ⟨PUnit.unit, z⟩) (Sum.inr ⟨PUnit.unit, m⟩)) = 0)
    (c d : Ch (namedAttachingCover q ρ u))
    (hc : c ∈ Inc _) (hd : d ∈ Inc _)
    (hcdegree : lengthProjection 3 c = c) (hddegree : lengthProjection 3 d = d)
    (yC yD : Ch (UOrder (namedQuotientPos ρ q u) (namedQuotientBase ρ q u)))
    (hyC : yC ∈ IncOn (fun p => InQOld (uOrderEnd p)))
    (hyD : yD ∈ IncOn (fun p => InQOld (uOrderEnd p)))
    (hC : quotientCorrectedRelativeNerveChain q ρ u hrho β =
      cmap Subtype.val c + Nerve.bdry yC)
    (hD : quotientCorrectedRelativeNerveChain q ρ u hrho γ =
      cmap Subtype.val d + Nerve.bdry yD)
    (v : NamedPolygonPole ρ q u)
    (hreference : namedAttachingNerveSurfaceChain ρ q u d = namedPolygonFillingAt ρ q u v)
    (hrelative : PolygonRelativeChain (gc q) (namedSurfaceProjection ρ q u)
      (namedAttachingNerveSurfaceChain ρ q u c))
    (hmark : quotientSurfaceMarkingChains q ρ u hrho
        ((ReceivedTree.cellCoordinates (Fin q × Bool)).symm (fun i => β (Sum.inr i))) =
      Finsupp.linearCombination ℤ (fun g => chain1
        ((univDeck (orderCx (namedQuotientPos ρ q u)) (namedQuotientBase ρ q u)).cellHom g)
        (quotientSurfaceMarkingChains q ρ u hrho
          ((ReceivedTree.cellCoordinates (Fin q × Bool)).symm (fun i => γ (Sum.inr i)))))
        (namedPolygonCoefficientAt ρ q u v (namedAttachingNerveSurfaceChain ρ q u c)).coeff) :
    ∃ a : MonoidAlgebra ℤ (PresGroup (substPresF ρ (finiteSpineWordBlock q u))),
      ∀ m, β m = a * γ m := by
  let w := namedPolygonCoefficientAt ρ q u v (namedAttachingNerveSurfaceChain ρ q u c)
  have hpolygon : namedAttachingNerveSurfaceChain ρ q u c =
      namedPolygonMultipleAt ρ q u v w :=
    namedPolygon_reconstruct_at_pole ρ q u v _ hrelative
  have hboundary : Nerve.bdry (quotientCorrectedRelativeNerveChain q ρ u hrho β) =
      namedQuotientNerveMultiple ρ q u
        (Nerve.bdry (quotientCorrectedRelativeNerveChain q ρ u hrho γ)) w := by
    rw [quotientCorrectedRelativeNerveChain_boundary q ρ u hrho β hβ,
      quotientCorrectedRelativeNerveChain_boundary q ρ u hrho γ hγ,
      namedQuotientNerveMultiple_universal1, hmark]
  obtain ⟨y, hy, hdy⟩ := namedAttaching_polygon_multiple_old_boundary ρ q u hrho
    (quotientCorrectedRelativeNerveChain q ρ u hrho β)
    (quotientCorrectedRelativeNerveChain q ρ u hrho γ)
    c d hc hd hcdegree hddegree yC yD hyC hyD hC hD v hreference w hpolygon hboundary
  apply finiteSpine_relative_class_principal q ρ u hrho β γ hβ hγ w hmark
  refine ⟨y, hy, ?_⟩
  rw [hdy, quotientCorrectedRelativeNerveChain, quotientCorrectedRelativeNerveChain,
    namedQuotientNerveMultiple_universal2, map_sub]

end FiniteChains.Davis.Genus
