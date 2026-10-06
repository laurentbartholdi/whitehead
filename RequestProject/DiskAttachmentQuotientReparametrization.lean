module

public import RequestProject.AttachmentQuotientHomeomorph
public import RequestProject.ClassicalCellAttachmentMaps

@[expose] public section

/-! A closed-disk quotient which preserves the interior bijectively may
replace the characteristic parametrization of an attached cell. Boundary
arcs may collapse: they were already attached to the old space. This
constructs an actual homeomorphism, also for infinite cell families.
 -/

noncomputable section
open scoped Classical
namespace FiniteChains.RelativeAttachment
open Topology

variable {J K X E : Type} [TopologicalSpace X]
  [NormedAddCommGroup E]
  (r : BoundaryFamily K E → X) (e : J ≃ K)
  (q : ∀ _ : J, C(ClosedUnitBall E, ClosedUnitBall E))
  (b : ∀ _ : J, C(UnitBoundary E, UnitBoundary E))
  (hb : ∀ j z, q j (unitBoundaryInclusion E z) = unitBoundaryInclusion E (b j z))
  (hq : ∀ j, IsQuotientMap (q j))
  (hint : ∀ j x, ‖(q j x).val‖ < 1 ↔ ‖x.val‖ < 1)
  (hinj : ∀ j, Set.InjOn (q j) {x | ‖x.val‖ < 1})

def reparametrizedAttaching (a : BoundaryFamily J E) : X :=
  r ⟨e a.1, b a.1 a.2⟩

def reparametrizedDiskFamily : C(DiskFamily J E, DiskFamily K E) where
  toFun d := ⟨e d.1, q d.1 d.2⟩
  continuous_toFun := continuous_sigma (fun j =>
    (show Continuous (Sigma.mk (β := fun _ : K => ClosedUnitBall E) (e j)) from
      continuous_sigmaMk).comp (q j).continuous)

include hint in
theorem reparametrizedDiskFamily_boundary_iff (d : DiskFamily J E) :
    reparametrizedDiskFamily e q d ∈ Set.range (boundaryFamilyInclusion K E) ↔
      d ∈ Set.range (boundaryFamilyInclusion J E) := by
  rw [boundaryFamilyInclusion_range, boundaryFamilyInclusion_range]
  change ‖(q d.1 d.2).val‖ = 1 ↔ ‖d.2.val‖ = 1
  have h := hint d.1 d.2
  have ha := (q d.1 d.2).property
  have hc := d.2.property
  constructor <;> intro he
  · by_contra hn
    have hl : ‖d.2.val‖ < 1 := lt_of_le_of_ne hc hn
    have := h.mpr hl
    linarith
  · by_contra hn
    have hl : ‖(q d.1 d.2).val‖ < 1 := lt_of_le_of_ne ha hn
    have := h.mp hl
    linarith

include hinj in
theorem reparametrizedDiskFamily_injective_interior
    (d d' : DiskFamily J E)
    (hd : d ∉ Set.range (boundaryFamilyInclusion J E))
    (hd' : d' ∉ Set.range (boundaryFamilyInclusion J E))
    (he : reparametrizedDiskFamily e q d = reparametrizedDiskFamily e q d') : d = d' := by
  rcases d with ⟨j, x⟩
  rcases d' with ⟨k, y⟩
  have hjk : j = k := e.injective (congrArg Sigma.fst he)
  subst k
  have hxy : q j x = q j y := eq_of_heq (Sigma.mk.inj_iff.mp he).2
  have hx : ‖x.val‖ < 1 := lt_of_le_of_ne x.property
    (fun h => hd ((boundaryFamilyInclusion_range J E _).mpr h))
  have hy : ‖y.val‖ < 1 := lt_of_le_of_ne y.property
    (fun h => hd' ((boundaryFamilyInclusion_range J E _).mpr h))
  exact congrArg (Sigma.mk (β := fun _ : J => ClosedUnitBall E) j) (hinj j hx hy hxy)

include hq in
theorem reparametrizedDiskFamily_isQuotientMap :
    IsQuotientMap (reparametrizedDiskFamily e q) := by
  apply isQuotientMap_iff_isClosed.mpr
  constructor
  · rintro ⟨k, y⟩
    obtain ⟨j, rfl⟩ := e.surjective k
    obtain ⟨x, rfl⟩ := (hq j).surjective y
    exact ⟨⟨j, x⟩, rfl⟩
  · intro S
    constructor
    · intro hS
      exact hS.preimage (reparametrizedDiskFamily e q).continuous
    · intro hS
      apply isClosed_sigma_iff.mpr
      intro k
      obtain ⟨j, rfl⟩ := e.surjective k
      apply (hq j).isClosed_preimage.mp
      exact (isClosed_sigma_iff.mp hS) j

def reparametrizedOldAndDisks : X ⊕ DiskFamily J E → X ⊕ DiskFamily K E :=
  Sum.map id (reparametrizedDiskFamily e q)

include hq in
theorem reparametrizedOldAndDisks_isQuotientMap :
    IsQuotientMap (reparametrizedOldAndDisks (X := X) e q) := by
  have hQ := reparametrizedDiskFamily_isQuotientMap e q hq
  apply isQuotientMap_iff_isClosed.mpr
  constructor
  · rintro (x | d)
    · exact ⟨Sum.inl x, rfl⟩
    · obtain ⟨d', rfl⟩ := hQ.surjective d
      exact ⟨Sum.inr d', rfl⟩
  · intro S
    rw [isClosed_sum_iff, isClosed_sum_iff]
    change (IsClosed (Sum.inl ⁻¹' S) ∧ IsClosed (Sum.inr ⁻¹' S)) ↔
      (IsClosed (Sum.inl ⁻¹' S) ∧
        IsClosed ((reparametrizedDiskFamily e q) ⁻¹' (Sum.inr ⁻¹' S)))
    exact and_congr Iff.rfl hQ.isClosed_preimage.symm

def reparametrizedDiskEvaluation : C(DiskFamily J E, DiskAttachment r) :=
  (⟨cell r (boundaryFamilyInclusion K E), cell_continuous r _⟩ :
    C(DiskFamily K E, DiskAttachment r)).comp
    (reparametrizedDiskFamily e q)

include hint in
theorem reparametrizedDiskEvaluation_separation (d : DiskFamily J E) :
    reparametrizedDiskEvaluation r e q d ∈ Set.range (old r (boundaryFamilyInclusion K E)) ↔
      d ∈ Set.range (boundaryFamilyInclusion J E) := by
  rw [← reparametrizedDiskFamily_boundary_iff e q hint d]
  let d' := reparametrizedDiskFamily e q d
  change cell r (boundaryFamilyInclusion K E) d' ∈ Set.range (old r _) ↔
    d' ∈ Set.range (boundaryFamilyInclusion K E)
  constructor
  · rintro ⟨x, hx⟩
    by_contra hd
    rw [cell_of_not_mem r _ d' hd] at hx
    exact Sum.inl_ne_inr hx
  · rintro ⟨a, ha⟩
    rw [← ha]
    exact ⟨r a, (cell_boundary r _
      (boundaryFamilyInclusion_isClosedEmbedding K E).injective a).symm⟩

def diskAttachmentQuotientReparametrization :
    DiskAttachment (reparametrizedAttaching r e b) ≃ₜ DiskAttachment r := by
  let f : C(X, DiskAttachment r) := ⟨old r (boundaryFamilyInclusion K E), old_continuous r _⟩
  let g := reparametrizedDiskEvaluation r e q
  have hbd : ∀ a, f (reparametrizedAttaching r e b a) =
      g (boundaryFamilyInclusion J E a) := by
    rintro ⟨j, z⟩
    change old r (boundaryFamilyInclusion K E) (r ⟨e j, b j z⟩) =
      cell r (boundaryFamilyInclusion K E) ⟨e j, q j (unitBoundaryInclusion E z)⟩
    rw [hb]
    exact (cell_boundary r _ (boundaryFamilyInclusion_isClosedEmbedding K E).injective
      ⟨e j, b j z⟩).symm
  have hnew : ∀ d d', d ∉ Set.range (boundaryFamilyInclusion J E) →
      d' ∉ Set.range (boundaryFamilyInclusion J E) → g d = g d' → d = d' := by
    intro d d' hd hd' he
    have hdq : reparametrizedDiskFamily e q d ∉ Set.range (boundaryFamilyInclusion K E) :=
      fun h => hd ((reparametrizedDiskFamily_boundary_iff e q hint d).mp h)
    have hdq' : reparametrizedDiskFamily e q d' ∉ Set.range (boundaryFamilyInclusion K E) :=
      fun h => hd' ((reparametrizedDiskFamily_boundary_iff e q hint d').mp h)
    change cell r _ (reparametrizedDiskFamily e q d) =
      cell r _ (reparametrizedDiskFamily e q d') at he
    rw [cell_of_not_mem r _ _ hdq, cell_of_not_mem r _ _ hdq'] at he
    exact reparametrizedDiskFamily_injective_interior e q hinj d d' hd hd'
      (congrArg Subtype.val (Sum.inr.inj he))
  have hq₀ : IsQuotientMap (quotientMap r (boundaryFamilyInclusion K E)) :=
    ⟨⟨rfl⟩, quotientMap_surjective r _⟩
  have hcomp : quotientMap r (boundaryFamilyInclusion K E) ∘
      reparametrizedOldAndDisks (X := X) e q = Sum.elim f g := by
    funext x
    cases x <;> rfl
  have hq' : IsQuotientMap (Sum.elim f g) := by
    rw [← hcomp]
    exact hq₀.comp (reparametrizedOldAndDisks_isQuotientMap (X := X) e q hq)
  exact attachmentQuotientHomeomorph (reparametrizedAttaching r e b)
    (boundaryFamilyInclusion J E) f g hbd (old_injective r _)
    (reparametrizedDiskEvaluation_separation r e q hint) hnew hq'

@[simp] theorem diskAttachmentQuotientReparametrization_old (x : X) :
    diskAttachmentQuotientReparametrization r e q b hb hq hint hinj
      (old (reparametrizedAttaching r e b) (boundaryFamilyInclusion J E) x) =
        old r (boundaryFamilyInclusion K E) x := rfl

@[simp] theorem diskAttachmentQuotientReparametrization_cell (d : DiskFamily J E) :
    diskAttachmentQuotientReparametrization r e q b hb hq hint hinj
      (cell (reparametrizedAttaching r e b) (boundaryFamilyInclusion J E) d) =
        cell r (boundaryFamilyInclusion K E) (reparametrizedDiskFamily e q d) := by
  unfold diskAttachmentQuotientReparametrization
  exact attachmentQuotientHomeomorph_cell ..

end FiniteChains.RelativeAttachment
