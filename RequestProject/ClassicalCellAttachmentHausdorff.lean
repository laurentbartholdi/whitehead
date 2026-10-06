module

public import RequestProject.ClassicalCellAttachmentMaps
public import Mathlib.Topology.Separation.Hausdorff

@[expose] public section

/-! Explicit Hausdorff separation for arbitrary families of attached normed
disks. Old open sets extend through radial annuli; there is no local finiteness
assumption on the cell family. Pending Lean verification. -/

noncomputable section
open scoped Classical
open Set Topology

namespace FiniteChains.RelativeAttachment

universe u
variable {J E X : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace X]

def annulusBoundary (c : ℝ) (hc : 0 ≤ c)
    (x : {x : ClosedUnitBall E // c < ‖x.val‖}) : UnitBoundary E :=
  ⟨‖x.val.val‖⁻¹ • x.val.val, by
    have hx : ‖x.val.val‖ ≠ 0 := ne_of_gt (lt_of_le_of_lt hc x.property)
    rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hx]⟩

theorem annulusBoundary_continuous (c : ℝ) (hc : 0 ≤ c) :
    Continuous (annulusBoundary (E := E) c hc) := by
  apply Continuous.subtype_mk
  apply Continuous.smul
  · exact (continuous_norm.comp
      (continuous_subtype_val.comp continuous_subtype_val)).inv₀
        (fun x => ne_of_gt (lt_of_le_of_lt hc x.property))
  · exact continuous_subtype_val.comp continuous_subtype_val

theorem annulusBoundary_boundary (c : ℝ) (hc : 0 ≤ c) (hcone : c < 1)
    (x : UnitBoundary E) :
    annulusBoundary c hc ⟨unitBoundaryInclusion E x, by
      change c < ‖x.val‖
      simpa only [x.property] using hcone⟩ =
      x := by
  apply Subtype.ext
  change ‖x.val‖⁻¹ • x.val = x.val
  rw [x.property, inv_one, one_smul]

/-- An open set of the old space together with its radial collar of width
`1-c` in every attached disk. -/
def oldCollar (r : BoundaryFamily J E → X) (c : ℝ) (hc : 0 ≤ c) (U : Set X) :
    Set (DiskAttachment r) :=
  fun z => match z with
    | Sum.inl x => x ∈ U
    | Sum.inr d => ∃ h : c < ‖d.val.2.val‖,
        r ⟨d.val.1, annulusBoundary c hc ⟨d.val.2, h⟩⟩ ∈ U

omit [TopologicalSpace X] in
@[simp] theorem old_mem_oldCollar (r : BoundaryFamily J E → X)
    (c : ℝ) (hc : 0 ≤ c) (U : Set X) (x : X) :
    old r (boundaryFamilyInclusion J E) x ∈ oldCollar r c hc U ↔ x ∈ U := Iff.rfl

omit [TopologicalSpace X] in
theorem cell_mem_oldCollar (r : BoundaryFamily J E → X)
    (c : ℝ) (hc : 0 ≤ c) (hcone : c < 1) (U : Set X)
    (j : J) (x : ClosedUnitBall E) :
    cell r (boundaryFamilyInclusion J E) ⟨j, x⟩ ∈ oldCollar r c hc U ↔
      ∃ h : c < ‖x.val‖, r ⟨j, annulusBoundary c hc ⟨x, h⟩⟩ ∈ U := by
  by_cases hx : ‖x.val‖ = 1
  · let a : UnitBoundary E := ⟨x.val, hx⟩
    have hx' : c < ‖x.val‖ := by simpa only [hx] using hcone
    have hb : cell r (boundaryFamilyInclusion J E) ⟨j, x⟩ =
        old r (boundaryFamilyInclusion J E) (r ⟨j, a⟩) :=
      cell_boundary r _ (boundaryFamilyInclusion_isClosedEmbedding J E).injective ⟨j, a⟩
    rw [hb, old_mem_oldCollar]
    have he (h : c < ‖x.val‖) : annulusBoundary c hc ⟨x, h⟩ = a := by
      apply Subtype.ext
      simp only [annulusBoundary, hx, inv_one, one_smul, a]
    constructor
    · intro ha
      exact ⟨hx', by simpa only [he hx'] using ha⟩
    · rintro ⟨h, ha⟩
      simpa only [he h] using ha
  · have hx' : (⟨j, x⟩ : DiskFamily J E) ∉ Set.range (boundaryFamilyInclusion J E) :=
      fun h => hx ((boundaryFamilyInclusion_range J E _).mp h)
    rw [cell_of_not_mem r _ _ hx']
    rfl

theorem oldCollar_isOpen (r : BoundaryFamily J E → X) (hr : Continuous r)
    (c : ℝ) (hc : 0 ≤ c) (hcone : c < 1) (U : Set X) (hU : IsOpen U) :
    IsOpen (oldCollar r c hc U) := by
  apply isOpen_coinduced.mpr
  apply isOpen_sum_iff.mpr
  refine ⟨hU, ?_⟩
  apply isOpen_sigma_iff.mpr
  intro j
  let A : Set (ClosedUnitBall E) := {x | c < ‖x.val‖}
  have hA : IsOpen A := isOpen_lt continuous_const (continuous_norm.comp continuous_subtype_val)
  have he : (fun x : ClosedUnitBall E => cell r (boundaryFamilyInclusion J E) ⟨j, x⟩) ⁻¹'
      oldCollar r c hc U =
      Subtype.val '' ((fun x : A => r ⟨j, annulusBoundary c hc x⟩) ⁻¹' U) := by
    ext x
    rw [Set.mem_preimage, cell_mem_oldCollar r c hc hcone U j x]
    constructor
    · rintro ⟨h, hh⟩
      exact ⟨⟨x, h⟩, hh, rfl⟩
    · rintro ⟨x', hx', rfl⟩
      exact ⟨x'.property, hx'⟩
  change IsOpen ((fun x : ClosedUnitBall E => cell r (boundaryFamilyInclusion J E) ⟨j, x⟩) ⁻¹'
    oldCollar r c hc U)
  rw [he]
  apply hA.isOpenEmbedding_subtypeVal.isOpenMap
  exact hU.preimage (hr.comp (continuous_sigmaMk.comp (annulusBoundary_continuous c hc)))

omit [TopologicalSpace X] in
theorem oldCollar_disjoint (r : BoundaryFamily J E → X) (c : ℝ) (hc : 0 ≤ c)
    {U V : Set X} (hUV : Disjoint U V) :
    Disjoint (oldCollar r c hc U) (oldCollar r c hc V) := by
  apply Set.disjoint_left.mpr
  rintro (x | d) hx hy
  · exact Set.disjoint_left.mp hUV hx hy
  · obtain ⟨h, hh⟩ := hx
    obtain ⟨h', hh'⟩ := hy
    exact Set.disjoint_left.mp hUV hh hh'

theorem separate_old_fresh (r : BoundaryFamily J E → X) (hr : Continuous r)
    (x : X) (d : {d : DiskFamily J E // d ∉ Set.range (boundaryFamilyInclusion J E)}) :
    ∃ U V : Set (DiskAttachment r), IsOpen U ∧ IsOpen V ∧
      old r (boundaryFamilyInclusion J E) x ∈ U ∧
      fresh r (boundaryFamilyInclusion J E) d ∈ V ∧ Disjoint U V := by
  have hdlt : ‖d.val.2.val‖ < 1 :=
    lt_of_le_of_ne d.val.2.property
      (fun h => d.property ((boundaryFamilyInclusion_range J E _).mpr h))
  let c : ℝ := (‖d.val.2.val‖ + 1) / 2
  have hc : 0 ≤ c := by dsimp [c]; positivity
  have hcone : c < 1 := by dsimp [c]; linarith
  have hdc : ‖d.val.2.val‖ < c := by dsimp [c]; linarith
  let V : Set {d : DiskFamily J E // d ∉ Set.range (boundaryFamilyInclusion J E)} :=
    {d | ‖d.val.2.val‖ < c}
  have hV : IsOpen V := by
    have hn : Continuous (fun d : DiskFamily J E => ‖d.2.val‖) := by
      apply continuous_sigma
      intro j
      exact continuous_norm.comp continuous_subtype_val
    exact isOpen_lt (hn.comp continuous_subtype_val) continuous_const
  refine ⟨oldCollar r c hc Set.univ,
    fresh r (boundaryFamilyInclusion J E) '' V,
    oldCollar_isOpen r hr c hc hcone Set.univ isOpen_univ,
    (fresh_isOpenEmbedding r _
      (boundaryFamilyInclusion_isClosedEmbedding J E).isClosed_range).isOpenMap _ hV,
    trivial, ⟨d, hdc, rfl⟩, ?_⟩
  apply Set.disjoint_left.mpr
  rintro _ hU ⟨d', hd', rfl⟩
  obtain ⟨h, _⟩ := hU
  exact (not_lt_of_ge h.le) hd'

/-- Adjoining any family of genuine normed disks to a Hausdorff space along
continuous boundary maps preserves Hausdorffness. -/
theorem diskAttachment_t2Space [T2Space X]
    (r : BoundaryFamily J E → X) (hr : Continuous r) : T2Space (DiskAttachment r) where
  t2 := by
    rintro (x | d) (y | e) hne
    · have hxy : x ≠ y := fun h => hne (congrArg Sum.inl h)
      obtain ⟨U, V, hU, hV, hx, hy, hUV⟩ := t2_separation hxy
      exact ⟨oldCollar r 0 le_rfl U, oldCollar r 0 le_rfl V,
        oldCollar_isOpen r hr 0 le_rfl zero_lt_one U hU,
        oldCollar_isOpen r hr 0 le_rfl zero_lt_one V hV,
        hx, hy, oldCollar_disjoint r 0 le_rfl hUV⟩
    · exact separate_old_fresh r hr x e
    · obtain ⟨U, V, hU, hV, hx, hy, hUV⟩ := separate_old_fresh r hr y d
      exact ⟨V, U, hV, hU, hy, hx, hUV.symm⟩
    · have hde : d ≠ e := fun h => hne (congrArg Sum.inr h)
      obtain ⟨U, V, hU, hV, hd, he, hUV⟩ := t2_separation hde
      have hf := fresh_isOpenEmbedding r (boundaryFamilyInclusion J E)
        (boundaryFamilyInclusion_isClosedEmbedding J E).isClosed_range
      refine ⟨fresh r _ '' U, fresh r _ '' V, hf.isOpenMap _ hU, hf.isOpenMap _ hV,
        ⟨d, hd, rfl⟩, ⟨e, he, rfl⟩, ?_⟩
      apply Set.disjoint_left.mpr
      rintro _ ⟨d', hd', rfl⟩ ⟨e', he', heq⟩
      have heq' := hf.injective heq
      subst e'
      exact Set.disjoint_left.mp hUV hd' he'

end FiniteChains.RelativeAttachment
