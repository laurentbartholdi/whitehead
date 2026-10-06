module

public import RequestProject.AttachmentHomotopyExtension
public import Mathlib.Topology.Homotopy.Equiv

@[expose] public section

/-! Actual maps under change of the base of a cell attachment. The first
homotopy inverse is constructed from disk homotopy extension. This file does
not assume that the induced map on attachments is an equivalence. -/

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains.RelativeAttachment
open scoped unitInterval Topology Classical

universe u
variable {A D P K Z : Type u}
variable [TopologicalSpace A] [TopologicalSpace D] [TopologicalSpace P]
variable [TopologicalSpace K] [TopologicalSpace Z]

def attachmentBaseMap (a : A → P) (i : A → D) (hi : Function.Injective i)
    (e : C(P, K)) : C(Space a i, Space (e ∘ a) i) :=
  desc a i ((⟨old (e ∘ a) i, old_continuous (e ∘ a) i⟩ : C(K, Space (e ∘ a) i)).comp e)
    ⟨cell (e ∘ a) i, cell_continuous (e ∘ a) i⟩
    (fun b => (cell_boundary (e ∘ a) i hi b).symm)

omit [TopologicalSpace A] in
@[simp] theorem attachmentBaseMap_old (a : A → P) (i : A → D)
    (hi : Function.Injective i) (e : C(P, K)) (p : P) :
    attachmentBaseMap a i hi e (old a i p) = old (e ∘ a) i (e p) := rfl

omit [TopologicalSpace A] in
@[simp] theorem attachmentBaseMap_cell (a : A → P) (i : A → D)
    (hi : Function.Injective i) (e : C(P, K)) (d : D) :
    attachmentBaseMap a i hi e (cell a i d) = cell (e ∘ a) i d := by
  unfold attachmentBaseMap
  rw [desc_cell]
  rfl

omit [TopologicalSpace A] in
theorem attachmentBaseMap_comp {Q : Type u} [TopologicalSpace Q]
    (a : A → P) (i : A → D) (hi : Function.Injective i)
    (e : C(P, K)) (g : C(K, Q)) :
    (attachmentBaseMap (e ∘ a) i hi g).comp (attachmentBaseMap a i hi e) =
      attachmentBaseMap a i hi (g.comp e) := by
  apply hom_ext a i
  · intro p
    rfl
  · intro d
    simp only [ContinuousMap.comp_apply, attachmentBaseMap_cell]
    exact (attachmentBaseMap_cell a i hi (g.comp e) d).symm

/-- A jointly continuous pasting on the attachment. The target is curried
in the compact time coordinate, so the base need not be locally compact. -/
def attachmentHomotopyPasting (a : A → P) (i : A → D)
    (H : C(I × P, Z)) (G : C(I × D, Z))
    (h : ∀ t b, H (t, a b) = G (t, i b)) : C(I × Space a i, Z) :=
  (desc a i ((H.comp ⟨Prod.swap, continuous_swap⟩).curry)
    ((G.comp ⟨Prod.swap, continuous_swap⟩).curry)
    (fun b => ContinuousMap.ext (fun t => h t b))).uncurry.comp
      ⟨Prod.swap, continuous_swap⟩

omit [TopologicalSpace A] in
@[simp] theorem attachmentHomotopyPasting_old (a : A → P) (i : A → D)
    (H : C(I × P, Z)) (G : C(I × D, Z))
    (h : ∀ t b, H (t, a b) = G (t, i b)) (t : I) (p : P) :
    attachmentHomotopyPasting a i H G h (t, old a i p) = H (t, p) := rfl

omit [TopologicalSpace A] in
@[simp] theorem attachmentHomotopyPasting_cell (a : A → P) (i : A → D)
    (H : C(I × P, Z)) (G : C(I × D, Z))
    (h : ∀ t b, H (t, a b) = G (t, i b)) (t : I) (d : D) :
    attachmentHomotopyPasting a i H G h (t, cell a i d) = G (t, d) := by
  dsimp only [attachmentHomotopyPasting, ContinuousMap.comp_apply,
    ContinuousMap.uncurry_apply, ContinuousMap.coe_mk, Function.uncurry, Prod.swap]
  change desc (Z := C(I, Z)) a i _ _ _ (cell a i d) t = _
  rw [desc_cell]
  rfl

/-- A homotopy left inverse on the base extends to a homotopy left inverse
of the actual map of attachments. The extension supplies its disk maps. -/
theorem attachmentBaseMap_leftInverse (a : A → P) (i : A → D)
    (ha : Continuous a) (hi : Function.Injective i) (hext : HasHomotopyExtension i)
    (e : C(P, K)) (g : C(K, P))
    (h : (g.comp e).Homotopic (ContinuousMap.id P)) :
    ∃ G : C(Space (e ∘ a) i, Space a i),
      (G.comp (attachmentBaseMap a i hi e)).Homotopic (ContinuousMap.id (Space a i)) ∧
      ∀ k, G (old (e ∘ a) i k) = old a i (g k) := by
  obtain ⟨H⟩ := h.symm
  let HB : C(I × P, Space a i) :=
    ⟨fun tp => old a i (H tp), (old_continuous a i).comp H.continuous⟩
  have hB₀ : ∀ p, HB (0, p) = (ContinuousMap.id (Space a i)) (old a i p) := by
    intro p
    exact congrArg (old a i) (H.apply_zero p)
  obtain ⟨L, hL₀, hLP⟩ := old_hasHomotopyExtension a i ha hi hext
    (Space a i) (ContinuousMap.id (Space a i)) HB hB₀
  let L₁ : C(Space a i, Space a i) := L.comp
    ⟨fun z => (1, z), continuous_const.prodMk continuous_id⟩
  let G₀ : C(K, Space a i) := (⟨old a i, old_continuous a i⟩ : C(P, Space a i)).comp g
  let G₂ : C(D, Space a i) := L₁.comp ⟨cell a i, cell_continuous a i⟩
  have hG : ∀ b, G₀ ((e ∘ a) b) = G₂ (i b) := by
    intro b
    change old a i (g (e (a b))) = L (1, cell a i (i b))
    rw [cell_boundary a i hi, hLP]
    exact (congrArg (old a i) (H.apply_one (a b))).symm
  let G : C(Space (e ∘ a) i, Space a i) := desc (e ∘ a) i G₀ G₂ hG
  have hend : L₁ = G.comp (attachmentBaseMap a i hi e) := by
    apply hom_ext a i
    · intro p
      change L (1, old a i p) = G (old (e ∘ a) i (e p))
      rw [hLP, desc_old]
      exact congrArg (old a i) (H.apply_one p)
    · intro d
      change L (1, cell a i d) = G (attachmentBaseMap a i hi e (cell a i d))
      rw [attachmentBaseMap_cell, desc_cell]
      rfl
  have HL : ContinuousMap.Homotopy (ContinuousMap.id (Space a i)) L₁ := {
    toContinuousMap := L
    map_zero_left := hL₀
    map_one_left := fun _ => rfl }
  refine ⟨G, ?_, fun _ => rfl⟩
  rw [← hend]
  exact ⟨HL.symm⟩

end FiniteChains.RelativeAttachment
