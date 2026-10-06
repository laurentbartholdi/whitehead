import RequestProject.Pi2ExtensionInjective

/-!
# The extension steps of rule 1 preserve the Cockcroft property

Lemma 3.9 concludes, from the generation statement (3.3), that the operation `T` preserves
Cockcroftness: "If `P` is Cockcroft, Hurewicz kills each structural image, by naturality, and
each translate, since the fundamental-group action becomes trivial in ordinary homology."

In the combinatorial model the Hurewicz map is the augmentation `ℤ[G] → ℤ` applied to each
coordinate of a Fox cycle (`RequestProject/Cockcroft.lean`), so the argument becomes: the
augmentation of a `ℤ[G']`-combination of images of Fox cycles of `P` is the corresponding
integer combination of the augmentations of those cycles, hence zero.  Together with
`RequestProject/Pi2Generation.lean` this proves, for the two extensions used in rule 1:

* `FiniteChains.isCockcroft_extRel` — the enlarged presentation is Cockcroft whenever the old
  one is;
* `FiniteChains.isCockcroft_tietze`, `FiniteChains.isCockcroft_hnn` — the two instances, with
  no hypothesis on the fundamental groups beyond the infinite-order condition of the paper.
-/

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains

open MonoidAlgebra

universe u

variable {α : Type u} [Fintype α] [DecidableEq α] {J : Type u} [Fintype J] [DecidableEq J]
variable (ρ : J → FreeGroup α) (w₀ : FreeGroup (Option α))

omit [Fintype α] [DecidableEq α] [Fintype J] [DecidableEq J] in
/-- The augmentation is unchanged by pushing coefficients along a homomorphism of groups. -/
theorem augQ_mapDomain {G G' : Type*} [Group G] [Group G'] (f : G →* G')
    (x : MonoidAlgebra ℤ G) :
    (MonoidAlgebra.lift ℤ ℤ G' 1).toRingHom (MonoidAlgebra.mapDomainRingHom ℤ f x)
      = (MonoidAlgebra.lift ℤ ℤ G 1).toRingHom x := by
  induction x using MonoidAlgebra.induction_linear with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | single g m =>
      show (MonoidAlgebra.lift ℤ ℤ G' 1).toRingHom (MonoidAlgebra.mapDomain f (single g m)) = _
      rw [MonoidAlgebra.mapDomain_single]
      simp [MonoidAlgebra.lift_apply]

omit [Fintype α] [DecidableEq α] [Fintype J] [DecidableEq J] in
/-- The augmentation of the enlarged group ring restricts to the augmentation of the old
one. -/
theorem augPres_extRingHom (z : MonoidAlgebra ℤ (PresGroup ρ)) :
    augPres (extRel ρ w₀) (extRingHom ρ w₀ z) = augPres ρ z :=
  augQ_mapDomain (extHom ρ w₀) z

omit [Fintype α] [DecidableEq J] in
/-- **The extension preserves the Cockcroft property** (the corresponding step of
Lemma 3.9).  Under the two hypotheses of the generation statement, if every Fox cycle of the
old presentation has zero augmentation, then so does every Fox cycle of the enlarged one. -/
theorem isCockcroft_extRel
    (hreg : ∀ x : MonoidAlgebra ℤ (PresGroup (extRel ρ w₀)),
      x * foxMatrixPres (extRel ρ w₀) none none = 0 → x = 0)
    (hinj : Function.Injective (extHom ρ w₀))
    (hP : IsCockcroft ρ) : IsCockcroft (extRel ρ w₀) := by
  intro v hv
  have hspan := extCycle_mem_span ρ w₀ hreg hinj hv
  -- the set of vectors all of whose coordinates have zero augmentation is a submodule
  set N : Submodule (MonoidAlgebra ℤ (PresGroup (extRel ρ w₀)))
      (Option J → MonoidAlgebra ℤ (PresGroup (extRel ρ w₀))) :=
    { carrier := {w | ∀ jo, augPres (extRel ρ w₀) (w jo) = 0}
      add_mem' := by
        intro a b ha hb jo
        rw [Pi.add_apply, map_add, ha jo, hb jo, add_zero]
      zero_mem' := by
        intro jo
        simp
      smul_mem' := by
        intro c a ha jo
        rw [Pi.smul_apply, smul_eq_mul, map_mul, ha jo, mul_zero] } with hN
  have hgen : ∀ w ∈ {w : Option J → MonoidAlgebra ℤ (PresGroup (extRel ρ w₀)) |
      ∃ y : J → MonoidAlgebra ℤ (PresGroup ρ), IsFoxCycle ρ y ∧ w = extCycleImage ρ w₀ y},
      w ∈ N := by
    rintro _ ⟨y, hy, rfl⟩ jo
    cases jo with
    | none => show augPres (extRel ρ w₀) 0 = 0; simp
    | some j =>
        show augPres (extRel ρ w₀) (extRingHom ρ w₀ (y j)) = 0
        rw [augPres_extRingHom, hP y hy j]
  exact Submodule.span_le.2 hgen hspan

omit [Fintype α] [DecidableEq J] in
/-- **The elimination step of rule 1 preserves Cockcroftness.** -/
theorem isCockcroft_tietze (s : FreeGroup α) (hP : IsCockcroft ρ) :
    IsCockcroft (extRel ρ (tietzeWord s)) :=
  isCockcroft_extRel ρ _ (fun x hx => by rwa [foxNew_tietze ρ s, mul_one] at hx)
    (extHom_tietze_injective ρ s) hP

omit [Fintype α] [DecidableEq J] in
/-- **The stable-letter step of rule 1 preserves Cockcroftness.** -/
theorem isCockcroft_hnn (u v : FreeGroup α)
    (hu : ¬ IsOfFinOrder (QuotientGroup.mk u : PresGroup ρ))
    (hv : ¬ IsOfFinOrder (QuotientGroup.mk v : PresGroup ρ))
    (hP : IsCockcroft ρ) : IsCockcroft (extRel ρ (hnnWord u v)) := by
  have hinj := extHom_hnn_injective ρ u v hu hv
  have hord : ¬ IsOfFinOrder (QuotientGroup.mk (FreeGroup.map Option.some v) :
      PresGroup (extRel ρ (hnnWord u v))) := by
    simpa using not_isOfFinOrder_map_of_injective hinj hv
  exact isCockcroft_extRel ρ _
    (fun x hx => mul_one_sub_single_eq_zero hord x (by rwa [foxNew_hnn ρ u v] at hx)) hinj hP

end FiniteChains
