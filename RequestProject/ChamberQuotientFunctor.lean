import RequestProject.ChamberQuotient

namespace FiniteChains.Davis
open RACG Mirror Comb
universe u
variable {V : Type u} [DecidableEq V] {A : CommRel V}
variable {X Y Z : Type u} [Preorder X] [Preorder Y] [Preorder Z]

/-- Apply a base map to every new vertex and retain each old quotient cube.
The attaching map of the target is the actual composite with the base map. -/
def qposMap (att : NeSpx A →o X) (f : X →o Y) :
    Qpos A X att →o Qpos A Y (f.comp att) where
  toFun := Sum.map id f
  monotone' := by
    intro p q hpq
    cases p with
    | inl p =>
      cases q with
      | inl q => exact hpq
      | inr y => exact hpq.elim
    | inr x =>
      cases q with
      | inl q =>
        obtain ⟨hs, hn, hx⟩ := hpq
        exact ⟨hs, hn, f.monotone hx⟩
      | inr y => exact f.monotone hpq

theorem qposMap_qNew (att : NeSpx A →o X) (f : X →o Y) (x : X) :
    qposMap att f (qNew x) = qNew (f x) := rfl

theorem qposMap_injective (att : NeSpx A →o X) (f : X →o Y)
    (hf : Function.Injective f) : Function.Injective (qposMap att f) := by
  intro p q h
  cases p with
  | inl p =>
    cases q with
    | inl q => exact congrArg Sum.inl (Sum.inl.inj h)
    | inr q =>
      change (Sum.inl p : QOld A ⊕ Y) = Sum.inr (f q) at h
      cases h
  | inr p =>
    cases q with
    | inl q =>
      change (Sum.inr (f p) : QOld A ⊕ Y) = Sum.inl q at h
      cases h
    | inr q => exact congrArg Sum.inr (hf (Sum.inr.inj h))

/-- Order embeddings of bases induce genuine order embeddings of chamber quotients. -/
def qposOrderEmbedding (att : NeSpx A →o X) (f : X ↪o Y) :
    Qpos A X att ↪o Qpos A Y (f.toOrderHom.comp att) where
  toFun := qposMap att f.toOrderHom
  inj' := qposMap_injective att f.toOrderHom f.injective
  map_rel_iff' := by
    intro p q
    cases p with
    | inl p =>
      cases q with
      | inl q => rfl
      | inr q => rfl
    | inr p =>
      cases q with
      | inl q =>
        change (q.1.sgn = 0 ∧ ∃ hn, f p ≤ f (att ⟨q.1.spx, hn, q.1.isSimplex⟩)) ↔
          q.1.sgn = 0 ∧ ∃ hn, p ≤ att ⟨q.1.spx, hn, q.1.isSimplex⟩
        simp only [f.le_iff_le]
      | inr q => exact f.le_iff_le

theorem qposMap_comp (att : NeSpx A →o X) (f : X →o Y) (g : Y →o Z)
    (p : Qpos A X att) :
    qposMap (f.comp att) g (qposMap att f p) = qposMap att (g.comp f) p := by
  cases p <;> rfl

end FiniteChains.Davis
