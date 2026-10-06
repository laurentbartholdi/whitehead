module

public import RequestProject.RelativeTreeExtension

@[expose] public section

/-! Cell inclusions between relative tree extensions with the same
extra generators. Pending final Lean verification. -/

noncomputable section
open scoped Classical
namespace FiniteChains.Comb.RelativeTreeExtension
open SpanningTree
variable {D : Complex2} (T : SpanningTree D) {Z S R : Type}
  (extra : S → FreeGroup (NonTree T ⊕ Z))
  (extra' : R → FreeGroup (NonTree T ⊕ Z))
  (f : S → R) (hf : ∀ s, extra' (f s) = extra s)

def inclusion : Hom (complex T extra) (complex T extra') where
  onV := id
  onE := id
  onF := Sum.map id f
  src_onE _ := rfl
  tgt_onE _ := rfl
  base_onF := by rintro (d | s) <;> rfl
  att_onF := by
    intro s
    cases s with
    | inl d => simp [complex]
    | inr s => simp [complex, hf]

theorem inclusion_tree (e : (complex T extra).E) :
    (tree T extra').isTree ((inclusion T extra extra' f hf).onE e) ↔
      (tree T extra).isTree e := Iff.rfl

theorem inclusion_injective_F (hinj : Function.Injective f) :
    Function.Injective (inclusion T extra extra' f hf).onF := by
  rintro (a | a) (b | b) h
  · exact congrArg Sum.inl (Sum.inl.inj h)
  · exact False.elim (Sum.inl_ne_inr h)
  · exact False.elim (Sum.inr_ne_inl h)
  · exact congrArg Sum.inr (hinj (Sum.inr.inj h))

theorem inclusion_generators (a : NonTree (tree T extra)) :
    generatorEquiv T extra'
      (nonTreeIncl (inclusion_tree T extra extra' f hf) a) = generatorEquiv T extra a := by
  rcases a with ⟨a | z, ha⟩ <;> rfl

end FiniteChains.Comb.RelativeTreeExtension
