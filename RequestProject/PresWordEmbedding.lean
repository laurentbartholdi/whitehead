module

public import RequestProject.PresValidPoset

@[expose] public section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains.PresModel
open Comb
universe u
variable {α β γ J K L : Type u}

/-- Literal inclusions of labelled attaching words. This retains positions, including
the chosen subdivisions, and does not choose new word representatives. -/
structure PresWordEmbedding (w : J → List (α × Bool)) (v : K → List (β × Bool)) where
  gen : α ↪ β
  cell : J ↪ K
  word : ∀ j, v (cell j) = (w j).map (fun p => (gen p.1, p.2))

namespace PresWordEmbedding
variable {w : J → List (α × Bool)} {v : K → List (β × Bool)}
  {z : L → List (γ × Bool)} (h : PresWordEmbedding w v)

def roseMap : Rose α ↪o Rose β where
  toFun
    | .base => .base
    | .mid a => .mid (h.gen a)
    | .edg a b => .edg (h.gen a) b
  inj' := by
    intro x y he
    cases x <;> cases y <;> simp_all [h.gen.injective.eq_iff]
  map_rel_iff' := by
    intro x y
    change Rose.le _ _ ↔ Rose.le x y
    cases x <;> cases y <;> simp [Rose.le, h.gen.injective.eq_iff, Function.Embedding.coeFn_mk]

def circleFun (c : TCirc w) : TCirc v := (h.cell c.1, c.2)

theorem word_length (j : J) : (v (h.cell j)).length = (w j).length := by
  simp only [h.word, List.length_map]

theorem circleFun_injective : Function.Injective h.circleFun := by
  rintro ⟨j, k, t⟩ ⟨j', k', t'⟩ he
  change (h.cell j, k, t) = (h.cell j', k', t') at he
  exact Prod.ext (h.cell.injective (congrArg Prod.fst he))
    (congrArg (Prod.snd : K × ℕ × CPos → ℕ × CPos) he)

theorem circleFun_le_iff (c d : TCirc w) : h.circleFun c ≤ h.circleFun d ↔ c ≤ d := by
  rcases c with ⟨j, k, t⟩
  rcases d with ⟨j', k', t'⟩
  change h.circleFun _ = h.circleFun _ ∨ TCirc.lt v _ _ ↔
    (j, k, t) = (j', k', t') ∨ TCirc.lt w _ _
  rw (config := { transparency := .default }) [h.circleFun_injective.eq_iff]
  simp only [circleFun, TCirc.lt, TCirc.csucc, h.cell.injective.eq_iff, h.word_length]

def circleMap : TCirc w ↪o TCirc v where
  toFun := h.circleFun
  inj' := h.circleFun_injective
  map_rel_iff' := h.circleFun_le_iff _ _

theorem attaching_map (c : TCirc w) : aFun v (h.circleFun c) = h.roseMap (aFun w c) := by
  rcases c with ⟨j, k, t⟩
  have he : (v (h.cell j))[k]? = ((w j)[k]?).map (fun p => (h.gen p.1, p.2)) := by
    rw [h.word, List.getElem?_map]
  cases t <;> simp only [circleFun, aFun, he] <;>
    cases hg : (w j)[k]? <;> rfl

def posFun : PresPos w → PresPos v
  | .inl (.inl r) => iRose v (h.roseMap r)
  | .inl (.inr c) => iCirc v (h.circleFun c)
  | .inr j => apexOf v (h.cell j)

theorem circle_le_apex_iff (c : TCirc w) (j : J) :
    iCirc w c ≤ apexOf w j ↔ c.1 = j ∧ c.2.1 < (w j).length := by
  constructor
  · intro hc
    rcases (presPos_le_apex_iff w j _).mp hc with he | ⟨k, t, hk, he⟩
    · cases he
    · have he' : c = (j, k, t) := Sum.inr.inj (Sum.inl.inj he)
      rw [he']
      exact ⟨rfl, hk⟩
  · rintro ⟨hj, hk⟩
    rcases c with ⟨j', k, t⟩
    change j' = j at hj
    subst j'
    exact iCirc_le_apexOf w t hk

theorem rose_not_le_apex (r : Rose α) (j : J) : ¬ iRose w r ≤ apexOf w j := by
  intro hr
  rcases (presPos_le_apex_iff w j _).mp hr with he | ⟨k, t, hk, he⟩ <;> cases he

theorem posFun_injective : Function.Injective h.posFun := by
  intro p q he
  cases p with
  | inr j =>
    cases q with
    | inr k => exact congrArg Sum.inr (h.cell.injective (Sum.inr.inj he))
    | inl q => cases q <;> cases he
  | inl p =>
    cases q with
    | inr k => cases p <;> cases he
    | inl q =>
      cases p with
      | inl r =>
        cases q with
        | inl s => exact congrArg (iRose w) (h.roseMap.injective (Sum.inl.inj (Sum.inl.inj he)))
        | inr c => cases he
      | inr c =>
        cases q with
        | inl r => cases he
        | inr d => exact congrArg (iCirc w) (h.circleFun_injective (Sum.inr.inj (Sum.inl.inj he)))

theorem posFun_le_iff (p q : PresPos w) : h.posFun p ≤ h.posFun q ↔ p ≤ q := by
  cases p with
  | inr j =>
    cases q with
    | inr k => exact h.cell.injective.eq_iff
    | inl q => cases q <;> exact Iff.rfl
  | inl p =>
    cases q with
    | inr j =>
      cases p with
      | inl r => exact iff_of_false (rose_not_le_apex _ _) (rose_not_le_apex _ _)
      | inr c =>
        change iCirc v (h.circleFun c) ≤ apexOf v (h.cell j) ↔ iCirc w c ≤ apexOf w j
        rw [circle_le_apex_iff, circle_le_apex_iff]
        simp only [circleFun, h.cell.injective.eq_iff, h.word_length]
    | inl q =>
      cases p with
      | inl r =>
        cases q with
        | inl s => exact h.roseMap.le_iff_le
        | inr c => exact Iff.rfl
      | inr c =>
        cases q with
        | inl r =>
          change aFun v (h.circleFun c) ≤ h.roseMap r ↔ aFun w c ≤ r
          rw [h.attaching_map]
          exact h.roseMap.le_iff_le
        | inr d => exact h.circleFun_le_iff c d

def posMap : PresPos w ↪o PresPos v where
  toFun := h.posFun
  inj' := h.posFun_injective
  map_rel_iff' := h.posFun_le_iff _ _

theorem valid_iff (p : PresPos w) :
    h.posFun p ∈ presValidVertices v ↔ p ∈ presValidVertices w := by
  cases p with
  | inr j => exact Iff.rfl
  | inl p =>
    cases p with
    | inl r => exact Iff.rfl
    | inr c =>
      change c.2.1 < (v (h.cell c.1)).length ↔ c.2.1 < (w c.1).length
      rw [h.word_length]

/-- An actual order embedding of the finite-position models. -/
def validMap : ValidPresPos w ↪o ValidPresPos v where
  toFun p := ⟨h.posFun p.val, (h.valid_iff p.val).mpr p.property⟩
  inj' := fun _ _ he => Subtype.ext (h.posFun_injective (congrArg Subtype.val he))
  map_rel_iff' := h.posFun_le_iff _ _

@[simp] theorem validMap_base : h.validMap (validPresBase w) = validPresBase v := rfl

def refl (w : J → List (α × Bool)) : PresWordEmbedding w w where
  gen := Function.Embedding.refl _
  cell := Function.Embedding.refl _
  word _ := by simp

def trans (k : PresWordEmbedding v z) : PresWordEmbedding w z where
  gen := h.gen.trans k.gen
  cell := h.cell.trans k.cell
  word j := by
    rw [Function.Embedding.trans_apply, k.word, h.word, List.map_map]
    rfl

@[simp] theorem validMap_refl (p : ValidPresPos w) : (refl w).validMap p = p := by
  apply Subtype.ext
  rcases p with ⟨p, hp⟩
  cases p with
  | inr j => rfl
  | inl p => cases p with
    | inl r => cases r <;> rfl
    | inr c => rfl

theorem validMap_trans (k : PresWordEmbedding v z) (p : ValidPresPos w) :
    (h.trans k).validMap p = k.validMap (h.validMap p) := by
  apply Subtype.ext
  rcases p with ⟨p, hp⟩
  cases p with
  | inr j => rfl
  | inl p => cases p with
    | inl r => cases r <;> rfl
    | inr c => rfl

end PresWordEmbedding
end FiniteChains.PresModel
