module

public import RequestProject.PresConeIntervals
public import RequestProject.PresPosetConnected

@[expose] public section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains.PresModel
open Comb
universe u
variable {α J : Type u} (w : J → List (α × Bool))

/-- Keep all rose vertices and relator apices, and only actual positions of the words. -/
def presValidVertices : Set (PresPos w)
  | .inl (.inl _) => True
  | .inl (.inr c) => c.2.1 < (w c.1).length
  | .inr _ => True

abbrev ValidPresPos := presValidVertices w

def validPresBase : ValidPresPos w := ⟨ptBase w, trivial⟩

instance validPresPos_nonempty : Nonempty (ValidPresPos w) := ⟨validPresBase w⟩

def presValidCollapse : PresPos w → PresPos w
  | .inl (.inl r) => iRose w r
  | .inl (.inr c) => if c.2.1 < (w c.1).length then iCirc w c else ptBase w
  | .inr j => apexOf w j

theorem presValidCollapse_mem (p : PresPos w) : presValidCollapse w p ∈ presValidVertices w := by
  cases p with
  | inl p =>
    cases p with
    | inl r => trivial
    | inr c =>
      dsimp [presValidCollapse]
      split_ifs with h
      · exact h
      · trivial
  | inr j => trivial

theorem presValidCollapse_of_mem (p : PresPos w) (hp : p ∈ presValidVertices w) :
    presValidCollapse w p = p := by
  cases p with
  | inl p =>
    cases p with
    | inl r => rfl
    | inr c => exact if_pos hp
  | inr j => rfl

theorem aFun_invalid {c : TCirc w} (hc : ¬ c.2.1 < (w c.1).length) :
    aFun w c = Rose.base := by
  obtain ⟨j, k, t⟩ := c
  have hget : (w j)[k]? = none := List.getElem?_eq_none (Nat.le_of_not_gt hc)
  cases t <;> simp [aFun, hget]

theorem le_presValidCollapse (p : PresPos w) : p ≤ presValidCollapse w p := by
  cases p with
  | inl p =>
    cases p with
    | inl r => exact le_rfl
    | inr c =>
      dsimp [presValidCollapse]
      split_ifs with h
      · exact le_rfl
      · change aFun w c ≤ Rose.base
        rw [aFun_invalid w h]
  | inr j => exact le_rfl

/-- Every predecessor of an invalid position is that same position. -/
theorem eq_of_le_presInvalid {p q : PresPos w} (hq : q ∉ presValidVertices w)
    (h : p ≤ q) : p = q := by
  cases q with
  | inr j => exact (hq trivial).elim
  | inl q =>
    cases q with
    | inl r => exact (hq trivial).elim
    | inr c =>
      cases p with
      | inr j => exact h.elim
      | inl p =>
        cases p with
        | inl r => exact h.elim
        | inr d =>
          change d = c ∨ TCirc.lt w d c at h
          rcases h with h | h
          · exact congrArg (iCirc w) h
          · exact (hq (by
              change c.2.1 < (w c.1).length
              simpa only [h.1] using h.2.1)).elim

/-- Below a retained vertex, every invalid tail can already be replaced by its base. -/
theorem presValidCollapse_le_of_mem {p q : PresPos w}
    (hq : q ∈ presValidVertices w) (h : p ≤ q) : presValidCollapse w p ≤ q := by
  by_cases hp : p ∈ presValidVertices w
  · rwa [presValidCollapse_of_mem w p hp]
  cases p with
  | inr j => exact (hp trivial).elim
  | inl p =>
    cases p with
    | inl r => exact (hp trivial).elim
    | inr c =>
      change ¬ c.2.1 < (w c.1).length at hp
      change (if c.2.1 < (w c.1).length then iCirc w c else ptBase w) ≤ q
      rw [if_neg hp]
      cases q with
      | inl q =>
        cases q with
        | inl r =>
          change aFun w c ≤ r at h
          rwa [aFun_invalid w hp] at h
        | inr d =>
          have hd := tCirc_valid_down w h hq
          exact (hp (by simpa only [hd.1] using hd.2)).elim
      | inr j =>
        rcases (presPos_le_apex_iff w j (iCirc w c)).mp h with he | ⟨k, t, hk, he⟩
        · cases he
        · have hc : c = TCirc.pt w j k t := Sum.inr.inj (Sum.inl.inj he)
          exact (hp (by simpa only [hc, TCirc.pt] using hk)).elim

theorem presValidCollapse_monotone : Monotone (presValidCollapse w) := by
  intro p q h
  exact presValidCollapse_le_of_mem w (presValidCollapse_mem w q)
    (h.trans (le_presValidCollapse w q))

def presValidRetraction : PresPos w →o ValidPresPos w where
  toFun p := ⟨presValidCollapse w p, presValidCollapse_mem w p⟩
  monotone' := presValidCollapse_monotone w

@[simp] theorem presValidRetraction_val (p : ValidPresPos w) :
    presValidRetraction w p.val = p := Subtype.ext (presValidCollapse_of_mem w p.val p.property)

/-- The retraction is contiguous to the identity on every actual order simplex. -/
theorem presValidCollapse_cross_comparable {p q : PresPos w} (h : p ≤ q ∨ q ≤ p) :
    p ≤ presValidCollapse w q ∨ presValidCollapse w q ≤ p := by
  by_cases hq : q ∈ presValidVertices w
  · rwa [presValidCollapse_of_mem w q hq]
  rcases h with h | h
  · have he := eq_of_le_presInvalid w hq h
    exact Or.inl (he ▸ le_presValidCollapse w q)
  · by_cases hp : p ∈ presValidVertices w
    · exact Or.inr (presValidCollapse_le_of_mem w hp h)
    · have he := eq_of_le_presInvalid w hp h
      subst p
      exact Or.inl (le_presValidCollapse w q)

theorem validPresPos_isConnected (hw : ∀ j, w j ≠ []) :
    IsConnected (orderCx (ValidPresPos w)) := by
  intro p q
  obtain ⟨l, hl⟩ := presPos_isConnected w hw p.val q.val
  refine ⟨mapPath (orderCxMap (presValidRetraction w) (presValidRetraction w).monotone) l, ?_⟩
  simpa only [orderCxMap, presValidRetraction_val] using
    isPath_mapPath (orderCxMap (presValidRetraction w) (presValidRetraction w).monotone) hl

end FiniteChains.PresModel
