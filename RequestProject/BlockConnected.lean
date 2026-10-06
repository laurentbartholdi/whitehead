module

public import RequestProject.BlockSpinePres

@[expose] public section

/-!
# The block is connected, so it carries a spanning tree

The marked presentation of the block is read off a spanning tree of the one-skeleton of the
order complex of the poset `FiniteChains.Davis.QOld A` of retained cubes.  This file proves that
such a tree exists: the block is connected.

The argument is the one for the cube complex `C(L)` with the all-positive vertex removed.  Every
cube lies above a vertex cube `(∅, ξ)` with `ξ ≠ 0` — for a cube with nonempty type one flips a
sign in one of its own directions, which does not change the cube — and two vertex cubes are
joined by flipping their signs one coordinate at a time through the edge cubes `({v}, ξ)`,
keeping the coordinate of a fixed vertex equal to `1` so that the removed vertex `(∅, 0)` is
never met.

* `FiniteChains.Davis.isConnected_orderCx_qOld` — the order complex of the block is connected;
* `FiniteChains.Davis.exists_spanningTree_qOld` — hence it has a spanning tree with any
  prescribed root, in particular rooted at a cell of the cut surface.
-/

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains
namespace Davis

open RACG Mirror Comb

universe u

variable {V : Type u} [DecidableEq V] [Fintype V] {A : CommRel V}

/-- Being joined by an edge path in the block. -/
def ConnQ (a b : QOld A) : Prop :=
  ∃ p, IsPath (orderCx (QOld A)).src (orderCx (QOld A)).tgt p a b

namespace ConnQ

omit [Fintype V] in
theorem refl (a : QOld A) : ConnQ a a := ⟨[], rfl⟩

omit [Fintype V] in
theorem symm {a b : QOld A} (h : ConnQ a b) : ConnQ b a :=
  ⟨revPath h.choose, isPath_revPath h.choose_spec⟩

omit [Fintype V] in
theorem trans {a b c : QOld A} (h : ConnQ a b) (h' : ConnQ b c) : ConnQ a c :=
  ⟨h.choose ++ h'.choose, h.choose_spec.append h'.choose_spec⟩

omit [Fintype V] in
theorem of_le {a b : QOld A} (h : a ≤ b) : ConnQ a b := ⟨[ordPos h], isPath_ordPos h⟩

omit [Fintype V] in
theorem of_ge {a b : QOld A} (h : b ≤ a) : ConnQ a b := ⟨[ordNeg h], isPath_ordNeg h⟩

end ConnQ

/-- **A vertex cube**: the cube `(∅, ξ)` of a nonzero sign vector. -/
def vtxCube (ξ : V → ZMod 2) (hξ : ξ ≠ 0) : QOld A :=
  ⟨⟨∅, ξ, isSimplex_empty (A := A), fun v hv => absurd hv (Finset.notMem_empty v)⟩,
    fun h => hξ h.2⟩

/-- **An edge cube**: the cube `({v}, ξ)` with the sign at `v` normalised away. -/
def oneCube (v : V) (ξ : V → ZMod 2) : QOld A :=
  ⟨⟨{v}, Function.update ξ v 0, isSimplex_singleton (A := A) v, fun w hw => by
      rw [Finset.mem_singleton] at hw
      subst hw
      simp⟩,
    fun h => by simpa using congrArg (fun s : Finset V => v ∈ s) h.1⟩

omit [Fintype V] in
theorem vtxCube_le_oneCube {ξ : V → ZMod 2} (hξ : ξ ≠ 0) (v : V) :
    (vtxCube ξ hξ : QOld A) ≤ oneCube v ξ := by
  refine ⟨Finset.empty_subset _, fun w hw => ?_⟩
  have hwv : w ≠ v := fun h => hw (by rw [h]; exact Finset.mem_singleton_self v)
  simp [oneCube, vtxCube, hwv]

omit [Fintype V] in
theorem vtxCube_update_le_oneCube {ξ : V → ZMod 2} (v : V) (a : ZMod 2)
    (h : Function.update ξ v a ≠ 0) :
    (vtxCube (Function.update ξ v a) h : QOld A) ≤ oneCube v ξ := by
  refine ⟨Finset.empty_subset _, fun w hw => ?_⟩
  have hwv : w ≠ v := fun h' => hw (by rw [h']; exact Finset.mem_singleton_self v)
  simp [oneCube, vtxCube, hwv]

/-- The support of a sign vector. -/
noncomputable def sgnSupport (ξ : V → ZMod 2) : Finset V :=
  Finset.univ.filter (fun v => ξ v ≠ 0)

omit [DecidableEq V] in
theorem mem_sgnSupport {ξ : V → ZMod 2} {v : V} : v ∈ sgnSupport ξ ↔ ξ v ≠ 0 := by
  simp [sgnSupport]

/-- The distinguished sign vector: `1` at `v₀` and `0` elsewhere. -/
def unitSgn (v₀ : V) : V → ZMod 2 := fun w => if w = v₀ then 1 else 0

omit [Fintype V] in
theorem unitSgn_ne_zero (v₀ : V) : unitSgn (V := V) v₀ ≠ 0 := by
  intro h
  simpa [unitSgn] using congrFun h v₀

/-- **Every vertex cube whose sign at `v₀` is `1` is joined to the distinguished one.** -/
theorem connQ_vtxCube_unit (v₀ : V) :
    ∀ (n : ℕ) (ξ : V → ZMod 2) (hξ : ξ ≠ 0), ξ v₀ = 1 → (sgnSupport ξ).card = n →
      ConnQ (vtxCube ξ hξ : QOld A) (vtxCube (unitSgn v₀) (unitSgn_ne_zero v₀)) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro ξ hξ hv₀ hcard
    by_cases hsupp : ∀ w, ξ w ≠ 0 → w = v₀
    · -- the support is `{v₀}`, so `ξ` is the distinguished vector
      have hxi : ξ = unitSgn v₀ := by
        funext w
        by_cases hw : w = v₀
        · subst hw
          simp [unitSgn, hv₀]
        · have : ξ w = 0 := by
            by_contra hne
            exact hw (hsupp w hne)
          simp [unitSgn, hw, this]
      subst hxi
      exact ConnQ.refl _
    · push_neg at hsupp
      obtain ⟨w, hw, hwv⟩ := hsupp
      set ξ' := Function.update ξ w 0 with hξ'
      have hξ'v₀ : ξ' v₀ = 1 := by
        rw [hξ', Function.update_apply, if_neg (Ne.symm hwv), hv₀]
      have hξ'ne : ξ' ≠ 0 := by
        intro h
        simpa [hξ'v₀] using congrFun h v₀
      -- the two vertex cubes are both faces of the edge cube at `w`
      have hstep : ConnQ (vtxCube ξ hξ : QOld A) (vtxCube ξ' hξ'ne) :=
        (ConnQ.of_le (vtxCube_le_oneCube hξ w)).trans
          (ConnQ.of_ge (vtxCube_update_le_oneCube (ξ := ξ) w 0 hξ'ne))
      -- the support has become smaller
      have hsub : sgnSupport ξ' ⊂ sgnSupport ξ := by
        constructor
        · intro x hx
          rw [mem_sgnSupport] at hx ⊢
          by_cases hxw : x = w
          · subst hxw
            simp [hξ'] at hx
          · rwa [hξ', Function.update_apply, if_neg hxw] at hx
        · intro hle
          have : w ∈ sgnSupport ξ' := hle (mem_sgnSupport.2 hw)
          rw [mem_sgnSupport, hξ'] at this
          simp at this
      have hlt : (sgnSupport ξ').card < n := by
        rw [← hcard]
        exact Finset.card_lt_card hsub
      exact hstep.trans (ih _ hlt ξ' hξ'ne hξ'v₀ rfl)

omit [Fintype V] in
/-- **Every cell of the block is joined to a vertex cube.** -/
theorem connQ_to_vtxCube (c : QOld A) :
    ∃ (ξ : V → ZMod 2) (hξ : ξ ≠ 0), ConnQ c (vtxCube ξ hξ) := by
  by_cases hs : c.1.spx = ∅
  · have hne : c.1.sgn ≠ 0 := fun h => c.2 ⟨hs, h⟩
    refine ⟨c.1.sgn, hne, ?_⟩
    have hEq : c = vtxCube c.1.sgn hne := by
      apply Subtype.ext
      exact QCube.ext' (by simpa [vtxCube] using hs) (fun v _ => rfl)
    exact ConnQ.of_le (le_of_eq hEq)
  · obtain ⟨v, hv⟩ := Finset.nonempty_iff_ne_empty.2 hs
    refine ⟨Function.update c.1.sgn v 1, ?_, ?_⟩
    · intro h
      simpa using congrFun h v
    · refine ConnQ.of_ge ⟨Finset.empty_subset _, fun w hw => ?_⟩
      have hwv : w ≠ v := fun h => hw (h ▸ hv)
      simp [vtxCube, hwv]

/-- **The block is connected.** -/
theorem isConnected_orderCx_qOld [Nonempty V] : IsConnected (orderCx (QOld A)) := by
  obtain ⟨v₀⟩ := ‹Nonempty V›
  have key : ∀ c : QOld A, ConnQ c (vtxCube (unitSgn v₀) (unitSgn_ne_zero v₀)) := by
    intro c
    obtain ⟨ξ, hξ, hc⟩ := connQ_to_vtxCube c
    refine hc.trans ?_
    -- first make the sign at `v₀` equal to `1`, then reduce the support
    set ξ₁ := Function.update ξ v₀ 1 with hξ₁
    have hξ₁v₀ : ξ₁ v₀ = 1 := by simp [hξ₁]
    have hξ₁ne : ξ₁ ≠ 0 := by
      intro h
      simpa [hξ₁v₀] using congrFun h v₀
    have hfirst : ConnQ (vtxCube ξ hξ : QOld A) (vtxCube ξ₁ hξ₁ne) :=
      (ConnQ.of_le (vtxCube_le_oneCube hξ v₀)).trans
        (ConnQ.of_ge (vtxCube_update_le_oneCube (ξ := ξ) v₀ 1 hξ₁ne))
    exact hfirst.trans (connQ_vtxCube_unit v₀ _ ξ₁ hξ₁ne hξ₁v₀ rfl)
  intro a b
  exact ((key a).trans (key b).symm)

/-- **The block carries a spanning tree with any prescribed root**, in particular one rooted at a
cell of the cut surface. -/
theorem exists_spanningTree_qOld [Nonempty V] (r : QOld A) :
    ∃ T : SpanningTree (orderCx (QOld A)), T.root = r :=
  SpanningTree.exists_of_isConnected isConnected_orderCx_qOld r

end Davis
end FiniteChains
