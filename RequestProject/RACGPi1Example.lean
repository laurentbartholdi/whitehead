module

public import RequestProject.RACGPi1

@[expose] public section

/-!
# Non-vacuity: the fundamental group of a concrete `C(L)`

Two letters and no commutation: `L` consists of two points, the complex `C(L)` is the
four-cycle with no two-cell, and its fundamental group is infinite cyclic.  Here it is only
checked that the computation of `RequestProject/RACGPi1.lean` is not vacuous: the kernel of the
parity map contains the element `(s t)²`, so the fundamental group of `C(L)` is **not** trivial
(`FiniteChains.RACG.pi1_cubeCx_nontrivial`), that is `C(L)` is not simply connected.
-/

namespace FiniteChains
namespace RACG

/-- Two letters, none of which commute. -/
def freeTwo : CommRel (Fin 2) where
  rel _ _ := False
  rel_symm := False.elim
  rel_irrefl _ := id

theorem freeTwo_dim (t : Finset (Fin 2))
    (_h : ∀ s ∈ t, ∀ r ∈ t, s ≠ r → freeTwo.rel s r) : t.card ≤ 3 := by
  calc t.card ≤ (Finset.univ : Finset (Fin 2)).card := Finset.card_le_univ t
    _ = 2 := by simp
    _ ≤ 3 := by norm_num

theorem isRed_stst : IsRed freeTwo.rel [(0 : Fin 2), 1, 0, 1] := by
  refine ⟨⟨⟨⟨trivial, by simp [canStart]⟩, ?_⟩, ?_⟩, ?_⟩ <;>
    simp [canStart, freeTwo]

/-- The element `(s t)²` of the right-angled Coxeter group on two non-commuting letters. -/
noncomputable def loopElt : CayGroup freeTwo := cword freeTwo [0, 1, 0, 1]

theorem loopElt_ne_one : loopElt ≠ 1 := by
  intro h
  have hlen : clen freeTwo loopElt = 4 := by
    rw [loopElt, clen_cword freeTwo isRed_stst]
    simp
  rw [h, clen_one] at hlen
  exact absurd hlen (by norm_num)

theorem loopElt_mem : loopElt ∈ kerPhi freeTwo := by
  show phi freeTwo loopElt = 0
  rw [loopElt, phi_cword]
  funext v
  fin_cases v <;> simp [parList] <;> decide

/-- **The fundamental group of this `C(L)` is not trivial**: the four-cycle without a two-cell
is not simply connected, and the monodromy isomorphism sees this. -/
theorem pi1_cubeCx_nontrivial :
    ∃ g : (cubeCx freeTwo).Pi1 (0 : Fin 2 → ZMod 2), g ≠ 1 := by
  obtain ⟨e⟩ := pi1_cubeCx_equiv freeTwo freeTwo_dim
  refine ⟨e.symm ⟨loopElt, loopElt_mem⟩, ?_⟩
  intro h
  have h1 : (⟨loopElt, loopElt_mem⟩ : kerPhi freeTwo) = 1 := by
    have h2 := congrArg e h
    simpa using h2
  exact loopElt_ne_one (congrArg Subtype.val h1)

end RACG
end FiniteChains
