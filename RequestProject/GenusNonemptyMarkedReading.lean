module

public import RequestProject.GenusNonemptyWords

@[expose] public section

/-! Actual marking paths for the connected, nonempty-word base model.

-/
namespace FiniteChains.Davis.Genus
open RACG Mirror Comb PresModel
variable {α Jr : Type} (ρ : Jr ⊕ PUnit → FreeGroup α)
  (a b : ℕ → α) (q : ℕ) [NeZero q]

/-- Adding cancelling letters to empty retained relators leaves the actual
surface marking and its reading unchanged. -/
theorem genusNonempty_hread (s : PUnit) (x : ℕ × Bool) :
    Htpy (orderCx (PresPos (genusNonemptyW ρ a b q)))
      (ptBase (genusNonemptyW ρ a b q)) (ptBase (genusNonemptyW ρ a b q))
      ([] ++ mapPath (orderCxMap (genusNonemptyAtt ρ a b q)
        (genusNonemptyAtt ρ a b q).monotone) (gSig q x) ++ revPath [])
      (wordLoop (genusNonemptyW ρ a b q) (genusLw a b q s x)) := by
  set k : ℕ := 4 * (x.1 % q) + (if x.2 then 1 else 0) with hkdef
  have hk : k < (genusNonemptyW ρ a b q (Sum.inr PUnit.unit)).length :=
    genus_index_lt a b q x
  have hsig : gSig q x = bdEdge (gc q) (cyc (8 * q) (2 * k)) ++
      bdEdge (gc q) (cyc (8 * q) (2 * k + 1)) := by
    have h1 : gSig q x = gPath q (2 * k) := by
      rw [gSig_eq, genus_index]
    rw [h1]
    exact pPath_eq (gc q) (2 * k)
  have hlet : (genusNonemptyW ρ a b q (Sum.inr PUnit.unit))[k]'hk = sLet a b k := by
    have h := surfWord_getElem? a b q k (by
      have := genus_index_lt a b q x
      rw [surfWord_length] at this
      exact this)
    have h' : (genusNonemptyW ρ a b q (Sum.inr PUnit.unit))[k]? = some (sLet a b k) := h
    rw [List.getElem?_eq_getElem hk] at h'
    exact Option.some.inj h'
  have hmain := htpy_mapPath_letter (w := genusNonemptyW ρ a b q)
    (j₀ := Sum.inr PUnit.unit) (genus_hM a b q) (genus_hvlab a b q)
    (genus_helb a b q) (gc q) k hk
  rw [hlet] at hmain
  rw [hsig]
  have hword : wordLoop (genusNonemptyW ρ a b q) (genusLw a b q s x) =
      letterLoop (genusNonemptyW ρ a b q) (sLet a b k) := by
    simp [genusLw, wordLoop, hkdef]
  rw [hword]
  simpa using hmain

end FiniteChains.Davis.Genus
