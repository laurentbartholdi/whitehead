module

public import RequestProject.OrderCxNatHtpy
public import RequestProject.StrictOrderComplex

@[expose] public section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains.Comb
universe u
variable {P : Type u} [PartialOrder P]

/-- The reversed actual reflexive order edge is null-homotopic. -/
theorem htpy_ordNegSelf_nil (a : P) :
    Htpy (orderCx P) a a [ordNeg (le_refl a)] [] := by
  have h := htpy_revPath (isPath_ordPos (le_refl a)) (htpy_ordSelf_nil a)
  simpa only [revPath, List.reverse_cons, List.reverse_nil, List.nil_append,
    List.map_cons, List.map_nil, revGerm, ordPos, ordNeg, Bool.not] using h

/-- Reflexive edge conjugation does not alter the actual based loop class. -/
theorem htpy_reflexive_conjugation {a : P} (p : List ((orderCx P).E × Bool))
    (hp : IsPath (orderCx P).src (orderCx P).tgt p a a) :
    Htpy (orderCx P) a a ([ordNeg (le_refl a)] ++ p ++ [ordPos (le_refl a)]) p := by
  have h1 := (htpy_ordNegSelf_nil a).congr_append (isPath_nil' a)
    (hp.append (isPath_ordPos (le_refl a)))
  have h2 := (htpy_ordSelf_nil a).congr_append hp (isPath_nil' a)
  have h1' : Htpy (orderCx P) a a
      ([ordNeg (le_refl a)] ++ p ++ [ordPos (le_refl a)]) (p ++ [ordPos (le_refl a)]) := by
    simpa only [List.nil_append, List.append_assoc] using h1
  have h2' : Htpy (orderCx P) a a (p ++ [ordPos (le_refl a)]) p := by
    simpa only [List.append_nil] using h2
  exact h1'.trans h2'

/-- Order-homotopic actual maps agreeing at the basepoint induce homotopic based loops. -/
theorem htpy_loop_mapPath_le_fixed {Q : Type u} [PartialOrder Q]
    {f g : P → Q} (hf : Monotone f) (hg : Monotone g) (hfg : ∀ x, f x ≤ g x)
    {a : P} (hfix : f a = g a) (p : List ((orderCx P).E × Bool))
    (hp : IsPath (orderCx P).src (orderCx P).tgt p a a) :
    Htpy (orderCx Q) (f a) (f a) (mapPath (orderCxMap f hf) p)
      (mapPath (orderCxMap g hg) p) := by
  have hn := htpy_loop_mapPath_le hf hg hfg hp
  have he : (⟨(f a, g a), hfg a⟩ : OrdEdge Q) = ⟨(f a, f a), le_refl (f a)⟩ :=
    Subtype.ext (Prod.ext rfl hfix.symm)
  change Htpy (orderCx Q) (g a) (g a) (mapPath (orderCxMap g hg) p)
    ([(⟨(f a, g a), hfg a⟩, false)] ++ mapPath (orderCxMap f hf) p ++
      [(⟨(f a, g a), hfg a⟩, true)]) at hn
  rw [he, ← hfix] at hn
  exact (hn.trans (htpy_reflexive_conjugation _ (isPath_mapPath (orderCxMap f hf) hp))).symm

end FiniteChains.Comb
