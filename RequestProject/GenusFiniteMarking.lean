import RequestProject.GenusApply
import RequestProject.ChamberQuotientFinite

/-!
Finite marking of the genus block. The canonical loops are indexed by `Fin q × Bool`,
so there is one marking for each of the paper's `2q` distinguished generators.
This proves the filling and group injectivity for these actual loops; it does not assert
(B2), (B3), or a comparison with topological second homotopy groups.
-/

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains.Davis.Genus

open RACG Mirror Comb PresModel BlockFamily

variable {α Jr : Type} (ρ : Jr ⊕ PUnit.{1} → FreeGroup α) (a b : ℕ → α)
  (q : ℕ) [NeZero q]

abbrev finiteSig (x : Fin q × Bool) := gSig q (x.1.val, x.2)

def finitePairs (q : ℕ) : List ((Fin q × Bool) × (Fin q × Bool)) :=
  (List.finRange q).map fun h => ((h, false), (h, true))

omit [NeZero q] in
/-- Reindexing the surface word by the finite set of its handles. -/
theorem commWord_finitePairs {G : Type} [Group G] (f : ℕ × Bool → G) :
    commWord (fun x : Fin q × Bool => f (x.1.val, x.2)) (finitePairs q) =
      commWord f (genPairs q) := by
  simp only [finitePairs, genPairs, commWord, List.map_map]
  have h := List.map_coe_finRange_eq_range (n := q)
  rw [← h, List.map_map]
  rfl

local instance genusPi1Group : Group
    (Pi1 (orderCx (NeSpx (cmpRel (SCell (gvc q) (gec q) (gc q))))) (gBase q)) :=
  @Pi1.instGroup (orderCx (NeSpx (cmpRel (SCell (gvc q) (gec q) (gc q))))) (gBase q)

/-- The finite list of marked loops bounds the canonical surface polygon. -/
theorem finite_hfilling :
    commWord (fun x : Fin q × Bool =>
      Pi1.mk (⟨finiteSig q x, isPath_gSig q (x.1.val, x.2)⟩ :
        Loop (orderCx (NeSpx (cmpRel (SCell (gvc q) (gec q) (gc q))))) (gBase q)))
      (finitePairs q) = 1 := by
  exact (commWord_finitePairs q _).trans (genus_hfilling q)

abbrev finiteLw (_ : PUnit.{1}) (x : Fin q × Bool) : List (α × Bool) :=
  genusLw a b q (PUnit.unit.{1} : PUnit.{1}) (x.1.val, x.2)

omit [NeZero q] in
theorem finite_hrho (hrho : ρ (Sum.inr PUnit.unit.{1}) = FreeGroup.mk (surfWord a b q))
    (s : PUnit.{1}) :
    ρ (Sum.inr s) =
      commWord (fun x => FreeGroup.mk (finiteLw a b q s x)) (finitePairs q) := by
  cases s
  change ρ (Sum.inr PUnit.unit.{1}) = commWord
    (fun x : Fin q × Bool => FreeGroup.mk
      (genusLw a b q (PUnit.unit.{1} : PUnit.{1}) (x.1.val, x.2))) (finitePairs q)
  rw [commWord_finitePairs q (fun x => FreeGroup.mk
    (genusLw a b q PUnit.unit.{1} x))]
  exact genus_hrho ρ a b q hrho PUnit.unit.{1}

omit [NeZero q] in
/-- The finite marking has exactly the required number of generators. -/
theorem card_finite_marking : Fintype.card (Fin q × Bool) = 2 * q := by
  simp [Nat.mul_comm]

/-- The internal generators are finite, since the quotient has finitely many edges. -/
instance finite_spineGens
    (T : SpanningTree (orderCx (QOld (cmpRel (SCell (gvc q) (gec q) (gc q)))))) :
    Finite (spineGens T) := inferInstanceAs (Finite {e : _ // ¬ T.isTree e})

/-- The block has finitely many cell and marking relators. -/
instance finite_spineRels :
    Finite (spineRels (A := cmpRel (SCell (gvc q) (gec q) (gc q))) (Fin q × Bool)) :=
  inferInstanceAs (Finite (_ ⊕ (Fin q × Bool)))

/-- (B1) for the block with precisely `2q` distinguished generators. -/
theorem finite_filledF (hrho : ρ (Sum.inr PUnit.unit.{1}) = FreeGroup.mk (surfWord a b q))
    (T : SpanningTree (orderCx (QOld (cmpRel (SCell (gvc q) (gec q) (gc q)))))) :
    BlockFamily.FilledF ρ (fun s m =>
      BlockFamily.blockSubst (Zt := fun _ => spineGens T)
        (fun s x => FreeGroup.mk (finiteLw a b q s x)) s
        (spineBeta T (finiteSig q) m)) :=
  filledF_of_surface_filling ρ T (gBase q) (fun _ => finiteSig q)
    (fun _ x => isPath_gSig q (x.1.val, x.2)) (finiteLw a b q)
    (fun _ => finitePairs q) (finite_hrho ρ a b q hrho) (fun _ => finite_hfilling q)

/-- The structural group homomorphism is injective for the finite marking. -/
theorem injective_substHomF_genus_finite
    (hrho : ρ (Sum.inr PUnit.unit.{1}) = FreeGroup.mk (surfWord a b q))
    (T : SpanningTree (orderCx (QOld (cmpRel (SCell (gvc q) (gec q) (gc q)))))) :
    Function.Injective (BlockFamily.substHomF ρ (fun s m =>
      BlockFamily.blockSubst (Zt := fun _ => spineGens T)
        (fun s x => FreeGroup.mk (finiteLw a b q s x)) s
        (spineBeta T (finiteSig q) m)) (finite_filledF ρ a b q hrho T)) :=
  injective_substHomF_of_surfaceW ρ (genusW ρ a b q) (mk_genusW ρ a b q hrho)
    (genusAtt ρ a b q) (gBase q) [] (genus_hcb ρ a b q) T (fun _ => finiteSig q)
    (fun _ x => isPath_gSig q (x.1.val, x.2)) (finiteLw a b q)
    (fun _ => finitePairs q) (fun s x => genus_hread ρ a b q s (x.1.val, x.2))
    (finite_hrho ρ a b q hrho) (fun _ => finite_hfilling q)

end FiniteChains.Davis.Genus
