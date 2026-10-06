import RequestProject.GenusLoops
import RequestProject.BlockSurfaceApplyW

/-!
# The theorem applied to the block of the article, over the closed surface of genus `q`

This file feeds the genuine closed surface of genus `q` into the general theorem
`FiniteChains.Davis.injective_substHomF_of_surfaceW`.

The nerve of the block is the flag triangulation of the closed orientable surface of genus `q`
carried by the face poset `SCell (gvc q) (gec q)` of the `4q`-gon with its sides glued in pairs
according to the surface word `∏_{h<q} a_h b_h a_h⁻¹ b_h⁻¹`.  The marking
`FiniteChains.Davis.surfAtt` sends the boundary of the polygon onto the attaching circle of the
relator of the block, so that the side `4h` of the polygon reads the generator `a_h` and the
side `4h+1` reads `b_h`; the polygon itself is filled by the triangles of the surface, whence
`FiniteChains.Davis.Genus.genus_hfilling`, the hypothesis (B1) of the substitution.

* `FiniteChains.Davis.Genus.genusW` — the words of the presentation: the chosen words of the
  retained relators, and the surface word for the relator of the block;
* `FiniteChains.Davis.Genus.genusAtt` — the attaching map of the block, i.e. the marking of the
  surface;
* `FiniteChains.Davis.Genus.genus_hread` — the loop of the distinguished generator `(h, i)`
  reads exactly the letter `a_h`, resp. `b_h`;
* `FiniteChains.Davis.Genus.injective_substHomF_genus` — **the theorem applied to the block**:
  the structural homomorphism of the simultaneous substitution by the block of genus `q` is
  injective.
-/

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains
namespace Davis

open RACG Mirror Comb PresModel BlockFamily

namespace Genus

variable {α Jr : Type} (ρ : Jr ⊕ PUnit → FreeGroup α) (a b : ℕ → α) (q : ℕ) [NeZero q]

/-- The words of the presentation: the chosen words of the retained relators, and the surface
word of genus `q` for the relator of the block. -/
noncomputable def genusW : Jr ⊕ PUnit → List (α × Bool) :=
  Sum.elim (fun jr => presWords ρ (Sum.inl jr)) (fun _ => surfWord a b q)

omit [NeZero q] in
theorem genusW_inr (s : PUnit) : genusW ρ a b q (Sum.inr s) = surfWord a b q := rfl

omit [NeZero q] in
theorem mk_genusW (hrho : ρ (Sum.inr PUnit.unit) = FreeGroup.mk (surfWord a b q)) :
    ∀ j, FreeGroup.mk (genusW ρ a b q j) = ρ j := by
  rintro (jr | s)
  · exact mk_presWords ρ (Sum.inl jr)
  · cases s
    exact hrho.symm

/-- **The attaching map of the block**: the marking of the surface of genus `q`, which sends the
boundary of the polygon onto the attaching circle of the relator of the block. -/
noncomputable abbrev genusAtt :
    NeSpx (cmpRel (SCell (gvc q) (gec q) (gc q))) →o PresPos (genusW ρ a b q) :=
  surfAtt (w := genusW ρ a b q) (j₀ := Sum.inr PUnit.unit) (genus_hM a b q)
    (genus_hvlab a b q) (genus_helb a b q) (gc q)

/-- The word read by the loop of the distinguished generator `x = (h, i)`: the letter `a_h` for
`i = false`, the letter `b_h` for `i = true`. -/
def genusLw (_ : PUnit) (x : ℕ × Bool) : List (α × Bool) :=
  [sLet a b (4 * (x.1 % q) + (if x.2 then 1 else 0))]

/-! ### The base point -/

theorem genusAtt_base :
    genusAtt ρ a b q (gBase q) = ptBase (genusW ρ a b q) := by
  rw (config := { transparency := .default }) [gBase, att_V, vertLab_of_even (by rw [cyc_mod_two])]
  rfl

theorem genus_hcb :
    IsPath (orderCx (PresPos (genusW ρ a b q))).src (orderCx (PresPos (genusW ρ a b q))).tgt []
      (ptBase (genusW ρ a b q)) (genusAtt ρ a b q (gBase q)) :=
  (genusAtt_base ρ a b q).symm

/-! ### The reading -/

omit [NeZero q] in
theorem genus_index (x : ℕ × Bool) :
    8 * (x.1 % q) + (if x.2 then 2 else 0)
      = 2 * (4 * (x.1 % q) + (if x.2 then 1 else 0)) := by
  rcases x with ⟨n, i⟩
  cases i
  · show 8 * (n % q) + 0 = 2 * (4 * (n % q) + 0)
    ring
  · show 8 * (n % q) + 2 = 2 * (4 * (n % q) + 1)
    ring

theorem genus_index_lt (x : ℕ × Bool) :
    4 * (x.1 % q) + (if x.2 then 1 else 0) < (surfWord a b q).length := by
  have hq : x.1 % q < q := Nat.mod_lt _ (Nat.pos_of_neZero q)
  rw [surfWord_length]
  rcases x with ⟨n, i⟩
  cases i
  · show 4 * (n % q) + 0 < 4 * q
    simp at hq ⊢
    omega
  · show 4 * (n % q) + 1 < 4 * q
    simp at hq ⊢
    omega

/-- **The loop of the distinguished generator reads its letter.** -/
theorem genus_hread (s : PUnit) (x : ℕ × Bool) :
    Htpy (orderCx (PresPos (genusW ρ a b q))) (ptBase (genusW ρ a b q))
      (ptBase (genusW ρ a b q))
      ([] ++ mapPath (orderCxMap (genusAtt ρ a b q) (genusAtt ρ a b q).monotone) (gSig q x)
        ++ revPath [])
      (wordLoop (genusW ρ a b q) (genusLw a b q s x)) := by
  set k : ℕ := 4 * (x.1 % q) + (if x.2 then 1 else 0) with hkdef
  have hk : k < (genusW ρ a b q (Sum.inr PUnit.unit)).length := genus_index_lt a b q x
  -- the loop of the generator is the side of the polygon carrying the letter `k`
  have hsig : gSig q x
      = bdEdge (gc q) (cyc (8 * q) (2 * k)) ++ bdEdge (gc q) (cyc (8 * q) (2 * k + 1)) := by
    have h1 : gSig q x = gPath q (2 * k) := by
      rw [gSig_eq, genus_index]
    rw [h1]
    exact pPath_eq (gc q) (2 * k)
  -- the letter read is the letter `k` of the surface word
  have hlet : (genusW ρ a b q (Sum.inr PUnit.unit))[k]'hk = sLet a b k := by
    have h := surfWord_getElem? a b q k (by
      have := genus_index_lt a b q x
      rw [surfWord_length] at this
      exact this)
    have h' : (genusW ρ a b q (Sum.inr PUnit.unit))[k]? = some (sLet a b k) := h
    rw [List.getElem?_eq_getElem hk] at h'
    exact Option.some.inj h'
  have hmain := htpy_mapPath_letter (w := genusW ρ a b q) (j₀ := Sum.inr PUnit.unit)
    (genus_hM a b q) (genus_hvlab a b q) (genus_helb a b q) (gc q) k hk
  rw [hlet] at hmain
  rw [hsig]
  have hword : wordLoop (genusW ρ a b q) (genusLw a b q s x)
      = letterLoop (genusW ρ a b q) (sLet a b k) := by
    simp [genusLw, wordLoop, hkdef]
  rw [hword]
  simpa using hmain

/-! ### The relator of the block -/

omit [NeZero q] in
theorem genus_hrho (hrho : ρ (Sum.inr PUnit.unit) = FreeGroup.mk (surfWord a b q))
    (s : PUnit) :
    ρ (Sum.inr s) = commWord (fun x => FreeGroup.mk (genusLw a b q s x)) (genPairs q) := by
  cases s
  rw [hrho, mk_surfWord]
  refine commWord_congr_on ?_
  intro p hp
  simp only [genPairs, List.mem_map, List.mem_range] at hp
  obtain ⟨h, hh, rfl⟩ := hp
  have hmod : h % q = h := Nat.mod_eq_of_lt hh
  constructor
  · show FreeGroup.mk (genLw a b (h, false)) = FreeGroup.mk (genusLw a b q PUnit.unit (h, false))
    have e : genusLw a b q PUnit.unit (h, false) = [(a h, true)] := by
      show [sLet a b (4 * (h % q) + 0)] = _
      rw [hmod]
      show [sLet a b (4 * h)] = _
      rw [sLet, if_pos (by omega), show 4 * h / 4 = h from by omega]
    rw [e]
    rfl
  · show FreeGroup.mk (genLw a b (h, true)) = FreeGroup.mk (genusLw a b q PUnit.unit (h, true))
    have e : genusLw a b q PUnit.unit (h, true) = [(b h, true)] := by
      show [sLet a b (4 * (h % q) + 1)] = _
      rw [hmod]
      rw [sLet, if_neg (by omega), if_pos (by omega), show (4 * h + 1) / 4 = h from by omega]
    rw [e]
    rfl

/-! ### The theorem applied to the block -/

/-- **The theorem of the article applied to its own block.**

The nerve of the block is the flag triangulation of the closed orientable surface of genus `q`
obtained from the `4q`-gon by gluing its sides in pairs according to the surface word
`∏_{h<q} a_h b_h a_h⁻¹ b_h⁻¹`; its internal generators are the edges of the two-dimensional
order complex of the block outside a spanning tree `T`, and its relators are the two-cells of
the block together with the `2q` marking relators, which say that the distinguished generator
`(h, i)` is the word spelled inside the block by the loop that goes once along the side `4h + i`
of the polygon.  The relator of the block is the surface word, and it is filled by the polygon
itself, so the hypothesis (B1) of the substitution is not assumed but proved
(`FiniteChains.Davis.Genus.genus_filledF`).  Consequently the structural homomorphism of the
simultaneous substitution by this block is injective; the only hypotheses left are the
presentation, `q ≥ 1`, the chosen words, and the choice of a spanning tree of the block. -/
theorem genus_filledF (hrho : ρ (Sum.inr PUnit.unit) = FreeGroup.mk (surfWord a b q))
    (T : SpanningTree (orderCx (QOld (cmpRel (SCell (gvc q) (gec q) (gc q)))))) :
    BlockFamily.FilledF ρ (fun s m =>
      BlockFamily.blockSubst (Zt := fun _ => spineGens T)
        (fun (s : PUnit) (x : ℕ × Bool) => FreeGroup.mk (genusLw a b q s x)) s
        (spineBeta T (fun x : ℕ × Bool => gSig q x) m)) :=
  filledF_of_surface_filling ρ T (gBase q) (fun _ => gSig q) (fun _ => isPath_gSig q)
    (genusLw a b q) (fun _ => genPairs q) (genus_hrho ρ a b q hrho) (fun _ => genus_hfilling q)

theorem injective_substHomF_genus
    (hrho : ρ (Sum.inr PUnit.unit) = FreeGroup.mk (surfWord a b q))
    (T : SpanningTree (orderCx (QOld (cmpRel (SCell (gvc q) (gec q) (gc q)))))) :
    Function.Injective (BlockFamily.substHomF ρ (fun s m =>
      BlockFamily.blockSubst (Zt := fun _ => spineGens T)
        (fun (s : PUnit) (x : ℕ × Bool) => FreeGroup.mk (genusLw a b q s x)) s
        (spineBeta T (fun x : ℕ × Bool => gSig q x) m))
      (genus_filledF ρ a b q hrho T)) :=
  injective_substHomF_of_surfaceW ρ (genusW ρ a b q) (mk_genusW ρ a b q hrho)
    (genusAtt ρ a b q) (gBase q) [] (genus_hcb ρ a b q) T (fun _ => gSig q)
    (fun _ => isPath_gSig q) (genusLw a b q) (fun _ => genPairs q) (genus_hread ρ a b q)
    (genus_hrho ρ a b q hrho) (fun _ => genus_hfilling q)

/-! ### Simultaneous substitutions for an arbitrary family of relators -/

/-- The presentation words for a family of genus-`q` relators. -/
noncomputable def genusWFamily {Sx : Type} (ρ : Jr ⊕ Sx → FreeGroup α)
    (a b : Sx → ℕ → α) (q : ℕ) : Jr ⊕ Sx → List (α × Bool) :=
  Sum.elim (fun jr => presWords ρ (Sum.inl jr)) (fun s => surfWord (a s) (b s) q)

theorem genusWFamily_mk {Sx : Type} (ρ : Jr ⊕ Sx → FreeGroup α)
    (a b : Sx → ℕ → α) (q : ℕ)
    (hrho : ∀ s, ρ (Sum.inr s) = FreeGroup.mk (surfWord (a s) (b s) q)) :
    ∀ j, FreeGroup.mk (genusWFamily ρ a b q j) = ρ j := by
  rintro (jr | s)
  · exact mk_presWords ρ (Sum.inl jr)
  · exact (hrho s).symm

/-- The word read by a distinguished generator in the genus-`q` block at index `s`. -/
def genusLwFamily {Sx : Type} (a b : Sx → ℕ → α) (q : ℕ) (s : Sx)
    (x : ℕ × Bool) : List (α × Bool) :=
  [sLet (a s) (b s) (4 * (x.1 % q) + (if x.2 then 1 else 0))]

theorem genus_hrhoFamily {Sx : Type} (ρ : Jr ⊕ Sx → FreeGroup α)
    (a b : Sx → ℕ → α) (q : ℕ) [NeZero q]
    (hrho : ∀ s, ρ (Sum.inr s) = FreeGroup.mk (surfWord (a s) (b s) q))
    (s : Sx) :
    ρ (Sum.inr s) = commWord (fun x => FreeGroup.mk (genusLwFamily a b q s x)) (genPairs q) := by
  rw [hrho s, mk_surfWord]
  refine commWord_congr_on ?_
  intro p hp
  simp only [genPairs, List.mem_map, List.mem_range] at hp
  obtain ⟨h, hh, rfl⟩ := hp
  have hmod : h % q = h := Nat.mod_eq_of_lt hh
  constructor
  · show FreeGroup.mk (genLw (a s) (b s) (h, false)) =
      FreeGroup.mk (genusLwFamily a b q s (h, false))
    have e : genusLwFamily a b q s (h, false) = [(a s h, true)] := by
      show [sLet (a s) (b s) (4 * (h % q) + 0)] = _
      rw [hmod]
      have hdiv : (4 * h + 0) / 4 = h := by omega
      rw [sLet, if_pos (by omega), hdiv]
    rw [e]
    rfl
  · show FreeGroup.mk (genLw (a s) (b s) (h, true)) =
      FreeGroup.mk (genusLwFamily a b q s (h, true))
    have e : genusLwFamily a b q s (h, true) = [(b s h, true)] := by
      show [sLet (a s) (b s) (4 * (h % q) + 1)] = _
      rw [hmod]
      rw [sLet, if_neg (by omega), if_pos (by omega), show (4 * h + 1) / 4 = h from by omega]
    rw [e]
    rfl

/-- The genus-`q` block injectivity theorem for simultaneous substitution at any family of
relators.  The surface filling and the reading of each distinguished generator are supplied
uniformly by the closed genus-`q` polygon. -/
theorem injective_substHomF_genus_family {Sx : Type}
    (ρ : Jr ⊕ Sx → FreeGroup α) (a b : Sx → ℕ → α) (q : ℕ) [NeZero q]
    (hrho : ∀ s, ρ (Sum.inr s) = FreeGroup.mk (surfWord (a s) (b s) q))
    (w : Jr ⊕ Sx → List (α × Bool))
    (hw : ∀ j, FreeGroup.mk (w j) = ρ j)
    (att : NeSpx (cmpRel (SCell (gvc q) (gec q) (gc q))) →o PresPos w)
    (cb : List ((orderCx (PresPos w)).E × Bool))
    (hcb : IsPath (orderCx (PresPos w)).src (orderCx (PresPos w)).tgt cb
      (ptBase w) (att (gBase q)))
    (hread : ∀ (s : Sx) (x : ℕ × Bool),
      Htpy (orderCx (PresPos w)) (ptBase w) (ptBase w)
        (cb ++ mapPath (orderCxMap att att.monotone) (gSig q x) ++ revPath cb)
        (wordLoop w (genusLwFamily a b q s x)))
    (T : SpanningTree (orderCx (QOld (cmpRel (SCell (gvc q) (gec q) (gc q)))))) :
    Function.Injective (BlockFamily.substHomF ρ (fun s m =>
      BlockFamily.blockSubst (Zt := fun _ => spineGens T)
        (fun s x => FreeGroup.mk (genusLwFamily a b q s x)) s
        (spineBeta T (fun x : ℕ × Bool => gSig q x) m))
      (filledF_of_surface_filling ρ T (gBase q) (fun _ => gSig q)
        (fun _ => isPath_gSig q) (genusLwFamily a b q) (fun _ => genPairs q)
        (genus_hrhoFamily ρ a b q hrho) (fun _ => genus_hfilling q))) := by
  exact injective_substHomF_of_surfaceW ρ w hw att (gBase q) cb hcb T
    (fun _ => gSig q) (fun _ => isPath_gSig q)
    (genusLwFamily a b q) (fun _ => genPairs q) hread
    (genus_hrhoFamily ρ a b q hrho) (fun _ => genus_hfilling q)

/-- The block carries a spanning tree: the cut surface of the block of genus `q` is connected
and nonempty. -/
theorem exists_spanningTree_genus :
    ∃ T : SpanningTree (orderCx (QOld (cmpRel (SCell (gvc q) (gec q) (gc q))))),
      T.root = posQCube (gBase q) := by
  haveI : Nonempty (SCell (gvc q) (gec q) (gc q)) := ⟨toS _ _ _ Cell.ctr⟩
  exact exists_spanningTree_qOld _

end Genus

end Davis
end FiniteChains
