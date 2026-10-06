import RequestProject.GenusFiniteMarking
import RequestProject.SurfaceWordExpansion

/-! Structural group injectivity for substitution of arbitrary words in a finite genus block. -/

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains.Davis.Genus

open RACG Mirror Comb PresModel BlockFamily

variable {α Jr : Type} (ρ : Jr ⊕ PUnit.{1} → FreeGroup α)
  (q : ℕ) [NeZero q] (u : Fin q × Bool → FreeGroup α)

/-- Named generators for the two loops of a handle, extended periodically. -/
def namedA (h : ℕ) : α ⊕ (Fin q × Bool) :=
  Sum.inr (⟨h % q, Nat.mod_lt _ (Nat.pos_of_neZero q)⟩, false)

def namedB (h : ℕ) : α ⊕ (Fin q × Bool) :=
  Sum.inr (⟨h % q, Nat.mod_lt _ (Nat.pos_of_neZero q)⟩, true)

abbrev namedPres := SurfaceWordExpansion.expandedRel ρ u (finitePairs q)

 theorem namedPres_surface : namedPres ρ q u (Sum.inr PUnit.unit) =
    FreeGroup.mk (surfWord (namedA (α := α) q) (namedB (α := α) q) q) := by
  change commWord (fun x => FreeGroup.of (Sum.inr x)) (finitePairs q) = _
  have h : (fun x : Fin q × Bool =>
      FreeGroup.mk (genLw (namedA (α := α) q) (namedB (α := α) q) (x.1.val, x.2))) =
        (fun x => FreeGroup.of (Sum.inr x)) := by
    funext x
    obtain ⟨h, b⟩ := x
    have hm : h.val % q = h.val := Nat.mod_eq_of_lt h.isLt
    cases b <;> simp [genLw, namedA, namedB, hm] <;> rfl
  rw [← h, commWord_finitePairs q (fun x =>
    FreeGroup.mk (genLw (namedA (α := α) q) (namedB (α := α) q) x))]
  exact (mk_surfWord (namedA (α := α) q) (namedB (α := α) q) q).symm

 theorem namedLw_eq (s : PUnit.{1}) (x : Fin q × Bool) :
    finiteLw (namedA (α := α) q) (namedB (α := α) q) q s x = [(Sum.inr x, true)] := by
  obtain ⟨h, b⟩ := x
  have hm : h.val % q = h.val := Nat.mod_eq_of_lt h.isLt
  cases b
  · change [sLet (namedA (α := α) q) (namedB (α := α) q) (4 * (h.val % q) + 0)] = _
    rw [hm]
    rw [sLet, if_pos (by omega), show (4 * h.val + 0) / 4 = h.val from by omega]
    simp [namedA, hm]
  · change [sLet (namedA (α := α) q) (namedB (α := α) q) (4 * (h.val % q) + 1)] = _
    rw [hm]
    rw [sLet, if_neg (by omega), if_pos (by omega),
      show (4 * h.val + 1) / 4 = h.val from by omega]
    simp [namedB, hm]

variable (T : SpanningTree (orderCx (QOld (cmpRel (SCell (gvc q) (gec q) (gc q))))))

/-- The actual relators obtained by reading the finite block with the prescribed words. -/
noncomputable def wordBlock (s : PUnit.{1}) (m : spineRels
    (A := cmpRel (SCell (gvc q) (gec q) (gc q))) (Fin q × Bool)) :
    FreeGroup (α ⊕ spineGens T) :=
  blockSubst (Zt := fun _ : PUnit.{1} => spineGens T) (fun _ => u) s
    (spineBeta T (finiteSig q) m)

variable (hrho : ρ (Sum.inr PUnit.unit) = commWord u (finitePairs q))

include hrho in
/-- The surface polygon fills the replaced relator also for arbitrary old words. -/
theorem wordBlock_filledF : FilledF ρ (wordBlock q u T) := by
  classical
  have h := filledF_of_surface_filling ρ T (gBase q) (fun _ => finiteSig q)
    (fun _ x => isPath_gSig q (x.1.val, x.2))
    (fun (_ : PUnit.{1}) x => (u x).toWord) (fun _ => finitePairs q)
    (fun s => by cases s; simpa only [FreeGroup.mk_toWord] using hrho)
    (fun _ => finite_hfilling q)
  simp only [FreeGroup.mk_toWord] at h
  convert h using 1
  funext s m
  rfl

/-- The structural homomorphism is injective for arbitrary words `u_h,v_h`.
The auxiliary names are eliminated through a proved presentation-group isomorphism. -/
theorem injective_substHomF_genus_words :
    Function.Injective (substHomF ρ (wordBlock q u T) (wordBlock_filledF ρ q u T hrho)) := by
  let ep := namedPres ρ q u
  let aa := namedA (α := α) q
  let bb := namedB (α := α) q
  have he : ep (Sum.inr PUnit.unit) = FreeGroup.mk (surfWord aa bb q) := namedPres_surface ρ q u
  let ww := genusW ep aa bb q
  let att := genusAtt ep aa bb q
  let hh := mk_genusW ep aa bb q he
  let base := baseToQuotientW ep ww hh att
  let incl := SurfaceWordExpansion.inclusion ρ u (finitePairs q) hrho
  let j := base.comp incl
  have hj : Function.Injective j :=
    (baseToQuotientW_injective ep ww hh att).comp
      (SurfaceWordExpansion.groupEquiv ρ u (finitePairs q) hrho).injective
  let lw := finiteLw aa bb q PUnit.unit
  let bq := bqHomW ep ww hh att (gBase q) [] T (genus_hcb ep aa bb q)
    (fun x => FreeGroup.mk (lw x))
  apply injective_substHomF_of_markedBlock (fun _ : PUnit.{1} => u)
    (fun _ m => spineBeta T (finiteSig q) m) (wordBlock_filledF ρ q u T hrho)
    j hj (fun _ => bq)
  · intro s x
    simp only [bq, bqHomW, FreeGroup.lift_apply_of, Sum.elim_inl]
    change base (QuotientGroup.mk (FreeGroup.mk (lw x))) =
      base (incl (QuotientGroup.mk (u x)))
    have hnames : FreeGroup.mk (lw x) = FreeGroup.of (Sum.inr x) := by
      rw [show lw x = [(Sum.inr x, true)] from namedLw_eq q PUnit.unit x]
      rfl
    rw [hnames]
    apply congrArg base
    exact SurfaceWordExpansion.name_eq_word ρ u (finitePairs q) x
  · intro s m
    cases m with
    | inl f =>
        exact bqHomW_treeRel ep ww hh att (gBase q) [] T
          (genus_hcb ep aa bb q) (fun x => FreeGroup.mk (lw x)) f
    | inr x =>
        exact bqHomW_markRel ep ww hh att (gBase q) [] T (genus_hcb ep aa bb q)
          lw (finiteSig q) (fun x => isPath_gSig q (x.1.val, x.2))
          (fun x => genus_hread ep aa bb q PUnit.unit (x.1.val, x.2)) x

end FiniteChains.Davis.Genus
