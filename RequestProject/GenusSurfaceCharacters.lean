module

public import RequestProject.GenusCapSurfaceExtraction
public import RequestProject.GenusApply
public import RequestProject.PresPosetReading
public import RequestProject.OrderCocycleChains

@[expose] public section

/-! Explicit integral characters separating the actual genus marking loops. -/
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains.Davis.Genus
open RACG Mirror Comb PresModel
variable (q : ℕ) [NeZero q]

def characterRel : Empty ⊕ PUnit → FreeGroup (ℕ × Bool) := fun _ => 1
def characterA (h : ℕ) : ℕ × Bool := (h, false)
def characterB (h : ℕ) : ℕ × Bool := (h, true)
noncomputable def characterGen (x : ℕ × Bool) : Multiplicative ((ℕ × Bool) →₀ ℤ) :=
  Multiplicative.ofAdd (Finsupp.single x 1)

omit [NeZero q] in
theorem characterRel_read (j : Empty ⊕ PUnit) :
    wordVal characterGen (genusW characterRel characterA characterB q j) = 1 := by
  obtain j | j := j
  · exact j.elim
  · rw (config := { transparency := .default }) [genusW_inr, wordVal, mk_surfWord, map_commWord]
    simp [commWord, mul_comm]

noncomputable def surfaceCharacterCocycle :
    OrdCocycle (NeSpx (cmpRel (GenusVertex q))) (Multiplicative ((ℕ × Bool) →₀ ℤ)) :=
  (presCoc (genusW characterRel characterA characterB q) characterGen
    (characterRel_read q)).pullback
      (genusAtt characterRel characterA characterB q)
      (genusAtt characterRel characterA characterB q).monotone

/-- This explicit surface cocycle evaluates each actual marking to its distinct basis vector. -/
theorem surfaceCharacterCocycle_gSig (x : Fin q × Bool) :
    (surfaceCharacterCocycle q).readPath (gSig q (x.1.val, x.2)) =
      Multiplicative.ofAdd (Finsupp.single (x.1.val, x.2) (1 : ℤ)) := by
  rw (config := { transparency := .default }) [surfaceCharacterCocycle, OrdCocycle.pullback_readPath]
  have h := (presCoc (genusW characterRel characterA characterB q) characterGen
    (characterRel_read q)).readPath_htpy
      (genus_hread characterRel characterA characterB q PUnit.unit.{1} (x.1.val, x.2))
  simp only [List.nil_append, revPath_nil, List.append_nil] at h
  rw (config := { transparency := .default }) [h]
  have hl : genusLw characterA characterB q PUnit.unit.{1} (x.1.val, x.2) =
      [((x.1.val, x.2), true)] := by
    obtain ⟨i, b⟩ := x
    cases b <;>
      simp [genusLw, sLet, Nat.mod_eq_of_lt i.isLt, characterA, characterB,
        show (4 * i.val + 1) / 4 = i.val from by omega]
  rw (config := { transparency := .default }) [hl]
  change reading _ characterGen (characterRel_read q) (genClass _ (x.1.val, x.2)) = _
  exact reading_genClass _ _ _ _

/-- Evaluating this character extracts precisely the coefficient of each actual cap face. -/
theorem surfaceCharacter_capSurfaceChain2 (c : (cappedSpineCx q).F →₀ ℤ)
    (x : Fin q × Bool) :
    (surfaceCharacterCocycle q).chain1 (capSurfaceChain2 q c) (x.1.val, x.2) =
      c (.inr x) := by
  classical
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd =>
      rw (config := { transparency := .default }) [map_add, map_add, Finsupp.add_apply, hc, hd, Finsupp.add_apply]
  | single f n =>
      rw (config := { transparency := .default }) [capSurfaceChain2, Finsupp.linearCombination_single, LinearMap.map_smul]
      obtain f | z := f
      · simp [capSurfaceFace]
      · change (n • (surfaceCharacterCocycle q).chain1
          (pathChain (gSig q (z.1.val, z.2)))) (x.1.val, x.2) = _
        rw (config := { transparency := .default }) [OrdCocycle.chain1_pathChain, surfaceCharacterCocycle_gSig]
        change (n • Finsupp.single (z.1.val, z.2) (1 : ℤ)) (x.1.val, x.2) =
          (Finsupp.single (Sum.inr z) n :
            ((markedSpineCx q).F ⊕ (Fin q × Bool)) →₀ ℤ) (Sum.inr x)
        simp [Finsupp.single_apply, Prod.ext_iff, Fin.ext_iff]

/-- Every actual capped-cover cycle has zero augmented coefficient on every cap face. -/
theorem cappedCoverCycle_cap_augmentation_zero (c : (cappedTreeCover q).F →₀ ℤ)
    (hc : Comb.bdry2 (cappedTreeCover q) c = 0) (x : Fin q × Bool) :
    Finsupp.mapDomain Prod.snd c (.inr x) = 0 := by
  obtain ⟨d, hd⟩ := capSurfaceCycle_boundary q c hc
  have h := (surfaceCharacterCocycle q).chain1_bdry2 d
  rw (config := { transparency := .default }) [hd] at h
  have he := congrArg (fun z : (ℕ × Bool) →₀ ℤ => z (x.1.val, x.2)) h
  simpa only [surfaceCharacter_capSurfaceChain2, Finsupp.zero_apply] using he

end FiniteChains.Davis.Genus
