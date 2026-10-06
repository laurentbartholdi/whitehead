module

public import RequestProject.PresPosetModel
public import RequestProject.PresentationDictionary

@[expose] public section

/-!
# The generators of a presentation as loops of the poset model

This file constructs the first half of the marked comparison between a presentation and the
poset model `FiniteChains.PresModel.PresPos` of its presentation complex: the homomorphism

    `alphaHom : PresGroup ρ →* π₁(orderCx (PresPos w), ptBase)`

carrying the class of a generator to the loop of that generator.  What has to be proved for it
to exist is that the loop read off a relator word is null-homotopic in the model
(`FiniteChains.PresModel.htpy_wordLoop_nil`), and this is proved, not assumed: the attaching
circle of the relator is carried onto that loop by the cylinder (naturality homotopy
`FiniteChains.Comb.htpy_loop_mapPath_le`), and the attaching circle itself dies under the cone
point of the two-cell (`FiniteChains.Comb.htpy_nil_of_pathIn_le`).

Injectivity of `alphaHom` is proved in `RequestProject/PresPosetReading.lean` by constructing a
left inverse.
-/

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains
namespace PresModel

open Comb

universe u

variable {α J : Type u} (w : J → List (α × Bool))

/-! ### The attaching circle as a path -/

theorem isPath_segAt (j : J) {k : ℕ} (hk : k < (w j).length) :
    IsPath (orderCx (TCirc w)).src (orderCx (TCirc w)).tgt (segAt w j k)
      (TCirc.pt w j k CPos.cor) (TCirc.pt w j (TCirc.csucc w j k) CPos.cor) := by
  rw [segAt, dif_pos hk]
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem isPath_circPath (j : J) : ∀ {m : ℕ}, m ≤ (w j).length →
    IsPath (orderCx (TCirc w)).src (orderCx (TCirc w)).tgt (circPath w j m)
      (TCirc.pt w j 0 CPos.cor) (TCirc.pt w j (m % (w j).length) CPos.cor) := by
  intro m
  induction m with
  | zero =>
      intro _
      show TCirc.pt w j 0 CPos.cor = TCirc.pt w j (0 % (w j).length) CPos.cor
      rw [Nat.zero_mod]
  | succ m ih =>
      intro hm
      have hlt : m < (w j).length := lt_of_lt_of_le (Nat.lt_succ_self m) hm
      have hmod : m % (w j).length = m := Nat.mod_eq_of_lt hlt
      have hprev := ih (le_of_lt hlt)
      rw [hmod] at hprev
      show IsPath _ _ (circPath w j m ++ segAt w j m) _ _
      exact isPath_append_iff.mpr ⟨_, hprev, isPath_segAt w j hlt⟩

/-- The attaching loop of a relator is a loop at the corner in front of its first letter. -/
theorem isPath_circLoop (j : J) :
    IsPath (orderCx (TCirc w)).src (orderCx (TCirc w)).tgt (circLoop w j)
      (TCirc.pt w j 0 CPos.cor) (TCirc.pt w j 0 CPos.cor) := by
  have h := isPath_circPath w j (le_refl (w j).length)
  rwa [Nat.mod_self] at h

/-! ### The attaching circle lies under the two-cell -/

theorem pathIn_mapPath_segAt (j : J) {k : ℕ} (hk : k < (w j).length) :
    PathIn (fun x : PresPos w => x ≤ apexOf w j)
      (mapPath (orderCxMap (iCirc w) (iCirc_monotone w)) (segAt w j k)) := by
  have hcs : TCirc.csucc w j k < (w j).length :=
    Nat.mod_lt _ (lt_of_le_of_lt (Nat.zero_le k) hk)
  rw [segAt, dif_pos hk]
  intro e he
  simp only [mapPath, List.mem_map, List.mem_cons, List.not_mem_nil, or_false] at he
  obtain ⟨g, hg, rfl⟩ := he
  rcases hg with rfl | rfl | rfl | rfl
  · exact ⟨iCirc_le_apexOf w CPos.cor hk, iCirc_le_apexOf w CPos.cedgL hk⟩
  · exact ⟨iCirc_le_apexOf w CPos.cmid hk, iCirc_le_apexOf w CPos.cedgL hk⟩
  · exact ⟨iCirc_le_apexOf w CPos.cmid hk, iCirc_le_apexOf w CPos.cedgR hk⟩
  · exact ⟨iCirc_le_apexOf w CPos.cor hcs, iCirc_le_apexOf w CPos.cedgR hk⟩

theorem pathIn_mapPath_circPath (j : J) : ∀ {m : ℕ}, m ≤ (w j).length →
    PathIn (fun x : PresPos w => x ≤ apexOf w j)
      (mapPath (orderCxMap (iCirc w) (iCirc_monotone w)) (circPath w j m)) := by
  intro m
  induction m with
  | zero => intro _; exact pathIn_nil _
  | succ m ih =>
      intro hm
      have hlt : m < (w j).length := lt_of_lt_of_le (Nat.lt_succ_self m) hm
      show PathIn _ (mapPath _ (circPath w j m ++ segAt w j m))
      rw [mapPath_append]
      intro e he
      rcases List.mem_append.1 he with h | h
      · exact ih (le_of_lt hlt) e h
      · exact pathIn_mapPath_segAt w j hlt e h

/-! ### The attaching circle is carried onto the loop of its word -/

theorem mapPath_segAt (j : J) {k : ℕ} (hk : k < (w j).length) :
    mapPath (orderCxMap (fun x => iRose w (aFun w x)) (iRose_aFun_monotone w)) (segAt w j k)
      = letterLoop w (w j)[k] := by
  have hp : (w j)[k]? = some (w j)[k] := List.getElem?_eq_getElem hk
  have hcor : iRose w (aFun w (TCirc.pt w j k CPos.cor)) = iRose w Rose.base := rfl
  have hcorS : iRose w (aFun w (TCirc.pt w j (TCirc.csucc w j k) CPos.cor))
      = iRose w Rose.base := rfl
  have hmid : iRose w (aFun w (TCirc.pt w j k CPos.cmid))
      = iRose w (Rose.mid (w j)[k].1) := by rw [aFun_pt_cmid_of_get w hp]
  have hL : iRose w (aFun w (TCirc.pt w j k CPos.cedgL))
      = iRose w (Rose.edg (w j)[k].1 (!(w j)[k].2)) := by rw [aFun_pt_cedgL_of_get w hp]
  have hR : iRose w (aFun w (TCirc.pt w j k CPos.cedgR))
      = iRose w (Rose.edg (w j)[k].1 (w j)[k].2) := by rw [aFun_pt_cedgR_of_get w hp]
  rw [segAt, dif_pos hk]
  show [ordPos ((iRose_aFun_monotone w) (TCirc.cor_le_cedgL w hk)),
      ordNeg ((iRose_aFun_monotone w) (TCirc.cmid_le_cedgL w hk)),
      ordPos ((iRose_aFun_monotone w) (TCirc.cmid_le_cedgR w hk)),
      ordNeg ((iRose_aFun_monotone w) (TCirc.cor_csucc_le_cedgR w hk))]
    = letterLoop w (w j)[k]
  rcases hpair : (w j)[k] with ⟨i, b⟩
  rw [hpair] at hmid hL hR
  cases b with
  | true =>
      show _ = genLoop w i
      simp only [genLoop, List.cons.injEq, and_true]
      exact ⟨ordPos_congr hcor hL _ _, ordNeg_congr hmid hL _ _, ordPos_congr hmid hR _ _,
        ordNeg_congr hcorS hR _ _⟩
  | false =>
      show _ = genLoopRev w i
      simp only [genLoopRev, List.cons.injEq, and_true]
      exact ⟨ordPos_congr hcor hL _ _, ordNeg_congr hmid hL _ _, ordPos_congr hmid hR _ _,
        ordNeg_congr hcorS hR _ _⟩

theorem mapPath_circPath (j : J) : ∀ {m : ℕ}, m ≤ (w j).length →
    mapPath (orderCxMap (fun x => iRose w (aFun w x)) (iRose_aFun_monotone w)) (circPath w j m)
      = wordLoop w ((w j).take m) := by
  intro m
  induction m with
  | zero => intro _; rfl
  | succ m ih =>
      intro hm
      have hlt : m < (w j).length := lt_of_lt_of_le (Nat.lt_succ_self m) hm
      have hsplit : (w j).take (m + 1) = (w j).take m ++ [(w j)[m]] := by
        rw [List.take_add_one, List.getElem?_eq_getElem hlt]
        rfl
      show mapPath _ (circPath w j m ++ segAt w j m) = _
      rw [mapPath_append, ih (le_of_lt hlt), mapPath_segAt w j hlt, hsplit, wordLoop_append]
      congr 1
      simp [wordLoop]

/-! ### The loop of a relator word is null-homotopic in the model -/

theorem htpy_wordLoop_nil (j : J) :
    Htpy (orderCx (PresPos w)) (ptBase w) (ptBase w) (wordLoop w (w j)) [] := by
  by_cases h0 : 0 < (w j).length
  case neg =>
    have hnil : w j = [] := List.length_eq_zero_iff.mp (Nat.eq_zero_of_not_pos h0)
    rw [hnil]
    exact Htpy.refl _
  case pos =>
  set u : TCirc w := TCirc.pt w j 0 CPos.cor with hu
  have hloop : IsPath (orderCx (TCirc w)).src (orderCx (TCirc w)).tgt (circLoop w j) u u :=
    isPath_circLoop w j
  have hfg : ∀ x : TCirc w, iCirc w x ≤ iRose w (aFun w x) := iCirc_le_iRose_aFun w
  -- the image of the attaching circle in the base copy is the loop of the word
  have himg : mapPath (orderCxMap (fun x => iRose w (aFun w x)) (iRose_aFun_monotone w))
      (circLoop w j) = wordLoop w (w j) := by
    have h := mapPath_circPath w j (le_refl (w j).length)
    rwa [List.take_length] at h
  -- the attaching circle itself dies under the cone point of the two-cell
  have hcone : Htpy (orderCx (PresPos w)) (iCirc w u) (iCirc w u)
      (mapPath (orderCxMap (iCirc w) (iCirc_monotone w)) (circLoop w j)) [] :=
    htpy_nil_of_pathIn_le (apexOf w j) (iCirc_le_apexOf w CPos.cor h0)
      (isPath_mapPath (orderCxMap (iCirc w) (iCirc_monotone w)) hloop)
      (pathIn_mapPath_circPath w j (le_refl (w j).length))
  -- the naturality homotopy relates the two images
  have hnat := htpy_loop_mapPath_le (iCirc_monotone w) (iRose_aFun_monotone w) hfg hloop
  rw [himg] at hnat
  have h1 : Htpy (orderCx (PresPos w)) (ptBase w) (ptBase w)
      ([ordNeg (hfg u)] ++ mapPath (orderCxMap (iCirc w) (iCirc_monotone w)) (circLoop w j)
        ++ [ordPos (hfg u)])
      ([ordNeg (hfg u)] ++ [] ++ [ordPos (hfg u)]) :=
    hcone.congr_append (isPath_ordNeg (hfg u)) (isPath_ordPos (hfg u))
  have h2 : Htpy (orderCx (PresPos w)) (ptBase w) (ptBase w)
      [ordNeg (hfg u), ordPos (hfg u)] [] := htpy_ordNeg_ordPos (hfg u)
  refine hnat.trans (h1.trans ?_)
  simpa using h2

/-! ### The comparison homomorphism -/

/-- The class of the loop of a word. -/
def wordClass (l : List (α × Bool)) : Pi1 (orderCx (PresPos w)) (ptBase w) :=
  Pi1.mk ⟨wordLoop w l, isPath_wordLoop w l⟩

/-- The class of the loop of a generator. -/
def genClass (i : α) : Pi1 (orderCx (PresPos w)) (ptBase w) :=
  Pi1.mk ⟨genLoop w i, isPath_genLoop w i⟩

theorem wordClass_append (l l' : List (α × Bool)) :
    wordClass w (l ++ l') = wordClass w l * wordClass w l' := by
  refine Quotient.sound ?_
  show Htpy (orderCx (PresPos w)) (ptBase w) (ptBase w) (wordLoop w (l ++ l'))
    (wordLoop w l ++ wordLoop w l')
  rw [wordLoop_append]
  exact Htpy.refl _

theorem wordClass_single_true (i : α) : wordClass w [(i, true)] = genClass w i := rfl

theorem wordClass_single_false (i : α) : wordClass w [(i, false)] = (genClass w i)⁻¹ := rfl

/-- The homomorphism of the free group into the fundamental group of the model. -/
def alphaFree : FreeGroup α →* Pi1 (orderCx (PresPos w)) (ptBase w) :=
  FreeGroup.lift (genClass w)

theorem alphaFree_of (i : α) : alphaFree w (FreeGroup.of i) = genClass w i := by
  simp [alphaFree]

theorem alphaFree_mk (l : List (α × Bool)) : alphaFree w (FreeGroup.mk l) = wordClass w l := by
  induction l with
  | nil =>
      simp only [alphaFree, FreeGroup.lift_mk, List.map_nil, List.prod_nil]
      rfl
  | cons eb l ih =>
      obtain ⟨i, b⟩ := eb
      have hsplit : ((i, b) :: l) = [(i, b)] ++ l := rfl
      rw [hsplit, ← FreeGroup.mul_mk, map_mul, ih, wordClass_append]
      congr 1
      cases b
      · rw [wordClass_single_false]
        simp [alphaFree, FreeGroup.lift_mk]
      · rw [wordClass_single_true]
        simp [alphaFree, FreeGroup.lift_mk]

/-- **The relators die in the model.** -/
theorem alphaFree_relator (j : J) : alphaFree w (FreeGroup.mk (w j)) = 1 := by
  rw [alphaFree_mk]
  exact Quotient.sound (htpy_wordLoop_nil w j)

/-! ### The model of a presentation -/

/-- A word representing each relator of the presentation `ρ`. -/
noncomputable def presWords (ρ : J → FreeGroup α) : J → List (α × Bool) := fun j => Quot.out (ρ j)

theorem mk_presWords (ρ : J → FreeGroup α) (j : J) :
    FreeGroup.mk (presWords ρ j) = ρ j := Quot.out_eq _

/-- **The poset model of the presentation complex of `ρ`.** -/
noncomputable abbrev presModelPos (ρ : J → FreeGroup α) : Type u := PresPos (presWords ρ)

/-- **The marked comparison homomorphism** of the presentation `ρ` with its poset model: the
class of a generator goes to the loop of that generator. -/
noncomputable def alphaHom (ρ : J → FreeGroup α) :
    PresGroup ρ →* Pi1 (orderCx (presModelPos ρ)) (ptBase (presWords ρ)) :=
  QuotientGroup.lift _ (alphaFree (presWords ρ)) (by
    refine Subgroup.normalClosure_le_normal ?_
    rintro _ ⟨j, rfl⟩
    have h := alphaFree_relator (presWords ρ) j
    rwa [mk_presWords ρ j] at h)

@[simp] theorem alphaHom_mk (ρ : J → FreeGroup α) (x : FreeGroup α) :
    alphaHom ρ (QuotientGroup.mk x) = alphaFree (presWords ρ) x := rfl

theorem alphaHom_gen (ρ : J → FreeGroup α) (i : α) :
    alphaHom ρ (QuotientGroup.mk (FreeGroup.of i)) = genClass (presWords ρ) i := by
  rw [alphaHom_mk, alphaFree_of]

end PresModel
end FiniteChains
