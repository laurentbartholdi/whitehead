module

public import RequestProject.PresPosetAlpha

@[expose] public section

/-!
# The reading homomorphism of the poset model, and injectivity of the comparison

This file constructs the second half of the marked comparison of a presentation with the poset
model of its presentation complex: a **reading homomorphism**

    `reading : π₁(orderCx (PresPos w), ptBase) →* G`

for any group `G` with a chosen image `gen i` of every generator, provided every relator word
evaluates to `1` in `G`.  It is the monodromy (`FiniteChains.Comb.OrdCocycle.monodromy`) of an
explicit cocycle on the model:

* on the rose, the cocycle reads the generator off the second half of its subdivided loop;
* on the mapping cylinder it is pulled back along the retraction onto the rose;
* over the cone point of a relator it is trivialised by the prefix products of the relator word,
  which is consistent exactly because the whole word evaluates to `1`.

Composed with the comparison homomorphism of `RequestProject/PresPosetAlpha.lean` for
`G = PresGroup ρ` this gives a left inverse of `alphaHom`, hence **`alphaHom` is injective**:
the presentation group embeds in the fundamental group of the model, marked by the generators.
-/

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains
namespace PresModel

open Comb

universe u v

variable {α J : Type u} (w : J → List (α × Bool)) {G : Type v} [Group G] (gen : α → G)

/-! ### The values of letters and words -/

/-- The value of a letter. -/
def letterVal (p : α × Bool) : G := if p.2 then gen p.1 else (gen p.1)⁻¹

/-- The value of a word. -/
def wordVal (l : List (α × Bool)) : G := FreeGroup.lift gen (FreeGroup.mk l)

@[simp] theorem wordVal_nil : wordVal (gen := gen) [] = 1 := by
  simp [wordVal]

theorem wordVal_append (l l' : List (α × Bool)) :
    wordVal gen (l ++ l') = wordVal gen l * wordVal gen l' := by
  rw [wordVal, wordVal, wordVal, ← FreeGroup.mul_mk, map_mul]

theorem wordVal_single (p : α × Bool) : wordVal gen [p] = letterVal gen p := by
  obtain ⟨i, b⟩ := p
  cases b <;> simp [wordVal, letterVal, FreeGroup.lift_mk]

/-! ### The cocycle of the rose -/

/-- The cocycle of the subdivided rose: the generator is read off the second half of its loop. -/
def roseVal : Rose α → Rose α → G
  | Rose.base, Rose.edg i b => if b then (gen i)⁻¹ else 1
  | _, _ => 1

@[simp] theorem roseVal_base_edg (i : α) (b : Bool) :
    roseVal gen Rose.base (Rose.edg i b) = if b then (gen i)⁻¹ else 1 := rfl

@[simp] theorem roseVal_mid_edg (i i' : α) (b : Bool) :
    roseVal gen (Rose.mid i) (Rose.edg i' b) = 1 := rfl

@[simp] theorem roseVal_self (x : Rose α) : roseVal gen x x = 1 := by
  cases x <;> rfl

/-- The cocycle of the rose. -/
def roseCoc : OrdCocycle (Rose α) G where
  val := roseVal gen
  comp := by
    intro a b c hab hbc
    cases b with
    | base =>
        cases a with
        | base => rw [roseVal_self, one_mul]
        | mid i => exact hab.elim
        | edg i b => exact hab.elim
    | mid i =>
        cases a with
        | base => exact hab.elim
        | mid i' =>
            have hii : i' = i := hab
            subst hii
            rw [roseVal_self, one_mul]
        | edg i' b => exact hab.elim
    | edg i bb =>
        cases c with
        | base => exact hbc.elim
        | mid i' => exact hbc.elim
        | edg i' b' =>
            obtain ⟨hi, hb⟩ := hbc
            subst hi
            subst hb
            rw [roseVal_self, mul_one]

/-- The cocycle of the mapping cylinder: the cocycle of the rose read through the retraction. -/
def cylCoc : OrdCocycle (CylBase w) G :=
  (roseCoc gen).comap (cylRetr (aHom w)) (cylRetr_monotone (aHom w))

/-! ### The trivialisation over a two-cell -/

/-- The prefix product of the first `k` letters of the relator `j`. -/
def prefixVal (j : J) (k : ℕ) : G := wordVal gen ((w j).take k)

@[simp] theorem prefixVal_zero (j : J) : prefixVal w gen j 0 = 1 := by
  simp [prefixVal]

theorem prefixVal_succ (j : J) {k : ℕ} (hk : k < (w j).length) :
    prefixVal w gen j (k + 1) = prefixVal w gen j k * letterVal gen (w j)[k] := by
  have hsplit : (w j).take (k + 1) = (w j).take k ++ [(w j)[k]] := by
    rw [List.take_add_one, List.getElem?_eq_getElem hk]
    rfl
  rw [prefixVal, prefixVal, hsplit, wordVal_append, wordVal_single]

/-- The value of the trivialisation at a point of a circle. -/
def trivVal (j : J) (k : ℕ) (t : CPos) : G :=
  match t with
  | CPos.cor => (prefixVal w gen j k)⁻¹
  | _ => (roseVal gen Rose.base (aFun w (j, k, CPos.cedgL)))⁻¹ * (prefixVal w gen j k)⁻¹

/-- The trivialisation of the cocycle under the cone point of the relator `j`. -/
def trivFun (_j : J) : CylBase w → G :=
  Sum.elim (fun _ => 1) (fun x => trivVal w gen x.1 x.2.1 x.2.2)

/-- The prefix product at the cyclic successor of a position: the relator word closes up
because it evaluates to `1`. -/
theorem prefixVal_csucc (hrel : ∀ j : J, wordVal gen (w j) = 1) (j : J) {k : ℕ}
    (hk : k < (w j).length) :
    prefixVal w gen j (TCirc.csucc w j k) = prefixVal w gen j (k + 1) := by
  rcases lt_or_eq_of_le (Nat.succ_le_of_lt hk) with hlt | heq
  · rw [TCirc.csucc, Nat.mod_eq_of_lt hlt]
  · have hlen : (w j).length = k + 1 := heq.symm
    have h0 : TCirc.csucc w j k = 0 := by rw [TCirc.csucc, hlen, Nat.mod_self]
    rw [h0, prefixVal_zero, prefixVal, ← hlen, List.take_length, hrel j]

/-- **The trivialisation is parallel for the cocycle**: this is the cocycle identity for a
comparability of the attaching circle and the cone point over it. -/
theorem trivVal_step (hrel : ∀ j : J, wordVal gen (w j) = 1) {x y : TCirc w} (h : x ≤ y) :
    roseVal gen (aFun w x) (aFun w y) * trivVal w gen y.1 y.2.1 y.2.2
      = trivVal w gen x.1 x.2.1 x.2.2 := by
  rcases h with rfl | hlt
  · rw [roseVal_self, one_mul]
  obtain ⟨j, k, t⟩ := x
  obtain ⟨j', k', t'⟩ := y
  obtain ⟨hj, hk', hcase⟩ := hlt
  subst hj
  obtain ⟨p, hp⟩ := exists_get_of_lt w hk'
  have hL : aFun w (j, k', CPos.cedgL) = Rose.edg p.1 (!p.2) := aFun_cedgL_of_get w hp
  have hR : aFun w (j, k', CPos.cedgR) = Rose.edg p.1 p.2 := aFun_cedgR_of_get w hp
  have hM : aFun w (j, k', CPos.cmid) = Rose.mid p.1 := aFun_cmid_of_get w hp
  rcases hcase with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
  · -- corner ≤ left half
    show roseVal gen (aFun w (j, k, CPos.cor)) (aFun w (j, k, CPos.cedgL))
        * trivVal w gen j k CPos.cedgL = trivVal w gen j k CPos.cor
    show roseVal gen Rose.base (aFun w (j, k, CPos.cedgL))
        * ((roseVal gen Rose.base (aFun w (j, k, CPos.cedgL)))⁻¹
          * (prefixVal w gen j k)⁻¹) = (prefixVal w gen j k)⁻¹
    rw [← mul_assoc, mul_inv_cancel, one_mul]
  · -- midpoint ≤ left half
    show roseVal gen (aFun w (j, k, CPos.cmid)) (aFun w (j, k, CPos.cedgL))
        * trivVal w gen j k CPos.cedgL = trivVal w gen j k CPos.cmid
    rw [hM, hL, roseVal_mid_edg, one_mul]
    rfl
  · -- midpoint ≤ right half
    show roseVal gen (aFun w (j, k, CPos.cmid)) (aFun w (j, k, CPos.cedgR))
        * trivVal w gen j k CPos.cedgR = trivVal w gen j k CPos.cmid
    rw [hM, hR, roseVal_mid_edg, one_mul]
    rfl
  · -- the corner in front of the next letter ≤ right half: here the letter is read
    show roseVal gen (aFun w (j, TCirc.csucc w j k', CPos.cor)) (aFun w (j, k', CPos.cedgR))
        * trivVal w gen j k' CPos.cedgR = trivVal w gen j (TCirc.csucc w j k') CPos.cor
    show roseVal gen Rose.base (aFun w (j, k', CPos.cedgR))
        * ((roseVal gen Rose.base (aFun w (j, k', CPos.cedgL)))⁻¹
          * (prefixVal w gen j k')⁻¹) = (prefixVal w gen j (TCirc.csucc w j k'))⁻¹
    rw [prefixVal_csucc w gen hrel j hk', prefixVal_succ w gen j hk', hL, hR,
      roseVal_base_edg, roseVal_base_edg]
    have hpk : (w j)[k'] = p := by
      have := List.getElem?_eq_getElem hk'
      rw [hp] at this
      exact (Option.some.injEq _ _ ▸ this.symm) ▸ rfl
    rw [hpk, letterVal]
    cases hp2 : p.2 with
    | true => simp [mul_inv_rev]
    | false => simp [mul_inv_rev]

/-- **The cocycle of the model.**  The hypothesis is that every relator word evaluates to `1`,
which is what makes the trivialisation over a two-cell consistent. -/
def presCoc (hrel : ∀ j : J, wordVal gen (w j) = 1) : OrdCocycle (PresPos w) G :=
  (cylCoc w gen).coneAdj (trivFun w gen) (by
    intro t p q hpq hq
    obtain ⟨r, hr, hqr⟩ := hq
    obtain ⟨k0, t0, hk0, rfl⟩ := hr
    -- the elements under a cone point are the points of its circle
    cases q with
    | inl y => exact hqr.elim
    | inr y =>
        cases p with
        | inl x => exact hpq.elim
        | inr x => exact trivVal_step w gen hrel hpq)

/-! ### The reading homomorphism -/

/-- **The reading homomorphism** of the model: the monodromy of the cocycle. -/
def reading (hrel : ∀ j : J, wordVal gen (w j) = 1) :
    Pi1 (orderCx (PresPos w)) (ptBase w) →* G :=
  (presCoc w gen hrel).monodromy (ptBase w)

/-- **The reading homomorphism reads the generators.** -/
theorem reading_genClass (hrel : ∀ j : J, wordVal gen (w j) = 1) (i : α) :
    reading w gen hrel (genClass w i) = gen i := by
  show (presCoc w gen hrel).readPath (genLoop w i) = gen i
  show roseVal gen Rose.base (Rose.edg i false) *
      ((roseVal gen (Rose.mid i) (Rose.edg i false))⁻¹ *
        (roseVal gen (Rose.mid i) (Rose.edg i true) *
          ((roseVal gen Rose.base (Rose.edg i true))⁻¹ * 1))) = gen i
  simp

/-! ### Injectivity of the comparison -/

/-- The reading homomorphism of the model of `ρ` with values in the presentation group. -/
noncomputable def readingPres (ρ : J → FreeGroup α) :
    Pi1 (orderCx (presModelPos ρ)) (ptBase (presWords ρ)) →* PresGroup ρ :=
  reading (presWords ρ) (fun i => QuotientGroup.mk (FreeGroup.of i)) (by
    intro j
    have hlift : (FreeGroup.lift fun i : α => (QuotientGroup.mk (FreeGroup.of i) : PresGroup ρ))
        = QuotientGroup.mk' (relSub ρ) := by
      refine FreeGroup.ext_hom _ _ fun i => ?_
      simp
    show FreeGroup.lift _ (FreeGroup.mk (presWords ρ j)) = 1
    rw [hlift, mk_presWords]
    exact (QuotientGroup.eq_one_iff _).2
      (Subgroup.subset_normalClosure (Set.mem_range.2 ⟨j, rfl⟩)))

/-- **The reading homomorphism is a left inverse of the comparison homomorphism.** -/
theorem readingPres_alphaHom (ρ : J → FreeGroup α) (x : PresGroup ρ) :
    readingPres ρ (alphaHom ρ x) = x := by
  induction x using QuotientGroup.induction_on with
  | _ y =>
      have key : ((readingPres ρ).comp (alphaHom ρ)).comp (QuotientGroup.mk' (relSub ρ))
          = QuotientGroup.mk' (relSub ρ) := by
        refine FreeGroup.ext_hom _ _ fun i => ?_
        show readingPres ρ (alphaHom ρ (QuotientGroup.mk (FreeGroup.of i)))
          = QuotientGroup.mk (FreeGroup.of i)
        rw [alphaHom_gen]
        exact reading_genClass _ _ _ i
      exact DFunLike.congr_fun key y

/-- **The presentation group embeds into the fundamental group of the poset model**, marked by
the generators.  This is the faithfulness of the base model used by the one-way comparison. -/
theorem alphaHom_injective (ρ : J → FreeGroup α) : Function.Injective (alphaHom ρ) :=
  Function.LeftInverse.injective (readingPres_alphaHom ρ)

end PresModel
end FiniteChains
