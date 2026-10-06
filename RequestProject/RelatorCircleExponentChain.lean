module

public import RequestProject.RelatorCircleFundamentalChain
public import RequestProject.StrictNormalizedOneMaps
public import RequestProject.ExponentCorrection
public import RequestProject.CombHurewicz1Pres

@[expose] public section

/-! The actual normalized attaching-circle fundamental chain reads the
exponent vector in the subdivided rose. The rose coefficient realization
is injective and consists of genuine one-cycles. No genus modules or
topological classification hypotheses are used. Pending Lean verification. -/

noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains.PresModel
open Comb
open scoped Classical
universe u
variable {A J : Type u}

def roseIntegerBaseEdge (a : A) (b : Bool) : StrictOrdEdge (Rose A) :=
  ⟨(Rose.base, Rose.edg a b), lt_of_le_of_ne (Rose.base_le_edg a b) (by simp)⟩

def roseIntegerMidEdge (a : A) (b : Bool) : StrictOrdEdge (Rose A) :=
  ⟨(Rose.mid a, Rose.edg a b), lt_of_le_of_ne (Rose.mid_le_edg a b) (by simp)⟩

def roseIntegerGeneratorChain (a : A) : StrictOrdEdge (Rose A) →₀ ℤ :=
  Finsupp.single (roseIntegerBaseEdge a false) 1 -
    Finsupp.single (roseIntegerMidEdge a false) 1 +
    Finsupp.single (roseIntegerMidEdge a true) 1 -
    Finsupp.single (roseIntegerBaseEdge a true) 1

def roseIntegerRealize : (A →₀ ℤ) →ₗ[ℤ] (StrictOrdEdge (Rose A) →₀ ℤ) :=
  Finsupp.linearCombination ℤ roseIntegerGeneratorChain

theorem roseIntegerGeneratorChain_selected (a b : A) :
    roseIntegerGeneratorChain a (roseIntegerMidEdge b true) = if a = b then 1 else 0 := by
  classical
  have hb (s : Bool) : roseIntegerBaseEdge a s ≠ roseIntegerMidEdge b true := by
    intro h
    have he := congrArg (fun e : StrictOrdEdge (Rose A) => e.val.1) h
    change Rose.base = Rose.mid b at he
    cases he
  have hm : roseIntegerMidEdge a false ≠ roseIntegerMidEdge b true := by
    intro h
    have he := congrArg (fun e : StrictOrdEdge (Rose A) => e.val.2) h
    change Rose.edg a false = Rose.edg b true at he
    cases he
  have he : roseIntegerMidEdge a true = roseIntegerMidEdge b true ↔ a = b := by
    constructor
    · intro h
      exact Rose.mid.inj (congrArg (fun e : StrictOrdEdge (Rose A) => e.val.1) h)
    · rintro rfl
      rfl
  simp [roseIntegerGeneratorChain, Finsupp.single_apply, hb, hm, he]

theorem roseIntegerRealize_selected (c : A →₀ ℤ) (a : A) :
    roseIntegerRealize c (roseIntegerMidEdge a true) = c a := by
  classical
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd => simp only [map_add, Finsupp.add_apply, hc, hd]
  | single b n =>
    simp only [roseIntegerRealize, Finsupp.linearCombination_single, Finsupp.smul_apply,
      roseIntegerGeneratorChain_selected, Finsupp.single_apply]
    split_ifs <;> simp_all

theorem roseIntegerRealize_injective : Function.Injective (roseIntegerRealize (A := A)) := by
  intro c d h
  apply Finsupp.ext
  intro a
  have he := congrArg (fun z => z (roseIntegerMidEdge a true)) h
  simpa only [roseIntegerRealize_selected] using he

theorem roseIntegerGeneratorChain_cycle (a : A) :
    Comb.bdry1 (strictOrderCx (Rose A)) (roseIntegerGeneratorChain a) = 0 := by
  simp only [roseIntegerGeneratorChain, map_sub, map_add, Comb.bdry1_single (X := strictOrderCx (Rose A)),
    Finsupp.linearCombination_single, one_smul]
  change (Finsupp.single (Rose.edg a false) 1 - Finsupp.single Rose.base 1) -
      (Finsupp.single (Rose.edg a false) 1 - Finsupp.single (Rose.mid a) 1) +
      (Finsupp.single (Rose.edg a true) 1 - Finsupp.single (Rose.mid a) 1) -
      (Finsupp.single (Rose.edg a true) 1 - Finsupp.single Rose.base 1) = 0
  abel

theorem roseIntegerRealize_cycle (c : A →₀ ℤ) :
    Comb.bdry1 (strictOrderCx (Rose A)) (roseIntegerRealize c) = 0 := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd => simp only [map_add, hc, hd, add_zero]
  | single a n =>
    rw (config := { transparency := .default }) [roseIntegerRealize, Finsupp.linearCombination_single, map_smul,
      roseIntegerGeneratorChain_cycle, smul_zero]

theorem mapOne_single_of_endpoints {P Q : Type u} [PartialOrder P] [PartialOrder Q]
    (f : P → Q) (hf : Monotone f) (e : StrictOrdEdge P) (d : StrictOrdEdge Q)
    (he : (f e.val.1, f e.val.2) = d.val) :
    StrictNormalized.mapOne f hf (Finsupp.single e 1) = Finsupp.single d 1 := by
  rw (config := { transparency := .default }) [StrictNormalized.mapOne_single, one_smul]
  have hn : f e.val.1 ≠ f e.val.2 := by
    intro h
    exact d.property.ne ((congrArg Prod.fst he).symm.trans (h.trans (congrArg Prod.snd he)))
  unfold normalizeOrdEdge
  rw (config := { transparency := .default }) [dif_neg hn]
  congr 1
  exact Subtype.ext he

variable (w : J → List (A × Bool)) (j : J)

theorem relatorCircleLetterChain_exponent (k : Fin (w j).length) :
    StrictNormalized.mapOne (fun x : RelatorCircle w j => aFun w x.val)
      ((aFun_monotone w).comp (fun _ _ h => h)) (relatorCircleLetterChain w j k) =
        if (w j)[k.val].2 then roseIntegerGeneratorChain (w j)[k.val].1
          else -roseIntegerGeneratorChain (w j)[k.val].1 := by
  let f := fun x : RelatorCircle w j => aFun w x.val
  let hf : Monotone f := (aFun_monotone w).comp (fun _ _ h => h)
  have hp : (w j)[k.val]? = some (w j)[k.val] := List.getElem?_eq_getElem k.isLt
  have hmid : f (relatorCirclePoint w j k .cmid) = Rose.mid (w j)[k.val].1 :=
    aFun_pt_cmid_of_get w hp
  have hL : f (relatorCirclePoint w j k .cedgL) = Rose.edg (w j)[k.val].1 (!(w j)[k.val].2) :=
    aFun_pt_cedgL_of_get w hp
  have hR : f (relatorCirclePoint w j k .cedgR) = Rose.edg (w j)[k.val].1 (w j)[k.val].2 :=
    aFun_pt_cedgR_of_get w hp
  have h₀ := mapOne_single_of_endpoints f hf (relatorCircleEdge0 w j k)
    (roseIntegerBaseEdge (w j)[k.val].1 (!(w j)[k.val].2)) (Prod.ext rfl hL)
  have h₁ := mapOne_single_of_endpoints f hf (relatorCircleEdge1 w j k)
    (roseIntegerMidEdge (w j)[k.val].1 (!(w j)[k.val].2)) (Prod.ext hmid hL)
  have h₂ := mapOne_single_of_endpoints f hf (relatorCircleEdge2 w j k)
    (roseIntegerMidEdge (w j)[k.val].1 (w j)[k.val].2) (Prod.ext hmid hR)
  have h₃ := mapOne_single_of_endpoints f hf (relatorCircleEdge3 w j k)
    (roseIntegerBaseEdge (w j)[k.val].1 (w j)[k.val].2) (Prod.ext rfl hR)
  change StrictNormalized.mapOne f hf (relatorCircleLetterChain w j k) = _
  rw (config := { transparency := .default }) [relatorCircleLetterChain, map_sub, map_add, map_sub, h₀, h₁, h₂, h₃]
  cases (w j)[k.val].2 <;> simp only [Bool.not_false, Bool.not_true,
    Bool.false_eq_true, if_false, if_true, roseIntegerGeneratorChain]
  abel

theorem pathChain_eq_sum_get (l : List (A × Bool)) :
    pathChain l = ∑ k : Fin l.length,
      if l[k.val].2 then Finsupp.single l[k.val].1 (1 : ℤ) else -Finsupp.single l[k.val].1 1 := by
  induction l with
  | nil => simp
  | cons p l ih =>
    rw (config := { transparency := .default }) [pathChain_cons]
    change _ = ∑ k : Fin (l.length + 1),
      if (p :: l)[k.val].2 then Finsupp.single (p :: l)[k.val].1 (1 : ℤ)
        else -Finsupp.single (p :: l)[k.val].1 1
    rw (config := { transparency := .default }) [Fin.sum_univ_succ]
    simpa only [Fin.val_zero, Fin.val_succ, List.getElem_cons_zero, List.getElem_cons_succ] using
      congrArg (fun z => (if p.2 then Finsupp.single p.1 (1 : ℤ) else -Finsupp.single p.1 1) + z) ih

theorem expVec_mk_eq_pathChain (l : List (A × Bool)) :
    FiniteChains.expVec (FreeGroup.mk l) = pathChain l := by
  classical
  exact congrArg Multiplicative.toAdd (Comb.expVec_pathChain l)

/-- Exact exponent-vector formula for the normalized image of the genuine
attaching-circle fundamental chain; valid also for the empty circle. -/
theorem relatorCircleFundamentalChain_exponent :
    StrictNormalized.mapOne (fun x : RelatorCircle w j => aFun w x.val)
      ((aFun_monotone w).comp (fun _ _ h => h)) (relatorCircleFundamentalChain w j) =
        roseIntegerRealize (FiniteChains.expVec (FreeGroup.mk (w j))) := by
  rw (config := { transparency := .default }) [relatorCircleFundamentalChain, map_sum]
  simp_rw [relatorCircleLetterChain_exponent]
  rw (config := { transparency := .default }) [expVec_mk_eq_pathChain, pathChain_eq_sum_get, map_sum]
  apply Finset.sum_congr rfl
  intro k _
  cases (w j)[k.val].2 <;>
    simp only [Bool.false_eq_true, if_false, if_true, map_neg,
      roseIntegerRealize, Finsupp.linearCombination_single, one_smul]

end FiniteChains.PresModel
