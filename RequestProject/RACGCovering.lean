import RequestProject.RACGCayleyGraph

/-!
# The Cayley graph covers the one-skeleton of `C(L)`

The complex `C(L)` of the paper (the real moment-angle complex of `L`) has as vertex set the
sign vectors on the vertices of `L`, two of them being joined when they differ in exactly one
coordinate, and a square for every edge of `L`.  Its fundamental group is the kernel of the
abelianisation `W_L → (ℤ/2)^{L⁰}`.

This file constructs that abelianisation combinatorially and shows that it is a **covering map
of graphs** from the Cayley graph of `W_L` onto the one-skeleton of `C(L)`:

* `FiniteChains.RACG.phi` — the parity homomorphism `W_L → (ℤ/2)^{L⁰}`, defined on reduced
  traces (`FiniteChains.RACG.phi_mul`, `FiniteChains.RACG.phi_gen`);
* `FiniteChains.RACG.cubeGraph` — the one-skeleton of `C(L)`: sign vectors, with an edge for
  each change of one coordinate;
* `FiniteChains.RACG.phi_map_adj` — `phi` is a graph homomorphism;
* `FiniteChains.RACG.phi_unique_lift` — **the covering property**: every edge of `C(L)` at
  `phi x` lifts uniquely to an edge of the Cayley graph at `x`;
* `FiniteChains.RACG.phi_square` — squares of the Cayley graph go to squares of `C(L)`;
* `FiniteChains.RACG.phi_exists_preimage` — every vertex of `C(L)` (a finitely supported sign
  vector) is hit.

Together with `FiniteChains.RACG.cayleyGraph_connected`,
`FiniteChains.RACG.cayleyMedianSimpleGraph` and the simple connectivity of the square complex of
a median graph, this identifies the Cayley graph with the one-skeleton of the universal cover
of `C(L)`.
-/

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains
namespace RACG

universe u

variable {V : Type u} [DecidableEq V] (A : CommRel V)

/-! ### The parity of a word -/

theorem zmod2_add_self (a : ZMod 2) : a + a = 0 := by
  revert a
  decide

/-- The indicator vector of a generator. -/
def eVec (s : V) : V → ZMod 2 := fun v => if v = s then 1 else 0

/-- The parity vector of a word: the number of occurrences of each letter, modulo two. -/
def parList (l : List V) : V → ZMod 2 := fun v => (l.count v : ZMod 2)

@[simp] theorem parList_nil : parList ([] : List V) = fun _ => 0 := by
  funext v; simp [parList]

@[simp] theorem parList_cons (s : V) (l : List V) :
    parList (s :: l) = eVec s + parList l := by
  funext v
  by_cases h : v = s
  · subst h
    simp [parList, eVec, add_comm]
  · simp [parList, eVec, h, Ne.symm h]

theorem parList_append (l m : List V) : parList (l ++ m) = parList l + parList m := by
  funext v
  simp only [parList, List.count_append, Pi.add_apply, Nat.cast_add]

omit [DecidableEq V] in
/-- A commutation of adjacent letters permutes the word. -/
theorem Swap.perm {Cm : V → V → Prop} {l m : List V} (h : Swap Cm l m) : l.Perm m := by
  induction h with
  | head _ q => exact List.Perm.swap _ _ q
  | cons x _ ih => exact ih.cons x

theorem parList_ceq {l m : List V} (h : CEq A.rel l m) : parList l = parList m := by
  induction h with
  | refl => rfl
  | tail _ hstep ih =>
      refine ih.trans ?_
      funext v
      exact congrArg (Nat.cast) (Swap.perm hstep |>.count_eq v)

/-- The parity vector of a reduced trace. -/
def parTr : Tr A → V → ZMod 2 :=
  Quotient.lift (fun l : {l : List V // IsRed A.rel l} => parList l.1)
    (fun _ _ h => parList_ceq A h)

@[simp] theorem parTr_mkTr (l : List V) (h : IsRed A.rel l) :
    parTr A (mkTr A l h) = parList l := rfl

/-- An elementary move changes the parity vector by the corresponding generator. -/
theorem parTr_act (s : V) (t : Tr A) : parTr A (act A s t) = eVec s + parTr A t := by
  classical
  induction t using Quotient.inductionOn with
  | _ l =>
      by_cases hc : canStart A.rel s l.1
      · have hpop : (actRep A s l).1 = popStart s l.1 := actRep_of_canStart A hc
        have hceq : CEq A.rel l.1 (s :: popStart s l.1) :=
          ceq_popStart A.rel_symm hc
        have h1 : parList l.1 = eVec s + parList (popStart s l.1) := by
          rw [parList_ceq A hceq, parList_cons]
        have h2 : parTr A (act A s (Quotient.mk (redSetoid A) l)) = parList (popStart s l.1) := by
          show parList (actRep A s l).1 = _
          rw [hpop]
        rw [h2]
        show parList (popStart s l.1) = eVec s + parList l.1
        rw [h1]
        funext v
        simp only [Pi.add_apply]
        have h0 : eVec s v + eVec s v = 0 := zmod2_add_self _
        linear_combination (norm := ring_nf) -h0
      · have hact : (actRep A s l).1 = s :: l.1 := actRep_of_not_canStart A hc
        have h2 : parTr A (act A s (Quotient.mk (redSetoid A) l)) = parList (s :: l.1) := by
          show parList (actRep A s l).1 = _
          rw [hact]
        rw [h2, parList_cons]
        rfl

/-! ### The parity homomorphism of the group -/

/-- The parity homomorphism `W_L → (ℤ/2)^{L⁰}`: the abelianisation of the right-angled Coxeter
group, read on reduced traces. -/
noncomputable def phi (x : CayGroup A) : V → ZMod 2 :=
  parTr A ((x : Equiv.Perm (Tr A)) (oneTr A))

theorem cword_append (l m : List V) : cword A (l ++ m) = cword A l * cword A m :=
  Subtype.ext (by simpa using wordPerm_append A l m)

theorem phi_cword (l : List V) : phi A (cword A l) = parList l := by
  induction l with
  | nil =>
      show parTr A ((wordPerm A []) (oneTr A)) = parList []
      rfl
  | cons s t ih =>
      have hval : ((cword A (s :: t) : CayGroup A) : Equiv.Perm (Tr A)) (oneTr A)
          = act A s (((cword A t : CayGroup A) : Equiv.Perm (Tr A)) (oneTr A)) := by
        rw [cword_cons]
        show (actPerm A s) _ = _
        rw [actPerm_apply]
      show parTr A _ = _
      rw [hval, parTr_act, parList_cons]
      exact congrArg (fun z => eVec s + z) ih

theorem phi_gen (s : V) : phi A (gen A s) = eVec s := by
  have h : gen A s = cword A [s] := by simp
  rw [h, phi_cword, parList_cons, parList_nil]
  funext v
  simp

theorem phi_mul (x y : CayGroup A) : phi A (x * y) = phi A x + phi A y := by
  obtain ⟨l, _, rfl⟩ := exists_cword A x
  obtain ⟨m, _, rfl⟩ := exists_cword A y
  rw [← cword_append, phi_cword, phi_cword, phi_cword, parList_append]

/-! ### The one-skeleton of `C(L)` and the covering property -/

/-- The one-skeleton of the complex `C(L)`: sign vectors on the generators, joined when they
differ in exactly one coordinate. -/
def cubeGraph : SimpleGraph (V → ZMod 2) where
  Adj v w := ∃ s : V, w = v + eVec s
  symm := ⟨by
    rintro v w ⟨s, rfl⟩
    refine ⟨s, ?_⟩
    funext u
    simp only [Pi.add_apply]
    have h0 : eVec s u + eVec s u = 0 := zmod2_add_self _
    linear_combination (norm := ring_nf) -h0⟩
  loopless := by
    refine ⟨?_⟩
    rintro v ⟨s, hs⟩
    have := congrFun hs s
    simp [eVec] at this

/-- `phi` is a graph homomorphism onto the one-skeleton of `C(L)`. -/
theorem phi_map_adj {x y : CayGroup A} (h : (cayleyGraph A).Adj x y) :
    (cubeGraph (V := V)).Adj (phi A x) (phi A y) := by
  obtain ⟨s, rfl⟩ := h
  exact ⟨s, by rw [phi_mul, phi_gen]⟩

/-- **The covering property.**  Every edge of `C(L)` issuing from `phi x` has a unique lift to an
edge of the Cayley graph issuing from `x`. -/
theorem phi_unique_lift (x : CayGroup A) {w : V → ZMod 2}
    (h : (cubeGraph (V := V)).Adj (phi A x) w) :
    ∃! y : CayGroup A, (cayleyGraph A).Adj x y ∧ phi A y = w := by
  obtain ⟨s, rfl⟩ := h
  refine ⟨x * gen A s, ⟨⟨s, rfl⟩, by rw [phi_mul, phi_gen]⟩, ?_⟩
  rintro y ⟨⟨t, rfl⟩, hy⟩
  rw [phi_mul, phi_gen] at hy
  have hst : eVec t = (eVec s : V → ZMod 2) := by
    have := congrArg (fun z => z - phi A x) hy
    simpa [add_comm, add_sub_cancel_left] using this
  have : t = s := by
    have := congrFun hst t
    by_contra hne
    simp [eVec, hne] at this
  rw [this]

/-- Squares of the Cayley graph, spanned by two commuting generators, go to squares of `C(L)`. -/
theorem phi_square (x : CayGroup A) (s t : V) :
    phi A (x * gen A s * gen A t) = phi A x + eVec s + eVec t := by
  rw [phi_mul, phi_mul, phi_gen, phi_gen]

/-- Every vertex of `C(L)` is in the image: a sign vector supported on a finite set `S` is the
image of the element given by the word listing `S`. -/
theorem phi_exists_preimage (S : Finset V) :
    ∃ x : CayGroup A, phi A x = fun v => if v ∈ S then 1 else 0 := by
  classical
  refine ⟨cword A S.toList, ?_⟩
  rw [phi_cword]
  funext v
  by_cases hv : v ∈ S
  · have : S.toList.count v = 1 :=
      List.count_eq_one_of_mem S.nodup_toList (Finset.mem_toList.2 hv)
    simp [parList, this, hv]
  · have : S.toList.count v = 0 :=
      List.count_eq_zero_of_not_mem (by simpa using hv)
    simp [parList, this, hv]

/-! ### The deck transformations -/

@[simp] theorem phi_one : phi A (1 : CayGroup A) = 0 := by
  have h : (1 : CayGroup A) = cword A [] := by simp
  rw [h, phi_cword, parList_nil]
  rfl

theorem phi_inv (x : CayGroup A) : phi A x⁻¹ = phi A x := by
  have h : phi A x + phi A x⁻¹ = 0 := by
    rw [← phi_mul, mul_inv_cancel, phi_one]
  funext v
  have hv : phi A x v + phi A x⁻¹ v = 0 := congrFun h v
  have h0 : phi A x v + phi A x v = 0 := zmod2_add_self _
  linear_combination (norm := ring_nf) hv - h0

/-- Left multiplication by an element of the kernel of `phi` is a deck transformation: it
preserves the fibres. -/
theorem phi_deck {k x : CayGroup A} (hk : phi A k = 0) : phi A (k * x) = phi A x := by
  rw [phi_mul, hk, zero_add]

/-- Left multiplication is an automorphism of the Cayley graph. -/
theorem deck_adj (k : CayGroup A) {x y : CayGroup A} (h : (cayleyGraph A).Adj x y) :
    (cayleyGraph A).Adj (k * x) (k * y) := by
  obtain ⟨s, rfl⟩ := h
  exact ⟨s, by rw [mul_assoc]⟩

/-- **The fibres of the covering are the orbits of the kernel of `phi`**, that is, of the
fundamental group of `C(L)`. -/
theorem exists_deck_of_phi_eq {x y : CayGroup A} (h : phi A x = phi A y) :
    ∃ k : CayGroup A, phi A k = 0 ∧ y = k * x := by
  refine ⟨y * x⁻¹, ?_, by rw [mul_assoc, inv_mul_cancel, mul_one]⟩
  rw [phi_mul, phi_inv, ← h]
  funext v
  exact zmod2_add_self _

end RACG
end FiniteChains
