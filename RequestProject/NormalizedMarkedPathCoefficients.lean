import RequestProject.GenusNamedSurfaceCover

/-! Exact first-edge coefficients after a monotone map and order-chain
normalization. Degenerate tail edges are allowed. Written, unverified proofs. -/
noncomputable section
open scoped Classical
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

set_option maxHeartbeats 1600000

namespace FiniteChains.Comb
universe u
variable {P Q : Type u} [PartialOrder P] [PartialOrder Q]

def normalizedWeakChain1To (f : P → Q) (hf : Monotone f) :
    (OrdEdge P →₀ ℤ) →ₗ[ℤ] (StrictOrdEdge Q →₀ ℤ) :=
  normalizeOrdChain1.comp (chain1 (orderCxMap f hf))

theorem normalizeOrdEdge_apply_zero_of_endpoints_ne
    (d : OrdEdge Q) (e : StrictOrdEdge Q) (h : d.1 ≠ e.1) :
    normalizeOrdEdge d e = 0 := by
  unfold normalizeOrdEdge
  split_ifs with hd
  · rfl
  · have hne : (⟨d.1, lt_of_le_of_ne d.2 hd⟩ : StrictOrdEdge Q) ≠ e :=
      fun he => h (congrArg Subtype.val he)
    simp only [Finsupp.single_apply, if_neg hne]

theorem normalizedWeakChain1To_single (f : P → Q) (hf : Monotone f)
    (d : OrdEdge P) (n : ℤ) :
    normalizedWeakChain1To f hf (Finsupp.single d n) =
      n • normalizeOrdEdge ((orderCxMap f hf).onE d) := by
  change normalizeOrdChain1 (Finsupp.mapDomain (orderCxMap f hf).onE
    (Finsupp.single d n)) = _
  rw (config := { transparency := .default }) [Finsupp.mapDomain_single, normalizeOrdChain1_single]

theorem normalizedWeakChain1To_path_apply_zero
    (f : P → Q) (hf : Monotone f) (p : List (OrdEdge P × Bool))
    (e : StrictOrdEdge Q)
    (hp : ∀ a ∈ p, (f a.1.1.1, f a.1.1.2) ≠ e.1) :
    normalizedWeakChain1To f hf (pathChain p) e = 0 := by
  induction p with
  | nil => simp
  | cons a p ih =>
      have ha := hp a (List.mem_cons_self ..)
      have ht := ih (fun b hb => hp b (List.mem_cons_of_mem a hb))
      have hs : normalizedWeakChain1To f hf (Finsupp.single a.1 (1 : ℤ)) e = 0 := by
        rw (config := { transparency := .default }) [normalizedWeakChain1To_single, one_smul]
        exact normalizeOrdEdge_apply_zero_of_endpoints_ne _ e ha
      rw (config := { transparency := .default }) [pathChain_cons]
      cases a.2 <;>
        simp only [Bool.false_eq_true, ↓reduceIte, map_add,
          map_neg, Finsupp.add_apply, Finsupp.neg_apply, hs, ht, neg_zero, add_zero]

theorem normalizedWeakChain1To_positive_first_coefficient
    (f : P → Q) (hf : Monotone f) (d : OrdEdge P)
    (p : List (OrdEdge P × Bool)) (e₀ e : StrictOrdEdge Q)
    (hfirst : e₀.1 = (f d.1.1, f d.1.2))
    (htail : ∀ a ∈ p, (f a.1.1.1, f a.1.1.2) ≠ e.1) :
    normalizedWeakChain1To f hf (pathChain ((d, true) :: p)) e =
      if e₀ = e then 1 else 0 := by
  have hne : f d.1.1 ≠ f d.1.2 := by
    have h := e₀.2.ne
    simpa only [hfirst] using h
  have hs : normalizeOrdEdge ((orderCxMap f hf).onE d) = Finsupp.single e₀ 1 := by
    unfold normalizeOrdEdge
    dsimp only [orderCxMap]
    rw (config := { transparency := .default }) [dif_neg hne]
    congr 1
    exact Subtype.ext hfirst.symm
  rw (config := { transparency := .default }) [pathChain_cons]
  simp only [↓reduceIte, map_add, Finsupp.add_apply,
    normalizedWeakChain1To_single, one_smul, hs,
    normalizedWeakChain1To_path_apply_zero f hf p e htail, add_zero,
    Finsupp.single_apply]

theorem normalizedWeakChain1To_normalize (f : P → Q) (hf : Monotone f)
    (c : OrdEdge P →₀ ℤ) :
    normalizedWeakChain1To f hf c =
      normalizedChain1To f hf (normalizeOrdChain1 c) := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd => simp only [map_add, hc, hd]
  | single e n =>
      rw [normalizedWeakChain1To_single, normalizeOrdChain1_single, map_smul]
      congr 1
      obtain ⟨⟨a, b⟩, hab⟩ := e
      by_cases he : a = b
      · subst b
        simp [normalizeOrdEdge, orderCxMap]
      · have hlt : a < b := lt_of_le_of_ne hab he
        have hn : normalizeOrdEdge (⟨(a, b), hab⟩ : OrdEdge P) =
            Finsupp.single (⟨(a, b), hlt⟩ : StrictOrdEdge P) 1 := by
          simp [normalizeOrdEdge, he]
        rw (config := { transparency := .default }) [hn]
        change normalizeOrdEdge ((orderCxMap f hf).onE ⟨(a, b), hab⟩) =
          normalizeOrdChain1 (Finsupp.mapDomain (orderCxMap f hf).onE
            (Finsupp.mapDomain (strictOrderIncl P).onE
              (Finsupp.single (⟨(a, b), hlt⟩ : StrictOrdEdge P) (1 : ℤ))))
        rw (config := { transparency := .default }) [Finsupp.mapDomain_single, Finsupp.mapDomain_single,
          normalizeOrdChain1_single, one_smul]
        rfl

theorem normalizeOrdChain1_strict_map (f : P → Q) (hf : StrictMono f)
    (c : OrdEdge P →₀ ℤ) :
    normalizeOrdChain1 (chain1 (orderCxMap f hf.monotone) c) =
      chain1 (strictOrderCxMap f hf) (normalizeOrdChain1 c) := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd => simp only [map_add, hc, hd]
  | single e n =>
      obtain ⟨⟨a, b⟩, hab⟩ := e
      by_cases he : a = b
      · subst b
        simp [chain1, normalizeOrdChain1, normalizeOrdEdge, orderCxMap]
      · have hlt : a < b := lt_of_le_of_ne hab he
        simp [chain1, normalizeOrdChain1, normalizeOrdEdge, orderCxMap,
          strictOrderCxMap, he, (hf hlt).ne]

end FiniteChains.Comb
