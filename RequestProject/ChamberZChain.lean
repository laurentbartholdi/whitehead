module

public import RequestProject.ChamberZPoset
public import RequestProject.NerveRelativeGluing
public import RequestProject.DavisChainAcyclic

@[expose] public section

/-!
# Chains of the complex `Z` of modified chambers: only the copies of the base survive

This file applies the already-proved results to the actual object built in
`RequestProject/ChamberZPoset.lean`:

* the ordinary chambers of `Z` are acyclic — they are still cones on their apex
  (`FiniteChains.Davis.acyclicIn_zchamber_unmarked`);
* a modified chamber retracts, below the identity, onto its copy of the base poset, hence is
  acyclic **relative** to the union of those copies
  (`FiniteChains.Davis.acyclicRelIn_zchamber_marked`);
* the attaching intersection of a chamber of `Z` is `J_w`, which is acyclic by the mirror
  contraction (`FiniteChains.Davis.acyclicIn_zJSet`);
* gluing these along the filtration by word length
  (`FiniteChains.Nerve.acyclicRelIn_union_of_unmixed`) gives the main result

  `FiniteChains.Davis.exists_base_cycle_of_cycle`: **every increasing cycle of `Z`, in every
  degree, is the sum of an increasing cycle supported on the adjoined copies of the base and
  the boundary of an increasing chain of `Z`.**

In particular ordinary chambers contribute nothing and each modified chamber contributes exactly
the cycles of its copy of the base: this is the chain-level form, for the actual object `Z`, of
"the modified chambers contribute the cycles of their copies of the base".  It is a statement
about `Z` itself; transporting it to the universal cover with group-ring coefficients is a
separate obligation.
-/

namespace FiniteChains
namespace Davis

open RACG Mirror Comb Nerve

universe u

variable {V : Type u} [DecidableEq V] [Fintype V] {A : CommRel V} {X : Type u} [Preorder X]
  {M : CayGroup A → Prop} {att : NeSpx A →o X}

/-- **The base subcomplex of `Z`**: the union of the adjoined copies of the base poset. -/
def InZBase : Zpos A X M att → Prop
  | Sum.inl _ => False
  | Sum.inr _ => True

/-! ### Ordinary chambers -/

omit [Fintype V] in
theorem not_isMarkedApex_apex {w : CayGroup A} (hw : ¬ M w) :
    ¬ IsMarkedApex M (chamberPt w (isSimplex_empty (A := A))) := by
  rintro ⟨-, h⟩
  rw [chamberPt_empty_rep] at h
  exact hw h

/-- The apex of an unmarked chamber, as a cell of `Z`. -/
noncomputable def zApex {w : CayGroup A} (hw : ¬ M w) : Zpos A X M att :=
  zOld (chamberPt w (isSimplex_empty (A := A))) (not_isMarkedApex_apex hw)

omit [Fintype V] in
theorem inZChamber_zApex {w : CayGroup A} (hw : ¬ M w) :
    InZChamber w (zApex (X := X) (att := att) hw) :=
  chamberPt_inChamber w (isSimplex_empty (A := A))

omit [Fintype V] in
/-- The apex is the least cell of an unmarked chamber. -/
theorem zApex_le {w : CayGroup A} (hw : ¬ M w) {z : Zpos A X M att} (hz : InZChamber w z) :
    zApex (X := X) (att := att) hw ≤ z := by
  cases z with
  | inl p =>
      exact le_of_inChamber (chamberPt_inChamber w (isSimplex_empty (A := A))) hz
        (Finset.empty_subset _)
  | inr wx =>
      exact absurd (hz ▸ wx.1.2) hw

omit [Fintype V] in
/-- **An ordinary chamber of `Z` is acyclic**: it is still a cone on its apex. -/
theorem acyclicIn_zchamber_unmarked {w : CayGroup A} (hw : ¬ M w) :
    AcyclicIn (InZChamber (A := A) (X := X) (M := M) (att := att) w) := by
  refine Nerve.acyclicIn_of_subtype _ ⟨_, inZChamber_zApex (X := X) (att := att) hw⟩ ?_
  intro c hc hcyc
  refine Nerve.exists_bdry_eq_of_cycle
    (fun _ => (⟨zApex (X := X) (att := att) hw, inZChamber_zApex hw⟩ :
      {z : Zpos A X M att // InZChamber w z}))
    ⟨zApex (X := X) (att := att) hw, inZChamber_zApex hw⟩
    (fun _ _ _ => le_refl _) (fun q => zApex_le hw q.2) (fun _ => le_refl _) hc hcyc

/-! ### Modified chambers -/

omit [Fintype V] in
/-- **A modified chamber of `Z` is acyclic relative to the copies of the base.**  The retraction
of `RequestProject/ChamberZPoset.lean` lies below the identity and lands in the copy of `X`, so
the prism homotopy applies. -/
theorem acyclicRelIn_zchamber_marked [Nonempty X] {w : CayGroup A} (hw : M w) :
    AcyclicRelIn (InZChamber (A := A) (X := X) (M := M) (att := att) w) InZBase := by
  refine Nerve.acyclicRelIn_of_retraction
    ⟨zNew (att := att) ⟨w, hw⟩ (Classical.arbitrary X), rfl⟩ (zChamberRetr hw)
    (zChamberRetr_monotone hw) (zChamberRetr_le hw) ?_
  intro q
  obtain ⟨x, hx⟩ := zChamberRetr_mem hw q
  rw [hx]
  trivial

omit [Fintype V] in
/-- Either way, a chamber of `Z` is acyclic relative to the copies of the base. -/
theorem acyclicRelIn_zchamber [Nonempty X] (w : CayGroup A) :
    AcyclicRelIn (InZChamber (A := A) (X := X) (M := M) (att := att) w) InZBase := by
  by_cases hw : M w
  · exact acyclicRelIn_zchamber_marked hw
  · exact Nerve.acyclicRelIn_of_acyclicIn (acyclicIn_zchamber_unmarked hw)

/-! ### The attaching intersection -/

/-- The attaching subcomplex of the chamber of `w` inside `Z` is the attaching subcomplex of the
chamber `F_w` of the Davis poset. -/
noncomputable def zJSetOrderIso (w : CayGroup A) :
    {z : Zpos A X M att // ZJSet w z} ≃o ChamberInter A w where
  toFun z :=
    match z with
    | ⟨Sum.inl p, h⟩ => ⟨p.1, (jSet_iff.1 h).1, (jSet_iff.1 h).2⟩
    | ⟨Sum.inr _, h⟩ => h.elim
  invFun q :=
    ⟨zOld q.1 (by
        rintro ⟨hemp, -⟩
        obtain ⟨s, hs⟩ := q.2.2
        rw [hemp] at hs
        simp at hs),
      show JSet w q.1 from jSet_iff.2 ⟨q.2.1, q.2.2⟩⟩
  left_inv z := by
    rcases z with ⟨p | wx, h⟩
    · rfl
    · exact h.elim
  right_inv q := rfl
  map_rel_iff' {z z'} := by
    rcases z with ⟨p | wx, h⟩
    · rcases z' with ⟨q | wy, h'⟩
      · exact Iff.rfl
      · exact h'.elim
    · exact h.elim

/-- **The attaching intersection of a chamber of `Z` is acyclic**: it is `J_w`, contracted by
the mirror contraction. -/
theorem acyclicIn_zJSet {w : CayGroup A} (hw : w ≠ 1) :
    AcyclicIn (ZJSet (A := A) (X := X) (M := M) (att := att) w) := by
  have hz : {z : Zpos A X M att // ZJSet w z} :=
    (zJSetOrderIso (A := A) (X := X) (M := M) (att := att) w).symm (interTop hw)
  refine Nerve.acyclicIn_of_subtype _ ⟨hz.1, hz.2⟩ ?_
  refine Nerve.exists_bdry_eq_of_cycle_of_orderIso (zJSetOrderIso (X := X) (att := att) w) ?_
  intro c hc hcyc
  exact chamberInter_exists_bdry_eq_of_cycle hw hc hcyc

/-! ### The filtration by word length -/

/-- The union of the chambers of `Z` of length at most `n`. -/
def ZUpto (n : ℕ) (z : Zpos A X M att) : Prop := ∃ y : CayGroup A, RACG.clen A y ≤ n ∧ InZChamber y z

omit [Fintype V] in
theorem zUpto_up {n : ℕ} {z z' : Zpos A X M att} (h : z ≤ z') (hz : ZUpto n z) : ZUpto n z' := by
  obtain ⟨y, hy, hyz⟩ := hz
  exact ⟨y, hy, inZChamber_of_le h hyz⟩

omit [Fintype V] in
theorem zUpto_zero_iff (z : Zpos A X M att) : ZUpto 0 z ↔ InZChamber (1 : CayGroup A) z := by
  constructor
  · rintro ⟨y, hy, hyz⟩
    have : y = 1 := (RACG.clen_eq_zero_iff A).1 (Nat.le_zero.1 hy)
    rwa [this] at hyz
  · intro h
    exact ⟨1, by simp, h⟩

/-- **The gluing step for `Z`.** -/
theorem acyclicRelIn_zupto_insert [Nonempty X] (n : ℕ)
    (hprev : AcyclicRelIn (ZUpto (A := A) (X := X) (M := M) (att := att) n) InZBase) :
    ∀ S : Set (CayGroup A), S.Finite → (∀ y ∈ S, RACG.clen A y = n + 1) →
      AcyclicRelIn (fun z : Zpos A X M att => ZUpto n z ∨ ∃ y ∈ S, InZChamber y z) InZBase := by
  intro S hS
  induction S, hS using Set.Finite.induction_on with
  | empty =>
      intro _
      exact Nerve.acyclicRelIn_congr (fun z => by simp) hprev
  | @insert x S hxS hSfin ih =>
      intro hlen
      have hPrevAcyc := ih (fun y hy => hlen y (Set.mem_insert_of_mem _ hy))
      have hxlen : RACG.clen A x = n + 1 := hlen x (Set.mem_insert _ _)
      have hx1 : x ≠ 1 := by
        intro h
        rw [h, clen_one] at hxlen
        omega
      set Prev : Zpos A X M att → Prop :=
        fun z => ZUpto n z ∨ ∃ y ∈ S, InZChamber y z with hPrevDef
      have hup : ∀ z z' : Zpos A X M att, z ≤ z' → Prev z → Prev z' := by
        rintro z z' hzz' (h | ⟨y, hy, hyz⟩)
        · exact Or.inl (zUpto_up hzz' h)
        · exact Or.inr ⟨y, hy, inZChamber_of_le hzz' hyz⟩
      have hinter : ∀ z : Zpos A X M att, (Prev z ∧ InZChamber x z) ↔ ZJSet x z := by
        intro z
        constructor
        · rintro ⟨hprev', hzx⟩
          rcases hprev' with ⟨y, hy, hyz⟩ | ⟨y, hyS, hyz⟩
          · exact (mem_shorter_zchamber_iff hzx).1 ⟨y, by omega, hyz⟩
          · refine (mem_earlier_zchamber_iff hzx).1 ⟨y, ?_, ?_, hyz⟩
            · intro hxy
              exact hxS (hxy ▸ hyS)
            · rw [hlen y (Set.mem_insert_of_mem _ hyS), hxlen]
        · intro hJ
          have hzx : InZChamber x z := zJSet_imp_inZChamber hJ
          obtain ⟨y, hylt, hyz⟩ := (mem_shorter_zchamber_iff hzx).2 hJ
          exact ⟨Or.inl ⟨y, by omega, hyz⟩, hzx⟩
      have hmain : AcyclicRelIn (fun z : Zpos A X M att => Prev z ∨ InZChamber x z) InZBase := by
        refine Nerve.acyclicRelIn_union_of_unmixed (A := Prev)
          (B := InZChamber (A := A) (X := X) (M := M) (att := att) x)
          (fun _ => Iff.rfl) ?_ hPrevAcyc (acyclicRelIn_zchamber x)
          (Nerve.acyclicIn_congr (fun z => (hinter z).symm) (acyclicIn_zJSet hx1))
        rintro a b hab (ha | ha) hb
        · exact Or.inl ⟨ha, hup a b hab ha⟩
        · exact Or.inr ⟨ha, inZChamber_of_le hab ha⟩
      refine Nerve.acyclicRelIn_congr (fun z => ?_) hmain
      constructor
      · rintro ((h | ⟨y, hy, hyz⟩) | h)
        · exact Or.inl h
        · exact Or.inr ⟨y, Set.mem_insert_of_mem _ hy, hyz⟩
        · exact Or.inr ⟨x, Set.mem_insert _ _, h⟩
      · rintro (h | ⟨y, hy, hyz⟩)
        · exact Or.inl (Or.inl h)
        · rcases Set.mem_insert_iff.1 hy with rfl | hy
          · exact Or.inr hyz
          · exact Or.inl (Or.inr ⟨y, hy, hyz⟩)

/-- **Every cycle supported on the first `n` length levels of chambers of `Z` is a base cycle
plus a boundary.** -/
theorem acyclicRelIn_zupto (A : CommRel V) (X : Type u) [Preorder X] [Nonempty X]
    (M : CayGroup A → Prop) (att : NeSpx A →o X) :
    ∀ n : ℕ, AcyclicRelIn (ZUpto (A := A) (X := X) (M := M) (att := att) n) InZBase := by
  intro n
  induction n with
  | zero =>
      exact Nerve.acyclicRelIn_congr (fun z => (zUpto_zero_iff z).symm)
        (acyclicRelIn_zchamber 1)
  | succ n ih =>
      have h := acyclicRelIn_zupto_insert n ih {x : CayGroup A | RACG.clen A x = n + 1}
        (level_finite A (n + 1)) (fun _ hy => hy)
      refine Nerve.acyclicRelIn_congr (fun z => ?_) h
      constructor
      · rintro (⟨y, hy, hyz⟩ | ⟨y, hy, hyz⟩)
        · exact ⟨y, by omega, hyz⟩
        · exact ⟨y, le_of_eq hy, hyz⟩
      · rintro ⟨y, hy, hyz⟩
        rcases Nat.lt_or_ge (RACG.clen A y) (n + 1) with h' | h'
        · exact Or.inl ⟨y, by omega, hyz⟩
        · exact Or.inr ⟨y, le_antisymm hy h', hyz⟩

/-! ### The whole complex -/

/-- The length of the chamber a cell of `Z` belongs to. -/
noncomputable def zlen : Zpos A X M att → ℕ
  | Sum.inl p => RACG.clen A p.1.rep
  | Sum.inr wx => RACG.clen A wx.1.1

omit [Fintype V] in
theorem zUpto_zlen (z : Zpos A X M att) : ZUpto (zlen z) z := by
  cases z with
  | inl p => exact ⟨p.1.rep, le_refl _, inChamber_rep p.1⟩
  | inr wx => exact ⟨wx.1.1, le_refl _, rfl⟩

noncomputable def zChainBound (z : Nerve.Ch (Zpos A X M att)) : ℕ :=
  z.support.sup (fun l => (l.map (fun q : Zpos A X M att => zlen q)).sum)

omit [Fintype V] in
theorem mem_incOn_zupto_zChainBound {z : Nerve.Ch (Zpos A X M att)}
    (hz : z ∈ Nerve.Inc (Zpos A X M att)) :
    z ∈ Nerve.IncOn (ZUpto (A := A) (X := X) (M := M) (att := att) (zChainBound z)) := by
  rw [Nerve.mem_incOn_iff]
  intro l hl
  refine ⟨(Nerve.mem_inc_iff z).1 hz l hl, ?_⟩
  intro q hq
  obtain ⟨y, hy, hyq⟩ := zUpto_zlen q
  refine ⟨y, ?_, hyq⟩
  have h1 : zlen q ≤ (l.map (fun r : Zpos A X M att => zlen r)).sum :=
    List.single_le_sum (fun _ _ => Nat.zero_le _) _ (List.mem_map_of_mem hq)
  refine le_trans hy (le_trans h1 ?_)
  exact Finset.le_sup
    (f := fun l : List (Zpos A X M att) => (l.map (fun q : Zpos A X M att => zlen q)).sum) hl

/-- **The homology of `Z` comes from the copies of the base.**  Every increasing cycle of the
augmented simplicial chain complex of `Z`, in every degree, is the sum of an increasing cycle
supported on the adjoined copies of the base poset and the boundary of an increasing chain of
`Z`.  Ordinary chambers contribute nothing; each modified chamber contributes exactly the cycles
of its copy of the base. -/
theorem exists_base_cycle_of_cycle [Nonempty X] {z : Nerve.Ch (Zpos A X M att)}
    (hz : z ∈ Nerve.Inc (Zpos A X M att)) (hcyc : Nerve.bdry z = 0) :
    ∃ c ∈ Nerve.IncOn (InZBase (A := A) (X := X) (M := M) (att := att)),
      ∃ y ∈ Nerve.Inc (Zpos A X M att), Nerve.bdry c = 0 ∧ z = c + Nerve.bdry y := by
  obtain ⟨c, hc, y, hy, hdc, hzc⟩ :=
    acyclicRelIn_zupto A X M att (zChainBound z) z (mem_incOn_zupto_zChainBound hz) hcyc
  exact ⟨c, hc, y, Nerve.incOn_le_inc _ hy, hdc, hzc⟩

end Davis
end FiniteChains
