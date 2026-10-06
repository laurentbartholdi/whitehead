module

public import RequestProject.ChamberZCoverDegreeLocal

@[expose] public section

/-! Degree-two generation on actual poset covers of the modified chamber construction. -/
namespace FiniteChains.Davis
open RACG Mirror Comb Nerve
universe u
variable {V : Type u} [DecidableEq V] [Fintype V] {A : CommRel V}
  {X : Type u} [PartialOrder X] [Nonempty X]
  {M : CayGroup A → Prop} {att : NeSpx A →o X}
  {P : Type u} [PartialOrder P] {f : P → Zpos A X M att}

theorem generatesDegreeIn_cover_zupto_insert (hf : IsPosetCover f) (n : ℕ)
    (hprev : GeneratesDegreeIn (fun p : P => ZUpto n (f p))
      (fun p => InZBase (f p)) 3) :
    ∀ S : Set (CayGroup A), S.Finite → (∀ y ∈ S, RACG.clen A y = n + 1) →
      GeneratesDegreeIn
        (fun p : P => ZUpto n (f p) ∨ ∃ y ∈ S, InZChamber y (f p))
        (fun p => InZBase (f p)) 3 := by
  intro S hS
  induction S, hS using Set.Finite.induction_on with
  | empty =>
      intro _
      exact generatesDegreeIn_congr (fun p => by simp) hprev
  | @insert x S hxS hSfin ih =>
      intro hlen
      have hPrevGen := ih (fun y hy => hlen y (Set.mem_insert_of_mem _ hy))
      have hxlen : RACG.clen A x = n + 1 := hlen x (Set.mem_insert _ _)
      have hx1 : x ≠ 1 := by
        intro h
        rw [h, clen_one] at hxlen
        omega
      let Prev : P → Prop := fun p => ZUpto n (f p) ∨ ∃ y ∈ S, InZChamber y (f p)
      have hup : ∀ p q : P, p ≤ q → Prev p → Prev q := by
        rintro p q hpq (h | ⟨y, hy, hyp⟩)
        · exact Or.inl (zUpto_up (hf.mono hpq) h)
        · exact Or.inr ⟨y, hy, inZChamber_of_le (hf.mono hpq) hyp⟩
      have hinter : ∀ p : P, (Prev p ∧ InZChamber x (f p)) ↔ ZJSet x (f p) := by
        intro p
        constructor
        · rintro ⟨hprev', hpx⟩
          rcases hprev' with ⟨y, hy, hyp⟩ | ⟨y, hyS, hyp⟩
          · exact (mem_shorter_zchamber_iff hpx).1 ⟨y, by omega, hyp⟩
          · refine (mem_earlier_zchamber_iff hpx).1 ⟨y, ?_, ?_, hyp⟩
            · intro hxy
              exact hxS (hxy ▸ hyS)
            · rw [hlen y (Set.mem_insert_of_mem _ hyS), hxlen]
        · intro hJ
          have hpx : InZChamber x (f p) := zJSet_imp_inZChamber hJ
          obtain ⟨y, hylt, hyp⟩ := (mem_shorter_zchamber_iff hpx).2 hJ
          exact ⟨Or.inl ⟨y, by omega, hyp⟩, hpx⟩
      have hmain : GeneratesDegreeIn
          (fun p : P => Prev p ∨ InZChamber x (f p)) (fun p => InZBase (f p)) 3 := by
        refine generatesDegreeIn_union_of_unmixed (n := 2) (A := Prev)
          (B := fun p => InZChamber x (f p)) (fun _ => Iff.rfl) ?_
          hPrevGen (generatesDegreeIn_cover_chamber hf x)
          (fillsDegreeIn_congr (fun p => (hinter p).symm)
            (fillsDegreeIn_cover_attaching_intersection hf x hx1))
        rintro p q hpq (hp | hp) _
        · exact Or.inl ⟨hp, hup p q hpq hp⟩
        · exact Or.inr ⟨hp, inZChamber_of_le (hf.mono hpq) hp⟩
      refine generatesDegreeIn_congr (fun p => ?_) hmain
      constructor
      · rintro ((h | ⟨y, hy, hyp⟩) | h)
        · exact Or.inl h
        · exact Or.inr ⟨y, Set.mem_insert_of_mem _ hy, hyp⟩
        · exact Or.inr ⟨x, Set.mem_insert _ _, h⟩
      · rintro (h | ⟨y, hy, hyp⟩)
        · exact Or.inl (Or.inl h)
        · rcases Set.mem_insert_iff.1 hy with rfl | hy
          · exact Or.inr hyp
          · exact Or.inl (Or.inr ⟨y, hy, hyp⟩)

theorem generatesDegreeIn_cover_zupto (hf : IsPosetCover f) :
    ∀ n : ℕ, GeneratesDegreeIn (fun p : P => ZUpto n (f p))
      (fun p => InZBase (f p)) 3 := by
  intro n
  induction n with
  | zero =>
      exact generatesDegreeIn_congr (fun p => (zUpto_zero_iff (f p)).symm)
        (generatesDegreeIn_cover_chamber hf 1)
  | succ n ih =>
      have h := generatesDegreeIn_cover_zupto_insert hf n ih
        {x : CayGroup A | RACG.clen A x = n + 1} (level_finite A (n + 1)) (fun _ hy => hy)
      refine generatesDegreeIn_congr (fun p => ?_) h
      constructor
      · rintro (⟨y, hy, hyp⟩ | ⟨y, hy, hyp⟩)
        · exact ⟨y, by omega, hyp⟩
        · exact ⟨y, le_of_eq hy, hyp⟩
      · rintro ⟨y, hy, hyp⟩
        rcases Nat.lt_or_ge (RACG.clen A y) (n + 1) with h' | h'
        · exact Or.inl ⟨y, by omega, hyp⟩
        · exact Or.inr ⟨y, le_antisymm hy h', hyp⟩

noncomputable def coverChainBound (c : Nerve.Ch P) : ℕ :=
  c.support.sup (fun l => (l.map (fun p => zlen (f p))).sum)

omit [Fintype V] [Nonempty X] in
theorem mem_incOn_cover_bound {c : Nerve.Ch P} (hc : c ∈ Nerve.Inc P) :
    c ∈ IncOn (fun p => ZUpto (coverChainBound (f := f) c) (f p)) := by
  rw [mem_incOn_iff]
  intro l hl
  refine ⟨(mem_inc_iff c).1 hc l hl, ?_⟩
  intro p hp
  obtain ⟨y, hy, hyp⟩ := zUpto_zlen (f p)
  refine ⟨y, ?_, hyp⟩
  have h1 : zlen (f p) ≤ (l.map (fun q => zlen (f q))).sum :=
    List.single_le_sum (fun _ _ => Nat.zero_le _) _ (List.mem_map_of_mem hp)
  exact hy.trans (h1.trans (Finset.le_sup
    (f := fun l : List P => (l.map (fun q => zlen (f q))).sum) hl))

/-- Every homogeneous two-cycle in an actual covering poset is a cycle on the
actual preimage of the inserted bases plus a genuine finite three-boundary. -/
theorem exists_cover_base_twoCycle (hf : IsPosetCover f) {c : Nerve.Ch P}
    (hc : c ∈ Nerve.Inc P) (hd : lengthProjection 3 c = c) (hcyc : Nerve.bdry c = 0) :
    ∃ d ∈ IncOn (fun p => InZBase (f p)), ∃ y ∈ Nerve.Inc P,
      Nerve.bdry d = 0 ∧ c = d + Nerve.bdry y := by
  obtain ⟨d, hdb, y, hy, hdd, he⟩ := generatesDegreeIn_cover_zupto hf
    (coverChainBound (f := f) c) c (mem_incOn_cover_bound hc) hd hcyc
  exact ⟨d, hdb, y, incOn_le_inc _ hy, hdd, he⟩

end FiniteChains.Davis
