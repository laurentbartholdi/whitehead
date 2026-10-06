module

public import RequestProject.RACGGroup

@[expose] public section

/-!
# Length and descents in a right-angled Coxeter group

Building on the normal form theorem of `RequestProject/RACGGroup.lean`, this file introduces the
group `FiniteChains.RACG.CayGroup` of a right-angled Coxeter system, its word length
`FiniteChains.RACG.clen`, the distance `FiniteChains.RACG.cdist` of its Cayley graph and the
left descents `FiniteChains.RACG.IsDesc`.  The main result is the right-angled descent lemma
`FiniteChains.RACG.desc_two`: two distinct left descents of an element commute.
-/

namespace FiniteChains
namespace RACG

universe u

variable {V : Type u} [DecidableEq V] (A : CommRel V)

/-- The group of the right-angled Coxeter system, realised as permutations of the reduced
traces. -/
def CayGroup : Subgroup (Equiv.Perm (Tr A)) := Subgroup.closure (Set.range (actPerm A))

/-- A generator, as an element of the group. -/
noncomputable def gen (s : V) : CayGroup A :=
  ⟨actPerm A s, Subgroup.subset_closure ⟨s, rfl⟩⟩

/-- The word length of an element of the group. -/
noncomputable def clen (x : CayGroup A) : ℕ := len A (x : Equiv.Perm (Tr A))

/-- The distance of the Cayley graph. -/
noncomputable def cdist (x y : CayGroup A) : ℕ := clen A (x⁻¹ * y)

/-- The element of the group determined by a word. -/
noncomputable def cword (l : List V) : CayGroup A :=
  ⟨wordPerm A l, by
    induction l with
    | nil => simp
    | cons a t ih =>
        rw [wordPerm_cons]
        exact Subgroup.mul_mem _ (Subgroup.subset_closure ⟨a, rfl⟩) ih⟩

@[simp] theorem cword_val (l : List V) : ((cword A l : CayGroup A) : Equiv.Perm (Tr A))
    = wordPerm A l := rfl

@[simp] theorem cword_cons (s : V) (l : List V) : cword A (s :: l) = gen A s * cword A l :=
  Subtype.ext (by simp [gen])

@[simp] theorem cword_nil : cword A [] = 1 := Subtype.ext (by simp)

theorem cword_ceq {l m : List V} (h : CEq A.rel l m) : cword A l = cword A m :=
  Subtype.ext (by simpa using wordPerm_ceq A h)

theorem gen_mul_gen (s : V) : gen A s * gen A s = 1 :=
  Subtype.ext (by simpa [gen] using actPerm_mul_self A s)

theorem cword_apply_one {l : List V} (hl : IsRed A.rel l) :
    ((cword A l : CayGroup A) : Equiv.Perm (Tr A)) (oneTr A) = mkTr A l hl :=
  wordPerm_apply_one A hl

theorem exists_cword (x : CayGroup A) : ∃ l : List V, IsRed A.rel l ∧ cword A l = x := by
  obtain ⟨p, hp⟩ : ∃ l : List V, wordPerm A l = (x : Equiv.Perm (Tr A)) := by
    refine Subgroup.closure_induction (p := fun g _ => ∃ l : List V, wordPerm A l = g)
      ?_ ?_ ?_ ?_ x.2
    · rintro g ⟨s, rfl⟩
      exact ⟨[s], by simp⟩
    · exact ⟨[], by simp⟩
    · rintro g h - - ⟨l, rfl⟩ ⟨m, rfl⟩
      exact ⟨l ++ m, by rw [wordPerm_append]⟩
    · rintro g - ⟨l, rfl⟩
      exact ⟨l.reverse, by rw [wordPerm_reverse]⟩
  obtain ⟨m, hm, -, hmp⟩ := exists_isRed_word A p
  exact ⟨m, hm, Subtype.ext (by rw [cword_val, hmp, hp])⟩

/-- The orbit map to the reduced traces is injective on the group. -/
theorem eq_of_apply_one_eq {x y : CayGroup A}
    (h : (x : Equiv.Perm (Tr A)) (oneTr A) = (y : Equiv.Perm (Tr A)) (oneTr A)) : x = y := by
  obtain ⟨l, hl, rfl⟩ := exists_cword A x
  obtain ⟨m, hm, rfl⟩ := exists_cword A y
  rw [cword_apply_one A hl, cword_apply_one A hm] at h
  exact cword_ceq A ((mkTr_eq_iff A hl hm).1 h)

theorem clen_cword {l : List V} (hl : IsRed A.rel l) : clen A (cword A l) = l.length := by
  show trLen A (((cword A l : CayGroup A) : Equiv.Perm (Tr A)) (oneTr A)) = l.length
  rw [cword_apply_one A hl, trLen_mkTr]

theorem clen_eq_zero_iff {x : CayGroup A} : clen A x = 0 ↔ x = 1 := by
  constructor
  · intro h
    obtain ⟨l, hl, rfl⟩ := exists_cword A x
    rw [clen_cword A hl] at h
    have : l = [] := List.eq_nil_of_length_eq_zero h
    simp [this]
  · rintro rfl
    simp [clen, len]

@[simp] theorem clen_one : clen A (1 : CayGroup A) = 0 := (clen_eq_zero_iff A).2 rfl

theorem clen_le_of_cword {l : List V} {x : CayGroup A} (h : cword A l = x) :
    clen A x ≤ l.length := by
  rw [← h]
  exact len_le_length A l

theorem clen_inv (x : CayGroup A) : clen A x⁻¹ = clen A x := by
  have key : ∀ y : CayGroup A, clen A y⁻¹ ≤ clen A y := by
    intro y
    obtain ⟨l, hl, rfl⟩ := exists_cword A y
    have h1 : cword A l.reverse = (cword A l)⁻¹ :=
      Subtype.ext (by simpa using wordPerm_reverse A l)
    have := clen_le_of_cword A h1
    simpa [clen_cword A hl] using this
  have h1 := key x
  have h2 := key x⁻¹
  simp only [inv_inv] at h2
  omega

theorem clen_mul_le (x y : CayGroup A) : clen A (x * y) ≤ clen A x + clen A y := by
  obtain ⟨l, hl, rfl⟩ := exists_cword A x
  obtain ⟨m, hm, rfl⟩ := exists_cword A y
  have h1 : cword A (l ++ m) = cword A l * cword A m :=
    Subtype.ext (by simpa using wordPerm_append A l m)
  have := clen_le_of_cword A h1
  simpa [clen_cword A hl, clen_cword A hm] using this

/-- `s` is a left descent of `x`: multiplying by `s` on the left shortens `x`. -/
def IsDesc (x : CayGroup A) (s : V) : Prop := clen A (gen A s * x) < clen A x

/-- Descents are visible on any reduced word: `s` shortens `x` exactly when it can be moved to
the front of a reduced word for `x`. -/
theorem isDesc_iff_canStart {x : CayGroup A} {l : List V} (hl : IsRed A.rel l)
    (hx : cword A l = x) (s : V) : IsDesc A x s ↔ canStart A.rel s l := by
  subst hx
  by_cases hc : canStart A.rel s l
  · have hpop : gen A s * cword A l = cword A (popStart s l) := by
      have h1 : cword A l = cword A (s :: popStart s l) :=
        cword_ceq A (ceq_popStart A.rel_symm hc)
      rw [h1, cword_cons, ← mul_assoc, gen_mul_gen, one_mul]
    have hred : IsRed A.rel (popStart s l) := isRed_popStart A.rel_irrefl A.rel_symm hl hc
    have hlen : (popStart s l).length + 1 = l.length := length_popStart A.rel_symm hc
    simp only [IsDesc, hpop, clen_cword A hred, clen_cword A hl, hc, iff_true]
    omega
  · have hred : IsRed A.rel (s :: l) := ⟨hl, hc⟩
    have hcons : gen A s * cword A l = cword A (s :: l) := (cword_cons A s l).symm
    simp only [IsDesc, hcons, clen_cword A hred, clen_cword A hl, hc, iff_false,
      List.length_cons, not_lt]
    omega

theorem clen_gen_mul (x : CayGroup A) (s : V) :
    clen A (gen A s * x) + 1 = clen A x ∨ clen A (gen A s * x) = clen A x + 1 := by
  obtain ⟨l, hl, rfl⟩ := exists_cword A x
  by_cases hc : canStart A.rel s l
  · left
    have hpop : gen A s * cword A l = cword A (popStart s l) := by
      have h1 : cword A l = cword A (s :: popStart s l) :=
        cword_ceq A (ceq_popStart A.rel_symm hc)
      rw [h1, cword_cons, ← mul_assoc, gen_mul_gen, one_mul]
    have hred : IsRed A.rel (popStart s l) := isRed_popStart A.rel_irrefl A.rel_symm hl hc
    rw [hpop, clen_cword A hred, clen_cword A hl]
    exact length_popStart A.rel_symm hc
  · right
    have hred : IsRed A.rel (s :: l) := ⟨hl, hc⟩
    rw [← cword_cons, clen_cword A hred, clen_cword A hl]
    simp

theorem clen_gen_mul_of_desc {x : CayGroup A} {s : V} (h : IsDesc A x s) :
    clen A (gen A s * x) + 1 = clen A x := by
  have hlt : clen A (gen A s * x) < clen A x := h
  rcases clen_gen_mul A x s with h' | h'
  · exact h'
  · omega

theorem clen_gen_mul_of_not_desc {x : CayGroup A} {s : V} (h : ¬ IsDesc A x s) :
    clen A (gen A s * x) = clen A x + 1 := by
  have hlt : ¬ clen A (gen A s * x) < clen A x := h
  rcases clen_gen_mul A x s with h' | h'
  · omega
  · exact h'

theorem gen_mul_gen_mul (x : CayGroup A) (s : V) : gen A s * (gen A s * x) = x := by
  rw [← mul_assoc, gen_mul_gen, one_mul]

theorem not_desc_gen_mul {x : CayGroup A} {s : V} (h : IsDesc A x s) :
    ¬ IsDesc A (gen A s * x) s := by
  have hlt : clen A (gen A s * x) < clen A x := h
  intro hcon
  have : clen A (gen A s * (gen A s * x)) < clen A (gen A s * x) := hcon
  rw [gen_mul_gen_mul] at this
  omega

theorem desc_gen_mul_of_not_desc {x : CayGroup A} {s : V} (h : ¬ IsDesc A x s) :
    IsDesc A (gen A s * x) s := by
  have hlt : ¬ clen A (gen A s * x) < clen A x := h
  show clen A (gen A s * (gen A s * x)) < clen A (gen A s * x)
  rw [gen_mul_gen_mul]
  rcases clen_gen_mul A x s with h' | h'
  · omega
  · omega

theorem exists_desc {x : CayGroup A} (hx : x ≠ 1) : ∃ s : V, IsDesc A x s := by
  obtain ⟨l, hl, rfl⟩ := exists_cword A x
  match l, hl with
  | [], _ => exact absurd (cword_nil A) hx
  | a :: t, hl =>
      exact ⟨a, (isDesc_iff_canStart A hl rfl a).2 (Or.inl rfl)⟩

/-- **The right-angled descent lemma.**  Two distinct left descents of an element commute, and
the second one is still a descent after the first has been removed. -/
theorem desc_two {x : CayGroup A} {s r : V} (hsr : s ≠ r) (hs : IsDesc A x s)
    (hr : IsDesc A x r) : A.rel s r ∧ IsDesc A (gen A s * x) r := by
  obtain ⟨l, hl, rfl⟩ := exists_cword A x
  have hcs : canStart A.rel s l := (isDesc_iff_canStart A hl rfl s).1 hs
  have hcr : canStart A.rel r l := (isDesc_iff_canStart A hl rfl r).1 hr
  obtain ⟨hrel, hpopr⟩ := canStart_two A.rel_symm hsr hcs hcr
  refine ⟨hrel, ?_⟩
  have hpop : gen A s * cword A l = cword A (popStart s l) := by
    have h1 : cword A l = cword A (s :: popStart s l) :=
      cword_ceq A (ceq_popStart A.rel_symm hcs)
    rw [h1, cword_cons, ← mul_assoc, gen_mul_gen, one_mul]
  have hred : IsRed A.rel (popStart s l) := isRed_popStart A.rel_irrefl A.rel_symm hl hcs
  rw [hpop]
  exact (isDesc_iff_canStart A hred rfl r).2 hpopr

/-- The left descents of an element pairwise commute. -/
theorem desc_rel {x : CayGroup A} {s r : V} (hsr : s ≠ r) (hs : IsDesc A x s)
    (hr : IsDesc A x r) : A.rel s r := (desc_two A hsr hs hr).1

/-- A descent of a commuting letter survives prefixing. -/
theorem desc_gen_mul_of_rel {x : CayGroup A} {s r : V} (hrel : A.rel s r) (hs : IsDesc A x s) :
    IsDesc A (gen A r * x) s := by
  have hrs : s ≠ r := by rintro rfl; exact A.rel_irrefl s hrel
  obtain ⟨l, hl, rfl⟩ := exists_cword A x
  have hcs : canStart A.rel s l := (isDesc_iff_canStart A hl rfl s).1 hs
  by_cases hcr : canStart A.rel r l
  · obtain ⟨-, hpops⟩ := canStart_two A.rel_symm (Ne.symm hrs) hcr hcs
    have hpop : gen A r * cword A l = cword A (popStart r l) := by
      have h1 : cword A l = cword A (r :: popStart r l) :=
        cword_ceq A (ceq_popStart A.rel_symm hcr)
      rw [h1, cword_cons, ← mul_assoc, gen_mul_gen, one_mul]
    have hred : IsRed A.rel (popStart r l) := isRed_popStart A.rel_irrefl A.rel_symm hl hcr
    rw [hpop]
    exact (isDesc_iff_canStart A hred rfl s).2 hpops
  · have hred : IsRed A.rel (r :: l) := ⟨hl, hcr⟩
    rw [← cword_cons]
    exact (isDesc_iff_canStart A hred rfl s).2 (Or.inr ⟨hrel, hcs⟩)

/-- Elements of length one are the generators. -/
theorem clen_eq_one_iff {x : CayGroup A} : clen A x = 1 ↔ ∃ s : V, x = gen A s := by
  constructor
  · intro h
    obtain ⟨l, hl, rfl⟩ := exists_cword A x
    rw [clen_cword A hl] at h
    obtain ⟨s, rfl⟩ := List.length_eq_one_iff.1 h
    exact ⟨s, by simp⟩
  · rintro ⟨s, rfl⟩
    have : gen A s = cword A [s] := by simp
    rw [this, clen_cword A (by exact ⟨trivial, by simp [canStart]⟩ : IsRed A.rel [s])]
    simp

end RACG
end FiniteChains
