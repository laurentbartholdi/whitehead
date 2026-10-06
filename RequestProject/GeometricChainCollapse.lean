import RequestProject.CutSurfaceSpine

/-! Chosen free faces of geometric collapses, retained alongside their chain retractions. -/

namespace FiniteChains.Collapse
variable {T F : Type*} [DecidableEq T] (inc : F → Finset T)

/-- Each pair records the actual free face at the time its top cell is removed. -/
def IsPairCollapse : List (T × F) → Finset T → Prop
  | [], S => S = ∅
  | (t, f) :: lp, S => t ∈ S ∧ IsFree inc S f t ∧ IsPairCollapse lp (S.erase t)

variable {inc}

/-- The actual top cells left after deleting a prefix of recorded cell pairs. -/
def remainingTops : Finset T → List (T × F) → Finset T
  | S, [] => S
  | S, p :: lp => remainingTops (S.erase p.1) lp

theorem mem_remainingTops (S : Finset T) (lp : List (T × F)) (t : T) :
    t ∈ remainingTops S lp ↔ t ∈ S ∧ t ∉ lp.map Prod.fst := by
  induction lp generalizing S with
  | nil => simp [remainingTops]
  | cons p lp ih =>
    simp only [remainingTops, ih, Finset.mem_erase, List.map_cons, List.mem_cons]
    tauto

theorem IsPairCollapse.suffix {left right : List (T × F)} {S : Finset T}
    (h : IsPairCollapse inc (left ++ right) S) :
    IsPairCollapse inc right (remainingTops S left) := by
  induction left generalizing S with
  | nil => exact h
  | cons p left ih => exact ih h.2.2

theorem IsPairCollapse.top_mem {lp : List (T × F)} {S : Finset T}
    (h : IsPairCollapse inc lp S) {p : T × F} (hp : p ∈ lp) : p.1 ∈ S := by
  induction lp generalizing S with
  | nil => simp at hp
  | cons q lp ih =>
    rcases List.mem_cons.mp hp with rfl | hp
    · exact h.1
    · exact Finset.mem_of_mem_erase (ih h.2.2 hp)

theorem IsPairCollapse.map_fst {lp : List (T × F)} {S : Finset T}
    (h : IsPairCollapse inc lp S) : IsCollapse inc (lp.map Prod.fst) S := by
  induction lp generalizing S with
  | nil => exact h
  | cons p lp ih => exact ⟨h.1, ⟨p.2, h.2.1⟩, ih h.2.2⟩

theorem IsPairCollapse.pair_inc {lp : List (T × F)} {S : Finset T}
    (h : IsPairCollapse inc lp S) {p : T × F} (hp : p ∈ lp) : p.1 ∈ inc p.2 := by
  induction lp generalizing S with
  | nil => simp at hp
  | cons q lp ih =>
    rcases List.mem_cons.mp hp with rfl | hp
    · have hm : p.1 ∈ inc p.2 ∩ S := by
        rw [h.2.1]
        exact Finset.mem_singleton_self _
      exact (Finset.mem_inter.mp hm).1
    · exact ih h.2.2 hp

/-- No later top cell meets the face deleted by the first elementary collapse. -/
theorem IsPairCollapse.later_top_not_inc {t : T} {f : F} {lp : List (T × F)}
    {S : Finset T} (h : IsPairCollapse inc ((t, f) :: lp) S)
    {p : T × F} (hp : p ∈ lp) : p.1 ∉ inc f := by
  intro hi
  have hs := h.2.2.top_mem hp
  have hm := Finset.mem_inter.mpr ⟨hi, Finset.mem_of_mem_erase hs⟩
  rw [h.2.1] at hm
  exact (Finset.mem_erase.mp hs).1 (Finset.mem_singleton.mp hm)

/-- Earlier deleted faces never occur on the boundary of any later top cell. -/
theorem IsPairCollapse.prefix_faces_avoid_suffix_tops {left right : List (T × F)}
    {S : Finset T} (h : IsPairCollapse inc (left ++ right) S)
    {p r : T × F} (hp : p ∈ left) (hr : r ∈ right) : r.1 ∉ inc p.2 := by
  induction left generalizing S with
  | nil => simp at hp
  | cons a left ih =>
    rcases List.mem_cons.mp hp with rfl | hp
    · exact h.later_top_not_inc (List.mem_append.mpr (Or.inr hr))
    · exact ih h.2.2 hp

/-- A chosen face cannot be removed twice: its later incident cell would contradict freeness. -/
theorem IsPairCollapse.faces_nodup {lp : List (T × F)} {S : Finset T}
    (h : IsPairCollapse inc lp S) : (lp.map Prod.snd).Nodup := by
  induction lp generalizing S with
  | nil => exact List.nodup_nil
  | cons p lp ih =>
    apply List.nodup_cons.mpr
    refine ⟨?_, ih h.2.2⟩
    intro hm
    obtain ⟨q, hq, hqf⟩ := List.mem_map.mp hm
    have hi := h.2.2.pair_inc hq
    rw [hqf] at hi
    have hs := h.2.2.top_mem hq
    have hqt : q.1 = p.1 := by
      have hh : q.1 ∈ inc p.2 ∩ S :=
        Finset.mem_inter.mpr ⟨hi, Finset.mem_of_mem_erase hs⟩
      rw [h.2.1] at hh
      exact Finset.mem_singleton.mp hh
    exact (Finset.mem_erase.mp hs).1 hqt

theorem IsPairCollapse.tops_nodup {lp : List (T × F)} {S : Finset T}
    (h : IsPairCollapse inc lp S) : (lp.map Prod.fst).Nodup := by
  induction lp generalizing S with
  | nil => exact List.nodup_nil
  | cons p lp ih =>
    apply List.nodup_cons.mpr
    refine ⟨?_, ih h.2.2⟩
    intro hm
    obtain ⟨q, hq, hqt⟩ := List.mem_map.mp hm
    have hs := h.2.2.top_mem hq
    exact (Finset.mem_erase.mp hs).1 hqt

theorem IsPairCollapse.covers {lp : List (T × F)} {S : Finset T}
    (h : IsPairCollapse inc lp S) {t : T} (ht : t ∈ S) : ∃ f, (t, f) ∈ lp := by
  have hm := mem_list_of_isCollapse h.map_fst t ht
  obtain ⟨p, hp, he⟩ := List.mem_map.mp hm
  exact ⟨p.2, by simpa only [← he, Prod.eta] using hp⟩

/-- Choose the free faces without losing their geometric certificates. -/
theorem exists_pairCollapse {l : List T} {S : Finset T} (h : IsCollapse inc l S) :
    ∃ lp : List (T × F), lp.map Prod.fst = l ∧ IsPairCollapse inc lp S := by
  induction l generalizing S with
  | nil => exact ⟨[], rfl, h⟩
  | cons t l ih =>
    obtain ⟨ht, ⟨f, hf⟩, hr⟩ := h
    obtain ⟨lp, hm, hp⟩ := ih hr
    exact ⟨(t, f) :: lp, by simp [hm], ht, hf, hp⟩

/-- A genuine free-face collapse is also an oriented chain collapse whenever the
differential has unit incidences and vanishes outside actual face incidences. -/
theorem IsPairCollapse.chainCollapse {R : Type*} [Ring R]
    {d : T → F → R} {tops S : Finset T} {lp : List (T × F)}
    (hunit : ∀ t ∈ tops, ∀ f, t ∈ inc f → IsUnit (d t f))
    (hzero : ∀ t ∈ tops, ∀ f, t ∉ inc f → d t f = 0)
    (hS : S ⊆ tops) (h : IsPairCollapse inc lp S) : CollapseChain.IsChainCollapse d lp := by
  induction lp generalizing S with
  | nil => trivial
  | cons p lp ih =>
    have hpinc : p.1 ∈ inc p.2 := by
      have hm : p.1 ∈ inc p.2 ∩ S := by
        rw [h.2.1]
        exact Finset.mem_singleton_self _
      exact (Finset.mem_inter.mp hm).1
    refine ⟨hunit p.1 (hS h.1) p.2 hpinc, ?_,
      ih (fun t ht => hS (Finset.mem_of_mem_erase ht)) h.2.2⟩
    intro q hq
    have hqS := h.2.2.top_mem hq
    apply hzero q.1 (hS (Finset.mem_of_mem_erase hqS)) p.2
    intro hqi
    have hqt : q.1 = p.1 := by
      have hm : q.1 ∈ inc p.2 ∩ S :=
        Finset.mem_inter.mpr ⟨hqi, Finset.mem_of_mem_erase hqS⟩
      rw [h.2.1] at hm
      exact Finset.mem_singleton.mp hm
    exact (Finset.mem_erase.mp hqS).1 hqt

end FiniteChains.Collapse

namespace FiniteChains
variable {V : Type} [Fintype V] [DecidableEq V] [LinearOrder V]

/-- Both geometric and chain certificates for the very same chosen cubical collapse. -/
theorem exists_geometric_chainCollapse {L : ASC V} {l : List (Cube V)}
    {S : Finset (Cube V)} (hS : S ⊆ topCubes L)
    (h : Collapse.IsCollapse (spineInc L) l S) :
    ∃ lp : List (Cube V × (Cube V ⊕ Finset V)), lp.map Prod.fst = l ∧
      Collapse.IsPairCollapse (spineInc L) lp S ∧
      CollapseChain.IsChainCollapse (cubeBdry (V := V)) lp := by
  obtain ⟨lp, hm, hp⟩ := Collapse.exists_pairCollapse h
  refine ⟨lp, hm, hp, hp.chainCollapse ?_ ?_ hS⟩
  · intro t ht f htf
    cases f with
    | inl g =>
      by_cases hg : (freeSet g).card = 2
      · rw [spineInc, if_pos hg] at htf
        rcases cubeBdry_inl_eq_unit htf with h | h <;> rw [h] <;> simp
      · simp [spineInc, hg] at htf
    | inr σ =>
      by_cases hσ : IsTri L σ
      · rw [spineInc, if_pos hσ, Finset.mem_singleton] at htf
        subst t
        rw [cubeBdry_inr_eq_neg_one hσ.2]
        simp
      · simp [spineInc, hσ] at htf
  · intro t ht f htf
    cases f with
    | inl g =>
      apply cubeBdry_inl_eq_zero ht
      intro hg
      have hcard : (freeSet g).card = 2 := by
        obtain ⟨j, hj, _, he⟩ := mem_cofaces.mp hg
        have hfree : freeSet t = insert j (freeSet g) := by
          rw [he]
          exact freeSet_update_free g j
        have htop := (mem_topCubes.mp ht).2
        rw [hfree, Finset.card_insert_of_notMem (by simpa [mem_freeSet] using hj)] at htop
        omega
      exact htf (by simpa [spineInc, hcard] using hg)
    | inr σ =>
      apply cubeBdry_inr_eq_zero
      intro he
      have hσ : IsTri L σ := by simpa [he] using mem_topCubes.mp ht
      exact htf (by simp [spineInc, hσ, he])

end FiniteChains
