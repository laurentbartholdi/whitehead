module

public import RequestProject.GeometricChainCollapse

@[expose] public section

/-! Positive corner cubes may always be collapsed across their own cut facets. -/
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains
variable {V : Type} [Fintype V] [DecidableEq V] [LinearOrder V]

noncomputable def preferCutFace (p : Cube V × (Cube V ⊕ Finset V)) :
    Cube V × (Cube V ⊕ Finset V) := by
  classical
  exact if p.1 = posCube (freeSet p.1) then (p.1, Sum.inr (freeSet p.1)) else p

noncomputable def preferCutFaces (lp : List (Cube V × (Cube V ⊕ Finset V))) :=
  lp.map preferCutFace

omit [LinearOrder V] in
theorem preferCutFaces_tops (lp : List (Cube V × (Cube V ⊕ Finset V))) :
    (preferCutFaces lp).map Prod.fst = lp.map Prod.fst := by
  classical
  simp only [preferCutFaces, List.map_map]
  congr 1
  funext p
  dsimp only [Function.comp_def]
  unfold preferCutFace
  split <;> rfl

omit [LinearOrder V] in
theorem preferCutFaces_positive_pair {lp : List (Cube V × (Cube V ⊕ Finset V))}
    {p : Cube V × (Cube V ⊕ Finset V)} (hp : p ∈ preferCutFaces lp)
    (hpos : p.1 = posCube (freeSet p.1)) : p.2 = Sum.inr (freeSet p.1) := by
  classical
  obtain ⟨r, _, he⟩ := List.mem_map.mp hp
  subst p
  by_cases hr : r.1 = posCube (freeSet r.1)
  · simp only [preferCutFace, if_pos hr]
  · have hbad : r.1 = posCube (freeSet r.1) := by
      simpa [Collapse.IsPairCollapse,preferCutFace, if_neg hr] using hpos
    exact False.elim (hr hbad)

omit [LinearOrder V] in
theorem preferCutFaces_isPairCollapse {L : ASC V}
    {lp : List (Cube V × (Cube V ⊕ Finset V))} {S : Finset (Cube V)}
    (hS : S ⊆ topCubes L) (h : Collapse.IsPairCollapse (spineInc L) lp S) :
    Collapse.IsPairCollapse (spineInc L) (preferCutFaces lp) S := by
  classical
  induction lp generalizing S with
  | nil => exact h
  | cons p lp ih =>
    have ht := mem_topCubes.mp (hS h.1)
    have hrest := ih (fun t ht => hS (Finset.mem_of_mem_erase ht)) h.2.2
    by_cases hp : p.1 = posCube (freeSet p.1)
    · simp only [preferCutFaces, List.map_cons, preferCutFace, if_pos hp]
      refine ⟨h.1, ?_, hrest⟩
      change spineInc L (Sum.inr (freeSet p.1)) ∩ S = {p.1}
      rw [spineInc, if_pos ht, ← hp]
      exact Finset.singleton_inter_of_mem h.1
    · simpa [Collapse.IsPairCollapse,preferCutFaces, List.map_cons, preferCutFace, if_neg hp] using
        And.intro h.1 (And.intro h.2.1 hrest)

/-- The oriented chain certificate is determined by the actual free-face incidences. -/
theorem spine_pair_chainCollapse {L : ASC V}
    {lp : List (Cube V × (Cube V ⊕ Finset V))} {S : Finset (Cube V)}
    (hS : S ⊆ topCubes L) (h : Collapse.IsPairCollapse (spineInc L) lp S) :
    CollapseChain.IsChainCollapse (cubeBdry (V := V)) lp := by
  apply h.chainCollapse (tops := topCubes L) ?_ ?_ hS
  · intro t ht f htf
    cases f with
    | inl g =>
      by_cases hg : (freeSet g).card = 2
      · rw [spineInc, if_pos hg] at htf
        rcases cubeBdry_inl_eq_unit htf with hh | hh <;> rw [hh] <;> simp
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

theorem preferCutFaces_isChainCollapse {L : ASC V}
    {lp : List (Cube V × (Cube V ⊕ Finset V))} {S : Finset (Cube V)}
    (hS : S ⊆ topCubes L) (h : Collapse.IsPairCollapse (spineInc L) lp S) :
    CollapseChain.IsChainCollapse (cubeBdry (V := V)) (preferCutFaces lp) :=
  spine_pair_chainCollapse hS (preferCutFaces_isPairCollapse hS h)

end FiniteChains
