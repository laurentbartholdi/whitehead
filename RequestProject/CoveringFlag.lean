import RequestProject.FlagComplex

/-!
# Coverings of flag complexes are flag

Step 2 of the generation lemma (Lemma `lem:geometric-pushout` of the paper) needs the
following combinatorial fact about the links appearing in the collapsed space `V`:

> "At a new vertex the link is a disjoint union of covers of `L_q`.  Each cover is flag.
> A clique projects to a clique of distinct vertices in `L_q`; its simplex lifts because
> its triangular faces are simply connected.  The lifted simplex contains the original
> clique.  A disjoint union of flag complexes is flag."

The second half ("a disjoint union of flag complexes is flag") is
`FiniteChains.ASC.isFlag_of_fibres` in `RequestProject/FlagComplex.lean`.  This file proves
the first half: *a simplicial covering of a flag complex is flag*.

A simplicial covering is recorded combinatorially by the two properties of a covering map
that the argument uses: it is injective on the closed star of each vertex, and every face
of the base containing the image of a vertex `v` lifts to a face containing `v`.
-/

namespace FiniteChains

namespace ASC

universe u

variable {V W : Type u} [DecidableEq V] [DecidableEq W]

/-- A *combinatorial covering* `p : K → L` of abstract simplicial complexes: `p` is
simplicial, injective on the closed star of every vertex, and every face of `L` through
`p v` lifts to a face of `K` through `v`. -/
structure IsCovering (K : ASC V) (L : ASC W) (p : V → W) : Prop where
  /-- `p` is simplicial: the image of a face is a face. -/
  map_face : ∀ s ∈ K.faces, s.image p ∈ L.faces
  /-- `p` is injective on the closed star of each vertex. -/
  star_inj : ∀ {v x y : V}, ({v, x} : Finset V) ∈ K.faces → ({v, y} : Finset V) ∈ K.faces →
    p x = p y → x = y
  /-- Faces of `L` lift: every face of `L` containing `p v` is the image of a face of `K`
  containing `v`. -/
  lift : ∀ {v : V}, ({v} : Finset V) ∈ K.faces → ∀ t ∈ L.faces, p v ∈ t →
    ∃ s ∈ K.faces, v ∈ s ∧ s.image p = t

variable {K : ASC V} {L : ASC W} {p : V → W}

/-- A clique of a covering complex maps to a clique of the base. -/
theorem IsCovering.image_clique (hp : IsCovering K L p) {s : Finset V}
    (hs : ∀ t ⊆ s, t.card ≤ 2 → t ∈ K.faces) :
    ∀ u ⊆ s.image p, u.card ≤ 2 → u ∈ L.faces := by
  classical
  intro u hu hcard
  -- every vertex of `u` is `p x` for some `x ∈ s`; pick such preimages
  interval_cases h : u.card
  · rw [Finset.card_eq_zero] at h
    subst h
    exact L.empty_mem
  · obtain ⟨w, rfl⟩ := Finset.card_eq_one.mp h
    obtain ⟨x, hx, hxw⟩ := Finset.mem_image.mp (hu (Finset.mem_singleton_self w))
    have hxface : ({x} : Finset V) ∈ K.faces := by
      refine hs {x} ?_ (by simp)
      simpa using hx
    have himg := hp.map_face _ hxface
    simpa [hxw] using himg
  · obtain ⟨w₁, w₂, hne, rfl⟩ := Finset.card_eq_two.mp h
    obtain ⟨x₁, hx₁, hxw₁⟩ :=
      Finset.mem_image.mp (hu (by simp : w₁ ∈ ({w₁, w₂} : Finset W)))
    obtain ⟨x₂, hx₂, hxw₂⟩ :=
      Finset.mem_image.mp (hu (by simp : w₂ ∈ ({w₁, w₂} : Finset W)))
    have hsub : ({x₁, x₂} : Finset V) ⊆ s := by
      intro z hz
      simp only [Finset.mem_insert, Finset.mem_singleton] at hz
      rcases hz with rfl | rfl <;> assumption
    have hface : ({x₁, x₂} : Finset V) ∈ K.faces :=
      hs {x₁, x₂} hsub ((Finset.card_insert_le _ _).trans (by simp))
    have himg := hp.map_face _ hface
    simpa [hxw₁, hxw₂] using himg

/-- **A combinatorial covering of a flag complex is flag.** -/
theorem IsFlag.of_covering (hp : IsCovering K L p) (hL : L.IsFlag) : K.IsFlag := by
  classical
  intro s hs
  rcases s.eq_empty_or_nonempty with rfl | ⟨v, hv⟩
  · exact K.empty_mem
  -- the image clique spans a face of `L`
  have htface : s.image p ∈ L.faces := hL (s.image p) (hp.image_clique hs)
  have hvface : ({v} : Finset V) ∈ K.faces :=
    hs {v} (by simpa using hv) (by simp)
  have hpv : p v ∈ s.image p := Finset.mem_image_of_mem _ hv
  obtain ⟨σ, hσ, hvσ, himg⟩ := hp.lift hvface _ htface hpv
  -- the lift contains the original clique
  have hsub : s ⊆ σ := by
    intro x hx
    have : p x ∈ σ.image p := by rw [himg]; exact Finset.mem_image_of_mem _ hx
    obtain ⟨y, hy, hxy⟩ := Finset.mem_image.mp this
    have hvy : ({v, y} : Finset V) ∈ K.faces := by
      refine K.down_closed hσ ?_
      intro z hz
      simp only [Finset.mem_insert, Finset.mem_singleton] at hz
      rcases hz with rfl | rfl <;> assumption
    have hvx : ({v, x} : Finset V) ∈ K.faces := by
      refine hs {v, x} ?_ ((Finset.card_insert_le _ _).trans (by simp))
      intro z hz
      simp only [Finset.mem_insert, Finset.mem_singleton] at hz
      rcases hz with rfl | rfl <;> assumption
    have : y = x := hp.star_inj hvy hvx hxy
    exact this ▸ hy
  exact K.down_closed hσ hsub

/-- The identity is a covering; in particular the notion is not vacuous. -/
theorem isCovering_id (K : ASC V) : IsCovering K K id where
  map_face := by
    intro s hs
    simpa using hs
  star_inj := by
    intro v x y _ _ h
    simpa using h
  lift := by
    intro v _ t ht hv
    exact ⟨t, ht, hv, by simp⟩

/-- **The link of a new vertex is flag.**  This is the combination used in Step 2 of the
generation lemma: a complex which splits into components (the fibres of `c`), each of which
is a combinatorial covering of one fixed flag complex `L`, is flag. -/
theorem isFlag_of_fibre_coverings {ι : Type u} (K : ASC V) (L : ASC W) (c : V → ι)
    (hsep : ∀ s ∈ K.faces, ∀ x ∈ s, ∀ y ∈ s, c x = c y)
    (hL : L.IsFlag)
    (hcov : ∀ i, ∃ p : V → W, IsCovering (K.restrict (fun x => c x = i)) L p) :
    K.IsFlag := by
  refine K.isFlag_of_fibres c hsep (fun i => ?_)
  obtain ⟨p, hp⟩ := hcov i
  exact IsFlag.of_covering hp hL

end ASC

end FiniteChains
