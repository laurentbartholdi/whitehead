module

public import RequestProject.RACGMedian
public import RequestProject.CubeMedianGraph

@[expose] public section

/-!
# The Cayley graph of a right-angled Coxeter group is a median graph

This file assembles `RequestProject/RACGMedian.lean` into the interface
`FiniteChains.MedianGraph` used by `RequestProject/CubeMedianGraph.lean`, that is, into the
CAT(0) input of the paper in its standard combinatorial form.

* `FiniteChains.RACG.medianGraph` — for a commutation graph without cliques of four vertices
  (equivalently: for a cube complex of dimension at most three) the Cayley graph of the
  right-angled Coxeter group, with the word metric, is a median graph;
* `FiniteChains.RACG.cycles_bound` — consequently every two-cycle of its cellular chain complex
  bounds, which is exactly the vanishing `H₂(V) = 0` used in the generation lemma of the paper.

Together with `RequestProject/MedianSimplyConnected.lean` (the converse implication: the square
complex of a median graph is simply connected with flag links) this makes Gromov's criterion a
theorem for the cube complexes `C(L)` of the paper: the one-skeleton of the universal cover of
`C(L)` is the Cayley graph above.
-/

namespace FiniteChains
namespace RACG

universe u

variable {V : Type u} [DecidableEq V] (A : CommRel V)

/-- An arbitrary linear order on the group, needed only to orient the cells. -/
noncomputable instance instLinearOrderCayGroup : LinearOrder (CayGroup A) := by
  classical
  exact linearOrderOfSTO (@WellOrderingRel (CayGroup A))

theorem cdist_self (x : CayGroup A) : cdist A x x = 0 := by
  simp [cdist]

theorem eq_of_cdist_eq_zero {x y : CayGroup A} (h : cdist A x y = 0) : x = y := by
  have : x⁻¹ * y = 1 := (clen_eq_zero_iff A).1 h
  have := mul_eq_one_iff_eq_inv.1 this
  simpa [eq_comm] using this

theorem cdist_comm (x y : CayGroup A) : cdist A x y = cdist A y x := by
  have h : (x⁻¹ * y)⁻¹ = y⁻¹ * x := by group
  calc cdist A x y = clen A (x⁻¹ * y) := rfl
    _ = clen A (x⁻¹ * y)⁻¹ := (clen_inv A _).symm
    _ = clen A (y⁻¹ * x) := by rw [h]
    _ = cdist A y x := rfl

theorem cdist_triangle (x y z : CayGroup A) : cdist A x z ≤ cdist A x y + cdist A y z := by
  have h : x⁻¹ * z = (x⁻¹ * y) * (y⁻¹ * z) := by group
  calc cdist A x z = clen A ((x⁻¹ * y) * (y⁻¹ * z)) := by rw [cdist, h]
    _ ≤ clen A (x⁻¹ * y) + clen A (y⁻¹ * z) := clen_mul_le A _ _
    _ = cdist A x y + cdist A y z := rfl

/-- The median of three vertices of the Cayley graph. -/
noncomputable def cmed (a b c : CayGroup A) : CayGroup A := (exists_median A a b c).choose

theorem cmed_spec (a b c : CayGroup A) : IsMedian A a b c (cmed A a b c) :=
  (exists_median A a b c).choose_spec

/-- The descending neighbours of a vertex correspond to the right descents, and those are the
left descents of the inverse. -/
theorem exists_desc_of_neighbour {w a : CayGroup A} (h1 : cdist A a w = 1)
    (h2 : clen A a + 1 = clen A w) : ∃ r : V, a = w * gen A r ∧ IsDesc A w⁻¹ r := by
  obtain ⟨r, hr⟩ := (clen_eq_one_iff A).1 h1
  have hw : w = a * gen A r := by
    have : a * (a⁻¹ * w) = a * gen A r := by rw [hr]
    simpa using this
  have ha : a = w * gen A r := by
    rw [hw, mul_assoc, gen_mul_gen, mul_one]
  refine ⟨r, ha, ?_⟩
  have hinv : gen A r * w⁻¹ = a⁻¹ := by
    rw [hw, mul_inv_rev, gen_inv, ← mul_assoc, gen_mul_gen, one_mul]
  show clen A (gen A r * w⁻¹) < clen A w⁻¹
  rw [hinv, clen_inv, clen_inv]
  omega

/-- **The Cayley graph of a right-angled Coxeter group is a median graph**, provided the
commutation graph has no clique with four vertices (which is the bound on the dimension of the
cube complex). -/
noncomputable def medianGraph
    (hdim : ∀ t : Finset V, (∀ s ∈ t, ∀ r ∈ t, s ≠ r → A.rel s r) → t.card ≤ 3) :
    MedianGraph (CayGroup A) where
  dist := cdist A
  base := 1
  dist_self := cdist_self A
  eq_of_dist_eq_zero := eq_of_cdist_eq_zero A
  dist_comm := cdist_comm A
  dist_triangle := cdist_triangle A
  med := cmed A
  med_ab a b c := (cmed_spec A a b c).1
  med_bc a b c := (cmed_spec A a b c).2.1
  med_ac a b c := (cmed_spec A a b c).2.2
  med_unique a b c z h1 h2 h3 := median_unique A ⟨h1, h2, h3⟩ (cmed_spec A a b c)
  dim_le := by
    classical
    intro w t ht
    have hex : ∀ a ∈ t, ∃ r : V, a = w * gen A r ∧ IsDesc A w⁻¹ r := by
      intro a ha
      obtain ⟨hd, hh⟩ := ht a ha
      refine exists_desc_of_neighbour A hd ?_
      simpa [cdist] using hh
    choose f hf1 hf2 using hex
    set u : Finset V := t.attach.image (fun a => f a.1 a.2) with hu
    have hinj : Set.InjOn (fun a : {x // x ∈ t} => f a.1 a.2) ↑t.attach := by
      intro a _ b _ hab
      have : a.1 = b.1 := by
        rw [hf1 a.1 a.2, hf1 b.1 b.2]
        simp only at hab
        rw [hab]
      exact Subtype.ext this
    have hcard : u.card = t.card := by
      rw [hu, Finset.card_image_of_injOn hinj, Finset.card_attach]
    have hcomm : ∀ s ∈ u, ∀ r ∈ u, s ≠ r → A.rel s r := by
      intro s hs r hr hsr
      rw [hu, Finset.mem_image] at hs hr
      obtain ⟨a, -, rfl⟩ := hs
      obtain ⟨b, -, rfl⟩ := hr
      exact desc_rel A hsr (hf2 a.1 a.2) (hf2 b.1 b.2)
    rw [← hcard]
    exact hdim u hcomm

/-- **Every two-cycle of the cellular chain complex bounds**: the vanishing `H₂ = 0` used in the
generation lemma of the paper, now for the cube complex of a right-angled Coxeter group. -/
theorem cycles_bound
    (hdim : ∀ t : Finset V, (∀ s ∈ t, ∀ r ∈ t, s ≠ r → A.rel s r) → t.card ≤ 3)
    (z : ((medianGraph A hdim).toDescCubeStr).SqC →₀ ℤ)
    (hz : ((medianGraph A hdim).toDescCubeStr).d₂ z = 0) :
    ∃ y : ((medianGraph A hdim).toDescCubeStr).CbC →₀ ℤ,
      ((medianGraph A hdim).toDescCubeStr).d₃ y = z :=
  (medianGraph A hdim).exists_d₃_eq z hz

end RACG
end FiniteChains
