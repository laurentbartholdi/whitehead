import RequestProject.CubeCartanHadamard

/-!
# CAT(0) cube complexes in their combinatorial (Roller) form, and `H₂ = 0`

`RequestProject/CubeCartanHadamard.lean` proves the vanishing of the second homology of an at
most three-dimensional cube complex from the *descending-cube* axioms collected in
`FiniteChains.DescCubeStr` (heights, descending neighbours, and the squares and cubes that
descending edges span).  Those axioms were stated there as an explicit combinatorial shadow
of the CAT(0) input of the paper.

This file replaces them by the standard combinatorial description of a CAT(0) cube complex,
namely its *Roller (halfspace) model*: the vertices of a CAT(0) cube complex are the
consistent orientations of its system of hyperplanes, two vertices are joined by an edge when
they differ in exactly one hyperplane, and the vertex set is closed under the *median*
(majority) operation.  Fixing a base vertex and recording each vertex by the finite set of
hyperplanes on which it differs from the base vertex, this becomes:

* a set `W` of finite subsets of a type `ι` of hyperplanes,
* containing the base vertex `∅`,
* closed under the majority operation `medFinset A B C = (A ∩ B) ∪ (B ∩ C) ∪ (A ∩ C)`.

This is the structure `FiniteChains.RollerModel`.  Together with the dimension bound (a
vertex has at most three descending neighbours, i.e. the complex is at most three
dimensional) it *implies* all the descending-cube axioms:
`FiniteChains.RollerModel.toDescCubeStr`.  Consequently

* `FiniteChains.RollerModel.exists_d₃_eq` and
* `FiniteChains.RollerModel.ker_d₂_eq_range_d₃`

hold: in the cellular chain complex of such a complex every two-cycle bounds.

Combinatorially the point is elementary, and it is exactly the geometric content used by the
paper: with the base vertex at `∅`, a descending neighbour of a vertex `A` is `A.erase p`,
the square spanned by two descending neighbours `A.erase p`, `A.erase q` has fourth vertex
their intersection `A \ {p, q}` (which is again a vertex, by median-closedness), and three
descending neighbours span the three-cube with bottom vertex `A \ {p, q, r}`.
-/

namespace FiniteChains

universe u

variable {ι : Type u} [DecidableEq ι]

/-- The majority vote (median) of three finite sets: an element belongs to it when it belongs
to at least two of them. -/
def medFinset (A B C : Finset ι) : Finset ι := (A ∩ B) ∪ (B ∩ C) ∪ (A ∩ C)

theorem medFinset_empty (A B : Finset ι) : medFinset A B ∅ = A ∩ B := by
  simp [medFinset]

/-- The **Roller model** of a CAT(0) cube complex based at one of its vertices: the vertices
are recorded as the finite sets of hyperplanes separating them from the base vertex, so that
the base vertex is `∅`, edges connect sets differing in one element, and the vertex set is
closed under the median (majority) operation.  The last field is the hypothesis that the
complex is at most three dimensional: a vertex has at most three descending neighbours. -/
structure RollerModel (ι : Type u) [DecidableEq ι] where
  /-- The vertex set, each vertex recorded by the set of hyperplanes separating it from the
  base vertex. -/
  W : Set (Finset ι)
  /-- The base vertex belongs to the complex. -/
  base_mem : (∅ : Finset ι) ∈ W
  /-- The vertex set is closed under the median operation. -/
  med_mem : ∀ {A B C : Finset ι}, A ∈ W → B ∈ W → C ∈ W → medFinset A B C ∈ W
  /-- The complex is at most three dimensional: a vertex has at most three descending
  neighbours. -/
  dim_le : ∀ A ∈ W, ∀ s : Finset (Finset ι),
    (∀ B ∈ s, B ∈ W ∧ B ⊆ A ∧ B.card + 1 = A.card) → s.card ≤ 3

/-- Three distinct descending neighbours of a vertex span a three-cube: listing them in the
order of `Vx` produces a cell of `FiniteChains.DescCubeStr.CbC`. -/
theorem DescCubeStr.nonempty_CbC {Vx : Type*} [LinearOrder Vx] {S : DescCubeStr Vx}
    {w a b c : Vx} (ha : a ∈ S.dn w) (hb : b ∈ S.dn w) (hc : c ∈ S.dn w)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) : Nonempty S.CbC := by
  rcases hab.lt_or_gt with h1 | h1 <;> rcases hac.lt_or_gt with h2 | h2 <;>
    rcases hbc.lt_or_gt with h3 | h3
  · exact ⟨⟨(w, a, b, c), ha, hb, hc, h1, h3⟩⟩
  · exact ⟨⟨(w, a, c, b), ha, hc, hb, h2, h3⟩⟩
  · exact ⟨⟨(w, c, a, b), hc, ha, hb, h2, h1⟩⟩
  · exact ⟨⟨(w, c, a, b), hc, ha, hb, h2, h1⟩⟩
  · exact ⟨⟨(w, b, a, c), hb, ha, hc, h1, h2⟩⟩
  · exact ⟨⟨(w, b, a, c), hb, ha, hc, h1, h2⟩⟩
  · exact ⟨⟨(w, b, c, a), hb, hc, ha, h3, h2⟩⟩
  · exact ⟨⟨(w, c, b, a), hc, hb, ha, h3, h1⟩⟩

namespace RollerModel

variable (M : RollerModel ι)

/-- The vertices of the complex. -/
def Vtx : Type u := {A : Finset ι // A ∈ M.W}

/-- A linear order on the vertices, used only to orient the cells. -/
noncomputable instance : LinearOrder M.Vtx := IsWellOrder.linearOrder WellOrderingRel

/-- The descending neighbours of a vertex: the vertices of the complex contained in it whose
cardinality (the distance to the base vertex) is one less. -/
def dnR (v : M.Vtx) : Set M.Vtx := {u : M.Vtx | u.1 ⊆ v.1 ∧ u.1.card + 1 = v.1.card}

variable {M}

theorem inter_mem {A B : Finset ι} (hA : A ∈ M.W) (hB : B ∈ M.W) : A ∩ B ∈ M.W := by
  have h := M.med_mem hA hB M.base_mem
  rwa [medFinset_empty] at h

variable (M) in
/-- The fourth vertex of the square spanned by two descending neighbours: their
intersection. -/
def medR (_w u v : M.Vtx) : M.Vtx := ⟨u.1 ∩ v.1, inter_mem u.2 v.2⟩

@[simp] theorem medR_val (w u v : M.Vtx) : (M.medR w u v).1 = u.1 ∩ v.1 := rfl

theorem mem_dnR {u v : M.Vtx} : u ∈ M.dnR v ↔ u.1 ⊆ v.1 ∧ u.1.card + 1 = v.1.card := Iff.rfl

/-- A subset of `w` of cardinality one less is obtained from `w` by erasing one element. -/
theorem exists_eq_erase {a w : Finset ι} (hsub : a ⊆ w) (hcard : a.card + 1 = w.card) :
    ∃ p ∈ w, p ∉ a ∧ a = w.erase p := by
  obtain ⟨p, hpw, hpa⟩ := Finset.exists_mem_notMem_of_card_lt_card (s := a) (t := w) (by omega)
  refine ⟨p, hpw, hpa, ?_⟩
  refine Finset.eq_of_subset_of_card_le (Finset.subset_erase.2 ⟨hsub, hpa⟩) ?_
  rw [Finset.card_erase_of_mem hpw]
  omega

theorem inter_erase_erase {w : Finset ι} {p q : ι} :
    (w.erase p) ∩ (w.erase q) = (w.erase p).erase q := by
  ext x
  simp only [Finset.mem_inter, Finset.mem_erase]
  tauto

/-- A subset of `A` of cardinality one less, missing `p ∈ A`, is `A.erase p`. -/
theorem eq_erase_of_notMem {A B : Finset ι} {p : ι} (hsub : B ⊆ A) (hcard : B.card + 1 = A.card)
    (hp : p ∈ A) (hpB : p ∉ B) : B = A.erase p := by
  refine Finset.eq_of_subset_of_card_le (Finset.subset_erase.2 ⟨hsub, hpB⟩) ?_
  rw [Finset.card_erase_of_mem hp]
  omega

/-- Counting descending neighbours: if all the elements of `A` that a descending neighbour
misses lie in a set `T`, then a vertex has at most `T.card` descending neighbours. -/
theorem card_dn_le_of_tops {A T : Finset ι} {s : Finset (Finset ι)}
    (h : ∀ B ∈ s, B ⊆ A ∧ B.card + 1 = A.card)
    (hT : ∀ B ∈ s, ∀ p ∈ A, p ∉ B → p ∈ T) : s.card ≤ T.card := by
  have hinj : Set.InjOn (fun B => A \ B) s := by
    intro B hB C hC hBC
    have hB' : B ⊆ A := (h B hB).1
    have hC' : C ⊆ A := (h C hC).1
    have hst : A \ (A \ B) = A \ (A \ C) := by
      simp only at hBC
      rw [hBC]
    rwa [Finset.sdiff_sdiff_eq_self hB', Finset.sdiff_sdiff_eq_self hC'] at hst
  have hsub : s.image (fun B => A \ B) ⊆ T.image (fun p => ({p} : Finset ι)) := by
    intro X hX
    obtain ⟨B, hB, rfl⟩ := Finset.mem_image.1 hX
    obtain ⟨p, hp, hpB, hBe⟩ := exists_eq_erase (h B hB).1 (h B hB).2
    refine Finset.mem_image.2 ⟨p, hT B hB p hp hpB, ?_⟩
    rw [hBe]
    ext x
    by_cases hxp : x = p <;> simp [hxp, hp, Finset.mem_sdiff, Finset.mem_erase]
  calc s.card = (s.image (fun B => A \ B)).card := (Finset.card_image_of_injOn hinj).symm
    _ ≤ (T.image (fun p => ({p} : Finset ι))).card := Finset.card_le_card hsub
    _ ≤ T.card := Finset.card_image_le

/-- A vertex has at most `A.card` descending neighbours: erasing distinct elements gives
distinct sets.  In particular the dimension hypothesis of a `FiniteChains.RollerModel` is
automatic as soon as all vertices have at most three elements. -/
theorem card_dn_le {A : Finset ι} {s : Finset (Finset ι)}
    (h : ∀ B ∈ s, B ⊆ A ∧ B.card + 1 = A.card) : s.card ≤ A.card :=
  card_dn_le_of_tops h (fun _ _ _ hp _ => hp)

/-- Two distinct descending neighbours of `w` are obtained from `w` by erasing two distinct
elements. -/
theorem exists_erase_pair {w a b : M.Vtx} (ha : a ∈ M.dnR w) (hb : b ∈ M.dnR w) (hab : a ≠ b) :
    ∃ p ∈ w.1, ∃ q ∈ w.1, p ≠ q ∧ a.1 = w.1.erase p ∧ b.1 = w.1.erase q := by
  obtain ⟨p, hpw, -, hp⟩ := exists_eq_erase ha.1 ha.2
  obtain ⟨q, hqw, -, hq⟩ := exists_eq_erase hb.1 hb.2
  refine ⟨p, hpw, q, hqw, ?_, hp, hq⟩
  rintro rfl
  exact hab (Subtype.ext (hp.trans hq.symm))

end RollerModel

/-- **The descending-cube axioms hold in the Roller model.**  A median-closed set of finite
sets of hyperplanes, based at `∅` and of dimension at most three, is an at most
three-dimensional cube complex with the descending-cube property. -/
noncomputable def RollerModel.toDescCubeStr (M : RollerModel ι) : DescCubeStr M.Vtx where
  ht v := v.1.card
  dn v := M.dnR v
  med w u v := M.medR w u v
  ht_dn := by
    intro w a ha
    exact ha.2
  dim_le := by
    intro w s hs
    have hinj : Set.InjOn (fun v : M.Vtx => v.1) s := fun x _ y _ h => Subtype.ext h
    have hcard : (s.image (fun v : M.Vtx => v.1)).card = s.card :=
      Finset.card_image_of_injOn hinj
    rw [← hcard]
    refine M.dim_le w.1 w.2 _ ?_
    intro B hB
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.1 hB
    have hvd : v ∈ M.dnR w := hs hv
    exact ⟨v.2, hvd.1, hvd.2⟩
  med_comm := by
    intro w a b
    exact Subtype.ext (Finset.inter_comm _ _)
  med_mem := by
    intro w a b ha hb hab
    obtain ⟨p, hpw, q, hqw, hpq, hp, hq⟩ := RollerModel.exists_erase_pair ha hb hab
    have hint : (M.medR w a b).1 = (w.1.erase p).erase q := by
      simp only [RollerModel.medR_val, hp, hq]
      exact RollerModel.inter_erase_erase
    have hq' : q ∈ w.1.erase p := Finset.mem_erase.2 ⟨Ne.symm hpq, hqw⟩
    have hpos : 0 < (w.1.erase p).card := Finset.card_pos.2 ⟨q, hq'⟩
    refine ⟨?_, ?_⟩
    · rw [hint, hp]
      exact Finset.erase_subset _ _
    · rw [hint, hp, Finset.card_erase_of_mem hq']
      omega
  med_ne := by
    intro w a b c ha hb hc hab _ hbc
    obtain ⟨p, -, -, hp⟩ := RollerModel.exists_eq_erase ha.1 ha.2
    obtain ⟨q, hqw, hqb, hq⟩ := RollerModel.exists_eq_erase hb.1 hb.2
    obtain ⟨r, -, -, hr⟩ := RollerModel.exists_eq_erase hc.1 hc.2
    have hpq : p ≠ q := by
      rintro rfl
      exact hab (Subtype.ext (hp.trans hq.symm))
    have hqr : q ≠ r := by
      rintro rfl
      exact hbc (Subtype.ext (hq.trans hr.symm))
    intro hcontra
    have hval : a.1 ∩ b.1 = a.1 ∩ c.1 := congrArg Subtype.val hcontra
    have hqa : q ∈ a.1 := by
      rw [hp]
      exact Finset.mem_erase.2 ⟨hpq.symm, hqw⟩
    have hqc : q ∈ c.1 := by
      rw [hr]
      exact Finset.mem_erase.2 ⟨hqr, hqw⟩
    have hmem : q ∈ a.1 ∩ b.1 := by
      rw [hval]
      exact Finset.mem_inter.2 ⟨hqa, hqc⟩
    exact hqb (Finset.mem_inter.1 hmem).2
  med_bottom₁ := by
    intro w a b c _ _ _ _ _ _
    refine Subtype.ext ?_
    simp only [RollerModel.medR_val]
    ext x
    simp only [Finset.mem_inter]
    tauto
  med_bottom₂ := by
    intro w a b c _ _ _ _ _ _
    refine Subtype.ext ?_
    simp only [RollerModel.medR_val]
    ext x
    simp only [Finset.mem_inter]
    tauto

namespace RollerModel

variable (M : RollerModel ι)

/-- **Every two-cycle of a three-dimensional CAT(0) cube complex, in its Roller model,
bounds.**  This is `H₂ = 0` for the cellular chain complex, with the descending-cube axioms
of `FiniteChains.DescCubeStr` now *derived* from median-closedness. -/
theorem exists_d₃_eq (z : M.toDescCubeStr.SqC →₀ ℤ) (hz : M.toDescCubeStr.d₂ z = 0) :
    ∃ c : M.toDescCubeStr.CbC →₀ ℤ, M.toDescCubeStr.d₃ c = z :=
  M.toDescCubeStr.exists_d₃_eq z hz

/-- The kernel–image form of the previous statement: `ker d₂ = im d₃`. -/
theorem ker_d₂_eq_range_d₃ :
    LinearMap.ker M.toDescCubeStr.d₂ = LinearMap.range M.toDescCubeStr.d₃ :=
  M.toDescCubeStr.ker_d₂_eq_range_d₃

end RollerModel

end FiniteChains
