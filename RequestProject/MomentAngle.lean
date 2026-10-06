import RequestProject.FlagComplex

/-!
# The cube complex `C(L)` and the fundamental cycle of Lemma 3.2 (i), (iii)

Section 3.3 of the paper uses the real moment–angle complex of a finite simplicial complex
`L` on the vertex set `{1, …, d}`,

  `C(L) = ⋃_{σ ∈ L} [-1,1]^σ × {-1,1}^{{1,…,d} ∖ σ}`,

and two facts about it:

* every vertex link of `C(L)` is `L` (this is what feeds the flagness criterion, together
  with `RequestProject/FlagComplex.lean`);
* for `L` a triangulated closed oriented surface the signed sum of the top-dimensional
  cubes, with the cube indexed by an ordered triangle `σ` and signs `ε` given the
  coefficient `o(σ)·∏_{h ∉ σ} ε_h`, is a cycle: "the two incidences at each square cancel".
  This is the chain-level computation behind Lemma 3.2 (iii) (the vanishing of `[Σ_q]` in
  `H₂(M_q)`), and, in the untruncated complex, behind Lemma 3.2 (i).

Both are proved here in the combinatorial model.  A cube of `C(L)` is encoded as a function
`f : V → CubeCoord` assigning to each coordinate either the value `free` (the coordinate
runs through `[-1,1]`) or one of the two signs; the *free set* of `f` is required to be a
face of `L`.  The cubical boundary is the usual one, with the sign of the face obtained by
fixing the `k`-th free coordinate at `δ = ±1` equal to `(-1)^k·δ`.

The main result `bdry_cubeChain` is stronger than what the paper needs: the assignment
`o ↦ c_o` of the above signed cubical chain to a simplicial chain of top-dimensional
simplices is a chain map, that is, `∂(c_o) = c_{∂o}`.  In particular a simplicial cycle
gives a cubical cycle (`cubeChain_cycle`).
-/

namespace FiniteChains

open Finset

/-- The state of one coordinate of a cube of `C(L)`: either free, or fixed at `+1`, or
fixed at `-1`. -/
inductive CubeCoord
  | free : CubeCoord
  | pos : CubeCoord
  | neg : CubeCoord
  deriving DecidableEq

namespace CubeCoord

/-- The sign of a fixed coordinate; free coordinates get the value `0`. -/
def sgn : CubeCoord → ℤ
  | .free => 0
  | .pos => 1
  | .neg => -1

end CubeCoord

variable {V : Type} [Fintype V] [DecidableEq V] [LinearOrder V]

/-- A cube of the moment-angle complex: an assignment of a state to each coordinate. -/
abbrev Cube (V : Type) := V → CubeCoord

/-- The set of free coordinates of a cube; its cardinality is the dimension of the cube. -/
def freeSet (f : Cube V) : Finset V := univ.filter fun v => f v = CubeCoord.free

omit [DecidableEq V] [LinearOrder V] in
@[simp] theorem mem_freeSet {f : Cube V} {v : V} : v ∈ freeSet f ↔ f v = CubeCoord.free := by
  simp [freeSet]

/-- The cube obtained from the vertex (or cube) `f` by making all coordinates in `σ` free. -/
def freeing (f : Cube V) (σ : Finset V) : Cube V :=
  fun v => if v ∈ σ then CubeCoord.free else f v

/-- `C(L)`: a cube belongs to the moment-angle complex of `L` exactly when its set of free
coordinates is a face of `L`. -/
def InMA (L : ASC V) (f : Cube V) : Prop := freeSet f ∈ L.faces

/-- A vertex of `C(L)`: a cube with no free coordinate, i.e. a sign vector. -/
def IsVertexCube (f : Cube V) : Prop := ∀ v, f v ≠ CubeCoord.free

omit [LinearOrder V] in
theorem freeSet_freeing_of_isVertex {f : Cube V} (hf : IsVertexCube f) (σ : Finset V) :
    freeSet (freeing f σ) = σ := by
  ext v
  by_cases hv : v ∈ σ <;> simp [freeing, hv, hf v]

/-- The link of the vertex `f` in `C(L)`: the simplicial complex whose simplices are the
sets of coordinate directions along which `f` can be made free inside `C(L)`. -/
def linkASC (L : ASC V) (f : Cube V) (hf : InMA L f) : ASC V where
  faces := {σ : Finset V | InMA L (freeing f σ)}
  empty_mem := by
    have hff : freeing f ∅ = f := by funext v; simp [freeing]
    simpa [InMA, hff] using hf
  down_closed := by
    intro s t hs hts
    refine L.down_closed hs ?_
    intro v hv
    simp only [mem_freeSet, freeing] at hv ⊢
    by_cases hvt : v ∈ t
    · simp [hts hvt]
    · simp only [hvt, if_false] at hv; simp [hv]

omit [DecidableEq V] [LinearOrder V] in
/-- A vertex of `C(L)` always lies in `C(L)`. -/
theorem inMA_of_isVertexCube (L : ASC V) {f : Cube V} (hf : IsVertexCube f) : InMA L f := by
  have : freeSet f = ∅ := by
    ext v; simp [hf v]
  simpa [InMA, this] using L.empty_mem

omit [LinearOrder V] in
/-- **Every vertex link of `C(L)` is `L`.** -/
theorem linkASC_eq (L : ASC V) {f : Cube V} (hf : IsVertexCube f) :
    (linkASC L f (inMA_of_isVertexCube L hf)).faces = L.faces := by
  ext σ
  simp [linkASC, InMA, freeSet_freeing_of_isVertex hf]

omit [DecidableEq V] [LinearOrder V] in
/-- If `L` has dimension at most two (all faces have at most three vertices) then all cubes
of `C(L)` have dimension at most three. -/
theorem dim_le_of_dim_le (L : ASC V) (h : ∀ s ∈ L.faces, s.card ≤ 3) {f : Cube V}
    (hf : InMA L f) : (freeSet f).card ≤ 3 := h _ hf

/-! ### The cubical boundary and the fundamental cycle -/

/-- The incidence number of the cube obtained from `g` by freeing the coordinate `j`
(which must be fixed in `g`) with its face `g`: the sign `(-1)^k·δ`, where `k` is the
position of `j` among the free coordinates of the bigger cube and `δ` is the sign at which
the coordinate `j` is fixed. -/
def incid (g : Cube V) (j : V) : ℤ :=
  (-1) ^ ((freeSet g).filter (fun i => i < j)).card * (g j).sgn

theorem incid_eq_card_bigger (g : Cube V) (j : V) (hj : g j ≠ CubeCoord.free) :
    incid g j =
      (-1) ^ ((freeSet (Function.update g j CubeCoord.free)).filter (fun i => i < j)).card
        * (g j).sgn := by
  have hset : (freeSet (Function.update g j CubeCoord.free)).filter (fun i => i < j)
      = (freeSet g).filter (fun i => i < j) := by
    ext i
    by_cases hij : i = j <;>
      simp [hij, mem_freeSet, and_comm, hj]
  rw [incid, hset]

/-- The cubical boundary operator, written on coefficient functions: the coefficient of the
cube `g` in `∂c`. -/
def bdry (c : Cube V → ℤ) : Cube V → ℤ := fun g =>
  ∑ j ∈ univ.filter (fun j => g j ≠ CubeCoord.free),
    incid g j * c (Function.update g j CubeCoord.free)

/-- The simplicial boundary of a chain of `n`-simplices, written on coefficient functions:
the coefficient of the face `τ` in `∂o`. -/
def simpBdry (o : Finset V → ℤ) : Finset V → ℤ := fun τ =>
  ∑ j ∈ univ.filter (fun j => j ∉ τ),
    (-1) ^ (τ.filter (fun i => i < j)).card * o (insert j τ)

/-- The cubical chain attached to a simplicial chain `o`: the cube with free set `σ` and
signs `ε` off `σ` gets the coefficient `o(σ)·∏_{h ∉ σ} ε_h`. -/
def cubeChain (o : Finset V → ℤ) : Cube V → ℤ := fun f =>
  o (freeSet f) * ∏ h ∈ univ \ freeSet f, (f h).sgn

omit [LinearOrder V] in
/-- The chain `c_o` lives in `C(L)` as soon as the simplicial chain `o` does. -/
theorem cubeChain_eq_zero_of_not_mem (L : ASC V) {o : Finset V → ℤ}
    (ho : ∀ s, s ∉ L.faces → o s = 0) {f : Cube V} (hf : ¬ InMA L f) : cubeChain o f = 0 := by
  simp [cubeChain, ho _ hf]

/-- **The signed cubical chains of the moment-angle complex form a chain map**:
`∂(c_o) = c_{∂o}`.  This is the computation "every square meets exactly two three-cubes …
the two incidences at each square cancel" of Lemma 3.2, in the form valid in every degree
and for an arbitrary coefficient function. -/
theorem bdry_cubeChain (o : Finset V → ℤ) :
    bdry (cubeChain o) = cubeChain (simpBdry o) := by
  funext g
  have hindex : (univ.filter fun j => g j ≠ CubeCoord.free)
      = univ.filter fun j => j ∉ freeSet g := by
    ext j; simp
  rw [bdry, hindex, cubeChain, simpBdry, Finset.sum_mul]
  refine Finset.sum_congr rfl ?_
  intro j hj
  have hjτ : j ∉ freeSet g := by simpa using hj
  -- the free set of the bigger cube
  have hfree : freeSet (Function.update g j CubeCoord.free) = insert j (freeSet g) := by
    ext i
    by_cases hij : i = j <;> simp [hij]
  -- the sign product over the complement of the bigger cube
  have hprodeq : ∏ h ∈ univ \ insert j (freeSet g),
      (Function.update g j CubeCoord.free h).sgn
      = ∏ h ∈ univ \ insert j (freeSet g), (g h).sgn := by
    refine Finset.prod_congr rfl ?_
    intro h hh
    have hhj : h ≠ j := by
      intro hhj; subst hhj
      simp at hh
    simp [hhj]
  -- split off the `j`-th factor
  have hsplit : ∏ h ∈ univ \ freeSet g, (g h).sgn
      = (g j).sgn * ∏ h ∈ univ \ insert j (freeSet g), (g h).sgn := by
    have hmem : j ∈ univ \ freeSet g := by simp [hjτ]
    rw [← Finset.prod_erase_mul _ _ hmem, mul_comm]
    congr 2
    ext i
    by_cases hij : i = j <;> simp [hij, hjτ]
  rw [cubeChain, hfree, hprodeq, incid, hsplit]
  ring


/-! ### Incidences: every square lies in exactly two three-cubes -/

section Incidence

open scoped Classical

/-- The cubes of `C(L)` having `g` as a codimension one face: those obtained from `g` by
making one further coordinate free. -/
noncomputable def cofaces (L : ASC V) (g : Cube V) : Finset (Cube V) :=
  ((univ.filter fun j => g j ≠ CubeCoord.free).filter
      fun j => insert j (freeSet g) ∈ L.faces).image
    fun j => Function.update g j CubeCoord.free

omit [LinearOrder V] in
theorem mem_cofaces {L : ASC V} {g f : Cube V} :
    f ∈ cofaces L g ↔ ∃ j, g j ≠ CubeCoord.free ∧ insert j (freeSet g) ∈ L.faces ∧
      f = Function.update g j CubeCoord.free := by
  simp only [cofaces, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨j, ⟨hj, hjL⟩, rfl⟩
    exact ⟨j, hj, hjL, rfl⟩
  · rintro ⟨j, hj, hjL, rfl⟩
    exact ⟨j, ⟨hj, hjL⟩, rfl⟩

omit [LinearOrder V] in
/-- **Counting the cubes above a given face.**  The number of cubes of `C(L)` having `g` as
a codimension one face is the number of ways of enlarging the free set of `g` by one vertex
inside `L`. -/
theorem card_cofaces (L : ASC V) (g : Cube V) :
    (cofaces L g).card
      = ((univ.filter fun j => j ∉ freeSet g).filter
          fun j => insert j (freeSet g) ∈ L.faces).card := by
  rw [cofaces, Finset.card_image_of_injOn]
  · congr 1
    ext j
    simp
  · intro j hj k hk hjk
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hj hk
    by_contra hne
    have hval : Function.update g j CubeCoord.free j
        = Function.update g k CubeCoord.free j := congrFun hjk j
    simp only [Function.update_apply, if_neg hne] at hval
    exact hj.1 hval.symm

omit [LinearOrder V] in
/-- **Every square of `C(L)` lies in exactly two three-cubes**, provided every edge of `L`
lies in exactly two triangles — that is, provided `L` is a closed surface.  This is the
incidence count used in the proof of Lemma 3.2. -/
theorem card_cofaces_eq_two (L : ASC V) (g : Cube V)
    (h : ((univ.filter fun j => j ∉ freeSet g).filter
        fun j => insert j (freeSet g) ∈ L.faces).card = 2) :
    (cofaces L g).card = 2 := by
  rw [card_cofaces, h]

end Incidence

/-! ### The cubical boundary is a differential -/

omit [LinearOrder V] in
theorem freeSet_update_free (g : Cube V) (j : V) :
    freeSet (Function.update g j CubeCoord.free) = insert j (freeSet g) := by
  ext i
  by_cases hij : i = j <;> simp [hij]

omit [Fintype V] in
theorem card_filter_insert (τ : Finset V) (j k : V) (hj : j ∉ τ) :
    ((insert j τ).filter (fun i => i < k)).card
      = (τ.filter (fun i => i < k)).card + (if j < k then 1 else 0) := by
  by_cases h : j < k
  · rw [Finset.filter_insert, if_pos h, Finset.card_insert_of_notMem (by simp [hj])]
    simp [h]
  · rw [Finset.filter_insert, if_neg h]
    simp [h]

/-- The two ways of passing from a cube to a codimension two face carry opposite incidence
signs. -/
theorem incid_mul_incid_antisymm (g : Cube V) {j k : V} (hjk : j ≠ k) :
    incid g j * incid (Function.update g j CubeCoord.free) k
      = -(incid g k * incid (Function.update g k CubeCoord.free) j) := by
  by_cases hj : g j = CubeCoord.free
  · simp [incid, hj, CubeCoord.sgn, hjk, Ne.symm hjk]
  by_cases hk : g k = CubeCoord.free
  · simp [incid, hk, CubeCoord.sgn, hjk, Ne.symm hjk]
  have hjτ : j ∉ freeSet g := by simpa using hj
  have hkτ : k ∉ freeSet g := by simpa using hk
  have hgj : Function.update g j CubeCoord.free k = g k := by
    simp [Ne.symm hjk]
  have hgk : Function.update g k CubeCoord.free j = g j := by
    simp [hjk]
  rw [incid, incid, incid, incid, freeSet_update_free, freeSet_update_free, hgj, hgk,
    card_filter_insert _ _ _ hjτ, card_filter_insert _ _ _ hkτ]
  rcases lt_or_gt_of_ne hjk with h | h
  · rw [if_pos h, if_neg (asymm h)]
    rw [pow_add, pow_add]
    ring
  · rw [if_neg (asymm h), if_pos h]
    rw [pow_add, pow_add]
    ring

/-- **The cubical boundary operator squares to zero.**  This certifies that `bdry` is the
differential of the cellular chain complex of the cube complex. -/
theorem bdry_bdry (c : Cube V → ℤ) : bdry (bdry c) = 0 := by
  funext h
  show ∑ j ∈ univ.filter (fun j => h j ≠ CubeCoord.free),
      incid h j * bdry c (Function.update h j CubeCoord.free) = 0
  set F : Finset V := univ.filter (fun j => h j ≠ CubeCoord.free) with hF
  -- write the iterated boundary as a sum over ordered pairs of distinct free directions
  have hinner : ∀ j ∈ F, incid h j * bdry c (Function.update h j CubeCoord.free)
      = ∑ k ∈ F, (if k ≠ j then
          incid h j * (incid (Function.update h j CubeCoord.free) k *
            c (Function.update (Function.update h j CubeCoord.free) k CubeCoord.free))
        else 0) := by
    intro j _
    have hidx : (univ.filter fun k => Function.update h j CubeCoord.free k ≠ CubeCoord.free)
        = F.filter (fun k => k ≠ j) := by
      ext k
      by_cases hkj : k = j <;> simp [hF, hkj, Function.update_apply]
    rw [bdry, hidx, Finset.mul_sum, Finset.sum_filter]
  rw [Finset.sum_congr rfl hinner, ← Finset.sum_product']
  refine Finset.sum_involution (fun p _ => (p.2, p.1)) ?_ ?_ ?_ ?_
  · rintro ⟨j, k⟩ -
    by_cases hkj : k = j
    · simp [hkj]
    · have hjk : j ≠ k := fun hh => hkj hh.symm
      have hcomm : Function.update (Function.update h j CubeCoord.free) k CubeCoord.free
          = Function.update (Function.update h k CubeCoord.free) j CubeCoord.free :=
        Function.update_comm hjk _ _ _
      simp only [hkj, ne_eq, not_false_eq_true, if_true, hjk]
      rw [hcomm, ← mul_assoc, ← mul_assoc, incid_mul_incid_antisymm h hjk]
      ring
  · rintro ⟨j, k⟩ - hne
    have hkj : k ≠ j := by
      by_contra hcon
      exact hne (by simp [hcon])
    exact fun hcon => hkj (congrArg Prod.fst hcon)
  · rintro ⟨j, k⟩ hp
    simp only [Finset.mem_product] at hp ⊢
    exact ⟨hp.2, hp.1⟩
  · rintro ⟨j, k⟩ -
    rfl

omit [Fintype V] in
/-- The simplicial boundary carries opposite signs on the two ways of reaching a
codimension two face. -/
theorem simp_sign_antisymm (τ : Finset V) {j k : V} (hj : j ∉ τ) (hk : k ∉ τ)
    (hjk : j ≠ k) :
    ((-1 : ℤ) ^ (τ.filter (fun i => i < j)).card)
        * (-1) ^ ((insert j τ).filter (fun i => i < k)).card
      = -(((-1 : ℤ) ^ (τ.filter (fun i => i < k)).card)
        * (-1) ^ ((insert k τ).filter (fun i => i < j)).card) := by
  rw [card_filter_insert _ _ _ hj, card_filter_insert _ _ _ hk]
  rcases lt_or_gt_of_ne hjk with h | h
  · rw [if_pos h, if_neg (asymm h), pow_add, pow_add]
    ring
  · rw [if_neg (asymm h), if_pos h, pow_add, pow_add]
    ring

/-- **The simplicial boundary operator squares to zero.** -/
theorem simpBdry_simpBdry (o : Finset V → ℤ) : simpBdry (simpBdry o) = 0 := by
  funext τ
  show ∑ j ∈ univ.filter (fun j => j ∉ τ),
      (-1 : ℤ) ^ (τ.filter (fun i => i < j)).card * simpBdry o (insert j τ) = 0
  set F : Finset V := univ.filter (fun j => j ∉ τ) with hF
  have hinner : ∀ j ∈ F, (-1 : ℤ) ^ (τ.filter (fun i => i < j)).card * simpBdry o (insert j τ)
      = ∑ k ∈ F, (if k ≠ j then
          ((-1 : ℤ) ^ (τ.filter (fun i => i < j)).card)
            * ((-1 : ℤ) ^ ((insert j τ).filter (fun i => i < k)).card
              * o (insert k (insert j τ)))
        else 0) := by
    intro j _
    have hidx : (univ.filter fun k => k ∉ insert j τ) = F.filter (fun k => k ≠ j) := by
      ext k
      by_cases hkj : k = j <;> simp [hF, hkj, and_comm]
    rw [simpBdry, hidx, Finset.mul_sum, Finset.sum_filter]
  rw [Finset.sum_congr rfl hinner, ← Finset.sum_product']
  refine Finset.sum_involution (fun p _ => (p.2, p.1)) ?_ ?_ ?_ ?_
  · rintro ⟨j, k⟩ hp
    by_cases hkj : k = j
    · simp [hkj]
    · have hjk : j ≠ k := fun hh => hkj hh.symm
      have hjF : j ∈ F := (Finset.mem_product.mp hp).1
      have hkF : k ∈ F := (Finset.mem_product.mp hp).2
      have hjτ : j ∉ τ := by simpa [hF] using hjF
      have hkτ : k ∉ τ := by simpa [hF] using hkF
      have hins : insert k (insert j τ) = insert j (insert k τ) := Finset.insert_comm _ _ _
      simp only [hkj, ne_eq, not_false_eq_true, if_true, hjk]
      rw [hins, ← mul_assoc, ← mul_assoc, simp_sign_antisymm τ hjτ hkτ hjk]
      ring
  · rintro ⟨j, k⟩ - hne
    have hkj : k ≠ j := by
      by_contra hcon
      exact hne (by simp [hcon])
    exact fun hcon => hkj (congrArg Prod.fst hcon)
  · rintro ⟨j, k⟩ hp
    simp only [Finset.mem_product] at hp ⊢
    exact ⟨hp.2, hp.1⟩
  · rintro ⟨j, k⟩ -
    rfl

/-- **A simplicial cycle gives a cubical cycle.**  For a triangulated closed oriented
surface `L` with orientation coefficients `o` the hypothesis says that `Σ_σ o(σ)·σ` is a
cycle; the conclusion is that the corresponding signed sum of top-dimensional cubes of
`C(L)` is a cycle, which is the chain used in the proof of Lemma 3.2. -/
theorem cubeChain_cycle {o : Finset V → ℤ} (ho : simpBdry o = 0) :
    bdry (cubeChain o) = 0 := by
  rw [bdry_cubeChain, ho]
  funext f
  simp [cubeChain]

end FiniteChains
