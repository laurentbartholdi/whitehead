import RequestProject.CollapseChainMap
import RequestProject.SpineCollapse

/-!
# Lemma 3.3 (iii) in the form used by the capping argument: the cut surface is the zero
chain of the spine

`RequestProject/TruncatedCube.lean` proves the chain-level half of Lemma 3.3 (iii): in the
truncated complex `M = C(L) ∖ (neighbourhood of the corner)` the fundamental cycle of the cut
surface is the boundary of the signed sum of the three-cubes
(`FiniteChains.cutSurface_isBoundary`).  `RequestProject/SpineCollapse.lean` proves Lemma
3.3 (ii): all three-cubes of `M` are removed by elementary collapses, leaving a
two-dimensional spine.

This file combines the two, through the chain map of a collapse
(`RequestProject/CollapseChainMap.lean`): the collapse carries the fundamental cycle of the
cut surface to the **zero** cellular chain of the spine.  This is exactly the form in which
the proof of (B3) uses Lemma 3.3 (iii): the block part of the boundary of the cone
three-cell, which is the image of `[Σ_q]`, is the zero chain, hence has zero augmentation.

The cells are those of `RequestProject/SpineCollapse.lean`: the three-cells are the cubes
with a triangle as free set, and the codimension one faces are the squares of `C(L)`
together with the cut cells created by the truncation.  `FiniteChains.cubeBdry` is the
cellular boundary of a three-cube, read off from the boundary operator `bdryT` of the
truncated complex.
-/

namespace FiniteChains

open Finset

variable {V : Type} [Fintype V] [DecidableEq V] [LinearOrder V]

/-- The cellular boundary of the three-cube `t` in the truncated complex, as a coefficient
function on the codimension one faces used by the collapse (squares and cut cells). -/
noncomputable def cubeBdry (t : Cube V) : Cube V ⊕ Finset V → ℤ :=
  Sum.elim (fun g => bdry (fun f => if f = t then 1 else 0) g)
    (fun τ => cutSign τ * (if posCube τ = t then 1 else 0))

theorem cubeBdry_inl (t g : Cube V) :
    cubeBdry t (Sum.inl g)
      = ∑ j ∈ univ.filter (fun j => g j ≠ CubeCoord.free),
          incid g j * (if Function.update g j CubeCoord.free = t then 1 else 0) := rfl

theorem cubeBdry_inr (t : Cube V) (τ : Finset V) :
    cubeBdry t (Sum.inr τ) = cutSign τ * (if posCube τ = t then 1 else 0) := rfl

omit [Fintype V] [LinearOrder V] in
/-- Freeing a coordinate of a square determines that coordinate: distinct coordinates give
distinct cubes above it. -/
theorem update_free_injective {g : Cube V} {j k : V} (hj : g j ≠ CubeCoord.free)
    (h : Function.update g j CubeCoord.free = Function.update g k CubeCoord.free) : j = k := by
  by_contra hjk
  have hval := congrFun h j
  rw [Function.update_apply, if_pos rfl, Function.update_apply, if_neg hjk] at hval
  exact hj hval.symm

omit [DecidableEq V] in
/-- The incidence number of a cube with a codimension one face is a unit. -/
theorem incid_eq_unit {g : Cube V} {j : V} (hj : g j ≠ CubeCoord.free) :
    incid g j = 1 ∨ incid g j = -1 := by
  have hs : (g j).sgn = 1 ∨ (g j).sgn = -1 := by
    rcases h : g j with _ | _ | _
    · exact absurd h hj
    · exact Or.inl rfl
    · exact Or.inr rfl
  rcases Nat.even_or_odd ((freeSet g).filter (fun i => i < j)).card with he | ho
  · rw [incid, he.neg_one_pow, one_mul]
    exact hs
  · rw [incid, ho.neg_one_pow]
    rcases hs with h | h <;> rw [h] <;> simp

/-- **The boundary of a three-cube on a square face is `±1` when the cube lies above that
face.** -/
theorem cubeBdry_inl_eq_unit {L : ASC V} {g t : Cube V} (ht : t ∈ cofaces L g) :
    cubeBdry t (Sum.inl g) = 1 ∨ cubeBdry t (Sum.inl g) = -1 := by
  classical
  obtain ⟨j, hj, -, rfl⟩ := mem_cofaces.1 ht
  have hmem : j ∈ univ.filter (fun k => g k ≠ CubeCoord.free) := by simp [hj]
  rw [cubeBdry_inl, Finset.sum_eq_single j]
  · rw [if_pos rfl, mul_one]
    exact incid_eq_unit hj
  · intro k hk hkj
    have hk' : g k ≠ CubeCoord.free := by simpa using hk
    rw [if_neg, mul_zero]
    intro hcon
    exact hkj (update_free_injective hk' hcon)
  · intro hcon; exact absurd hmem hcon

/-- **A three-cube not lying above a square has zero boundary coefficient there.** -/
theorem cubeBdry_inl_eq_zero {L : ASC V} {g t : Cube V} (htop : t ∈ topCubes L)
    (ht : t ∉ cofaces L g) : cubeBdry t (Sum.inl g) = 0 := by
  classical
  rw [cubeBdry_inl]
  refine Finset.sum_eq_zero fun j hj => ?_
  have hj' : g j ≠ CubeCoord.free := by simpa using hj
  rw [if_neg, mul_zero]
  intro hcon
  refine ht (mem_cofaces.2 ⟨j, hj', ?_, hcon.symm⟩)
  have hfree : freeSet (Function.update g j CubeCoord.free) = insert j (freeSet g) := by
    ext i
    by_cases hij : i = j <;> simp [hij]
  rw [← hfree, hcon]
  exact (mem_topCubes.1 htop).1

/-- **The boundary of the truncated corner cube over a triangle on its cut face is `-1`.** -/
theorem cubeBdry_inr_eq_neg_one {τ : Finset V} (hτ : τ.card = 3) :
    cubeBdry (posCube τ) (Sum.inr τ) = -1 := by
  rw [cubeBdry_inr, if_pos rfl, mul_one, cutSign, hτ]
  norm_num

/-- A three-cube other than the truncated corner cube over `τ` has zero coefficient on the
cut face of `τ`. -/
theorem cubeBdry_inr_eq_zero {t : Cube V} {τ : Finset V} (h : t ≠ posCube τ) :
    cubeBdry t (Sum.inr τ) = 0 := by
  rw [cubeBdry_inr, if_neg (Ne.symm h), mul_zero]

/-! ### From a combinatorial collapse to a chain collapse -/

/-- Every cell occurring in a collapse belongs to the collapsed set. -/
theorem Collapse.mem_of_isCollapse {T F : Type*} [DecidableEq T] {inc : F → Finset T}
    {l : List T} {S : Finset T} (h : Collapse.IsCollapse inc l S) : ∀ t ∈ l, t ∈ S := by
  induction l generalizing S with
  | nil => intro t ht; exact absurd ht List.not_mem_nil
  | cons u l ih =>
      obtain ⟨huS, -, hrest⟩ := h
      intro t ht
      rcases List.mem_cons.1 ht with rfl | htl
      · exact huS
      · exact Finset.mem_of_mem_erase (ih hrest t htl)

/-- A collapse removes every cell of the collapsed set. -/
theorem Collapse.mem_list_of_isCollapse {T F : Type*} [DecidableEq T] {inc : F → Finset T}
    {l : List T} {S : Finset T} (h : Collapse.IsCollapse inc l S) : ∀ t ∈ S, t ∈ l := by
  induction l generalizing S with
  | nil =>
      intro t ht
      rw [show S = ∅ from h] at ht
      exact absurd ht (Finset.notMem_empty t)
  | cons u l ih =>
      obtain ⟨huS, -, hrest⟩ := h
      intro t ht
      by_cases htu : t = u
      · exact htu ▸ List.mem_cons_self
      · exact List.mem_cons_of_mem _ (ih hrest t (Finset.mem_erase.2 ⟨htu, ht⟩))

/-- **A collapse of the truncated complex is a chain collapse.**  The free face of each step
carries the coefficient `±1` on the cell removed at that step, and the coefficient `0` on
every cell removed later — the latter is exactly the freeness of the face at that moment. -/
theorem exists_chainCollapse {L : ASC V} {l : List (Cube V)} {S : Finset (Cube V)}
    (hS : S ⊆ topCubes L) (h : Collapse.IsCollapse (spineInc L) l S) :
    ∃ lp : List (Cube V × (Cube V ⊕ Finset V)), lp.map Prod.fst = l ∧
      CollapseChain.IsChainCollapse (cubeBdry (V := V)) lp := by
  classical
  induction l generalizing S with
  | nil => exact ⟨[], rfl, trivial⟩
  | cons t l ih =>
      obtain ⟨htS, ⟨f, hfree⟩, hrest⟩ := h
      have hSerase : S.erase t ⊆ topCubes L := fun u hu => hS (Finset.mem_of_mem_erase hu)
      obtain ⟨lp, hmap, hchain⟩ := ih hSerase hrest
      have htf : t ∈ spineInc L f := by
        have : t ∈ spineInc L f ∩ S := by rw [hfree]; exact Finset.mem_singleton_self t
        exact (Finset.mem_inter.1 this).1
      have hunit : cubeBdry t f = 1 ∨ cubeBdry t f = -1 := by
        cases f with
        | inl g =>
            by_cases hg : (freeSet g).card = 2
            · rw [spineInc, if_pos hg] at htf
              exact cubeBdry_inl_eq_unit htf
            · rw [spineInc, if_neg hg] at htf
              exact absurd htf (Finset.notMem_empty t)
        | inr τ =>
            by_cases hτ : IsTri L τ
            · rw [spineInc, if_pos hτ, Finset.mem_singleton] at htf
              subst htf
              exact Or.inr (cubeBdry_inr_eq_neg_one hτ.2)
            · rw [spineInc, if_neg hτ] at htf
              exact absurd htf (Finset.notMem_empty t)
      have hunit' : IsUnit (cubeBdry t f) := by
        rcases hunit with h | h <;> rw [h]
        · exact isUnit_one
        · exact (isUnit_one (M := ℤ)).neg
      refine ⟨(t, f) :: lp, by simp [hmap], hunit', ?_, hchain⟩
      intro p hp
      have hp1 : p.1 ∈ l := by
        rw [← hmap]
        exact List.mem_map_of_mem hp
      have hpS : p.1 ∈ S.erase t := Collapse.mem_of_isCollapse hrest p.1 hp1
      have hpnot : p.1 ∉ spineInc L f := by
        intro hcon
        have : p.1 ∈ spineInc L f ∩ S :=
          Finset.mem_inter.2 ⟨hcon, Finset.mem_of_mem_erase hpS⟩
        rw [hfree, Finset.mem_singleton] at this
        exact (Finset.ne_of_mem_erase hpS) this
      have hptop : p.1 ∈ topCubes L := hS (Finset.mem_of_mem_erase hpS)
      cases f with
      | inl g =>
          by_cases hg : (freeSet g).card = 2
          · rw [spineInc, if_pos hg] at hpnot
            exact cubeBdry_inl_eq_zero hptop hpnot
          · rw [spineInc, if_neg hg] at htf
            exact absurd htf (Finset.notMem_empty t)
      | inr τ =>
          by_cases hτ : IsTri L τ
          · rw [spineInc, if_pos hτ, Finset.mem_singleton] at hpnot
            exact cubeBdry_inr_eq_zero hpnot
          · rw [spineInc, if_neg hτ] at htf
            exact absurd htf (Finset.notMem_empty t)

/-! ### The boundary of a three-chain, cell by cell -/

/-- The boundary of a three-chain of the truncated complex, written as the combination of the
boundaries of its three-cubes. -/
theorem bdryT_eq_sum {c : Cube V → ℤ} {S : Finset (Cube V)} (hc : ∀ t, c t ≠ 0 → t ∈ S)
    (f : Cube V ⊕ Finset V) :
    Sum.elim (bdryT (c, 0)).1 (bdryT (c, 0)).2 f = ∑ t ∈ S, c t * cubeBdry t f := by
  classical
  cases f with
  | inl g =>
      show bdry c g = _
      rw [bdry]
      have hswap : ∑ t ∈ S, c t * cubeBdry t (Sum.inl g)
          = ∑ j ∈ univ.filter (fun j => g j ≠ CubeCoord.free),
              incid g j * c (Function.update g j CubeCoord.free) := by
        simp only [cubeBdry_inl, Finset.mul_sum]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun j _ => ?_
        have : ∀ t ∈ S, c t * (incid g j * if Function.update g j CubeCoord.free = t then 1
            else 0) = if t = Function.update g j CubeCoord.free then
              c t * incid g j else 0 := by
          intro t _
          by_cases htj : t = Function.update g j CubeCoord.free
          · subst htj; simp
          · rw [if_neg htj, if_neg (fun hcon => htj hcon.symm), mul_zero, mul_zero]
        rw [Finset.sum_congr rfl this, Finset.sum_ite_eq' S
          (Function.update g j CubeCoord.free) (fun t => c t * incid g j)]
        by_cases hmem : Function.update g j CubeCoord.free ∈ S
        · rw [if_pos hmem, mul_comm]
        · rw [if_neg hmem]
          have : c (Function.update g j CubeCoord.free) = 0 := by
            by_contra hcon
            exact hmem (hc _ hcon)
          rw [this, mul_zero]
      rw [hswap]
  | inr τ =>
      show cutSign τ * c (posCube τ) + simpBdry 0 τ = _
      have hz : simpBdry (0 : Finset V → ℤ) τ = 0 := by simp [simpBdry]
      rw [hz, add_zero]
      have : ∀ t ∈ S, c t * cubeBdry t (Sum.inr τ)
          = if t = posCube τ then cutSign τ * c t else 0 := by
        intro t _
        rw [cubeBdry_inr]
        by_cases htp : t = posCube τ
        · subst htp; ring_nf; simp
        · rw [if_neg (fun hcon => htp hcon.symm), if_neg htp, mul_zero, mul_zero]
      rw [Finset.sum_congr rfl this,
        Finset.sum_ite_eq' S (posCube τ) (fun t => cutSign τ * c t)]
      by_cases hmem : posCube τ ∈ S
      · rw [if_pos hmem]
      · rw [if_neg hmem]
        have : c (posCube τ) = 0 := by
          by_contra hcon
          exact hmem (hc _ hcon)
        rw [this, mul_zero]

/-! ### Lemma 3.3 (iii) after the collapse -/

/-- **The cut surface collapses to the zero chain.**  Let `o` be the fundamental cycle of an
oriented triangulated closed surface `L`, so that the cut surface of the truncated complex
`M = C(L) ∖ (neighbourhood of the corner)` carries the cycle `-o` on its cut cells.  Then
after the collapse of all three-cubes of `M` — the collapse of Lemma 3.3 (ii) — the cellular
chain of the cut surface is zero.  This is Lemma 3.3 (iii) in the form used by the capping
argument of (B3): the image of `[Σ_q]` in the two-dimensional spine is the zero chain. -/
theorem cutSurface_cmap_eq_zero {L : ASC V} {o : Finset V → ℤ} (hcyc : simpBdry o = 0)
    (hsupp : ∀ σ : Finset V, σ.card ≠ 3 → o σ = 0)
    (hfaces : ∀ σ : Finset V, σ ∉ L.faces → o σ = 0)
    {l : List (Cube V)} (hl : Collapse.IsCollapse (spineInc L) l (topCubes L))
    {lp : List (Cube V × (Cube V ⊕ Finset V))} (hmap : lp.map Prod.fst = l)
    (hchain : CollapseChain.IsChainCollapse (cubeBdry (V := V)) lp) :
    CollapseChain.cmap (cubeBdry (V := V)) lp (Sum.elim 0 (fun τ => -o τ)) = 0 := by
  classical
  have hc : ∀ t : Cube V, cubeChain o t ≠ 0 → t ∈ topCubes L := by
    intro t ht
    rw [mem_topCubes]
    refine ⟨?_, ?_⟩
    · by_contra hcon
      exact ht (by simp [cubeChain, hfaces _ hcon])
    · by_contra hcon
      exact ht (by simp [cubeChain, hsupp _ hcon])
  have hx : ∀ f : Cube V ⊕ Finset V,
      Sum.elim (0 : Cube V → ℤ) (fun τ => -o τ) f
        = ∑ t ∈ topCubes L, cubeChain o t * cubeBdry t f := by
    intro f
    rw [← bdryT_eq_sum hc f, cutSurface_isBoundary hcyc hsupp]
    cases f with
    | inl g => rfl
    | inr τ => rfl
  have hsub : ∀ t ∈ topCubes L, ∃ f, (t, f) ∈ lp := by
    intro t ht
    have htl : t ∈ l := Collapse.mem_list_of_isCollapse hl t ht
    rw [← hmap] at htl
    obtain ⟨p, hp, hp1⟩ := List.mem_map.1 htl
    exact ⟨p.2, by rw [← hp1]; simpa using hp⟩
  exact CollapseChain.cmap_eq_zero_of_isBoundary hchain hsub hx

/-- **Lemma 3.3 (ii) and (iii) together.**  For a triangulated closed surface `L` whose dual
graph is connected and each of whose vertices lies in a triangle, there is a collapse of all
three-cubes of the truncated complex `M = C(L) ∖ (neighbourhood of the corner)`, and the
fundamental cycle of the cut surface becomes the zero chain of the resulting two-dimensional
spine. -/
theorem exists_collapse_cutSurface_eq_zero {L : ASC V} (hsurf : ASC.EdgeInTwoTriangles L)
    (hdual : ∀ σ σ', IsTri L σ → IsTri L σ' → Relation.ReflTransGen (TriAdj L) σ σ')
    (hcover : ∀ v : V, ∃ σ, IsTri L σ ∧ v ∈ σ) {σ₀ : Finset V} (hσ₀ : IsTri L σ₀)
    {o : Finset V → ℤ} (hcyc : simpBdry o = 0)
    (hsupp : ∀ σ : Finset V, σ.card ≠ 3 → o σ = 0)
    (hfaces : ∀ σ : Finset V, σ ∉ L.faces → o σ = 0) :
    ∃ lp : List (Cube V × (Cube V ⊕ Finset V)),
      CollapseChain.IsChainCollapse (cubeBdry (V := V)) lp ∧
        CollapseChain.cmap (cubeBdry (V := V)) lp (Sum.elim 0 (fun τ => -o τ)) = 0 := by
  obtain ⟨l, hl⟩ := exists_spine_collapse_of_surface hsurf hdual hcover hσ₀
  obtain ⟨lp, hmap, hchain⟩ := exists_chainCollapse (Finset.Subset.refl _) hl
  exact ⟨lp, hchain, cutSurface_cmap_eq_zero hcyc hsupp hfaces hl hmap hchain⟩

end FiniteChains
