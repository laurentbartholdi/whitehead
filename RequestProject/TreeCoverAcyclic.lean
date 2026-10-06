module

public import RequestProject.CoverComplexFinsupp
public import RequestProject.TreeCover

@[expose] public section

/-!
# The cover of `K` is acyclic when the cover of the collapsed presentation complex is

`RequestProject/TreeCover.lean` constructs, for a spanning tree `T` of a two-complex `K` and a
normal subgroup `N ◁ F(E ∖ T)` containing the relators, a connected regular covering
`treeCover T N hN → K` with deck group `Q = F(E ∖ T)/N`.  Collapsing the tree identifies its
cellular chain complex with that of the cover `coverComplex N (treeRel T) hN` of the
presentation complex, up to the tree edges, which carry no homology: this file proves that the
cover of `K` is acyclic as soon as the cover of the presentation complex is
(`treeCover_isAcyclic`).

The comparison is given by the chain maps

* `piV`, which forgets the vertex of `K` (the vertices of `treeCover` are `Q × V`, those of the
  presentation cover are `Q`);
* `piE`, which deletes the tree edges;
* the identity on two-cells, the two covers having the same two-cells `Q × F`.
-/

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains
namespace Comb
namespace SpanningTree

universe u

variable {K : Complex2.{u}} (T : SpanningTree K)
variable (N : Subgroup (FreeGroup (NonTree T))) [N.Normal]

/-! ### The letters of a path outside the tree -/

open Classical in
/-- The word in the non-tree edges spelled by an edge path, as a list of letters. -/
noncomputable def letters : List (K.E × Bool) → List (NonTree T × Bool)
  | [] => []
  | g :: L => if h : T.isTree g.1 then letters L else (⟨g.1, h⟩, g.2) :: letters L

variable {T}

@[simp] theorem letters_nil : letters T [] = [] := rfl

theorem letters_cons_tree {g : K.E × Bool} (h : T.isTree g.1) (L : List (K.E × Bool)) :
    letters T (g :: L) = letters T L := by
  classical
  simp [letters, h]

theorem letters_cons_nontree {g : K.E × Bool} (h : ¬ T.isTree g.1) (L : List (K.E × Bool)) :
    letters T (g :: L) = (⟨g.1, h⟩, g.2) :: letters T L := by
  classical
  simp [letters, h]

/-- The list of non-tree letters spells the word of the path. -/
theorem mk_letters (L : List (K.E × Bool)) :
    FreeGroup.mk (letters T L) = pathWord T L := by
  classical
  induction L with
  | nil => rfl
  | cons g L ih =>
      by_cases h : T.isTree g.1
      · rw [letters_cons_tree h, ih, pathWord_cons, germWord_of_isTree T h, one_mul]
      · rw [letters_cons_nontree h, pathWord_cons]
        obtain ⟨e, b⟩ := g
        cases b
        · rw [mk_cons_false, ih, show germWord T (e, false)
            = (FreeGroup.of (⟨e, h⟩ : NonTree T))⁻¹ by simp [germWord, h]]
        · rw [mk_cons_true, ih, show germWord T (e, true)
            = FreeGroup.of (⟨e, h⟩ : NonTree T) by simp [germWord, h]]

/-! ### The comparison maps on chains -/

theorem germQ_eq_one_of_isTree {g : K.E × Bool} (h : T.isTree g.1) : germQ T N g = 1 := by
  show QuotientGroup.mk (germWord T g) = 1
  rw [germWord_of_isTree T h]
  rfl

omit [N.Normal] in
theorem germQ_true_eq_qof {e : K.E} (h : ¬ T.isTree e) :
    germQ T N (e, true) = qof N (⟨e, h⟩ : NonTree T) := by
  classical
  show QuotientGroup.mk (germWord T (e, true)) = _
  rw [show germWord T (e, true) = FreeGroup.of (⟨e, h⟩ : NonTree T) by simp [germWord, h]]
  rfl

theorem germQ_false_eq_qof_inv {e : K.E} (h : ¬ T.isTree e) :
    germQ T N (e, false) = (qof N (⟨e, h⟩ : NonTree T))⁻¹ := by
  rw [germQ_false_eq_inv, germQ_true_eq_qof (N := N) h]

variable (T)

open Classical in
/-- Deleting the tree edges: the comparison map on one-chains. -/
noncomputable def piE : ((CovQ T N × K.E) →₀ ℤ) →ₗ[ℤ] ((CovQ T N × NonTree T) →₀ ℤ) :=
  Finsupp.linearCombination ℤ (fun x : CovQ T N × K.E =>
    if h : T.isTree x.2 then 0 else Finsupp.single (x.1, (⟨x.2, h⟩ : NonTree T)) (1 : ℤ))

/-- Forgetting the vertex of `K`: the comparison map on zero-chains. -/
noncomputable def piV : ((CovQ T N × K.V) →₀ ℤ) →ₗ[ℤ] ((CovQ T N) →₀ ℤ) :=
  Finsupp.lmapDomain ℤ ℤ Prod.fst

/-- Putting a vertex of the presentation cover at the root of its tree. -/
noncomputable def iotaV : ((CovQ T N) →₀ ℤ) →ₗ[ℤ] ((CovQ T N × K.V) →₀ ℤ) :=
  Finsupp.lmapDomain ℤ ℤ (fun q => (q, T.root))

variable {T}

omit [N.Normal] in
theorem piE_single_tree {x : CovQ T N × K.E} (h : T.isTree x.2) (n : ℤ) :
    piE T N (Finsupp.single x n) = 0 := by
  classical
  rw [piE, Finsupp.linearCombination_single]
  simp [h]

omit [N.Normal] in
theorem piE_single_nontree {x : CovQ T N × K.E} (h : ¬ T.isTree x.2) (n : ℤ) :
    piE T N (Finsupp.single x n) = Finsupp.single (x.1, (⟨x.2, h⟩ : NonTree T)) n := by
  classical
  rw [piE, Finsupp.linearCombination_single]
  simp [h, Finsupp.smul_single]

omit [N.Normal] in
@[simp] theorem piV_single (x : CovQ T N × K.V) (n : ℤ) :
    piV T N (Finsupp.single x n) = Finsupp.single x.1 n := by
  rw [piV]
  simp [Finsupp.lmapDomain_apply]

omit [N.Normal] in
@[simp] theorem iotaV_single (q : CovQ T N) (n : ℤ) :
    iotaV T N (Finsupp.single q n) = Finsupp.single (q, T.root) n := by
  rw [iotaV]
  simp [Finsupp.lmapDomain_apply]

/-- **Deleting the tree edges from a lifted path** gives the lift of the word it spells. -/
theorem piE_pathChain_liftK (L : List (K.E × Bool)) (q : CovQ T N) :
    piE T N (pathChain (liftK T N L q)) = pathChain (liftPath (letters T L) q) := by
  classical
  induction L generalizing q with
  | nil => simp [pathChain]
  | cons g L ih =>
      obtain ⟨e, b⟩ := g
      by_cases h : T.isTree e
      · have hq : q * germQ T N (e, b) = q := by
          rw [germQ_eq_one_of_isTree (N := N) (g := (e, b)) h, mul_one]
        have hsnd : (liftGerm T N q (e, b)).2 = b := by cases b <;> rfl
        have hfst : (liftGerm T N q (e, b)).1.2 = e := by cases b <;> rfl
        have hz : piE T N (Finsupp.single (liftGerm T N q (e, b)).1 (1 : ℤ)) = 0 :=
          piE_single_tree (N := N) (x := (liftGerm T N q (e, b)).1) (by rw [hfst]; exact h) 1
        rw [liftK_cons, pathChain_cons, map_add, letters_cons_tree (g := (e, b)) h, hq, ih q,
          hsnd]
        cases b
        · simp [hz]
        · simp [hz]
      · rw [liftK_cons, pathChain_cons, map_add, letters_cons_nontree (g := (e, b)) h]
        cases b
        · have hlift : liftGerm T N q (e, false) =
              ((q * germQ T N (e, false), e), false) := rfl
          rw [hlift]
          simp only [Bool.false_eq_true, if_false, map_neg]
          rw [piE_single_nontree (N := N) (x := (q * germQ T N (e, false), e)) h 1,
            ih (q * germQ T N (e, false)), germQ_false_eq_qof_inv (N := N) h,
            liftPath_cons_false, pathChain_cons]
          simp
        · have hlift : liftGerm T N q (e, true) = ((q, e), true) := rfl
          rw [hlift]
          simp only [if_true]
          rw [piE_single_nontree (N := N) (x := (q, e)) h 1,
            germQ_true_eq_qof (N := N) h, ih (q * qof N ⟨e, h⟩)]
          rw [liftPath_cons_true, pathChain_cons]
          simp

/-! ### The comparison maps are chain maps -/

variable [Fintype (NonTree T)] [DecidableEq (NonTree T)]

omit [Fintype (NonTree T)] in
/-- The chain of a lifted word depends only on the free-group element it spells. -/
theorem pathChain_liftPath_congr {L L' : List (NonTree T × Bool)}
    (h : FreeGroup.mk L = FreeGroup.mk L') (q : CovQ T N) :
    pathChain (liftPath (Nsub := N) L q) = pathChain (liftPath (Nsub := N) L' q) := by
  apply (fsCoords N (NonTree T)).injective
  apply Finsupp.ext
  intro i
  rw [fsCoords_pathChain_liftPath_apply, fsCoords_pathChain_liftPath_apply, h]

variable (hN : ∀ f, treeRel T f ∈ N)

omit [Fintype (NonTree T)] in
/-- **The comparison map is a chain map in degree two**: the two covers have the same
two-cells, and deleting the tree edges from the attaching path of a two-cell of the cover of
`K` gives the attaching path of the corresponding two-cell of the cover of the presentation
complex. -/
theorem piE_bdry2 (u : (CovQ T N × K.F) →₀ ℤ) :
    piE T N (bdry2 (treeCover T N hN) u) = bdry2 (coverComplex N (treeRel T) hN) u := by
  classical
  induction u using Finsupp.induction_linear with
  | zero => simp
  | add u₁ u₂ h₁ h₂ => rw [map_add, map_add, map_add, h₁, h₂]
  | single x n =>
      obtain ⟨q, f⟩ := x
      rw [bdry2_single, bdry2_single, map_smul]
      show n • piE T N (pathChain (liftK T N (K.att f) q)) = _
      rw [piE_pathChain_liftK]
      congr 1
      refine pathChain_liftPath_congr (N := N) ?_ q
      rw [mk_letters, FreeGroup.mk_toWord]
      rfl

omit [Fintype (NonTree T)] in
/-- **The comparison map is a chain map in degree one.** -/
theorem piV_bdry1 (c : (CovQ T N × K.E) →₀ ℤ) :
    piV T N (bdry1 (treeCover T N hN) c) = bdry1 (coverComplex N (treeRel T) hN) (piE T N c) := by
  classical
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c₁ c₂ h₁ h₂ => rw [map_add, map_add, map_add, map_add, h₁, h₂]
  | single x n =>
      obtain ⟨q, e⟩ := x
      rw [bdry1_single]
      by_cases h : T.isTree e
      · rw [piE_single_tree (N := N) (x := (q, e)) h n, map_zero]
        have hg : germQ T N (e, true) = 1 := germQ_eq_one_of_isTree (N := N) (g := (e, true)) h
        show piV T N (n • (Finsupp.single (covTgt T N (q, e)) (1 : ℤ)
          - Finsupp.single (covSrc T N (q, e)) (1 : ℤ))) = 0
        rw [map_smul, map_sub, piV_single, piV_single]
        show n • (Finsupp.single (covTgt T N (q, e)).1 (1 : ℤ)
          - Finsupp.single (covSrc T N (q, e)).1 (1 : ℤ)) = 0
        show n • (Finsupp.single (q * germQ T N (e, true)) (1 : ℤ)
          - Finsupp.single q (1 : ℤ)) = 0
        rw [hg, mul_one, sub_self, smul_zero]
      · rw [piE_single_nontree (N := N) (x := (q, e)) h n, bdry1_single]
        show piV T N (n • (Finsupp.single (covTgt T N (q, e)) (1 : ℤ)
          - Finsupp.single (covSrc T N (q, e)) (1 : ℤ))) = _
        rw [map_smul, map_sub, piV_single, piV_single]
        show n • (Finsupp.single (covTgt T N (q, e)).1 (1 : ℤ)
          - Finsupp.single (covSrc T N (q, e)).1 (1 : ℤ)) = _
        show n • (Finsupp.single (q * germQ T N (e, true)) (1 : ℤ)
          - Finsupp.single q (1 : ℤ)) = _
        rw [germQ_true_eq_qof (N := N) h]

omit [Fintype (NonTree T)] in
/-- The augmentations agree. -/
theorem augC_piV (c : (CovQ T N × K.V) →₀ ℤ) :
    augC (coverComplex N (treeRel T) hN) (piV T N c) = augC (treeCover T N hN) c := by
  classical
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c₁ c₂ h₁ h₂ => rw [map_add, map_add, map_add, h₁, h₂]
  | single x n =>
      obtain ⟨q, a⟩ := x
      rw [piV_single]
      show augC (coverComplex N (treeRel T) hN) (Finsupp.single q n) = _
      rw [augC_single, augC_single]

/-! ### Contracting the tree and lifting the generators -/

variable (T)

/-- The one-chain of the lifted tree path: it bounds the difference between a vertex of the
cover and the root of its sheet. -/
noncomputable def treeCorr : ((CovQ T N × K.V) →₀ ℤ) →ₗ[ℤ] ((CovQ T N × K.E) →₀ ℤ) :=
  Finsupp.linearCombination ℤ (fun x : CovQ T N × K.V =>
    pathChain (liftK T N (T.treePath x.2) x.1))

/-- The loop of `K` at the root carried by a non-tree edge. -/
noncomputable def loopPath (ε : NonTree T) : List (K.E × Bool) :=
  conjPath T [((ε : K.E), true)] (K.src (ε : K.E)) (K.tgt (ε : K.E))

/-- Lifting the loops of the generators: a section of the comparison map on one-chains. -/
noncomputable def sectionE :
    ((CovQ T N × NonTree T) →₀ ℤ) →ₗ[ℤ] ((CovQ T N × K.E) →₀ ℤ) :=
  Finsupp.linearCombination ℤ (fun x : CovQ T N × NonTree T =>
    pathChain (liftK T N (loopPath T x.2) x.1))

variable {T}

omit [Fintype (NonTree T)] [DecidableEq (NonTree T)] in
theorem isPath_loopPath (ε : NonTree T) :
    IsPath K.src K.tgt (loopPath T ε) T.root T.root :=
  conjPath_isLoop T (isPath_single _)

omit [Fintype (NonTree T)] [DecidableEq (NonTree T)] in
theorem pathWord_loopPath (ε : NonTree T) : pathWord T (loopPath T ε) = FreeGroup.of ε := by
  classical
  rw [loopPath, conjPath, pathWord_append, pathWord_append, pathWord_treePath,
    pathWord_revPath, pathWord_treePath]
  simp [pathWord, germWord, dif_neg ε.2]

omit [N.Normal] [Fintype (NonTree T)] [DecidableEq (NonTree T)] in
theorem wordQ_loopPath (ε : NonTree T) : wordQ T N (loopPath T ε) = qof N ε := by
  show QuotientGroup.mk (pathWord T (loopPath T ε)) = _
  rw [pathWord_loopPath]
  rfl

variable (hN : ∀ f, treeRel T f ∈ N)

omit [Fintype (NonTree T)] [DecidableEq (NonTree T)] in
/-- **Contracting the tree**: the tree correction chain bounds the difference between a chain
and its push-down to the roots of the sheets. -/
theorem bdry1_treeCorr (c : (CovQ T N × K.V) →₀ ℤ) :
    bdry1 (treeCover T N hN) (treeCorr T N c) = c - iotaV T N (piV T N c) := by
  classical
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c₁ c₂ h₁ h₂ =>
      rw [map_add, map_add, map_add, map_add, h₁, h₂]
      abel
  | single x n =>
      obtain ⟨q, a⟩ := x
      have hpath := liftK_isPath (T := T) (N := N) (T.treePath_isPath a) q
      rw [wordQ_treePath, mul_one] at hpath
      rw [treeCorr, Finsupp.linearCombination_single, map_smul]
      have hb : bdry1 (treeCover T N hN) (pathChain (liftK T N (T.treePath a) q))
          = Finsupp.single ((q, a) : CovQ T N × K.V) (1 : ℤ)
            - Finsupp.single ((q, T.root) : CovQ T N × K.V) (1 : ℤ) :=
        bdry1_pathChain_of_isPath (X := treeCover T N hN) hpath
      rw [hb, piV_single, iotaV_single, smul_sub, Finsupp.smul_single, Finsupp.smul_single,
        smul_eq_mul, mul_one]

omit [Fintype (NonTree T)] in
/-- **Lifting the generators**: the section is a chain homotopy inverse in degree one. -/
theorem bdry1_sectionE (u : (CovQ T N × NonTree T) →₀ ℤ) :
    bdry1 (treeCover T N hN) (sectionE T N u)
      = iotaV T N (bdry1 (coverComplex N (treeRel T) hN) u) := by
  classical
  induction u using Finsupp.induction_linear with
  | zero => simp
  | add u₁ u₂ h₁ h₂ => rw [map_add, map_add, map_add, map_add, h₁, h₂]
  | single x n =>
      obtain ⟨q, ε⟩ := x
      have hpath := liftK_isPath (T := T) (N := N) (isPath_loopPath (T := T) ε) q
      rw [wordQ_loopPath (N := N)] at hpath
      rw [sectionE, Finsupp.linearCombination_single, map_smul, bdry1_single]
      have hb : bdry1 (treeCover T N hN) (pathChain (liftK T N (loopPath T ε) q))
          = Finsupp.single ((q * qof N ε, T.root) : CovQ T N × K.V) (1 : ℤ)
            - Finsupp.single ((q, T.root) : CovQ T N × K.V) (1 : ℤ) :=
        bdry1_pathChain_of_isPath (X := treeCover T N hN) hpath
      rw [hb, map_smul, map_sub, iotaV_single, iotaV_single]

/-! ### One-cycles supported on the tree vanish -/

/-- The coefficient of a boundary at a vertex. -/
theorem bdry1_apply (X : Complex2.{u}) (z : X.E →₀ ℤ) (w : X.V) :
    bdry1 X z w = ∑ x ∈ z.support, z x *
      ((Finsupp.single (X.tgt x) (1 : ℤ)) w - (Finsupp.single (X.src x) (1 : ℤ)) w) := by
  classical
  rw [bdry1, Finsupp.linearCombination_apply, Finsupp.sum]
  rw [Finsupp.finset_sum_apply]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  rw [Finsupp.smul_apply, Finsupp.sub_apply, smul_eq_mul]

/-- The non-root vertex whose tree edge is the given tree edge. -/
noncomputable def treeTop {e : K.E} (he : T.isTree e) : K.V :=
  ((T.isTree_iff e).1 he).choose

omit [Fintype (NonTree T)] [DecidableEq (NonTree T)] in
theorem treeTop_ne_root {e : K.E} (he : T.isTree e) : treeTop he ≠ T.root :=
  ((T.isTree_iff e).1 he).choose_spec.choose

omit [Fintype (NonTree T)] [DecidableEq (NonTree T)] in
theorem up_treeTop {e : K.E} (he : T.isTree e) :
    (T.up (treeTop he) (treeTop_ne_root he)).1 = e :=
  ((T.isTree_iff e).1 he).choose_spec.choose_spec

omit [Fintype (NonTree T)] [DecidableEq (NonTree T)] in
/-- The vertex of a tree edge farther from the root is unique. -/
theorem up_edge_unique {a b : K.V} (ha : a ≠ T.root) (hb : b ≠ T.root)
    (h : (T.up a ha).1 = (T.up b hb).1) : a = b := by
  by_cases hs : (T.up a ha).2 = (T.up b hb).2
  · have huv : T.up a ha = T.up b hb := Prod.ext h hs
    have h1 : germSrc K.src K.tgt (T.up a ha) = a := T.up_src a ha
    have h2 : germSrc K.src K.tgt (T.up b hb) = b := T.up_src b hb
    rw [huv, h2] at h1
    exact h1.symm
  · exfalso
    have huv : T.up b hb = revGerm (T.up a ha) := by
      refine Prod.ext h.symm ?_
      show (T.up b hb).2 = !(T.up a ha).2
      cases hx : (T.up a ha).2 <;> cases hy : (T.up b hb).2 <;> simp_all
    have hb' : b = T.parent a ha := by
      have h2 : germSrc K.src K.tgt (T.up b hb) = b := T.up_src b hb
      rw [huv] at h2
      rw [← h2]
      show germSrc K.src K.tgt (revGerm (T.up a ha)) = T.parent a ha
      simp [parent]
    have ha' : T.parent b hb = a := by
      show germTgt K.src K.tgt (T.up b hb) = a
      rw [huv]
      simpa using T.up_src a ha
    have h1 : T.ht (T.parent a ha) + 1 = T.ht a := T.ht_parent ha
    have h2 : T.ht (T.parent b hb) + 1 = T.ht b := T.ht_parent hb
    rw [← hb'] at h1
    rw [ha'] at h2
    omega

omit [Fintype (NonTree T)] [DecidableEq (NonTree T)] in
theorem treeTop_eq {e : K.E} (he : T.isTree e) {a : K.V} (ha : a ≠ T.root)
    (h : (T.up a ha).1 = e) : treeTop he = a :=
  up_edge_unique (treeTop_ne_root he) ha ((up_treeTop he).trans h.symm)

omit [Fintype (NonTree T)] [DecidableEq (NonTree T)] in
/-- The endpoints of a tree edge are the vertex it belongs to and its parent. -/
theorem tree_edge_endpoints {e : K.E} {a : K.V} (ha : a ≠ T.root) (hup : (T.up a ha).1 = e) :
    (K.src e = a ∧ K.tgt e = T.parent a ha) ∨ (K.src e = T.parent a ha ∧ K.tgt e = a) := by
  have hsrc : germSrc K.src K.tgt (T.up a ha) = a := T.up_src a ha
  have htgt : germTgt K.src K.tgt (T.up a ha) = T.parent a ha := rfl
  cases hb : (T.up a ha).2
  · right
    have hg : T.up a ha = (e, false) := Prod.ext hup hb
    rw [hg] at hsrc htgt
    simp only [germSrc_false, germTgt_false] at hsrc htgt
    exact ⟨htgt, hsrc⟩
  · left
    have hg : T.up a ha = (e, true) := Prod.ext hup hb
    rw [hg] at hsrc htgt
    simp only [germSrc_true, germTgt_true] at hsrc htgt
    exact ⟨hsrc, htgt⟩

omit [Fintype (NonTree T)] [DecidableEq (NonTree T)] in
theorem parent_ne_self {a : K.V} (ha : a ≠ T.root) : T.parent a ha ≠ a := by
  intro h
  have := T.ht_parent ha
  rw [h] at this
  omega

omit [Fintype (NonTree T)] [DecidableEq (NonTree T)] in
theorem covTgt_of_isTree {e : K.E} (he : T.isTree e) (q : CovQ T N) :
    covTgt T N (q, e) = (q, K.tgt e) := by
  show (q * germQ T N (e, true), K.tgt e) = (q, K.tgt e)
  rw [germQ_eq_one_of_isTree (N := N) (g := (e, true)) he, mul_one]

omit [Fintype (NonTree T)] [DecidableEq (NonTree T)] in
/-- **A one-cycle of the cover supported on the tree edges vanishes**: the tree edges of each
sheet form a tree, so they carry no cycle. -/
theorem treeChain_eq_zero {z : (CovQ T N × K.E) →₀ ℤ}
    (hsupp : ∀ x ∈ z.support, T.isTree x.2)
    (hz : bdry1 (treeCover T N hN) z = 0) : z = 0 := by
  classical
  by_contra hzne
  have hne : z.support.Nonempty := Finsupp.support_nonempty_iff.2 hzne
  obtain ⟨x₀, hx₀mem, hx₀max⟩ := z.support.exists_max_image
    (fun x => if h : T.isTree x.2 then T.ht (treeTop h) else 0) hne
  have he₀ : T.isTree x₀.2 := hsupp x₀ hx₀mem
  obtain ⟨a₀, ha₀ne, ha₀up⟩ := (T.isTree_iff x₀.2).1 he₀
  have hg : ∀ x ∈ z.support, ∀ (a : K.V) (ha : a ≠ T.root), (T.up a ha).1 = x.2 →
      (if h : T.isTree x.2 then T.ht (treeTop h) else 0) = T.ht a := by
    intro x hx a ha hup
    have hex : T.isTree x.2 := hsupp x hx
    rw [dif_pos hex, treeTop_eq hex ha hup]
  have hg₀ : (if h : T.isTree x₀.2 then T.ht (treeTop h) else 0) = T.ht a₀ :=
    hg x₀ hx₀mem a₀ ha₀ne ha₀up
  -- all terms but the one of `x₀` vanish at the vertex `(x₀.1, a₀)`
  have hterm : ∀ x ∈ z.support, x ≠ x₀ →
      z x * ((Finsupp.single ((treeCover T N hN).tgt x) (1 : ℤ)) (x₀.1, a₀)
        - (Finsupp.single ((treeCover T N hN).src x) (1 : ℤ)) (x₀.1, a₀)) = 0 := by
    intro x hx hxne
    have hex : T.isTree x.2 := hsupp x hx
    obtain ⟨a, hane, haup⟩ := (T.isTree_iff x.2).1 hex
    have hle : T.ht a ≤ T.ht a₀ := by
      have hmax := hx₀max x hx
      rw [hg x hx a hane haup, hg₀] at hmax
      exact hmax
    have key : ∀ v : K.V, (v = K.src x.2 ∨ v = K.tgt x.2) → (x.1, v) ≠ (x₀.1, a₀) := by
      intro v hv hc
      rw [Prod.mk.injEq] at hc
      obtain ⟨hq, hva⟩ := hc
      have hvertex : a = a₀ → False := by
        intro haa
        subst haa
        have hxe : x.2 = x₀.2 := haup.symm.trans ha₀up
        exact hxne (Prod.ext hq hxe)
      have hparent : T.parent a hane = a₀ → False := by
        intro hp
        have hht := T.ht_parent hane
        rw [hp] at hht
        omega
      rcases tree_edge_endpoints hane haup with ⟨hs, ht⟩ | ⟨hs, ht⟩
      · rcases hv with hv | hv
        · exact hvertex (by rw [← hs, ← hv, hva])
        · exact hparent (by rw [← ht, ← hv, hva])
      · rcases hv with hv | hv
        · exact hparent (by rw [← hs, ← hv, hva])
        · exact hvertex (by rw [← ht, ← hv, hva])
    have h1 : (treeCover T N hN).tgt x ≠ (x₀.1, a₀) := by
      rw [treeCover_tgt, show x = (x.1, x.2) from rfl, covTgt_of_isTree (N := N) hex]
      exact key (K.tgt x.2) (Or.inr rfl)
    have h2 : (treeCover T N hN).src x ≠ (x₀.1, a₀) := by
      rw [treeCover_src]
      exact key (K.src x.2) (Or.inl rfl)
    rw [Finsupp.single_eq_of_ne (Ne.symm h1), Finsupp.single_eq_of_ne (Ne.symm h2)]
    ring
  -- evaluate the boundary at the vertex `(x₀.1, a₀)`
  have hzero : (0 : ℤ) = z x₀ *
      ((Finsupp.single ((treeCover T N hN).tgt x₀) (1 : ℤ)) (x₀.1, a₀)
        - (Finsupp.single ((treeCover T N hN).src x₀) (1 : ℤ)) (x₀.1, a₀)) := by
    have h := bdry1_apply (treeCover T N hN) z (x₀.1, a₀)
    rw [hz] at h
    have h2 := h.trans (Finset.sum_eq_single_of_mem x₀ hx₀mem hterm)
    convert h2 using 1 <;> congr 2
  have hzx₀ : z x₀ ≠ 0 := Finsupp.mem_support_iff.1 hx₀mem
  have hsrc : (treeCover T N hN).src x₀ = (x₀.1, K.src x₀.2) := rfl
  have htgt : (treeCover T N hN).tgt x₀ = (x₀.1, K.tgt x₀.2) := by
    rw [treeCover_tgt, show x₀ = (x₀.1, x₀.2) from rfl, covTgt_of_isTree (N := N) he₀]
  have hpne : T.parent a₀ ha₀ne ≠ a₀ := parent_ne_self (T := T) ha₀ne
  rcases tree_edge_endpoints ha₀ne ha₀up with ⟨hs, ht⟩ | ⟨hs, ht⟩
  · have h1 : (treeCover T N hN).tgt x₀ ≠ (x₀.1, a₀) := by
      rw [htgt, ht]
      intro hc
      rw [Prod.mk.injEq] at hc
      exact hpne hc.2
    have h2 : (treeCover T N hN).src x₀ = (x₀.1, a₀) := by rw [hsrc, hs]
    rw [Finsupp.single_eq_of_ne (Ne.symm h1), h2, Finsupp.single_eq_same] at hzero
    simp at hzero
    omega
  · have h1 : (treeCover T N hN).tgt x₀ = (x₀.1, a₀) := by rw [htgt, ht]
    have h2 : (treeCover T N hN).src x₀ ≠ (x₀.1, a₀) := by
      rw [hsrc, hs]
      intro hc
      rw [Prod.mk.injEq] at hc
      exact hpne hc.2
    rw [Finsupp.single_eq_of_ne (Ne.symm h2), h1, Finsupp.single_eq_same] at hzero
    simp at hzero
    omega

/-! ### Acyclicity -/

omit [Fintype (NonTree T)] [N.Normal] in
/-- The coefficient of the comparison map at a non-tree edge. -/
theorem piE_apply (z : (CovQ T N × K.E) →₀ ℤ) (q : CovQ T N) (ε : NonTree T) :
    piE T N z (q, ε) = z (q, (ε : K.E)) := by
  classical
  induction z using Finsupp.induction_linear with
  | zero => simp
  | add z₁ z₂ h₁ h₂ => rw [map_add, Finsupp.add_apply, Finsupp.add_apply, h₁, h₂]
  | single x n =>
      by_cases h : T.isTree x.2
      · rw [piE_single_tree (N := N) h n]
        have hne : x ≠ (q, (ε : K.E)) := by
          intro hc
          exact ε.2 (by rw [hc] at h; exact h)
        simp [hne]
      · rw [piE_single_nontree (N := N) h n, Finsupp.single_apply, Finsupp.single_apply]
        congr 1
        simp only [Prod.ext_iff, Subtype.ext_iff]

omit [Fintype (NonTree T)] [N.Normal] in
theorem support_isTree_of_piE_eq_zero {z : (CovQ T N × K.E) →₀ ℤ} (h : piE T N z = 0) :
    ∀ x ∈ z.support, T.isTree x.2 := by
  intro x hx
  by_contra hnt
  have hval := piE_apply (N := N) z x.1 ⟨x.2, hnt⟩
  rw [h] at hval
  exact (Finsupp.mem_support_iff.1 hx) (by simpa using hval.symm)

omit [Fintype (NonTree T)] in
/-- **The cover of `K` is acyclic as soon as the cover of the collapsed presentation complex
is.**  The two chain complexes differ by the tree edges, which carry no homology. -/
theorem treeCover_isAcyclic (hac : IsAcyclic (coverComplex N (treeRel T) hN)) :
    IsAcyclic (treeCover T N hN) := by
  classical
  refine ⟨?_, ?_, ?_⟩
  · -- `H₂ = 0`
    intro u v huv
    refine hac.h2 ?_
    rw [← piE_bdry2 (hN := hN), ← piE_bdry2 (hN := hN), huv]
  · -- `H₁ = 0`
    intro c hc
    have h1 : bdry1 (coverComplex N (treeRel T) hN) (piE T N c) = 0 := by
      rw [← piV_bdry1 (hN := hN), hc, map_zero]
    obtain ⟨u, hu⟩ := hac.h1 _ h1
    refine ⟨u, ?_⟩
    have hz : piE T N (c - bdry2 (treeCover T N hN) u) = 0 := by
      rw [map_sub, piE_bdry2 (hN := hN), hu, sub_self]
    have hb : bdry1 (treeCover T N hN) (c - bdry2 (treeCover T N hN) u) = 0 := by
      rw [map_sub, hc, bdry1_bdry2, sub_zero]
    have hzero := treeChain_eq_zero (N := N) (hN := hN) (support_isTree_of_piE_eq_zero (N := N) hz) hb
    exact (sub_eq_zero.1 hzero).symm
  · -- `H̃₀ = 0`
    intro c hc
    have hpiv : augC (coverComplex N (treeRel T) hN) (piV T N c) = 0 := by
      rw [augC_piV (hN := hN), hc]
    obtain ⟨u, hu⟩ := hac.h0 _ hpiv
    refine ⟨treeCorr T N c + sectionE T N u, ?_⟩
    rw [map_add, bdry1_treeCorr (hN := hN), bdry1_sectionE (hN := hN), hu]
    exact sub_add_cancel c _

end SpanningTree
end Comb
end FiniteChains
