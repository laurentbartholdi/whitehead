module

public import RequestProject.SpanningTree
public import RequestProject.PresentationDictionary

@[expose] public section

/-!
# The presentation of `π₁` read off a spanning tree

Let `K` be a combinatorial two-complex and `T` a spanning tree of its one-skeleton
(`RequestProject/SpanningTree.lean`).  Collapsing `T` turns `K` into a presentation complex,
whose generators are the edges outside the tree and whose relators are the attaching words of
the two-cells with the tree letters deleted.  This file proves the group-theoretic half of
that statement, without any finiteness assumption:

* `FiniteChains.Comb.SpanningTree.NonTree` — the edges outside the tree;
* `FiniteChains.Comb.SpanningTree.pathWord` — the word in the non-tree edges spelled by an edge
  path (tree letters are deleted; this is the retraction `F(E) → F(E ∖ T)`);
* `FiniteChains.Comb.SpanningTree.treeRel` — the relator of a two-cell;
* `FiniteChains.Comb.SpanningTree.pi1EquivPres` — **the fundamental group of `K` at the root is
  the group presented by `⟨E ∖ T | attaching words⟩`**.

The proof is the classical one.  One homomorphism reads off the word spelled by an edge loop;
it is well defined because a backtrack spells a trivial word and an attaching path spells a
relator.  The other sends a non-tree edge `e` to the loop "tree path to the source of `e`, then
`e`, then back along the tree path from the target"; the verification that the relators die is
`freeToPi1_pathWord`, which computes the image of an arbitrary path.
-/

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains
namespace Comb
namespace SpanningTree

universe u

variable {K : Complex2.{u}} (T : SpanningTree K)

/-! ### The word spelled by an edge path -/

/-- The edges of `K` outside the spanning tree: the generators of the presentation. -/
abbrev NonTree (T : SpanningTree K) : Type u := {e : K.E // ¬ T.isTree e}

open Classical in
/-- The letter contributed by an oriented edge: nothing for a tree edge, the generator (or its
inverse) for an edge outside the tree. -/
noncomputable def germWord (g : K.E × Bool) : FreeGroup (NonTree T) :=
  if h : T.isTree g.1 then 1 else
    if g.2 then FreeGroup.of (⟨g.1, h⟩ : NonTree T) else (FreeGroup.of (⟨g.1, h⟩ : NonTree T))⁻¹

/-- The word in the non-tree edges spelled by an edge path. -/
noncomputable def pathWord (l : List (K.E × Bool)) : FreeGroup (NonTree T) :=
  (l.map (germWord T)).prod

/-- The relator of a two-cell: the word spelled by its attaching path. -/
noncomputable def treeRel (f : K.F) : FreeGroup (NonTree T) := pathWord T (K.att f)

@[simp] theorem pathWord_nil : pathWord T [] = 1 := rfl

theorem pathWord_cons (g : K.E × Bool) (l : List (K.E × Bool)) :
    pathWord T (g :: l) = germWord T g * pathWord T l := by
  simp [pathWord]

theorem pathWord_append (l l' : List (K.E × Bool)) :
    pathWord T (l ++ l') = pathWord T l * pathWord T l' := by
  simp [pathWord, List.prod_append]

theorem germWord_revGerm (g : K.E × Bool) :
    germWord T (revGerm g) = (germWord T g)⁻¹ := by
  classical
  obtain ⟨e, b⟩ := g
  by_cases h : T.isTree e
  · simp [germWord, revGerm, h]
  · cases b <;> simp [germWord, revGerm, h]

theorem pathWord_revPath (l : List (K.E × Bool)) :
    pathWord T (revPath l) = (pathWord T l)⁻¹ := by
  induction l with
  | nil => simp [revPath]
  | cons g l ih =>
      rw [revPath_cons, pathWord_append, ih, pathWord_cons, germWord_revGerm]
      simp [pathWord]

theorem germWord_of_isTree {g : K.E × Bool} (h : T.isTree g.1) : germWord T g = 1 := by
  classical
  simp [germWord, h]

theorem pathWord_eq_one_of_tree {l : List (K.E × Bool)} (hl : ∀ g ∈ l, T.isTree g.1) :
    pathWord T l = 1 := by
  induction l with
  | nil => simp
  | cons g l ih =>
      rw [pathWord_cons, germWord_of_isTree T (hl g (by simp)), one_mul]
      exact ih (fun g' hg' => hl g' (by simp [hg']))

/-- Tree paths spell the empty word. -/
@[simp] theorem pathWord_treePath (a : K.V) : pathWord T (T.treePath a) = 1 :=
  pathWord_eq_one_of_tree T (fun _ hg => T.isTree_of_mem_treePath a hg)

/-! ### From edge loops to the presented group -/

/-- The class of the word spelled by an edge path, in the presented group. -/
noncomputable def wordClass (l : List (K.E × Bool)) : PresGroup (treeRel T) :=
  QuotientGroup.mk (pathWord T l)

theorem wordClass_append (l l' : List (K.E × Bool)) :
    wordClass T (l ++ l') = wordClass T l * wordClass T l' := by
  unfold wordClass
  rw [pathWord_append, QuotientGroup.mk_mul]

theorem wordClass_att (f : K.F) : wordClass T (K.att f) = 1 := by
  rw [show wordClass T (K.att f) = QuotientGroup.mk (treeRel T f) from rfl,
    QuotientGroup.eq_one_iff]
  exact Subgroup.subset_normalClosure ⟨f, rfl⟩

theorem wordClass_cancels {l l' : List (K.E × Bool)} (h : Cancels K l l') :
    wordClass T l = wordClass T l' := by
  rcases h with ⟨p, q, g, hl, hl'⟩ | ⟨p, q, f, hl, hl'⟩
  · subst hl; subst hl'
    rw [wordClass_append, wordClass_append]
    congr 1
    show QuotientGroup.mk (pathWord T (g :: revGerm g :: q)) = QuotientGroup.mk (pathWord T q)
    rw [pathWord_cons, pathWord_cons, germWord_revGerm]
    group
  · subst hl; subst hl'
    rw [wordClass_append, wordClass_append, wordClass_append, wordClass_att, mul_one]

theorem wordClass_htpy {a b : K.V} {l l' : List (K.E × Bool)} (h : Htpy K a b l l') :
    wordClass T l = wordClass T l' := by
  induction h with
  | refl => rfl
  | tail _ hstep ih =>
      rcases hstep with hs | hs
      · exact ih.trans (wordClass_cancels T hs.2.2)
      · exact ih.trans (wordClass_cancels T hs.2.2).symm

/-- The homomorphism `π₁(K) → ⟨E ∖ T | r⟩` reading off the word spelled by an edge loop. -/
noncomputable def pi1ToPres : Pi1 K T.root →* PresGroup (treeRel T) where
  toFun := Quotient.lift (fun p => wordClass T p.1) (fun _ _ h => wordClass_htpy T h)
  map_one' := rfl
  map_mul' := by
    rintro ⟨p⟩ ⟨q⟩
    exact wordClass_append T p.1 q.1

@[simp] theorem pi1ToPres_mk (p : Loop K T.root) :
    pi1ToPres T (Pi1.mk p) = wordClass T p.1 := rfl

/-! ### From the presented group to edge loops -/

/-- The loop obtained from a path by prefixing and suffixing tree paths. -/
noncomputable def conjPath (l : List (K.E × Bool)) (a b : K.V) : List (K.E × Bool) :=
  T.treePath a ++ l ++ revPath (T.treePath b)

theorem conjPath_isLoop {l : List (K.E × Bool)} {a b : K.V}
    (hl : IsPath K.src K.tgt l a b) :
    IsPath K.src K.tgt (conjPath T l a b) T.root T.root :=
  isPath_append_iff.mpr ⟨b, isPath_append_iff.mpr ⟨a, T.treePath_isPath a, hl⟩,
    isPath_revPath (T.treePath_isPath b)⟩

/-- The class in `π₁(K, root)` of a path, conjugated into a loop by the tree paths. -/
noncomputable def loopOf {l : List (K.E × Bool)} {a b : K.V}
    (hl : IsPath K.src K.tgt l a b) : Pi1 K T.root :=
  Pi1.mk ⟨conjPath T l a b, conjPath_isLoop T hl⟩

theorem loopOf_congr {l l' : List (K.E × Bool)} {a b : K.V}
    (hl : IsPath K.src K.tgt l a b) (hl' : IsPath K.src K.tgt l' a b)
    (h : Htpy K a b l l') : loopOf T hl = loopOf T hl' :=
  Quotient.sound (h.congr_append (T.treePath_isPath a) (isPath_revPath (T.treePath_isPath b)))

@[simp] theorem loopOf_nil (a : K.V) :
    loopOf T (l := []) (a := a) (b := a) rfl = 1 := by
  refine Quotient.sound ?_
  show Htpy K T.root T.root (conjPath T [] a a) []
  simpa [conjPath] using htpy_append_revPath (T.treePath_isPath a)

/-- Concatenation of paths corresponds to multiplication of their classes. -/
theorem loopOf_mul {p q : List (K.E × Bool)} {a m b : K.V}
    (hp : IsPath K.src K.tgt p a m) (hq : IsPath K.src K.tgt q m b) :
    loopOf T hp * loopOf T hq = loopOf T (hp.append hq) := by
  refine Quotient.sound ?_
  show Htpy K T.root T.root (conjPath T p a m ++ conjPath T q m b) (conjPath T (p ++ q) a b)
  have hcancel : Htpy K m m (revPath (T.treePath m) ++ T.treePath m) [] :=
    htpy_revPath_append (T.treePath_isPath m)
  have hleft : IsPath K.src K.tgt (T.treePath a ++ p) T.root m :=
    isPath_append_iff.mpr ⟨a, T.treePath_isPath a, hp⟩
  have hright : IsPath K.src K.tgt (q ++ revPath (T.treePath b)) m T.root :=
    isPath_append_iff.mpr ⟨b, hq, isPath_revPath (T.treePath_isPath b)⟩
  have hmain := hcancel.congr_append hleft hright
  have hrw₁ : (T.treePath a ++ p) ++ (revPath (T.treePath m) ++ T.treePath m) ++
      (q ++ revPath (T.treePath b)) = conjPath T p a m ++ conjPath T q m b := by
    simp [conjPath, List.append_assoc]
  have hrw₂ : (T.treePath a ++ p) ++ ([] : List (K.E × Bool)) ++
      (q ++ revPath (T.treePath b)) = conjPath T (p ++ q) a b := by
    simp [conjPath, List.append_assoc]
  rw [hrw₁, hrw₂] at hmain
  exact hmain

/-- Reversing a path inverts its class. -/
theorem loopOf_rev {l : List (K.E × Bool)} {a b : K.V} (hl : IsPath K.src K.tgt l a b) :
    loopOf T (isPath_revPath hl) = (loopOf T hl)⁻¹ := by
  refine Quotient.sound ?_
  show Htpy K T.root T.root (conjPath T (revPath l) b a) (revPath (conjPath T l a b))
  have hrw : revPath (conjPath T l a b) = conjPath T (revPath l) b a := by
    simp [conjPath, revPath_append, List.append_assoc, revPath_revPath]
  rw [hrw]
  exact Htpy.refl _

/-- `loopOf` depends only on the path and its endpoints. -/
theorem loopOf_eq {l l' : List (K.E × Bool)} {a b a' b' : K.V}
    (hl : IsPath K.src K.tgt l a b) (hl' : IsPath K.src K.tgt l' a' b')
    (hll : l = l') (ha : a = a') (hb : b = b') : loopOf T hl = loopOf T hl' := by
  subst hll; subst ha; subst hb; rfl

/-- The loop of a single non-tree edge: the generator of the presentation. -/
noncomputable def genLoop (e : NonTree T) : Pi1 K T.root :=
  loopOf T (isPath_single ((e : K.E), true))

/-- The homomorphism from the free group on the non-tree edges to `π₁(K)`. -/
noncomputable def freeToPi1 : FreeGroup (NonTree T) →* Pi1 K T.root :=
  FreeGroup.lift (genLoop T)

@[simp] theorem freeToPi1_of (e : NonTree T) :
    freeToPi1 T (FreeGroup.of e) = genLoop T e := by
  simp [freeToPi1]

/-- A tree edge, traversed from the vertex towards the root, gives the trivial class. -/
theorem loopOf_up {a : K.V} (ha : a ≠ T.root) :
    loopOf T (isPath_single (T.up a ha)) = 1 := by
  set u := T.up a ha with hu
  set m := T.parent a ha with hm
  have hsrc : germSrc K.src K.tgt u = a := T.up_src a ha
  have htgt : germTgt K.src K.tgt u = m := rfl
  have hpar : T.treePath a = T.treePath m ++ [revGerm u] := T.treePath_of_ne ha
  refine Quotient.sound ?_
  show Htpy K T.root T.root
    (conjPath T [u] (germSrc K.src K.tgt u) (germTgt K.src K.tgt u)) []
  have hrw : conjPath T [u] (germSrc K.src K.tgt u) (germTgt K.src K.tgt u) =
      (T.treePath m ++ [revGerm u, u]) ++ revPath (T.treePath m) := by
    rw [conjPath, hsrc, htgt, hpar]
    simp
  rw [hrw]
  have hpath : IsPath K.src K.tgt [revGerm u, u] m m := by
    refine ⟨?_, ?_, ?_⟩
    · simp [hm, parent, hu]
    · simp
    · exact htgt
  have hstep : Htpy K m m [revGerm u, u] [] := by
    refine Htpy.of_step ⟨hpath, rfl, Or.inl ⟨[], [], revGerm u, ?_, rfl⟩⟩
    simp
  have hbig := hstep.congr_append (T.treePath_isPath m) (isPath_revPath (T.treePath_isPath m))
  refine hbig.trans ?_
  simpa using htpy_append_revPath (T.treePath_isPath m)

/-- A tree edge, traversed in either direction, gives the trivial class. -/
theorem loopOf_single_eq_one_of_isTree {g : K.E × Bool} (hg : T.isTree g.1) :
    loopOf T (isPath_single g) = 1 := by
  classical
  obtain ⟨a, ha, hae⟩ := (T.isTree_iff g.1).1 hg
  by_cases hb : g.2 = (T.up a ha).2
  · have hgeq : g = T.up a ha := Prod.ext hae.symm hb
    subst hgeq
    exact loopOf_up T ha
  · have hgeq : g = revGerm (T.up a ha) := by
      refine Prod.ext hae.symm ?_
      show g.2 = !(T.up a ha).2
      cases hg2 : g.2 <;> cases hu2 : (T.up a ha).2 <;> simp_all
    subst hgeq
    have h := loopOf_rev T (isPath_single (T.up a ha))
    rw [loopOf_up T ha, inv_one] at h
    rw [loopOf_eq T (isPath_single (revGerm (T.up a ha)))
      (isPath_revPath (isPath_single (T.up a ha))) (by simp [revPath]) (by simp) (by simp)]
    exact h

theorem freeToPi1_germWord (g : K.E × Bool) :
    freeToPi1 T (germWord T g) = loopOf T (isPath_single g) := by
  classical
  by_cases h : T.isTree g.1
  · rw [germWord_of_isTree T h, map_one, loopOf_single_eq_one_of_isTree T h]
  · obtain ⟨e, b⟩ := g
    cases b
    · have hgw : germWord T (e, false) = (FreeGroup.of (⟨e, h⟩ : NonTree T))⁻¹ := by
        simp [germWord, h]
      rw [hgw, map_inv, freeToPi1_of, genLoop]
      have h1 := loopOf_rev T (isPath_single ((e, true) : K.E × Bool))
      rw [← h1]
      all_goals rfl
    · have hgw : germWord T (e, true) = FreeGroup.of (⟨e, h⟩ : NonTree T) := by
        simp [germWord, h]
      rw [hgw, freeToPi1_of, genLoop]

/-- **The image of an arbitrary edge path**: the free group element it spells is sent to the
class of the path, conjugated into a loop by the tree paths. -/
theorem freeToPi1_pathWord {l : List (K.E × Bool)} {a b : K.V}
    (hl : IsPath K.src K.tgt l a b) :
    freeToPi1 T (pathWord T l) = loopOf T hl := by
  induction l generalizing a with
  | nil =>
      cases hl
      simp [pathWord]
  | cons g l ih =>
      obtain ⟨ha, hrest⟩ := hl
      subst ha
      rw [pathWord_cons, map_mul, freeToPi1_germWord T g, ih hrest]
      exact loopOf_mul T (isPath_single g) hrest

theorem freeToPi1_treeRel (f : K.F) : freeToPi1 T (treeRel T f) = 1 := by
  have hf := K.att_isLoop f
  rw [show treeRel T f = pathWord T (K.att f) from rfl, freeToPi1_pathWord T hf]
  refine Quotient.sound ?_
  show Htpy K T.root T.root (conjPath T (K.att f) (K.base f) (K.base f)) []
  have hstep : Htpy K (K.base f) (K.base f) (K.att f) [] :=
    Htpy.of_step ⟨hf, rfl, Or.inr ⟨[], [], f, by simp, rfl⟩⟩
  have hbig := hstep.congr_append (T.treePath_isPath (K.base f))
    (isPath_revPath (T.treePath_isPath (K.base f)))
  rw [conjPath]
  refine hbig.trans ?_
  simpa using htpy_append_revPath (T.treePath_isPath (K.base f))

theorem relSub_le_ker_freeToPi1 : relSub (treeRel T) ≤ (freeToPi1 T).ker := by
  refine Subgroup.normalClosure_le_normal ?_
  rintro x ⟨f, rfl⟩
  exact freeToPi1_treeRel T f

/-- The homomorphism `⟨E ∖ T | r⟩ → π₁(K)`. -/
noncomputable def presToPi1 : PresGroup (treeRel T) →* Pi1 K T.root :=
  QuotientGroup.lift (relSub (treeRel T)) (freeToPi1 T)
    (fun _ hx => relSub_le_ker_freeToPi1 T hx)

@[simp] theorem presToPi1_mk (w : FreeGroup (NonTree T)) :
    presToPi1 T (QuotientGroup.mk w) = freeToPi1 T w := rfl

/-! ### The isomorphism -/

theorem presToPi1_pi1ToPres (x : Pi1 K T.root) : presToPi1 T (pi1ToPres T x) = x := by
  induction x using Quotient.inductionOn with
  | h p =>
      obtain ⟨l, hl⟩ := p
      show presToPi1 T (wordClass T l) = Pi1.mk ⟨l, hl⟩
      rw [show wordClass T l = QuotientGroup.mk (pathWord T l) from rfl, presToPi1_mk,
        freeToPi1_pathWord T hl]
      refine Quotient.sound ?_
      show Htpy K T.root T.root (conjPath T l T.root T.root) l
      simpa [conjPath] using Htpy.refl (X := K) (a := T.root) (b := T.root) l

theorem pi1ToPres_presToPi1 (g : PresGroup (treeRel T)) :
    pi1ToPres T (presToPi1 T g) = g := by
  induction g using QuotientGroup.induction_on with
  | H w =>
      rw [presToPi1_mk]
      induction w using FreeGroup.induction_on with
      | one => simp
      | of e =>
          rw [freeToPi1_of, genLoop]
          show wordClass T (conjPath T [((e : K.E), true)] _ _) = _
          rw [conjPath, wordClass_append, wordClass_append]
          have h1 : wordClass T (T.treePath (germSrc K.src K.tgt ((e : K.E), true))) = 1 := by
            simp [wordClass]
          have h2 : wordClass T
              (revPath (T.treePath (germTgt K.src K.tgt ((e : K.E), true)))) = 1 := by
            simp [wordClass, pathWord_revPath]
          rw [h1, h2, one_mul, mul_one]
          show QuotientGroup.mk (pathWord T [((e : K.E), true)]) = _
          have hw : pathWord T [((e : K.E), true)] = FreeGroup.of e := by
            classical
            simp [pathWord, germWord, dif_neg e.2]
          rw [hw]
      | inv_of e ih =>
          rw [map_inv, map_inv, ih, QuotientGroup.mk_inv]
      | mul x y hx hy =>
          rw [map_mul, map_mul, hx, hy, ← QuotientGroup.mk_mul]

/-- **The fundamental group of a two-complex is presented by the non-tree edges and the
attaching words.**  For any spanning tree `T` of the one-skeleton, `π₁(K, root)` is isomorphic
to `⟨E ∖ T | the attaching words of the two-cells, with the tree letters deleted⟩`. -/
noncomputable def pi1EquivPres : Pi1 K T.root ≃* PresGroup (treeRel T) where
  toFun := pi1ToPres T
  invFun := presToPi1 T
  left_inv := presToPi1_pi1ToPres T
  right_inv := pi1ToPres_presToPi1 T
  map_mul' := (pi1ToPres T).map_mul

/-- **The fundamental group of a two-complex is the group presented by the non-tree edges and
the attaching words.** -/
theorem pi1_mulEquiv_presGroup :
    Nonempty (Pi1 K T.root ≃* PresGroup (treeRel T)) := ⟨pi1EquivPres T⟩

end SpanningTree
end Comb
end FiniteChains
