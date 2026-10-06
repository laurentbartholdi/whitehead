import RequestProject.SubstOneWayBlockLoops
import RequestProject.TreePresentation
import RequestProject.CombPi1Conj

/-!
# The block of the article: its spine, its marked presentation, its loops and its fillings

`RequestProject/SubstOneWayQuotient.lean` reduces the injectivity of the structural homomorphism
`FiniteChains.BlockFamily.substHomF` of the actual substitution to a marked homomorphism of each
substituted block into the fundamental group of the quotient `Q = Z/Γ` of the model of modified
chambers.  This file constructs that homomorphism **for the block itself**, and constructs the
block presentation it is defined on **from the geometry of the block**, not as data.

The block is the truncated cube complex

    `M = C(L) ∖ (the all-positive vertex)`,

which inside the quotient is the poset `FiniteChains.Davis.QOld A` of retained cubes; the
boundary of the chamber — the cut surface — is the subposet of the cubes `(σ, 0)` of a nonempty
simplex `σ`, that is, the image of `FiniteChains.Davis.posQCube`.  Everything is read off the
two-dimensional order complex of that poset:

* `FiniteChains.Davis.spineGens` — the **internal generators** `Z` of the block: the edges of
  the block outside a spanning tree of its one-skeleton (the generators of the presentation
  carried by the two-dimensional spine of the block);
* `FiniteChains.Davis.spineBeta` — the **relators** `β_m` of the marked presentation
  `B_q = ⟨s_h, t_h, Z ∣ β_m⟩`: one relator for every two-cell of the block, and one *marking
  relator* for every distinguished generator `s_h`, which says that `s_h` is the word spelled by
  the corresponding loop of the cut surface inside the block;
* `FiniteChains.Davis.blockToQ` — the **geometric loops**: the homomorphism which carries the
  class of a loop of the block to its class in `Q`, conjugated to the base point of the copy of
  the base along the fixed path through the cylinder;
* `FiniteChains.Davis.blockToQ_surfLoop` — the **cylinder computation**: the class in `Q` of a
  loop of the cut surface, read through the block, equals the class of its image under the
  attaching map, read through the base copy.  This is the naturality homotopy of the mapping
  cylinder, and it is what makes the marking relators die;
* `FiniteChains.Davis.injective_substHomF_of_spine` — **the application**: for the marked
  presentation just constructed, the structural homomorphism of the actual simultaneous
  substitution is injective.  The relators of the block are filled by the two-cells of the block
  (`FiniteChains.Comb.SpanningTree.freeToPi1_treeRel`) and the marking relators by the cylinder;
  the only remaining input is the attaching map itself, through the hypothesis that it reads the
  prescribed old word `u_h` along the chosen loop of the cut surface.
-/

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains
namespace Davis

open RACG Mirror Comb PresModel BlockFamily

universe u

variable {V : Type u} [DecidableEq V] [Fintype V] {A : CommRel V}

/-- The retained cubes of `C(L)` form a poset: the face order of the cubes. -/
instance : PartialOrder (QOld A) := Subtype.partialOrder _

omit [Fintype V] in
theorem qOld_le_iff {c d : QOld A} : c ≤ d ↔ c.1 ≤ d.1 := Iff.rfl

/-! ### The cut surface inside the block -/

/-- The cube `(σ, 0)` of a nonempty simplex `σ`: a cell of the cut surface, that is, of the part
of the block which is glued to the copy of the base. -/
def posQCube (σ : NeSpx A) : QOld A :=
  ⟨⟨σ.1, 0, σ.2.2, fun _ _ => rfl⟩, fun h => (Finset.nonempty_iff_ne_empty.mp σ.2.1) h.1⟩

omit [Fintype V] in
theorem posQCube_monotone : Monotone (posQCube (A := A)) := fun _ _ h => ⟨h, fun _ _ => rfl⟩

/-- The cut surface as a cellular map into the block. -/
def surfCx (A : CommRel V) : Hom (orderCx (NeSpx A)) (orderCx (QOld A)) :=
  orderCxMap posQCube posQCube_monotone

section Block

variable {X : Type u} [Preorder X] {att : NeSpx A →o X}

/-- The block inside the quotient `Q`: a retained cube is a cell of `Q`. -/
def qOldIncl (c : QOld A) : Qpos A X att := qOld c.1 c.2

omit [Fintype V] in
theorem qOldIncl_monotone : Monotone (qOldIncl (X := X) (att := att)) := fun _ _ h => h

/-- The block as a cellular map into the quotient. -/
def blockCx (A : CommRel V) (X : Type u) [Preorder X] (att : NeSpx A →o X) :
    Hom (orderCx (QOld A)) (orderCx (Qpos A X att)) :=
  orderCxMap qOldIncl qOldIncl_monotone

omit [Fintype V] in
/-- **The defining relation of the cylinder**: the image of a cell of the cut surface under the
attaching map lies below that cell. -/
theorem qNew_att_le_qOldIncl (σ : NeSpx A) :
    (qNew (A := A) (att := att) (att σ)) ≤ qOldIncl (posQCube σ) :=
  ⟨rfl, σ.2.1, le_refl _⟩

end Block

/-! ### The block inside the quotient, based at the base point of the copy of the base -/

section Spine

variable {α J : Type u} (ρ : J → FreeGroup α) (att : NeSpx A →o presModelPos ρ) (σ₀ : NeSpx A)
  (cb : List ((orderCx (presModelPos ρ)).E × Bool)) (T : SpanningTree (orderCx (QOld A)))

/-- The cut surface, mapped into the quotient through the block. -/
noncomputable abbrev surfQ : (NeSpx A) → Qpos A (presModelPos ρ) att :=
  fun σ => qOldIncl (X := presModelPos ρ) (att := att) (posQCube σ)

omit [Fintype V] in
theorem surfQ_monotone : Monotone (surfQ ρ att) :=
  qOldIncl_monotone.comp posQCube_monotone

/-- The cut surface, mapped into the quotient through the copy of the base by the attaching
map. -/
noncomputable abbrev surfBase : (NeSpx A) → Qpos A (presModelPos ρ) att :=
  fun σ => qNew (att σ)

omit [Fintype V] in
theorem surfBase_monotone : Monotone (surfBase ρ att) :=
  qNew_monotone.comp att.monotone

/-- **The path from the base point of the copy of the base to the block**: the chosen path of
the base copy to the image of the base simplex, followed by the cylinder edge. -/
noncomputable def cylPath : List ((orderCx (Qpos A (presModelPos ρ) att)).E × Bool) :=
  mapPath (qInclCx ρ att) cb ++ [ordPos (qNew_att_le_qOldIncl (att := att) σ₀)]

omit [Fintype V] in
theorem isPath_cylPath (hcb : IsPath (orderCx (presModelPos ρ)).src (orderCx (presModelPos ρ)).tgt
    cb (ptBase (presWords ρ)) (att σ₀)) :
    IsPath (orderCx (Qpos A (presModelPos ρ) att)).src (orderCx (Qpos A (presModelPos ρ) att)).tgt
      (cylPath ρ att σ₀ cb) (qBasePt ρ att) (surfQ ρ att σ₀) :=
  isPath_append_iff.mpr ⟨_, isPath_mapPath (qInclCx ρ att) hcb, isPath_ordPos _⟩

/-- The path from the base point of the copy of the base to the root of the spanning tree of the
block: the cylinder path followed by the tree path backwards. -/
noncomputable def rootPath : List ((orderCx (Qpos A (presModelPos ρ) att)).E × Bool) :=
  cylPath ρ att σ₀ cb ++
    revPath (mapPath (blockCx A (presModelPos ρ) att) (T.treePath (posQCube σ₀)))

omit [Fintype V] in
theorem isPath_rootPath (hcb : IsPath (orderCx (presModelPos ρ)).src (orderCx (presModelPos ρ)).tgt
    cb (ptBase (presWords ρ)) (att σ₀)) :
    IsPath (orderCx (Qpos A (presModelPos ρ) att)).src (orderCx (Qpos A (presModelPos ρ) att)).tgt
      (rootPath ρ att σ₀ cb T) (qBasePt ρ att)
      (qOldIncl (X := presModelPos ρ) (att := att) T.root) :=
  (isPath_cylPath ρ att σ₀ cb hcb).append
    (isPath_revPath (isPath_mapPath _ (T.treePath_isPath (posQCube σ₀))))

/-- **The geometric loops of the block**: the class of a loop of the block, transported to the
base point of the copy of the base along the fixed path through the cylinder. -/
noncomputable def blockToQ (hcb : IsPath (orderCx (presModelPos ρ)).src
    (orderCx (presModelPos ρ)).tgt cb (ptBase (presWords ρ)) (att σ₀)) :
    Pi1 (orderCx (QOld A)) T.root →*
      Pi1 (orderCx (Qpos A (presModelPos ρ) att)) (qBasePt ρ att) :=
  (pi1Conj (isPath_rootPath ρ att σ₀ cb T hcb)).comp
    (pi1Map (blockCx A (presModelPos ρ) att) T.root)

omit [Fintype V] in
/-- **The cylinder computation.**  A loop of the cut surface, read inside the block and
transported to the base point, is the image of its attaching word read inside the copy of the
base.  This is the naturality homotopy of the mapping cylinder `qNew (att σ) ≤ (σ, 0)`. -/
theorem blockToQ_surfLoop
    (hcb : IsPath (orderCx (presModelPos ρ)).src (orderCx (presModelPos ρ)).tgt cb
      (ptBase (presWords ρ)) (att σ₀))
    {p : List ((orderCx (NeSpx A)).E × Bool)}
    (hp : IsPath (orderCx (NeSpx A)).src (orderCx (NeSpx A)).tgt p σ₀ σ₀) :
    blockToQ ρ att σ₀ cb T hcb (SpanningTree.loopOf T (isPath_mapPath (surfCx A) hp))
      = pi1Map (qInclCx ρ att) (ptBase (presWords ρ))
          (pi1Conj hcb (Pi1.mk ⟨mapPath (orderCxMap att att.monotone) p,
            isPath_mapPath _ hp⟩)) := by
  classical
  have htp : IsPath (orderCx (QOld A)).src (orderCx (QOld A)).tgt (T.treePath (posQCube σ₀))
      T.root (posQCube σ₀) := T.treePath_isPath _
  have hmtp := isPath_mapPath (blockCx A (presModelPos ρ) att) htp
  have hcyl := isPath_cylPath ρ att σ₀ cb hcb
  set X : Pi1 (orderCx (QOld A)) (posQCube σ₀) :=
    Pi1.mk ⟨mapPath (surfCx A) p, isPath_mapPath (surfCx A) hp⟩ with hX
  set Y : Pi1 (orderCx (presModelPos ρ)) (att σ₀) :=
    Pi1.mk ⟨mapPath (orderCxMap att att.monotone) p, isPath_mapPath _ hp⟩ with hY
  set Z : Pi1 (orderCx (Qpos A (presModelPos ρ) att)) (surfBase ρ att σ₀) :=
    Pi1.mk ⟨mapPath (orderCxMap (surfBase ρ att) (surfBase_monotone ρ att)) p,
      isPath_mapPath _ hp⟩ with hZ
  -- the tree path cancels against its reverse
  have hcancel : Htpy (orderCx (Qpos A (presModelPos ρ) att)) (qBasePt ρ att) (surfQ ρ att σ₀)
      (rootPath ρ att σ₀ cb T ++ mapPath (blockCx A (presModelPos ρ) att)
        (T.treePath (posQCube σ₀))) (cylPath ρ att σ₀ cb) := by
    have h := (htpy_revPath_append hmtp).congr_append hcyl (isPath_nil' (surfQ ρ att σ₀))
    simpa [rootPath, List.append_assoc] using h
  -- the cylinder edge cancels
  have hback : Htpy (orderCx (Qpos A (presModelPos ρ) att)) (qBasePt ρ att) (surfBase ρ att σ₀)
      (cylPath ρ att σ₀ cb ++ [ordNeg (qNew_att_le_qOldIncl (att := att) σ₀)])
      (mapPath (qInclCx ρ att) cb) := by
    have h := (htpy_ordPos_ordNeg (qNew_att_le_qOldIncl (att := att) σ₀)).congr_append
      (isPath_mapPath (qInclCx ρ att) hcb) (isPath_nil' (surfBase ρ att σ₀))
    simpa [cylPath, List.append_assoc] using h
  -- the naturality homotopy of the cylinder
  have hnat := htpy_loop_mapPath_le (surfBase_monotone ρ att) (surfQ_monotone ρ att)
    (fun σ => qNew_att_le_qOldIncl (att := att) σ) hp
  have hE : pi1Map (blockCx A (presModelPos ρ) att) (posQCube σ₀) X
      = pi1Conj (isPath_ordNeg (qNew_att_le_qOldIncl (att := att) σ₀)) Z := by
    refine Quotient.sound ?_
    show Htpy (orderCx (Qpos A (presModelPos ρ) att)) (surfQ ρ att σ₀) (surfQ ρ att σ₀)
      (mapPath (blockCx A (presModelPos ρ) att) (mapPath (surfCx A) p))
      ([ordNeg (qNew_att_le_qOldIncl (att := att) σ₀)] ++
        mapPath (orderCxMap (surfBase ρ att) (surfBase_monotone ρ att)) p ++
        [ordPos (qNew_att_le_qOldIncl (att := att) σ₀)])
    have hlist : mapPath (blockCx A (presModelPos ρ) att) (mapPath (surfCx A) p)
        = mapPath (orderCxMap (surfQ ρ att) (surfQ_monotone ρ att)) p := by
      simp [mapPath, blockCx, surfCx, orderCxMap, List.map_map, Function.comp_def]
    rw [hlist]
    exact hnat
  have hH : Z = pi1Map (qInclCx ρ att) (att σ₀) Y := by
    refine Quotient.sound ?_
    show Htpy (orderCx (Qpos A (presModelPos ρ) att)) (surfBase ρ att σ₀) (surfBase ρ att σ₀)
      (mapPath (orderCxMap (surfBase ρ att) (surfBase_monotone ρ att)) p)
      (mapPath (qInclCx ρ att) (mapPath (orderCxMap att att.monotone) p))
    have hlist : mapPath (qInclCx ρ att) (mapPath (orderCxMap att att.monotone) p)
        = mapPath (orderCxMap (surfBase ρ att) (surfBase_monotone ρ att)) p := by
      simp [mapPath, orderCxMap, List.map_map, Function.comp_def]
    rw [hlist]
    exact Htpy.refl _
  calc blockToQ ρ att σ₀ cb T hcb (SpanningTree.loopOf T (isPath_mapPath (surfCx A) hp))
      = pi1Conj (isPath_rootPath ρ att σ₀ cb T hcb)
          (pi1Map (blockCx A (presModelPos ρ) att) T.root (pi1Conj htp X)) := rfl
    _ = pi1Conj (isPath_rootPath ρ att σ₀ cb T hcb)
          (pi1Conj hmtp (pi1Map (blockCx A (presModelPos ρ) att) (posQCube σ₀) X)) :=
        congrArg _ (pi1Map_pi1Conj (blockCx A (presModelPos ρ) att) htp X)
    _ = pi1Conj ((isPath_rootPath ρ att σ₀ cb T hcb).append hmtp)
          (pi1Map (blockCx A (presModelPos ρ) att) (posQCube σ₀) X) :=
        pi1Conj_pi1Conj _ hmtp _
    _ = pi1Conj hcyl (pi1Map (blockCx A (presModelPos ρ) att) (posQCube σ₀) X) :=
        pi1Conj_congr _ hcyl hcancel _
    _ = pi1Conj hcyl (pi1Conj (isPath_ordNeg (qNew_att_le_qOldIncl (att := att) σ₀)) Z) :=
        congrArg _ hE
    _ = pi1Conj (hcyl.append (isPath_ordNeg (qNew_att_le_qOldIncl (att := att) σ₀))) Z :=
        pi1Conj_pi1Conj _ _ _
    _ = pi1Conj (isPath_mapPath (qInclCx ρ att) hcb) Z :=
        pi1Conj_congr _ (isPath_mapPath (qInclCx ρ att) hcb) hback _
    _ = pi1Conj (isPath_mapPath (qInclCx ρ att) hcb)
          (pi1Map (qInclCx ρ att) (att σ₀) Y) := congrArg _ hH
    _ = pi1Map (qInclCx ρ att) (ptBase (presWords ρ)) (pi1Conj hcb Y) :=
        (pi1Map_pi1Conj (qInclCx ρ att) hcb Y).symm

end Spine

/-! ### The marked presentation of the block and the application -/

/-- **The internal generators `Z` of the block**: the edges of the two-dimensional order complex
of the block outside the chosen spanning tree of its one-skeleton. -/
abbrev spineGens (T : SpanningTree (orderCx (QOld A))) : Type u := SpanningTree.NonTree T

/-- **The relators of the marked block presentation** `B_q = ⟨s_h, t_h, Z ∣ β_m⟩`: the two-cells
of the block, and one marking relator per distinguished generator. -/
abbrev spineRels (Su : Type u) : Type u := (orderCx (QOld A)).F ⊕ Su

/-- **The marked presentation of the block read off its geometry.**  A two-cell of the block
contributes the word spelled by its attaching path; a distinguished generator `s_h` contributes
the marking relator `s_h · w_h⁻¹`, where `w_h` is the word in the internal generators spelled by
the chosen loop `sig h` of the cut surface, read inside the block. -/
noncomputable def spineBeta {Su : Type u} (T : SpanningTree (orderCx (QOld A)))
    (sig : Su → List ((orderCx (NeSpx A)).E × Bool)) :
    spineRels (A := A) Su → FreeGroup (Su ⊕ spineGens T)
  | Sum.inl f => FreeGroup.map Sum.inr (SpanningTree.treeRel T f)
  | Sum.inr x => FreeGroup.of (Sum.inl x) *
      (FreeGroup.map Sum.inr (SpanningTree.pathWord T (mapPath (surfCx A) (sig x))))⁻¹

section Application

variable {α J : Type u} (ρ : J → FreeGroup α) (att : NeSpx A →o presModelPos ρ) (σ₀ : NeSpx A)
  (cb : List ((orderCx (presModelPos ρ)).E × Bool)) (T : SpanningTree (orderCx (QOld A)))
  {Su : Type u}

/-- **The marked homomorphism of the block into the fundamental group of the quotient.**  A
distinguished generator goes to the image of its prescribed old word; an internal generator to
the class of its edge loop in the block, transported to the base point through the cylinder. -/
noncomputable def bqHom (hcb : IsPath (orderCx (presModelPos ρ)).src
    (orderCx (presModelPos ρ)).tgt cb (ptBase (presWords ρ)) (att σ₀))
    (u : Su → FreeGroup α) :
    FreeGroup (Su ⊕ spineGens T) →*
      Pi1 (orderCx (Qpos A (presModelPos ρ) att)) (qBasePt ρ att) :=
  FreeGroup.lift (Sum.elim (fun x => baseToQuotient ρ att (QuotientGroup.mk (u x)))
    (fun z => blockToQ ρ att σ₀ cb T hcb (SpanningTree.genLoop T z)))

omit [Fintype V] in
theorem bqHom_map_inr (hcb : IsPath (orderCx (presModelPos ρ)).src
    (orderCx (presModelPos ρ)).tgt cb (ptBase (presWords ρ)) (att σ₀))
    (u : Su → FreeGroup α) (w : FreeGroup (spineGens T)) :
    bqHom ρ att σ₀ cb T hcb u (FreeGroup.map (Sum.inr (α := Su)) w)
      = blockToQ ρ att σ₀ cb T hcb (SpanningTree.freeToPi1 T w) := by
  have key : (bqHom ρ att σ₀ cb T hcb u).comp (FreeGroup.map (Sum.inr (α := Su)))
      = (blockToQ ρ att σ₀ cb T hcb).comp (SpanningTree.freeToPi1 T) := by
    refine FreeGroup.ext_hom _ _ fun z => ?_
    simp [bqHom, SpanningTree.freeToPi1]
  exact DFunLike.congr_fun key w

omit [Fintype V] in
/-- **The two-cells of the block fill its relators.** -/
theorem bqHom_treeRel (hcb : IsPath (orderCx (presModelPos ρ)).src
    (orderCx (presModelPos ρ)).tgt cb (ptBase (presWords ρ)) (att σ₀))
    (u : Su → FreeGroup α) (f : (orderCx (QOld A)).F) :
    bqHom ρ att σ₀ cb T hcb u (FreeGroup.map (Sum.inr (α := Su)) (SpanningTree.treeRel T f))
      = 1 := by
  rw [bqHom_map_inr, SpanningTree.freeToPi1_treeRel, map_one]

omit [Fintype V] in
/-- **The cylinder fills the marking relators**: the loop of the cut surface, read inside the
block, is the prescribed old word read inside the copy of the base. -/
theorem bqHom_markRel (hcb : IsPath (orderCx (presModelPos ρ)).src
    (orderCx (presModelPos ρ)).tgt cb (ptBase (presWords ρ)) (att σ₀))
    (lw : Su → List (α × Bool)) (sig : Su → List ((orderCx (NeSpx A)).E × Bool))
    (hsig : ∀ x, IsPath (orderCx (NeSpx A)).src (orderCx (NeSpx A)).tgt (sig x) σ₀ σ₀)
    (hread : ∀ x, Htpy (orderCx (presModelPos ρ)) (ptBase (presWords ρ)) (ptBase (presWords ρ))
      (cb ++ mapPath (orderCxMap att att.monotone) (sig x) ++ revPath cb)
      (wordLoop (presWords ρ) (lw x)))
    (x : Su) :
    bqHom ρ att σ₀ cb T hcb (fun y => FreeGroup.mk (lw y))
        (spineBeta T sig (Sum.inr x)) = 1 := by
  have hpw := SpanningTree.freeToPi1_pathWord T (isPath_mapPath (surfCx A) (hsig x))
  have hgeom := blockToQ_surfLoop ρ att σ₀ cb T hcb (hsig x)
  have hbase : pi1Conj hcb (Pi1.mk ⟨mapPath (orderCxMap att att.monotone) (sig x),
      isPath_mapPath _ (hsig x)⟩) = alphaHom ρ (QuotientGroup.mk (FreeGroup.mk (lw x))) := by
    rw [alphaHom_mk, alphaFree_mk]
    exact Quotient.sound (hread x)
  have hval : bqHom ρ att σ₀ cb T hcb (fun y => FreeGroup.mk (lw y))
      (FreeGroup.map (Sum.inr (α := Su))
        (SpanningTree.pathWord T (mapPath (surfCx A) (sig x))))
      = baseToQuotient ρ att (QuotientGroup.mk (FreeGroup.mk (lw x))) := by
    rw [bqHom_map_inr, hpw, hgeom, hbase]
    rfl
  rw [spineBeta, map_mul, map_inv, hval]
  simp [bqHom]


end Application

end Davis
end FiniteChains
