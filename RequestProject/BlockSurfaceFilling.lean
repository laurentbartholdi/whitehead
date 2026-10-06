module

public import RequestProject.BlockSpineSubst

@[expose] public section

/-!
# From a surface filling to the hypothesis `hfill` of the substitution

`RequestProject/BlockSpinePres.lean` reads the marked presentation `B = ⟨s_h, t_h, Z ∣ β_m⟩` of
the block off the two-dimensional spine of the block, and
`RequestProject/BlockSpineSubst.lean` deduces the injectivity of the structural homomorphism
`FiniteChains.BlockFamily.substHomF` of the simultaneous substitution — but only under the
hypothesis `hfill`, the hypothesis (B1) which says that the replaced relator dies in the
substituted presentation.

This file **derives** `hfill` from geometry: from a *filling of the surface relator inside the
cut surface of the block*.  The replaced relator is the surface word

    `∏_h [u_h, v_h]`

(the product of the commutators of the prescribed old words, over a list of pairs of
distinguished generators), and the geometric input is that the corresponding product of
commutators of the chosen loops of the cut surface is trivial in the fundamental group of the
cut surface — which is exactly what the polygon of the closed surface of genus `q` provides,
its boundary being that product of commutators.

* `FiniteChains.Davis.commWord` — the product of commutators over a list of pairs;
* `FiniteChains.Davis.mem_relSub_spineBeta_commWord` — the surface word in the distinguished
  generators is a consequence of the relators of the block, once its loops bound in the cut
  surface;
* `FiniteChains.Davis.filledF_of_surface_filling` — hence the replaced relator is a consequence
  of the substituted presentation: the hypothesis (B1);
* `FiniteChains.Davis.injective_substHomF_of_surface` — the application with `hfill`
  discharged: the only remaining inputs are the reading of the prescribed words by the
  attaching map and the filling of the surface relator.
-/

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains
namespace Davis

open RACG Mirror Comb PresModel BlockFamily

universe u v

/-! ### Products of commutators -/

/-- The product of the commutators `[f x, f y]` over a list of pairs `(x, y)`. -/
def commWord {ι : Type*} {G : Type*} [Group G] (f : ι → G) (ps : List (ι × ι)) : G :=
  (ps.map fun p => f p.1 * f p.2 * (f p.1)⁻¹ * (f p.2)⁻¹).prod

@[simp] theorem commWord_nil {ι : Type*} {G : Type*} [Group G] (f : ι → G) :
    commWord f [] = 1 := rfl

theorem commWord_cons {ι : Type*} {G : Type*} [Group G] (f : ι → G) (p : ι × ι)
    (ps : List (ι × ι)) :
    commWord f (p :: ps) = (f p.1 * f p.2 * (f p.1)⁻¹ * (f p.2)⁻¹) * commWord f ps := by
  simp [commWord]

/-- A homomorphism carries the product of commutators to the product of commutators of the
images. -/
theorem map_commWord {ι : Type*} {G H : Type*} [Group G] [Group H] (φ : G →* H) (f : ι → G)
    (ps : List (ι × ι)) : φ (commWord f ps) = commWord (fun i => φ (f i)) ps := by
  induction ps with
  | nil => simp
  | cons p ps ih => rw [commWord_cons, map_mul, ih, commWord_cons]; simp

theorem commWord_congr {ι : Type*} {G : Type*} [Group G] {f g : ι → G} (h : ∀ i, f i = g i)
    (ps : List (ι × ι)) : commWord f ps = commWord g ps := by
  simp only [commWord, h]

/-! ### Two general facts about normal closures -/

/-- A homomorphism carries a normal closure into any normal closure containing the images of the
generators. -/
theorem map_mem_normalClosure {G H : Type*} [Group G] [Group H] (φ : G →* H) {S : Set G}
    {N : Set H} (hS : ∀ g ∈ S, φ g ∈ Subgroup.normalClosure N) {x : G}
    (hx : x ∈ Subgroup.normalClosure S) : φ x ∈ Subgroup.normalClosure N := by
  have hle : Subgroup.normalClosure S ≤ (Subgroup.normalClosure N).comap φ :=
    Subgroup.normalClosure_le_normal (fun g hg => hS g hg)
  exact hle hx

/-- An element of the free group on the non-tree edges whose loop is null-homotopic is a
consequence of the relators of the spine presentation. -/
theorem mem_relSub_of_freeToPi1_eq_one {K : Complex2.{u}} (T : SpanningTree K)
    {w : FreeGroup (SpanningTree.NonTree T)} (h : SpanningTree.freeToPi1 T w = 1) :
    w ∈ relSub (SpanningTree.treeRel T) := by
  have hmk : (QuotientGroup.mk w : PresGroup (SpanningTree.treeRel T)) = 1 := by
    have := SpanningTree.pi1ToPres_presToPi1 T (QuotientGroup.mk w)
    rw [SpanningTree.presToPi1_mk, h, map_one] at this
    exact this.symm
  exact (QuotientGroup.eq_one_iff _).1 hmk

/-! ### The surface word is a consequence of the block relators -/

variable {V : Type u} [DecidableEq V] [Fintype V] {A : CommRel V}

/-- The homomorphism from the fundamental group of the cut surface to the fundamental group of
the block: read the loop inside the block and conjugate it to the root of the spanning tree. -/
noncomputable def surfToBlock (T : SpanningTree (orderCx (QOld A))) (σ₀ : NeSpx A) :
    Pi1 (orderCx (NeSpx A)) σ₀ →* Pi1 (orderCx (QOld A)) T.root :=
  (pi1Conj (T.treePath_isPath (posQCube σ₀))).comp (pi1Map (surfCx A) σ₀)

omit [Fintype V] in
theorem surfToBlock_mk (T : SpanningTree (orderCx (QOld A))) (σ₀ : NeSpx A)
    {p : List ((orderCx (NeSpx A)).E × Bool)}
    (hp : IsPath (orderCx (NeSpx A)).src (orderCx (NeSpx A)).tgt p σ₀ σ₀) :
    surfToBlock T σ₀ (Pi1.mk ⟨p, hp⟩)
      = SpanningTree.loopOf T (isPath_mapPath (surfCx A) hp) := rfl

omit [Fintype V] in
/-- **The surface word in the distinguished generators is a consequence of the relators of the
block.**  The marking relators identify each distinguished generator with the word spelled by
its loop of the cut surface; if the corresponding product of commutators of those loops bounds
in the cut surface, then the product of commutators of the distinguished generators is a
consequence of the relators `β_m`. -/
theorem mem_relSub_spineBeta_commWord (T : SpanningTree (orderCx (QOld A))) {Su : Type u}
    (σ₀ : NeSpx A) (sig : Su → List ((orderCx (NeSpx A)).E × Bool))
    (hsig : ∀ x, IsPath (orderCx (NeSpx A)).src (orderCx (NeSpx A)).tgt (sig x) σ₀ σ₀)
    (ps : List (Su × Su))
    (hfilling :
      commWord (fun x => Pi1.mk (⟨sig x, hsig x⟩ : Loop (orderCx (NeSpx A)) σ₀)) ps = 1) :
    commWord (fun x => FreeGroup.of (Sum.inl x : Su ⊕ spineGens T)) ps
      ∈ relSub (spineBeta T sig) := by
  classical
  -- the word spelled inside the block by the loop of the distinguished generator `x`
  set pw : Su → FreeGroup (spineGens T) :=
    fun x => SpanningTree.pathWord T (mapPath (surfCx A) (sig x)) with hpw
  -- the product of commutators of those words is a consequence of the two-cells of the block
  have htree : commWord pw ps ∈ relSub (SpanningTree.treeRel T) := by
    refine mem_relSub_of_freeToPi1_eq_one T ?_
    rw [map_commWord]
    have hval : ∀ x, SpanningTree.freeToPi1 T (pw x)
        = surfToBlock T σ₀ (Pi1.mk (⟨sig x, hsig x⟩ : Loop (orderCx (NeSpx A)) σ₀)) := by
      intro x
      rw [hpw, SpanningTree.freeToPi1_pathWord T (isPath_mapPath (surfCx A) (hsig x)),
        surfToBlock_mk]
    rw [commWord_congr hval ps, ← map_commWord, hfilling, map_one]
  -- pass to the group presented by the block
  set N : Subgroup (FreeGroup (Su ⊕ spineGens T)) := relSub (spineBeta T sig) with hN
  have hmk : (QuotientGroup.mk (commWord (fun x => FreeGroup.of (Sum.inl x : Su ⊕ spineGens T)) ps)
      : FreeGroup (Su ⊕ spineGens T) ⧸ N) = 1 := by
    have hgen : ∀ x : Su, (QuotientGroup.mk (FreeGroup.of (Sum.inl x : Su ⊕ spineGens T))
        : FreeGroup (Su ⊕ spineGens T) ⧸ N)
        = QuotientGroup.mk (FreeGroup.map Sum.inr (pw x)) := by
      intro x
      have hrel : spineBeta T sig (Sum.inr x) ∈ N :=
        Subgroup.subset_normalClosure ⟨Sum.inr x, rfl⟩
      have h1 : (QuotientGroup.mk (spineBeta T sig (Sum.inr x))
          : FreeGroup (Su ⊕ spineGens T) ⧸ N) = 1 := (QuotientGroup.eq_one_iff _).2 hrel
      rw [show spineBeta T sig (Sum.inr x)
          = FreeGroup.of (Sum.inl x) * (FreeGroup.map Sum.inr (pw x))⁻¹ from rfl,
        QuotientGroup.mk_mul, QuotientGroup.mk_inv] at h1
      exact mul_inv_eq_one.1 h1
    have hmap : (QuotientGroup.mk' N).comp (FreeGroup.map (Sum.inr (α := Su)))
        (commWord pw ps) = 1 := by
      have hmem : FreeGroup.map (Sum.inr (α := Su)) (commWord pw ps) ∈ N := by
        refine map_mem_normalClosure (FreeGroup.map (Sum.inr (α := Su))) ?_ htree
        rintro g ⟨f, rfl⟩
        exact Subgroup.subset_normalClosure ⟨Sum.inl f, rfl⟩
      exact (QuotientGroup.eq_one_iff _).2 hmem
    calc (QuotientGroup.mk' N) (commWord
          (fun x => FreeGroup.of (Sum.inl x : Su ⊕ spineGens T)) ps)
        = commWord (fun x => (QuotientGroup.mk' N)
            (FreeGroup.of (Sum.inl x : Su ⊕ spineGens T))) ps := map_commWord _ _ _
      _ = commWord (fun x => (QuotientGroup.mk' N) (FreeGroup.map Sum.inr (pw x))) ps :=
          commWord_congr (fun x => hgen x) ps
      _ = (QuotientGroup.mk' N) (FreeGroup.map (Sum.inr (α := Su)) (commWord pw ps)) := by
          rw [map_commWord, map_commWord]
      _ = 1 := hmap
  exact (QuotientGroup.eq_one_iff _).1 hmk

/-! ### The hypothesis (B1), derived -/

omit [Fintype V] in
/-- **The hypothesis (B1) of the substitution, derived from the filling of the surface
relator.**  The replaced relator is the product of the commutators of the prescribed old words;
the geometric input is that the corresponding product of commutators of the chosen loops of the
cut surface bounds in the cut surface. -/
theorem filledF_of_surface_filling {α Jr Sx : Type u} {Su : Sx → Type u}
    (ρ : Jr ⊕ Sx → FreeGroup α) (T : SpanningTree (orderCx (QOld A))) (σ₀ : NeSpx A)
    (sig : ∀ s : Sx, Su s → List ((orderCx (NeSpx A)).E × Bool))
    (hsig : ∀ (s : Sx) (x : Su s),
      IsPath (orderCx (NeSpx A)).src (orderCx (NeSpx A)).tgt (sig s x) σ₀ σ₀)
    (lw : ∀ s : Sx, Su s → List (α × Bool)) (ps : ∀ s : Sx, List (Su s × Su s))
    (hrho : ∀ s : Sx, ρ (Sum.inr s) = commWord (fun x => FreeGroup.mk (lw s x)) (ps s))
    (hfilling : ∀ s : Sx,
      commWord (fun x => Pi1.mk (⟨sig s x, hsig s x⟩ : Loop (orderCx (NeSpx A)) σ₀)) (ps s) = 1) :
    BlockFamily.FilledF ρ (fun s m =>
      BlockFamily.blockSubst (Zt := fun _ => spineGens T)
        (fun s x => FreeGroup.mk (lw s x)) s (spineBeta T (sig s) m)) := by
  classical
  intro s
  set u : ∀ s : Sx, Su s → FreeGroup α := fun s x => FreeGroup.mk (lw s x) with hu
  set bsub : ∀ s : Sx, spineRels (A := A) (Su s) → FreeGroup (α ⊕ spineGens T) :=
    fun s m => BlockFamily.blockSubst (Zt := fun _ => spineGens T) u s (spineBeta T (sig s) m)
    with hbsub
  -- the homomorphism which substitutes the block at `s` and embeds it into the big free group
  set φ : FreeGroup (Su s ⊕ spineGens T) →*
      FreeGroup (α ⊕ (Σ s : Sx, spineGens T)) :=
    (FreeGroup.map (BlockFamily.genEmb (Zt := fun _ => spineGens T) s)).comp
      (BlockFamily.blockSubst (Zt := fun _ => spineGens T) u s) with hφ
  -- the surface word in the distinguished generators is a consequence of the block relators
  have hW : commWord (fun x => FreeGroup.of (Sum.inl x : Su s ⊕ spineGens T)) (ps s)
      ∈ relSub (spineBeta T (sig s)) :=
    mem_relSub_spineBeta_commWord T σ₀ (sig s) (hsig s) (ps s) (hfilling s)
  -- its image under `φ` is the replaced relator
  have hval : φ (commWord (fun x => FreeGroup.of (Sum.inl x : Su s ⊕ spineGens T)) (ps s))
      = FreeGroup.map (Sum.inl (β := Σ s : Sx, spineGens T)) (ρ (Sum.inr s)) := by
    have hgen : ∀ x : Su s, φ (FreeGroup.of (Sum.inl x : Su s ⊕ spineGens T))
        = FreeGroup.map (Sum.inl (β := Σ s : Sx, spineGens T)) (u s x) := by
      intro x
      show FreeGroup.map (BlockFamily.genEmb (Zt := fun _ => spineGens T) s)
        (BlockFamily.blockSubst (Zt := fun _ => spineGens T) u s (FreeGroup.of (Sum.inl x))) = _
      rw [BlockFamily.blockSubst_of_inl]
      have hcomp : (FreeGroup.map
            (BlockFamily.genEmb (α := α) (Zt := fun _ => spineGens T) s)).comp
          (FreeGroup.map (Sum.inl (α := α) (β := spineGens T)))
          = FreeGroup.map (Sum.inl (α := α) (β := Σ _ : Sx, spineGens T)) := by
        refine FreeGroup.ext_hom _ _ fun a => ?_
        simp [BlockFamily.genEmb]
      exact DFunLike.congr_fun hcomp (u s x)
    rw [map_commWord, commWord_congr hgen (ps s), hrho s, map_commWord]
  -- and `φ` carries the block relators into the relators of the substituted presentation
  rw [← hval]
  refine map_mem_normalClosure φ ?_ hW
  rintro g ⟨m, rfl⟩
  exact Subgroup.subset_normalClosure ⟨Sum.inr ⟨s, m⟩, rfl⟩

/-! ### The application -/

/-- **The theorem applied to the block of the article, with `hfill` derived from the surface
filling.**  The marked presentation of the block is read off its spine; the attaching map reads
the prescribed old word `u_h` along the chosen loop of the cut surface (`hread`); the replaced
relator is the surface word `∏_h [u_h, v_h]` (`hrho`), and the corresponding product of
commutators of the chosen loops bounds in the cut surface (`hfilling`).  Then the structural
homomorphism of the simultaneous substitution is injective — no algebraic hypothesis is
left. -/
theorem injective_substHomF_of_surface {α Jr Sx : Type u} {Su : Sx → Type u}
    (ρ : Jr ⊕ Sx → FreeGroup α) (att : NeSpx A →o presModelPos ρ) (σ₀ : NeSpx A)
    (cb : List ((orderCx (presModelPos ρ)).E × Bool))
    (hcb : IsPath (orderCx (presModelPos ρ)).src (orderCx (presModelPos ρ)).tgt cb
      (ptBase (presWords ρ)) (att σ₀))
    (T : SpanningTree (orderCx (QOld A)))
    (sig : ∀ s : Sx, Su s → List ((orderCx (NeSpx A)).E × Bool))
    (hsig : ∀ (s : Sx) (x : Su s),
      IsPath (orderCx (NeSpx A)).src (orderCx (NeSpx A)).tgt (sig s x) σ₀ σ₀)
    (lw : ∀ s : Sx, Su s → List (α × Bool)) (ps : ∀ s : Sx, List (Su s × Su s))
    (hread : ∀ (s : Sx) (x : Su s),
      Htpy (orderCx (presModelPos ρ)) (ptBase (presWords ρ)) (ptBase (presWords ρ))
        (cb ++ mapPath (orderCxMap att att.monotone) (sig s x) ++ revPath cb)
        (wordLoop (presWords ρ) (lw s x)))
    (hrho : ∀ s : Sx, ρ (Sum.inr s) = commWord (fun x => FreeGroup.mk (lw s x)) (ps s))
    (hfilling : ∀ s : Sx,
      commWord (fun x => Pi1.mk (⟨sig s x, hsig s x⟩ : Loop (orderCx (NeSpx A)) σ₀)) (ps s) = 1) :
    Function.Injective (BlockFamily.substHomF ρ (fun s m =>
      BlockFamily.blockSubst (Zt := fun _ => spineGens T)
        (fun s x => FreeGroup.mk (lw s x)) s (spineBeta T (sig s) m))
      (filledF_of_surface_filling ρ T σ₀ sig hsig lw ps hrho hfilling)) :=
  injective_substHomF_of_spine ρ att σ₀ cb hcb T sig hsig lw hread
    (filledF_of_surface_filling ρ T σ₀ sig hsig lw ps hrho hfilling)

end Davis
end FiniteChains
