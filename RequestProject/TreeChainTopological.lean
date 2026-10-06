module

public import RequestProject.TreeUnivCoverIso
public import RequestProject.TreeChain

@[expose] public section

/-!
# `(1) ⇒ (2)` of Theorem A for chains of arbitrary two-complexes, topologically

`RequestProject/TreeChain.lean` proves `(1) ⇒ (2)` of Theorem A for chains of arbitrary finite
two-complexes, but with the hypothesis "the inclusion is zero on `π₂`" read *after* collapsing
compatible spanning trees.  `RequestProject/TreeUnivCoverIso.lean` shows that collapsing a
spanning tree does not change `π₂`.  Putting the two together removes the collapse from the
hypothesis:

* `FiniteChains.Comb.SpanningTree.zeroPi2_presInclHom_of_zeroPi2` — **if a subcomplex inclusion
  is zero on `π₂`, so is the induced inclusion of the collapsed presentation complexes**;
* `FiniteChains.Comb.SpanningTree.ComplexChainTop` — a chain `K ⊂ X₀ ⊂ ⋯ ⊂ Xₙ` of two-complexes
  with compatible spanning trees, whose inclusions are zero on `π₂` in the sense of the
  interface of Theorem A (`FiniteChains.Comb.ZeroPi2`);
* `FiniteChains.Comb.SpanningTree.hasAcyclicRegularCover_of_topComplexChains` — such chains of
  every length give a connected acyclic regular cover of `K`;
* `FiniteChains.Comb.TopChain` and
  `FiniteChains.Comb.hasAcyclicRegularCover_of_topChains_of_isConnected` — the same statement
  with no mention of spanning trees at all: **a finite connected two-complex which begins
  chains of every finite length of finite connected two-complexes, each inclusion being zero on
  `π₂`, has a connected acyclic regular cover.**
-/

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains
namespace Comb
namespace SpanningTree

universe u

/-! ### Naturality of the identification of the two models -/

section Naturality

variable {X Y : Complex2.{u}} {TX : SpanningTree X} {TY : SpanningTree Y}
variable [Fintype (NonTree TX)] [DecidableEq (NonTree TX)] [Fintype X.F] [DecidableEq X.F]
variable [Fintype (NonTree TY)] [DecidableEq (NonTree TY)] [Fintype Y.F] [DecidableEq Y.F]
variable {h : Hom X Y} (hiff : ∀ e : X.E, TY.isTree (h.onE e) ↔ TX.isTree e)

omit [Fintype (NonTree TX)] [DecidableEq (NonTree TX)] [Fintype X.F] [DecidableEq X.F]
  [Fintype (NonTree TY)] [DecidableEq (NonTree TY)] [Fintype Y.F] [DecidableEq Y.F] in
/-- The element of `π₁` spelled by the image of a path is the image of the element spelled by
the path. -/
theorem uvQ_univLiftV {x₀ : X.V} (c : UV X x₀) :
    uvQ (T := TY) (univLiftV x₀ h c)
      = presInclGroupHom (nonTreeIncl hiff) (treeRel TX) (treeRel TY) h.onF
          (treeRel_onF hiff) (uvQ (T := TX) c) := by
  induction c using UV.ind with
  | h p =>
      show wordQ TY (relTree TY) (mapPath h p.1) = _
      show QuotientGroup.mk (pathWord TY (mapPath h p.1)) = _
      rw [pathWord_mapPath hiff]
      rfl

omit [Fintype (NonTree TX)] [Fintype X.F] [DecidableEq X.F] [Fintype (NonTree TY)]
  [Fintype Y.F] [DecidableEq Y.F] in
/-- The identification of the two models of the universal cover is natural in a subcomplex
inclusion: on two-cells it carries the lift of the inclusion to the inclusion of the universal
covers of the collapsed presentation complexes. -/
theorem uvFace_univLiftF (hE : Function.Injective h.onE) {x₀ : X.V} (F : UF X x₀) :
    uvFace TY (univLiftF x₀ h F)
      = (univCoverInclHom (nonTreeIncl hiff) (nonTreeIncl_injective hiff hE) (treeRel TX)
          (treeRel TY) h.onF (treeRel_onF hiff)).onF (uvFace TX F) := by
  show ((uvQ (T := TY) (univLiftV x₀ h F.1.1), h.onF F.1.2) : (treeUniv TY).F)
    = Prod.map (presInclGroupHom (nonTreeIncl hiff) (treeRel TX) (treeRel TY) h.onF
        (treeRel_onF hiff)) h.onF (uvQ (T := TX) F.1.1, F.1.2)
  rw [uvQ_univLiftV hiff]
  rfl

omit [Fintype (NonTree TX)] [Fintype X.F] [DecidableEq X.F] [Fintype (NonTree TY)]
  [Fintype Y.F] [DecidableEq Y.F] in
/-- The square of two-chains commutes. -/
theorem chain2_treeUnivHom_square (hE : Function.Injective h.onE) {x₀ : X.V}
    (u : (uCover X x₀).F →₀ ℤ) :
    chain2 (treeUnivHom TY (h.onV x₀)) (chain2 (univLift X h x₀) u)
      = chain2 (univCoverInclHom (nonTreeIncl hiff) (nonTreeIncl_injective hiff hE)
          (treeRel TX) (treeRel TY) h.onF (treeRel_onF hiff)) (chain2 (treeUnivHom TX x₀) u) := by
  classical
  show Finsupp.mapDomain (uvFace TY) (Finsupp.mapDomain (univLiftF x₀ h) u)
    = Finsupp.mapDomain (univCoverInclHom (nonTreeIncl hiff) (nonTreeIncl_injective hiff hE)
        (treeRel TX) (treeRel TY) h.onF (treeRel_onF hiff)).onF (Finsupp.mapDomain (uvFace TX) u)
  rw [← Finsupp.mapDomain_comp, ← Finsupp.mapDomain_comp]
  refine congrArg (fun k => Finsupp.mapDomain k u) ?_
  funext F
  exact uvFace_univLiftF hiff hE F

omit [Fintype (NonTree TX)] [Fintype X.F] [DecidableEq X.F] [Fintype (NonTree TY)] [Fintype Y.F] [DecidableEq Y.F] in
/-- **If a subcomplex inclusion is zero on `π₂`, so is the induced inclusion of the collapsed
presentation complexes.**  This is the dictionary that turns the topological form of condition
(1) of Theorem A into the algebraic one used in Section 2 of the paper. -/
theorem zeroPi2_presInclHom_of_zeroPi2 (hE : Function.Injective h.onE) (hzero : ZeroPi2 h) :
    ZeroPi2 (presInclHom (nonTreeIncl hiff) (nonTreeIncl_injective hiff hE) (treeRel TX)
      (treeRel TY) h.onF (treeRel_onF hiff)) := by
  refine (Comb.zeroPi2_presInclHom_iff (ρ := treeRel TX) (σ := treeRel TY) (nonTreeIncl hiff)
    (nonTreeIncl_injective hiff hE) h.onF (treeRel_onF hiff)).2 ?_
  intro v hv
  obtain ⟨u, rfl⟩ := chain2_treeUnivHom_surjective TX (x₀ := TX.root) v
  have hu : u ∈ Pi2 X TX.root := (mem_pi2_iff_bdry2_univCover TX u).2 hv
  rw [← chain2_treeUnivHom_square hiff hE u, hzero TX.root u hu, map_zero]

end Naturality

/-! ### Chains of two-complexes with the topological hypothesis -/

/-- A chain `K ⊂ X₀ ⊂ X₁ ⊂ ⋯ ⊂ Xₙ` of two-complexes over `K`, equipped with spanning trees
extending the given spanning tree `T₀` of `K`, whose inclusions are zero on `π₂` in the sense
of the interface of Theorem A.  Unlike `FiniteChains.Comb.SpanningTree.ComplexChain`, the
hypothesis is stated on the complexes themselves, not on their collapses. -/
structure ComplexChainTop (K : Complex2.{u}) (T₀ : SpanningTree K) (n : ℕ) where
  /-- The stages of the chain. -/
  X : ℕ → Complex2.{u}
  /-- The spanning tree of the stage `X r`. -/
  T : ∀ r, SpanningTree (X r)
  /-- The inclusion of `X r` in `X (r + 1)`. -/
  inc : ∀ r, Hom (X r) (X (r + 1))
  incE : ∀ r, Function.Injective (inc r).onE
  incF : ∀ r, Function.Injective (inc r).onF
  /-- The tree of `X (r + 1)` meets `X r` exactly in the tree of `X r`. -/
  tree_inc : ∀ (r : ℕ) (e : (X r).E), (T (r + 1)).isTree ((inc r).onE e) ↔ (T r).isTree e
  /-- The inclusion of `K` in the first stage. -/
  base : Hom K (X 0)
  baseE : Function.Injective base.onE
  baseF : Function.Injective base.onF
  /-- The tree of the first stage meets `K` exactly in `T₀`. -/
  tree_base : ∀ e : K.E, (T 0).isTree (base.onE e) ↔ T₀.isTree e
  decGen : ∀ r, DecidableEq (NonTree (T r))
  finGen : ∀ r, Fintype (NonTree (T r))
  decCell : ∀ r, DecidableEq (X r).F
  finCell : ∀ r, Fintype (X r).F
  /-- **The inclusion `X r ⊂ X (r + 1)` is zero on `π₂`.** -/
  zero_pi2 : ∀ r, r < n → Comb.ZeroPi2 (inc r)

namespace ComplexChainTop

variable {K : Complex2.{u}} {T₀ : SpanningTree K} {n : ℕ} (c : ComplexChainTop K T₀ n)

/-- **A chain with the topological hypothesis is a chain in the sense of
`FiniteChains.Comb.SpanningTree.ComplexChain`**: collapsing the spanning trees preserves the
vanishing on `π₂`. -/
def toComplexChain : ComplexChain K T₀ n where
  X := c.X
  T := c.T
  inc := c.inc
  incE := c.incE
  incF := c.incF
  tree_inc := c.tree_inc
  base := c.base
  baseE := c.baseE
  baseF := c.baseF
  tree_base := c.tree_base
  decGen := c.decGen
  finGen := c.finGen
  finCell := c.finCell
  zero_pi2 := by
    intro r hr
    letI := c.decGen r
    letI := c.decGen (r + 1)
    letI := c.finGen r
    letI := c.finGen (r + 1)
    letI := c.decCell r
    letI := c.decCell (r + 1)
    letI := c.finCell r
    letI := c.finCell (r + 1)
    exact zeroPi2_presInclHom_of_zeroPi2 (c.tree_inc r) (c.incE r) (c.zero_pi2 r hr)

end ComplexChainTop

variable {K : Complex2.{u}} (T₀ : SpanningTree K)
variable [Fintype (NonTree T₀)] [DecidableEq (NonTree T₀)] [Fintype K.F] [DecidableEq K.F]

/-- **`(1) ⇒ (2)` of Theorem A for chains of arbitrary finite two-complexes, with condition (1)
in its topological form.**  If for every `n` there is a chain `K ⊂ X₀ ⊂ ⋯ ⊂ Xₙ` of two-complexes
whose inclusions are zero on `π₂`, then `K` has a connected acyclic regular cover. -/
theorem hasAcyclicRegularCover_of_topComplexChains
    (hchains : ∀ n : ℕ, Nonempty (ComplexChainTop K T₀ n)) :
    HasAcyclicRegularCover K :=
  hasAcyclicRegularCover_of_complexChains T₀
    (fun n => (hchains n).map ComplexChainTop.toComplexChain)

end SpanningTree

/-! ### The statement without spanning trees -/

/-- A chain `K ⊂ X₀ ⊂ X₁ ⊂ ⋯ ⊂ Xₙ` of finite connected two-complexes over `K`, every inclusion
being an inclusion of subcomplexes and every inclusion `X r ⊂ X (r + 1)` being zero on `π₂`.
This is condition (1) of Theorem A for a general two-complex. -/
structure TopChain (K : Complex2.{u}) (n : ℕ) where
  /-- The stages of the chain. -/
  X : ℕ → Complex2.{u}
  /-- The inclusion of `X r` in `X (r + 1)`. -/
  inc : ∀ r, Hom (X r) (X (r + 1))
  incV : ∀ r, Function.Injective (inc r).onV
  incE : ∀ r, Function.Injective (inc r).onE
  incF : ∀ r, Function.Injective (inc r).onF
  /-- Every stage is connected. -/
  conn : ∀ r, IsConnected (X r)
  /-- Every stage is finite. -/
  finE : ∀ r, Finite (X r).E
  finF : ∀ r, Finite (X r).F
  /-- The inclusion of `K` in the first stage. -/
  base : Hom K (X 0)
  baseV : Function.Injective base.onV
  baseE : Function.Injective base.onE
  baseF : Function.Injective base.onF
  /-- **The inclusion `X r ⊂ X (r + 1)` is zero on `π₂`.** -/
  zero_pi2 : ∀ r, r < n → ZeroPi2 (inc r)

namespace TopChain

variable {K : Complex2.{u}} {n : ℕ} (c : TopChain K n) (T₀ : SpanningTree K)

/-- The stages of a chain, with `K` itself put in front. -/
def shiftX : ℕ → Complex2.{u}
  | 0 => K
  | r + 1 => c.X r

/-- The inclusions of the shifted chain. -/
def shiftInc : ∀ r, Hom (c.shiftX r) (c.shiftX (r + 1))
  | 0 => c.base
  | r + 1 => c.inc r

theorem shiftInc_injective_onV : ∀ r, Function.Injective (c.shiftInc r).onV
  | 0 => c.baseV
  | r + 1 => c.incV r

theorem shiftInc_injective_onE : ∀ r, Function.Injective (c.shiftInc r).onE
  | 0 => c.baseE
  | r + 1 => c.incE r

theorem shiftConn (hconn : IsConnected K) : ∀ r, IsConnected (c.shiftX r)
  | 0 => hconn
  | r + 1 => c.conn r

/-- **Spanning trees compatible with the whole chain**, starting from the given spanning tree
of `K`. -/
theorem exists_trees (hconn : IsConnected K) :
    ∃ T : ∀ r, SpanningTree (c.shiftX r), T 0 = T₀ ∧
      ∀ (r : ℕ) (e : (c.shiftX r).E),
        (T (r + 1)).isTree ((c.shiftInc r).onE e) ↔ (T r).isTree e :=
  SpanningTree.exists_compatible_trees c.shiftX c.shiftInc (c.shiftConn hconn)
    c.shiftInc_injective_onV c.shiftInc_injective_onE T₀

end TopChain

/-- **`(1) ⇒ (2)` of Theorem A for a finite connected two-complex, with no mention of spanning
trees.**  If for every `n` there is a chain `K ⊂ X₀ ⊂ ⋯ ⊂ Xₙ` of finite connected two-complexes,
each inclusion being an inclusion of subcomplexes and each inclusion `X r ⊂ X (r + 1)` inducing
zero on `π₂`, then `K` has a connected acyclic regular cover. -/
theorem hasAcyclicRegularCover_of_topChains_of_isConnected {K : Complex2.{u}}
    [Finite K.E] [Finite K.F] (hconn : IsConnected K) (x₀ : K.V)
    (hchains : ∀ n : ℕ, Nonempty (TopChain K n)) :
    HasAcyclicRegularCover K := by
  classical
  obtain ⟨T₀⟩ := SpanningTree.exists_of_isConnected hconn x₀
  haveI : Fintype (SpanningTree.NonTree T₀) := Fintype.ofFinite _
  haveI : Fintype K.F := Fintype.ofFinite _
  refine SpanningTree.hasAcyclicRegularCover_of_topComplexChains T₀ (fun n => ?_)
  obtain ⟨c⟩ := hchains n
  obtain ⟨T, hT0, hTinc⟩ := c.exists_trees T₀ hconn
  refine ⟨{
    X := fun r => c.X r
    T := fun r => T (r + 1)
    inc := c.inc
    incE := c.incE
    incF := c.incF
    tree_inc := fun r e => hTinc (r + 1) e
    base := c.base
    baseE := c.baseE
    baseF := c.baseF
    tree_base := fun e => by
      have h := hTinc 0 e
      rw [hT0] at h
      exact h
    decGen := fun r => Classical.decEq _
    finGen := fun r => by
      haveI := c.finE r
      exact Fintype.ofFinite _
    decCell := fun r => Classical.decEq _
    finCell := fun r => by
      haveI := c.finF r
      exact Fintype.ofFinite _
    zero_pi2 := c.zero_pi2 }⟩

/-! ### Non-vacuity -/

/-- The interval is connected. -/
theorem intervalComplex_isConnected : IsConnected SpanningTree.intervalComplex.{u} := by
  rintro ⟨a⟩ ⟨b⟩
  cases a <;> cases b
  · exact ⟨[], rfl⟩
  · exact ⟨[(PUnit.unit, true)], ⟨rfl, rfl⟩⟩
  · exact ⟨[(PUnit.unit, false)], ⟨rfl, rfl⟩⟩
  · exact ⟨[], rfl⟩

/-- The constant chain on the interval: it has no two-cells, hence no second homotopy, so
every inclusion is zero on `π₂`. -/
noncomputable def intervalTopChain (n : ℕ) : TopChain SpanningTree.intervalComplex.{u} n where
  X _ := SpanningTree.intervalComplex
  inc _ := Hom.id _
  incV _ := fun _ _ h => h
  incE _ := fun _ _ h => h
  incF _ := fun _ _ h => h
  conn _ := intervalComplex_isConnected
  finE _ := inferInstanceAs (Finite PUnit.{u + 1})
  finF _ := inferInstanceAs (Finite PEmpty.{u + 1})
  base := Hom.id _
  baseV := fun _ _ h => h
  baseE := fun _ _ h => h
  baseF := fun _ _ h => h
  zero_pi2 := by
    intro r _ x₀ u _
    have hu : u = 0 := by
      ext F
      exact F.1.2.elim
    rw [hu, map_zero]

/-- **The topological form of condition (1) is not vacuous**: the interval satisfies it, and
therefore has a connected acyclic regular cover. -/
theorem intervalComplex_hasAcyclicRegularCover_topChain :
    HasAcyclicRegularCover SpanningTree.intervalComplex.{u} := by
  haveI : Finite SpanningTree.intervalComplex.{u}.E := inferInstanceAs (Finite PUnit.{u + 1})
  haveI : Finite SpanningTree.intervalComplex.{u}.F := inferInstanceAs (Finite PEmpty.{u + 1})
  exact hasAcyclicRegularCover_of_topChains_of_isConnected intervalComplex_isConnected
    (ULift.up false) (fun n => ⟨intervalTopChain n⟩)

end Comb
end FiniteChains
