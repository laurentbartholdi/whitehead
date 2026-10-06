module

public import RequestProject.ComponentComplex
public import RequestProject.TheoremAGeneral

@[expose] public section

/-!
# Condition (1) of Theorem A with disconnected stages

`RequestProject/TreeChainTopological.lean` proves the implication `(1) ⇒ (2)` of Theorem A
for chains `K ⊂ X₀ ⊂ ⋯ ⊂ Xₙ` whose stages are finite **and connected**; connectedness was
needed to collapse a spanning tree and to read off a finite presentation.  Condition (1) of
Theorem A, however, says nothing about connectedness of the stages.  This file removes the
hypothesis: each stage is replaced by the connected component carrying the image of `K`,
which changes neither the universal covers of the stages nor the hypothesis "zero on `π₂`"
(`RequestProject/ComponentComplex.lean`).

* `FiniteChains.Comb.TopChainDisc` — a chain of finite two-complexes with no connectedness
  assumption on the stages;
* `FiniteChains.Comb.TopChainDisc.toTopChain` — passing to components turns such a chain
  into a chain of connected stages;
* `FiniteChains.Comb.hasAcyclicRegularCover_of_topChainsDisc` — **`(1) ⇒ (2)` of Theorem A
  for a finite connected two-complex, with stages of the chains not assumed connected**;
* `FiniteChains.Comb.hasAcyclicRegularCover_of_hasZeroChains_comb_disc` — the same statement
  with condition (1) in the form carried by the interface `combData`.
-/

namespace FiniteChains
namespace Comb

universe u

/-- A chain `K ⊂ X₀ ⊂ ⋯ ⊂ Xₙ` of finite two-complexes, all of whose inclusions `X r ⊂ X (r+1)`
are zero on `π₂`.  Unlike `FiniteChains.Comb.TopChain`, the stages are **not** assumed
connected. -/
structure TopChainDisc (K : Complex2.{u}) (n : ℕ) where
  /-- The stages of the chain. -/
  X : ℕ → Complex2.{u}
  /-- The inclusion of `X r` in `X (r + 1)`. -/
  inc : ∀ r, Hom (X r) (X (r + 1))
  incV : ∀ r, Function.Injective (inc r).onV
  incE : ∀ r, Function.Injective (inc r).onE
  incF : ∀ r, Function.Injective (inc r).onF
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

namespace TopChainDisc

variable {K : Complex2.{u}} {n : ℕ} (c : TopChainDisc K n) (x₀ : K.V)

/-- The base vertex of the `r`-th stage: the image of `x₀`. -/
def bp : ∀ r : ℕ, (c.X r).V
  | 0 => c.base.onV x₀
  | r + 1 => (c.inc r).onV (bp r)

/-- The inclusion of the `r`-th component into the `r`-th stage, followed by the inclusion of
stages. -/
noncomputable def incComp (r : ℕ) : Hom (component (c.X r) (c.bp x₀ r)) (c.X (r + 1)) :=
  (c.inc r).comp (componentIncl (c.X r) (c.bp x₀ r))

theorem reach_incComp (r : ℕ) (v : (component (c.X r) (c.bp x₀ r)).V) :
    Reach (c.X (r + 1)) (c.bp x₀ (r + 1)) ((c.incComp x₀ r).onV v) :=
  Reach.map (c.inc r) v.2

theorem reach_base (hconn : IsConnected K) (v : K.V) :
    Reach (c.X 0) (c.bp x₀ 0) (c.base.onV v) := by
  obtain ⟨p, hp⟩ := hconn x₀ v
  exact Reach.map c.base ⟨p, hp⟩

/-- **Passing to components**: a chain with possibly disconnected stages yields a chain of
connected stages. -/
noncomputable def toTopChain (hconn : IsConnected K) : TopChain K n where
  X r := component (c.X r) (c.bp x₀ r)
  inc r := (c.incComp x₀ r).toComponent (c.bp x₀ (r + 1)) (c.reach_incComp x₀ r)
  incV r := toComponent_injective_onV _ ((c.incV r).comp fun _ _ h => Subtype.ext h)
  incE r := toComponent_injective_onE _ ((c.incE r).comp fun _ _ h => Subtype.ext h)
  incF r := toComponent_injective_onF _ ((c.incF r).comp fun _ _ h => Subtype.ext h)
  conn r := component_isConnected _
  finE r := by
    haveI := c.finE r
    infer_instance
  finF r := by
    haveI := c.finF r
    infer_instance
  base := c.base.toComponent (c.bp x₀ 0) (c.reach_base x₀ hconn)
  baseV := toComponent_injective_onV _ c.baseV
  baseE := toComponent_injective_onE _ c.baseE
  baseF := toComponent_injective_onF _ c.baseF
  zero_pi2 r hr :=
    zeroPi2_toComponent _
      (zeroPi2_comp_right (c.inc r) (componentIncl (c.X r) (c.bp x₀ r)) (c.zero_pi2 r hr))

end TopChainDisc

/-- **`(1) ⇒ (2)` of Theorem A for a finite connected two-complex, with no connectedness
assumption on the stages of the chains.**  If for every `n` there is a chain
`K ⊂ X₀ ⊂ ⋯ ⊂ Xₙ` of finite two-complexes, each inclusion being an inclusion of subcomplexes
and each inclusion `X r ⊂ X (r + 1)` zero on `π₂`, then `K` has a connected acyclic regular
cover. -/
theorem hasAcyclicRegularCover_of_topChainsDisc {K : Complex2.{u}} [Finite K.E] [Finite K.F]
    (hconn : IsConnected K) (x₀ : K.V) (h : ∀ n : ℕ, Nonempty (TopChainDisc K n)) :
    HasAcyclicRegularCover K :=
  hasAcyclicRegularCover_of_topChains_of_isConnected hconn x₀
    fun n => (h n).map fun c => c.toTopChain x₀ hconn

/-- **Condition (1) of Theorem A implies condition (2)**, for the interface `combData`, with
the stages of the chains assumed finite but **not** connected. -/
theorem hasAcyclicRegularCover_of_hasZeroChains_comb_disc {K : Complex2.{u}}
    [Finite K.E] [Finite K.F] (hconn : IsConnected K) (x₀ : K.V)
    (h : ∀ n : ℕ, ∃ c : ℕ → Complex2.{u}, c 0 = K ∧ IsZeroChain combData c n ∧
      (∀ i, i ≤ n → Finite (c i).E) ∧ (∀ i, i ≤ n → Finite (c i).F)) :
    HasAcyclicRegularCover K := by
  classical
  refine hasAcyclicRegularCover_of_topChainsDisc hconn x₀ fun n => ?_
  obtain ⟨c, hc0, hchain, hfinE, hfinF⟩ := h (n + 1)
  set X : ℕ → Complex2.{u} := fun r => c (min (r + 1) (n + 1)) with hX
  have hXle : ∀ r, min (r + 1) (n + 1) ≤ n + 1 := fun r => min_le_right _ _
  have step : ∀ r : ℕ, ∃ f : Hom (X r) (X (r + 1)),
      Function.Injective f.onV ∧ Function.Injective f.onE ∧ Function.Injective f.onF ∧
        (r < n → ZeroPi2 f) := by
    intro r
    by_cases hr : r < n
    · have h1 : min (r + 1) (n + 1) = r + 1 := by omega
      have h2 : min (r + 1 + 1) (n + 1) = r + 2 := by omega
      obtain ⟨f, hV, hE, hF⟩ := hchain.sub (r + 1) (by omega)
      refine ⟨Hom.congr (congrArg c h1).symm (congrArg c h2).symm f,
        Hom.congr_injective_onV _ _ f hV, Hom.congr_injective_onE _ _ f hE,
        Hom.congr_injective_onF _ _ f hF, fun _ => ?_⟩
      exact zeroPi2_congr _ _ f (hchain.zero (r + 1) (by omega) f hV hE hF)
    · have h1 : min (r + 1) (n + 1) = min (r + 1 + 1) (n + 1) := by omega
      refine ⟨Hom.congr rfl (congrArg c h1) (Hom.id (c (min (r + 1) (n + 1)))),
        Hom.congr_injective_onV _ _ _ (fun _ _ hx => hx),
        Hom.congr_injective_onE _ _ _ (fun _ _ hx => hx),
        Hom.congr_injective_onF _ _ _ (fun _ _ hx => hx), fun hcon => absurd hcon hr⟩
  choose f hfV hfE hfF hfZ using step
  have hbase : ∃ g : Hom K (X 0), Function.Injective g.onV ∧ Function.Injective g.onE ∧
      Function.Injective g.onF := by
    have h1 : min (0 + 1) (n + 1) = 1 := by omega
    obtain ⟨g, hV, hE, hF⟩ := hchain.sub 0 (by omega)
    exact ⟨Hom.congr hc0 (congrArg c h1).symm g, Hom.congr_injective_onV _ _ g hV,
      Hom.congr_injective_onE _ _ g hE, Hom.congr_injective_onF _ _ g hF⟩
  obtain ⟨g, hgV, hgE, hgF⟩ := hbase
  exact ⟨{
    X := X
    inc := f
    incV := hfV
    incE := hfE
    incF := hfF
    finE := fun r => hfinE _ (hXle r)
    finF := fun r => hfinF _ (hXle r)
    base := g
    baseV := hgV
    baseE := hgE
    baseF := hgF
    zero_pi2 := fun r hr => hfZ r hr }⟩

/-! ### Non-vacuity: chains with disconnected stages -/

/-- A complex without two-cells has no second homotopy, so every cellular map out of it is
zero on `π₂`. -/
theorem zeroPi2_of_isEmpty_F {X Y : Complex2.{u}} (hX : IsEmpty X.F) (f : Hom X Y) :
    ZeroPi2 f := by
  intro x₀ u _
  have hu : u = 0 := by
    ext F
    exact (hX.elim F.1.2)
  rw [hu, map_zero]

/-- The bouquet of `m` circles together with `k` isolated vertices: a **disconnected** graph
whenever `k ≠ 0`. -/
abbrev bouquetPlus (m k : ℕ) : Complex2.{u} where
  V := ULift.{u} (Fin (k + 1))
  E := ULift.{u} (Fin m)
  F := PEmpty.{u + 1}
  src _ := ⟨0⟩
  tgt _ := ⟨0⟩
  base := PEmpty.elim
  att := PEmpty.elim
  att_isLoop := fun f => f.elim

/-- The inclusion of `bouquetPlus m k` in `bouquetPlus (m + 1) (k + 1)`. -/
def bouquetPlusIncl (m k : ℕ) : Hom (bouquetPlus.{u} m k) (bouquetPlus.{u} (m + 1) (k + 1)) where
  onV v := ⟨v.down.castSucc⟩
  onE e := ⟨e.down.castSucc⟩
  onF := PEmpty.elim
  src_onE _ := rfl
  tgt_onE _ := rfl
  base_onF f := f.elim
  att_onF f := f.elim

theorem bouquetPlusIncl_injective_onV (m k : ℕ) :
    Function.Injective (bouquetPlusIncl.{u} m k).onV := by
  rintro ⟨a⟩ ⟨b⟩ hab
  have : a.castSucc = b.castSucc := congrArg ULift.down hab
  exact congrArg ULift.up (Fin.castSucc_injective _ this)

theorem bouquetPlusIncl_injective_onE (m k : ℕ) :
    Function.Injective (bouquetPlusIncl.{u} m k).onE := by
  rintro ⟨a⟩ ⟨b⟩ hab
  have : a.castSucc = b.castSucc := congrArg ULift.down hab
  exact congrArg ULift.up (Fin.castSucc_injective _ this)

/-- In `bouquetPlus m k` every edge is a loop at the vertex `0`, so a path either stays put
or ends at `0`. -/
theorem bouquetPlus_path {m k : ℕ} : ∀ (p : List ((bouquetPlus.{u} m k).E × Bool))
    (a b : (bouquetPlus.{u} m k).V),
    IsPath (bouquetPlus.{u} m k).src (bouquetPlus.{u} m k).tgt p a b → b = a ∨ b = ⟨0⟩
  | [], a, b, h => Or.inl h.symm
  | eb :: t, a, b, h => by
      rcases bouquetPlus_path t _ b h.2 with h' | h'
      · refine Or.inr ?_
        rw [h']
        obtain ⟨e, bb⟩ := eb
        cases bb <;> rfl
      · exact Or.inr h'

/-- The stages of the chain below really are disconnected. -/
theorem bouquetPlus_not_isConnected (m k : ℕ) : ¬ IsConnected (bouquetPlus.{u} m (k + 1)) := by
  intro h
  obtain ⟨p, hp⟩ := h ⟨0⟩ ⟨1⟩
  have hne : (⟨1⟩ : (bouquetPlus.{u} m (k + 1)).V) ≠ ⟨0⟩ := by
    intro hx
    have : ((1 : Fin (k + 2)) : ℕ) = ((0 : Fin (k + 2)) : ℕ) :=
      congrArg (fun z => (z.down : ℕ)) hx
    simp at this
  rcases bouquetPlus_path p _ _ hp with h' | h'
  · exact hne h'
  · exact hne h'

/-- The inclusion of the circle in `bouquetPlus 1 1`. -/
def circleToBouquetPlus : Hom (bouquet.{u} 1) (bouquetPlus.{u} 1 1) where
  onV _ := ⟨0⟩
  onE e := ⟨e.down⟩
  onF := PEmpty.elim
  src_onE _ := rfl
  tgt_onE _ := rfl
  base_onF f := f.elim
  att_onF f := f.elim

/-- **The criterion with disconnected stages is not vacuous**: the circle begins chains of
every length whose stages `bouquetPlus (r + 1) (r + 1)` are disconnected graphs, all
inclusions being zero on `π₂`, and therefore has a connected acyclic regular cover. -/
theorem circle_hasAcyclicRegularCover_disc :
    HasAcyclicRegularCover (bouquet.{u} 1) := by
  refine hasAcyclicRegularCover_of_topChainsDisc (bouquet_isConnected 1) PUnit.unit
    fun n => ⟨{
      X := fun r => bouquetPlus (r + 1) (r + 1)
      inc := fun r => bouquetPlusIncl (r + 1) (r + 1)
      incV := fun r => bouquetPlusIncl_injective_onV _ _
      incE := fun r => bouquetPlusIncl_injective_onE _ _
      incF := fun r => fun a => a.elim
      finE := fun r => inferInstance
      finF := fun r => inferInstance
      base := circleToBouquetPlus
      baseV := fun a b _ => Subsingleton.elim a b
      baseE := fun a b hab => by
        obtain ⟨a⟩ := a; obtain ⟨b⟩ := b
        exact congrArg ULift.up (congrArg ULift.down hab)
      baseF := fun a => a.elim
      zero_pi2 := fun r _ =>
        zeroPi2_of_isEmpty_F (X := bouquetPlus (r + 1) (r + 1)) inferInstance _ }⟩

end Comb
end FiniteChains
