import RequestProject.TreeChainTopological

/-!
# Condition (1) of Theorem A, as stated by the interface, implies condition (2)

`RequestProject/CombData.lean` instantiates the interface `FiniteChains.TwoComplexData` of
Theorem A by honest combinatorial two-complexes: `combData`.  Condition (1) of Theorem A is
then `FiniteChains.HasZeroChains combData K`, that is, the existence for every `n` of a chain

  `K = c 0 ⊊ c 1 ⊊ ⋯ ⊊ c n`

of two-complexes, each inclusion being an inclusion of subcomplexes inducing zero on `π₂`.

`RequestProject/TreeChainTopological.lean` proves `(1) ⇒ (2)` for chains packaged as
`FiniteChains.Comb.TopChain`.  This file feeds the interface-level condition into that theorem;
the only extra hypotheses are that the stages of the chains are connected and finite, which is
what the collapse to a finite presentation needs.

* `FiniteChains.Comb.Hom.congr` — transport of a cellular map along equalities of complexes,
  used to pad a finite chain to a family indexed by all of `ℕ`;
* `FiniteChains.Comb.hasAcyclicRegularCover_of_hasZeroChains_comb` — **condition (1) of
  Theorem A, in the form carried by the interface `combData`, implies condition (2)** for a
  finite connected two-complex whose chains have finite connected stages.
-/

namespace FiniteChains
namespace Comb

universe u

/-! ### Transport of cellular maps along equalities of complexes -/

/-- Transport of a cellular map along equalities of its source and target. -/
def Hom.congr : ∀ {X X' Y Y' : Complex2.{u}}, X = X' → Y = Y' → Hom X Y → Hom X' Y'
  | _, _, _, _, rfl, rfl, f => f

@[simp] theorem Hom.congr_rfl {X Y : Complex2.{u}} (f : Hom X Y) :
    Hom.congr rfl rfl f = f := rfl

theorem Hom.congr_injective_onV {X X' Y Y' : Complex2.{u}} (hX : X = X') (hY : Y = Y')
    (f : Hom X Y) (h : Function.Injective f.onV) :
    Function.Injective (Hom.congr hX hY f).onV := by
  subst hX; subst hY; exact h

theorem Hom.congr_injective_onE {X X' Y Y' : Complex2.{u}} (hX : X = X') (hY : Y = Y')
    (f : Hom X Y) (h : Function.Injective f.onE) :
    Function.Injective (Hom.congr hX hY f).onE := by
  subst hX; subst hY; exact h

theorem Hom.congr_injective_onF {X X' Y Y' : Complex2.{u}} (hX : X = X') (hY : Y = Y')
    (f : Hom X Y) (h : Function.Injective f.onF) :
    Function.Injective (Hom.congr hX hY f).onF := by
  subst hX; subst hY; exact h

theorem zeroPi2_congr {X X' Y Y' : Complex2.{u}} (hX : X = X') (hY : Y = Y')
    (f : Hom X Y) (h : ZeroPi2 f) : ZeroPi2 (Hom.congr hX hY f) := by
  subst hX; subst hY; exact h

/-! ### From the interface-level chains to `TopChain` -/

/-- **Condition (1) of Theorem A implies condition (2)**, for the interface `combData`.  If for
every `n` the complex `K` begins a chain `K = c 0 ⊊ c 1 ⊊ ⋯ ⊊ c n` of finite connected
two-complexes whose inclusions are zero on `π₂` — condition (1) exactly as the interface of
Theorem A states it — then `K` has a connected acyclic regular cover. -/
theorem hasAcyclicRegularCover_of_hasZeroChains_comb {K : Complex2.{u}}
    [Finite K.E] [Finite K.F] (hconn : IsConnected K) (x₀ : K.V)
    (h : ∀ n : ℕ, ∃ c : ℕ → Complex2.{u}, c 0 = K ∧ IsZeroChain combData c n ∧
      (∀ i, i ≤ n → IsConnected (c i)) ∧ (∀ i, i ≤ n → Finite (c i).E) ∧
      (∀ i, i ≤ n → Finite (c i).F)) :
    HasAcyclicRegularCover K := by
  classical
  refine hasAcyclicRegularCover_of_topChains_of_isConnected hconn x₀ (fun n => ?_)
  obtain ⟨c, hc0, hchain, hcon, hfinE, hfinF⟩ := h (n + 1)
  -- the stages of the chain, padded to a family indexed by all of `ℕ`
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
  -- the inclusion of `K` into the first stage
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
    conn := fun r => hcon _ (hXle r)
    finE := fun r => hfinE _ (hXle r)
    finF := fun r => hfinF _ (hXle r)
    base := g
    baseV := hgV
    baseE := hgE
    baseF := hgF
    zero_pi2 := fun r hr => hfZ r hr }⟩

/-! ### Non-vacuity: the circle -/

/-- The bouquet of `m` circles: one vertex, `m` loops, no two-cells. -/
abbrev bouquet (m : ℕ) : Complex2.{u} where
  V := PUnit.{u + 1}
  E := ULift.{u} (Fin m)
  F := PEmpty.{u + 1}
  src _ := PUnit.unit
  tgt _ := PUnit.unit
  base := PEmpty.elim
  att := PEmpty.elim
  att_isLoop := fun f => f.elim

theorem bouquet_isConnected (m : ℕ) : IsConnected (bouquet.{u} m) := by
  intro a b
  exact ⟨[], Subsingleton.elim a b⟩

theorem bouquet_ne {m k : ℕ} (h : m ≠ k) : bouquet.{u} m ≠ bouquet.{u} k := by
  intro hc
  have hE : (bouquet.{u} m).E = (bouquet.{u} k).E := congrArg Complex2.E hc
  have hcard : Fintype.card (ULift.{u} (Fin m)) = Fintype.card (ULift.{u} (Fin k)) :=
    Fintype.card_congr (Equiv.cast hE)
  simp at hcard
  exact h hcard

/-- The inclusion of the bouquet of `m` circles in the bouquet of `m + 1` circles. -/
def bouquetIncl (m : ℕ) : Hom (bouquet.{u} m) (bouquet.{u} (m + 1)) where
  onV := id
  onE e := ULift.up e.down.castSucc
  onF := PEmpty.elim
  src_onE _ := rfl
  tgt_onE _ := rfl
  base_onF f := f.elim
  att_onF f := f.elim

/-- A bouquet of circles has no second homotopy, so every cellular map out of it is zero on
`π₂`. -/
theorem bouquet_zeroPi2 {m : ℕ} {Y : Complex2.{u}} (f : Hom (bouquet.{u} m) Y) : ZeroPi2 f := by
  intro x₀ u _
  have hu : u = 0 := by
    ext F
    exact F.1.2.elim
  rw [hu, map_zero]

/-- **The interface-level criterion is not vacuous**: the circle begins strictly increasing
chains of finite connected two-complexes of every length, all inclusions being zero on `π₂`
(the stages are graphs, so they have no second homotopy at all), and therefore has a connected
acyclic regular cover. -/
theorem circle_hasAcyclicRegularCover :
    HasAcyclicRegularCover (bouquet.{u} 1) := by
  refine hasAcyclicRegularCover_of_hasZeroChains_comb (bouquet_isConnected 1) PUnit.unit
    (fun n => ⟨fun i => bouquet (i + 1), rfl, ⟨?_, ?_, ?_⟩, ?_, ?_, ?_⟩)
  · exact fun i _ => ⟨bouquetIncl (i + 1), fun _ _ hx => hx,
      fun a b hab => by
        obtain ⟨a⟩ := a; obtain ⟨b⟩ := b
        have : a.castSucc = b.castSucc := congrArg ULift.down hab
        exact congrArg ULift.up (Fin.castSucc_injective _ this),
      fun a => a.elim⟩
  · exact fun i _ => bouquet_ne (by omega)
  · exact fun i _ f _ _ _ => bouquet_zeroPi2 f
  · exact fun i _ => bouquet_isConnected _
  · exact fun i _ => inferInstance
  · exact fun i _ => inferInstance

end Comb
end FiniteChains
