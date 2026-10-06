module

public import RequestProject.MapChainDescent
public import RequestProject.TheoremAAcyclic

@[expose] public section

/-!
# Killing `π₁` inside the Cockcroft world: the extension step without `π₂`

The extension step of Section 3 (`FiniteChains.Comb.MapStep`, i.e. Lemmas 3.1, 3.9 and 3.10)
asks for a relative chain `D = L₀ ⊊ L₁ ⊊ ⋯ ⊊ Lₙ` in which *four* things hold at once: every
stage is Cockcroft, every inclusion is zero on `π₂`, `π₁(D)` dies from the first stage on,
and only finitely many cells are added.

This file removes the `π₂` condition from that list.  The paper's own observation (the first
paragraph of the proof of Lemma 3.10) is that

> a map out of a Cockcroft complex which kills the fundamental group is zero on `π₂`,

and this is proved here in the combinatorial model
(`FiniteChains.Comb.zeroPi2_of_isCockcroft_of_pi1Trivial`): the map lifts to the universal
cover of its target, so on two-cycles it factors through the Hurewicz map of the source,
which vanishes.

Consequently the whole extension step follows from a statement in which neither `π₂` nor
homotopy classes of spheres occur at all:

* `FiniteChains.Comb.CockcroftKillData`, `FiniteChains.Comb.CockcroftKillStep` — **from every
  finite-type connected Cockcroft complex `P` one can pass to a strictly larger connected
  Cockcroft complex `P'` in which `π₁(P)` dies**, adding only finitely many cells and at
  least one two-cell;
* `FiniteChains.Comb.mapStep_of_cockcroftKillStep` — iterating this single step produces the
  relative chains of Lemmas 3.1, 3.9, 3.10 together with their inclusions: the tower
  `D = L₀ ⊊ L₁ ⊊ ⋯` has Cockcroft stages, and *every* inclusion is automatically zero on
  `π₂` because its source is Cockcroft and it kills the fundamental group;
* `FiniteChains.Comb.hasMapChains_of_cockcroftKillStep_of_isAcyclic`,
  `FiniteChains.Comb.theoremA_maps_of_cockcroftKillStep_of_isAcyclic` — **for a finite
  connected acyclic two-complex, Theorem A in its faithful, map-carrying form follows from
  this one step alone** (the generation statement (3.5) is a theorem for the identity
  covering, see `RequestProject/TheoremAAcyclic.lean`);
* `FiniteChains.Comb.hasMapChains_of_cockcroftKillStep`,
  `FiniteChains.Comb.theoremA_maps_of_cockcroftKillStep` — for a general finite connected
  complex, the same with the generation statement (3.5) as the only further input.

So the remaining gap in the converse implication of Theorem A is now a statement about
Cockcroft complexes and fundamental groups only.

**The finite form.**  Asking the pass of `FiniteChains.Comb.CockcroftKillStep` of *every*
connected Cockcroft complex is more than the construction of the paper delivers: over an
infinite acyclic core the initial pair of Lemma 3.1 adjoins a pair of generators for every
generator of the core, hence infinitely many cells, whereas the pass as stated adds only
finitely many.  The form that the paper does prove — and the only form used for a finite
acyclic complex, where the covering may be taken to be the identity — restricts the pass to
complexes with finitely many cells:

* `FiniteChains.Comb.FiniteCockcroftKillStep` — the same pass, asked only of *finite*
  connected Cockcroft complexes (Proposition 3.7 for a finite core);
* `FiniteChains.Comb.hasMapChains_of_finiteCockcroftKillStep_of_isAcyclic`,
  `FiniteChains.Comb.theoremA_maps_of_finiteCockcroftKillStep_of_isAcyclic` — **Theorem A for
  a finite connected acyclic two-complex, in its faithful, map-carrying form, from that
  restricted pass alone.**
-/

namespace FiniteChains
namespace Comb

universe u

/-! ### A map out of a Cockcroft complex which kills `π₁` is zero on `π₂` -/

/-- **A `π₁`-trivial map out of a connected Cockcroft complex is zero on `π₂`.**  Because the
map kills `π₁` it lifts to the universal cover of the target, so the lift on universal covers
factors as `X̃ → X → Ỹ`.  The first arrow is the Hurewicz map of `X`, which is zero on
two-cycles by the Cockcroft property. -/
theorem zeroPi2_of_isCockcroft_of_pi1Trivial {X Y : Complex2.{u}} (hX : IsCockcroft X)
    (hconnX : IsConnected X) (hconnY : IsConnected Y) {f : Hom X Y}
    (htriv : Pi1Trivial f) : ZeroPi2 f := by
  intro x₀ c hc
  set psi : Hom X (uCover Y (f.onV x₀)) := liftHom hconnX htriv with hpsi
  set A : Hom (uCover X x₀) (uCover Y (f.onV x₀)) := univLift X f x₀ with hA
  set B : Hom (uCover X x₀) (uCover Y (f.onV x₀)) := psi.comp (univProj X x₀) with hB
  have hq : IsCovering (univProj Y (f.onV x₀)) := isCovering_univProj hconnY
  have hqE : ∀ e, (univProj Y (f.onV x₀)).onE (A.onE e)
      = (univProj Y (f.onV x₀)).onE (B.onE e) := by
    intro e
    show f.onE e.1.2 = f.onE e.1.2
    rfl
  have hqF : ∀ g, (univProj Y (f.onV x₀)).onF (A.onF g)
      = (univProj Y (f.onV x₀)).onF (B.onF g) := by
    intro g
    show f.onF g.1.2 = f.onF g.1.2
    rfl
  have hbase : A.onV (UV.base X x₀) = B.onV (UV.base X x₀) := by
    show UV.mk (mapPathFrom x₀ f ⟨[], rfl⟩) = psi.onV x₀
    rw [hpsi, liftHom_base hconnX htriv]
    rfl
  have hV := lift_onV_eq hq isConnected_univCover hqE hbase
  have hFeq := lift_onF_eq hq hqF hV
  have hcomp : chain2 A c = chain2 psi (chain2 (univProj X x₀) c) := by
    show Finsupp.mapDomain A.onF c
      = Finsupp.mapDomain psi.onF (Finsupp.mapDomain (univProj X x₀).onF c)
    rw [← Finsupp.mapDomain_comp]
    exact congrArg (fun m => Finsupp.mapDomain m c) (funext hFeq)
  have hhur : chain2 (univProj X x₀) c = 0 := hX x₀ c hc
  rw [hcomp, hhur, map_zero]

/-! ### Cells off a composite -/

/-- A cell of `C` off the composite `g ∘ f` either lies off `g`, or is the image under `g` of
a cell off `f`. -/
theorem finite_offE_comp {A B C : Complex2.{u}} (f : Hom A B) (g : Hom B C)
    (hf : Finite (OffE f)) (hg : Finite (OffE g)) : Finite (OffE (g.comp f)) := by
  classical
  haveI := hf
  haveI := hg
  refine Finite.of_injective (β := OffE g ⊕ OffE f)
    (fun w => if h : ∃ b, g.onE b = w.1 then
        Sum.inr ⟨h.choose, fun a ha => w.2 a (by
          show g.onE (f.onE a) = w.1
          rw [ha, h.choose_spec])⟩
      else Sum.inl ⟨w.1, fun b hb => h ⟨b, hb⟩⟩) ?_
  intro w₁ w₂ hw
  dsimp only at hw
  split_ifs at hw with h₁ h₂ h₂
  · have hch : h₁.choose = h₂.choose := congrArg Subtype.val (Sum.inr_injective hw)
    refine Subtype.ext ?_
    rw [← h₁.choose_spec, ← h₂.choose_spec, hch]
  · have hval := Sum.inl.inj hw
    exact Subtype.ext (congrArg (fun z => z.1) hval)

/-- The two-cell version of `FiniteChains.Comb.finite_offE_comp`. -/
theorem finite_offF_comp {A B C : Complex2.{u}} (f : Hom A B) (g : Hom B C)
    (hf : Finite (OffF f)) (hg : Finite (OffF g)) : Finite (OffF (g.comp f)) := by
  classical
  haveI := hf
  haveI := hg
  refine Finite.of_injective (β := OffF g ⊕ OffF f)
    (fun w => if h : ∃ b, g.onF b = w.1 then
        Sum.inr ⟨h.choose, fun a ha => w.2 a (by
          show g.onF (f.onF a) = w.1
          rw [ha, h.choose_spec])⟩
      else Sum.inl ⟨w.1, fun b hb => h ⟨b, hb⟩⟩) ?_
  intro w₁ w₂ hw
  dsimp only at hw
  split_ifs at hw with h₁ h₂ h₂
  · have hch : h₁.choose = h₂.choose := congrArg Subtype.val (Sum.inr_injective hw)
    refine Subtype.ext ?_
    rw [← h₁.choose_spec, ← h₂.choose_spec, hch]
  · have hval := Sum.inl.inj hw
    exact Subtype.ext (congrArg (fun z => z.1) hval)

/-! ### The extension step without `π₂` -/

/-- **One pass of the construction of Section 3, stated without any reference to `π₂`.**  It
enlarges a connected Cockcroft complex `P` to a connected Cockcroft complex `P'` in which the
fundamental group of `P` dies, adding finitely many cells and at least one two-cell.  In the
paper this is the composite `P ⊂ T(P) ⊂ Q(P)` of the structural operation and the terminal
extension (Lemmas 3.9 and 3.10). -/
structure CockcroftKillData (P : Complex2.{u}) where
  /-- The enlarged complex. -/
  next : Complex2.{u}
  /-- The inclusion. -/
  hom : Hom P next
  injV : Function.Injective hom.onV
  injE : Function.Injective hom.onE
  injF : Function.Injective hom.onF
  /-- The enlarged complex is connected. -/
  conn : IsConnected next
  /-- The enlarged complex is Cockcroft. -/
  cock : IsCockcroft next
  /-- The fundamental group of `P` dies in it. -/
  kill : Pi1Trivial hom
  /-- Only finitely many edges are added. -/
  finE : Finite (OffE hom)
  /-- Only finitely many two-cells are added. -/
  finF : Finite (OffF hom)
  /-- At least one two-cell is added, so the inclusion is strict. -/
  adds : Nonempty (OffF hom)

/-- **The remaining statement of the converse implication of Theorem A**: every connected
Cockcroft two-complex admits such a pass. -/
def CockcroftKillStep : Prop :=
  ∀ P : Complex2.{u}, IsConnected P → IsCockcroft P → Nonempty (CockcroftKillData P)

namespace CockcroftKill

variable (h : CockcroftKillStep.{u})

/-- A connected Cockcroft complex: the objects the pass moves between. -/
structure Stage where
  /-- The underlying complex. -/
  X : Complex2.{u}
  /-- It is connected. -/
  conn : IsConnected X
  /-- It is Cockcroft. -/
  cock : IsCockcroft X

/-- A choice of pass out of a stage. -/
noncomputable def pick (S : Stage.{u}) : CockcroftKillData S.X := (h S.X S.conn S.cock).some

/-- The next stage. -/
noncomputable def nextStage (S : Stage.{u}) : Stage.{u} :=
  ⟨(pick h S).next, (pick h S).conn, (pick h S).cock⟩

/-- The tower of stages obtained by iterating the pass. -/
noncomputable def tower (S : Stage.{u}) : ℕ → Stage.{u}
  | 0 => S
  | i + 1 => nextStage h (tower S i)

/-- The complexes of the tower. -/
noncomputable def cx (S : Stage.{u}) (i : ℕ) : Complex2.{u} := (tower h S i).X

/-- The inclusions of the tower. -/
noncomputable def step (S : Stage.{u}) (i : ℕ) : Hom (cx h S i) (cx h S (i + 1)) :=
  (pick h (tower h S i)).hom

theorem pi1Trivial_inclFrom (S : Stage.{u}) :
    ∀ i, 1 ≤ i → Pi1Trivial (inclFrom (cx h S) (step h S) i)
  | 1, _ => fun a m hm => (pick h (tower h S 0)).kill a m hm
  | i + 2, _ => by
      have ih := pi1Trivial_inclFrom S (i + 1) (by omega)
      exact Pi1Trivial.comp_left _ ih

theorem finite_offE_inclFrom (S : Stage.{u}) :
    ∀ i, Finite (OffE (inclFrom (cx h S) (step h S) i))
  | 0 => by
      haveI : IsEmpty (OffE (inclFrom (cx h S) (step h S) 0)) := ⟨fun w => w.2 w.1 rfl⟩
      exact Finite.of_subsingleton
  | i + 1 =>
      finite_offE_comp _ _ (finite_offE_inclFrom S i) (pick h (tower h S i)).finE

theorem finite_offF_inclFrom (S : Stage.{u}) :
    ∀ i, Finite (OffF (inclFrom (cx h S) (step h S) i))
  | 0 => by
      haveI : IsEmpty (OffF (inclFrom (cx h S) (step h S) 0)) := ⟨fun w => w.2 w.1 rfl⟩
      exact Finite.of_subsingleton
  | i + 1 =>
      finite_offF_comp _ _ (finite_offF_inclFrom S i) (pick h (tower h S i)).finF

/-- **The tower is a relative chain of Proposition 3.7 carrying its inclusions.**  All four
conditions hold: the stages are connected and Cockcroft by construction, the fundamental
group of the base dies from the first stage on, and every inclusion is zero on `π₂` because
its source is Cockcroft and it kills the fundamental group. -/
noncomputable def relChainW (S : Stage.{u}) (n : ℕ) :
    RelChainW S.X (cx h S) n where
  inc := step h S
  incV i := (pick h (tower h S i)).injV
  incE i := (pick h (tower h S i)).injE
  incF i := (pick h (tower h S i)).injF
  base := rfl
  conn i := (tower h S i).conn
  cockcroft i _ := (tower h S i).cock
  zero i _ :=
    zeroPi2_of_isCockcroft_of_pi1Trivial (tower h S i).cock (tower h S i).conn
      (tower h S (i + 1)).conn (pick h (tower h S i)).kill
  pi1 i hi _ := pi1Trivial_inclFrom h S i hi
  finE := finite_offE_inclFrom h S
  finF := finite_offF_inclFrom h S
  adds i _ := (pick h (tower h S i)).adds

end CockcroftKill

/-- **The extension step of Lemmas 3.1, 3.9, 3.10 follows from the single pass
`FiniteChains.Comb.CockcroftKillStep`.**  An acyclic complex is Cockcroft, so it is a stage of
the tower, and the tower is a relative chain of any length. -/
theorem mapStep_of_cockcroftKillStep (h : CockcroftKillStep.{u}) : MapStep.{u} := by
  intro D hD hconn n
  refine ⟨CockcroftKill.cx h ⟨D, hconn, isCockcroft_of_isAcyclic hD⟩, ⟨?_⟩⟩
  exact CockcroftKill.relChainW h ⟨D, hconn, isCockcroft_of_isAcyclic hD⟩ n

/-! ### Theorem A from the single pass -/

/-- **Condition (1) of Theorem A for a finite connected acyclic complex, from the single pass
alone.** -/
theorem hasMapChains_of_cockcroftKillStep_of_isAcyclic (h : CockcroftKillStep.{u})
    {K : Complex2.{u}} [Finite K.E] [Finite K.F] (hconn : IsConnected K) (hacyc : IsAcyclic K)
    (x₀ : K.V) : HasMapChains K :=
  hasMapChains_of_mapStep_of_isAcyclic (mapStep_of_cockcroftKillStep h) hconn hacyc x₀

/-- **Theorem A for a finite connected acyclic two-complex, in its faithful, map-carrying
form, from the single pass alone.** -/
theorem theoremA_maps_of_cockcroftKillStep_of_isAcyclic (h : CockcroftKillStep.{u})
    {K : Complex2.{u}} [Finite K.E] [Finite K.F] (hconn : IsConnected K) (hacyc : IsAcyclic K)
    (x₀ : K.V) : HasMapChains K ↔ HasAcyclicRegularCover K :=
  theoremA_maps_of_isAcyclic (mapStep_of_cockcroftKillStep h) hconn hacyc x₀

/-- **Condition (1) of Theorem A for a general finite connected complex**, from the single
pass and the generation statement (3.5). -/
theorem hasMapChains_of_cockcroftKillStep (h : CockcroftKillStep.{u})
    (hgen : Pi2GeneratedByUpstairs.{u}) {K : Complex2.{u}} [Finite K.E] [Finite K.F]
    (x₀ : K.V) (hK : HasAcyclicRegularCover K) : HasMapChains K :=
  hasMapChains_of_mapStep (mapStep_of_cockcroftKillStep h) hgen x₀ hK

/-- **Theorem A for finite connected combinatorial two-complexes** from the single pass and
the generation statement (3.5). -/
theorem theoremA_maps_of_cockcroftKillStep (h : CockcroftKillStep.{u})
    (hgen : Pi2GeneratedByUpstairs.{u}) {K : Complex2.{u}} [Finite K.E] [Finite K.F]
    (hconn : IsConnected K) (x₀ : K.V) : HasMapChains K ↔ HasAcyclicRegularCover K :=
  theoremA_maps (mapStep_of_cockcroftKillStep h) hgen hconn x₀

/-! ### The pass restricted to finite complexes -/

/-- A complex enlarged by finitely many edges still has finitely many edges. -/
theorem finite_E_of_offE {P Q : Complex2.{u}} (f : Hom P Q) (hP : Finite P.E)
    (hf : Finite (OffE f)) : Finite Q.E := by
  classical
  haveI := hP
  haveI := hf
  refine Finite.of_surjective (α := P.E ⊕ OffE f) (Sum.elim f.onE fun w => w.1) ?_
  intro e
  by_cases h : ∃ d, f.onE d = e
  · obtain ⟨d, hd⟩ := h
    exact ⟨Sum.inl d, hd⟩
  · exact ⟨Sum.inr ⟨e, fun d hd => h ⟨d, hd⟩⟩, rfl⟩

/-- A complex enlarged by finitely many two-cells still has finitely many two-cells. -/
theorem finite_F_of_offF {P Q : Complex2.{u}} (f : Hom P Q) (hP : Finite P.F)
    (hf : Finite (OffF f)) : Finite Q.F := by
  classical
  haveI := hP
  haveI := hf
  refine Finite.of_surjective (α := P.F ⊕ OffF f) (Sum.elim f.onF fun w => w.1) ?_
  intro g
  by_cases h : ∃ d, f.onF d = g
  · obtain ⟨d, hd⟩ := h
    exact ⟨Sum.inl d, hd⟩
  · exact ⟨Sum.inr ⟨g, fun d hd => h ⟨d, hd⟩⟩, rfl⟩

/-- **The pass of `FiniteChains.Comb.CockcroftKillStep` asked only of finite complexes.**  This
is the form the construction of Section 3 delivers (Proposition 3.7 over a finite core): every
*finite* connected Cockcroft complex `P` sits strictly inside a finite connected Cockcroft
complex in which `π₁(P)` dies. -/
def FiniteCockcroftKillStep : Prop :=
  ∀ P : Complex2.{u}, Finite P.E → Finite P.F → IsConnected P → IsCockcroft P →
    Nonempty (CockcroftKillData P)

namespace FiniteCockcroftKill

variable (h : FiniteCockcroftKillStep.{u})

/-- A finite connected Cockcroft complex: the objects the restricted pass moves between. -/
structure FStage where
  /-- The underlying complex. -/
  X : Complex2.{u}
  /-- It has finitely many edges. -/
  finE : Finite X.E
  /-- It has finitely many two-cells. -/
  finF : Finite X.F
  /-- It is connected. -/
  conn : IsConnected X
  /-- It is Cockcroft. -/
  cock : IsCockcroft X

/-- A choice of pass out of a finite stage. -/
noncomputable def pick (S : FStage.{u}) : CockcroftKillData S.X :=
  (h S.X S.finE S.finF S.conn S.cock).some

/-- The next finite stage. -/
noncomputable def nextStage (S : FStage.{u}) : FStage.{u} :=
  ⟨(pick h S).next, finite_E_of_offE (pick h S).hom S.finE (pick h S).finE,
    finite_F_of_offF (pick h S).hom S.finF (pick h S).finF, (pick h S).conn, (pick h S).cock⟩

/-- The tower of finite stages obtained by iterating the restricted pass. -/
noncomputable def tower (S : FStage.{u}) : ℕ → FStage.{u}
  | 0 => S
  | i + 1 => nextStage h (tower S i)

/-- The complexes of the tower. -/
noncomputable def cx (S : FStage.{u}) (i : ℕ) : Complex2.{u} := (tower h S i).X

/-- The inclusions of the tower. -/
noncomputable def step (S : FStage.{u}) (i : ℕ) : Hom (cx h S i) (cx h S (i + 1)) :=
  (pick h (tower h S i)).hom

theorem pi1Trivial_inclFrom (S : FStage.{u}) :
    ∀ i, 1 ≤ i → Pi1Trivial (inclFrom (cx h S) (step h S) i)
  | 1, _ => fun a m hm => (pick h (tower h S 0)).kill a m hm
  | i + 2, _ => by
      have ih := pi1Trivial_inclFrom S (i + 1) (by omega)
      exact Pi1Trivial.comp_left _ ih

theorem finite_offE_inclFrom (S : FStage.{u}) :
    ∀ i, Finite (OffE (inclFrom (cx h S) (step h S) i))
  | 0 => by
      haveI : IsEmpty (OffE (inclFrom (cx h S) (step h S) 0)) := ⟨fun w => w.2 w.1 rfl⟩
      exact Finite.of_subsingleton
  | i + 1 =>
      finite_offE_comp _ _ (finite_offE_inclFrom S i) (pick h (tower h S i)).finE

theorem finite_offF_inclFrom (S : FStage.{u}) :
    ∀ i, Finite (OffF (inclFrom (cx h S) (step h S) i))
  | 0 => by
      haveI : IsEmpty (OffF (inclFrom (cx h S) (step h S) 0)) := ⟨fun w => w.2 w.1 rfl⟩
      exact Finite.of_subsingleton
  | i + 1 =>
      finite_offF_comp _ _ (finite_offF_inclFrom S i) (pick h (tower h S i)).finF

/-- **The tower over a finite stage is a relative chain carrying its inclusions.** -/
noncomputable def relChainW (S : FStage.{u}) (n : ℕ) : RelChainW S.X (cx h S) n where
  inc := step h S
  incV i := (pick h (tower h S i)).injV
  incE i := (pick h (tower h S i)).injE
  incF i := (pick h (tower h S i)).injF
  base := rfl
  conn i := (tower h S i).conn
  cockcroft i _ := (tower h S i).cock
  zero i _ :=
    zeroPi2_of_isCockcroft_of_pi1Trivial (tower h S i).cock (tower h S i).conn
      (tower h S (i + 1)).conn (pick h (tower h S i)).kill
  pi1 i hi _ := pi1Trivial_inclFrom h S i hi
  finE := finite_offE_inclFrom h S
  finF := finite_offF_inclFrom h S
  adds i _ := (pick h (tower h S i)).adds

end FiniteCockcroftKill

/-- **Condition (1) of Theorem A for a finite connected acyclic two-complex, from the pass
restricted to finite complexes.**  Take the identity covering of `K`: the chain upstairs is
the chain downstairs, so the generation statement (3.5) is available
(`FiniteChains.Comb.pi2GeneratedByUpstairsFor_id`), and the chain upstairs is the tower of the
restricted pass over `K` itself. -/
theorem hasMapChains_of_finiteCockcroftKillStep_of_isAcyclic (h : FiniteCockcroftKillStep.{u})
    {K : Complex2.{u}} [Finite K.E] [Finite K.F] (hconn : IsConnected K) (hacyc : IsAcyclic K)
    (x₀ : K.V) : HasMapChains K := by
  intro n
  let S : FiniteCockcroftKill.FStage.{u} :=
    ⟨K, inferInstance, inferInstance, hconn, isCockcroft_of_isAcyclic hacyc⟩
  exact ⟨strictTopChain_of_relChainW (FiniteCockcroftKill.relChainW h S (n + 1)) (Hom.id K)
    (isCovering_id K) hacyc hconn inferInstance inferInstance x₀
    (pi2GeneratedByUpstairsFor_id K)⟩

/-- **Theorem A for a finite connected acyclic two-complex, in its faithful, map-carrying
form, from the pass restricted to finite complexes.** -/
theorem theoremA_maps_of_finiteCockcroftKillStep_of_isAcyclic
    (h : FiniteCockcroftKillStep.{u}) {K : Complex2.{u}} [Finite K.E] [Finite K.F]
    (hconn : IsConnected K) (hacyc : IsAcyclic K) (x₀ : K.V) :
    HasMapChains K ↔ HasAcyclicRegularCover K :=
  ⟨fun _ => hasAcyclicRegularCover_of_isAcyclic hconn hacyc,
    fun _ => hasMapChains_of_finiteCockcroftKillStep_of_isAcyclic h hconn hacyc x₀⟩

/-- The unrestricted pass implies the restricted one. -/
theorem finiteCockcroftKillStep_of_cockcroftKillStep (h : CockcroftKillStep.{u}) :
    FiniteCockcroftKillStep.{u} := fun P _ _ hconn hcock => h P hconn hcock

end Comb
end FiniteChains
