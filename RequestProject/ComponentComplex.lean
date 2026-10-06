module

public import RequestProject.CombData

@[expose] public section

/-!
# The connected component of a two-complex, and `π₂`

Condition (1) of Theorem A speaks of chains `K ⊂ X₀ ⊂ ⋯ ⊂ Xₙ` of two-complexes.  The
machinery of Section 2 (spanning trees, presentations, Fox matrices) needs the stages to be
*connected*, and up to now this was an extra hypothesis of the formalised implication
`(1) ⇒ (2)`.  This file removes it: a stage may be replaced by the connected component of the
image of `K`, and nothing is lost, because the inclusion of a component induces an injection
of universal covers, hence carries the condition "zero on `π₂`" along.

* `FiniteChains.Comb.Reach` — the vertex is joined to the base vertex by an edge path;
* `FiniteChains.Comb.component` — the connected component of `x₀`: the subcomplex of all
  cells reachable from `x₀`;
* `FiniteChains.Comb.componentIncl` — its inclusion into the ambient complex, injective on
  cells of every dimension;
* `FiniteChains.Comb.Hom.toComponent` — the corestriction of a cellular map whose image is
  reachable;
* `FiniteChains.Comb.htpy_liftGerms` — a homotopy inside the ambient complex between edge
  paths issued from a reachable vertex already takes place inside the component;
* `FiniteChains.Comb.univLiftV_componentIncl_injective` — consequently the inclusion of the
  component induces an injection of universal covers;
* `FiniteChains.Comb.zeroPi2_toComponent` and `FiniteChains.Comb.zeroPi2_comp_right` — being
  zero on `π₂` is inherited by the corestriction to a component and by precomposition.
-/

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains
namespace Comb

universe u

variable {A X Y Z : Complex2.{u}}

/-! ### Reachable cells -/

/-- `Reach X x₀ v` : the vertex `v` is joined to `x₀` by an edge path. -/
def Reach (X : Complex2.{u}) (x₀ v : X.V) : Prop := ∃ p, IsPath X.src X.tgt p x₀ v

theorem reach_self (X : Complex2.{u}) (x₀ : X.V) : Reach X x₀ x₀ := ⟨[], rfl⟩

theorem Reach.trans_path {x₀ a b : X.V} (h : Reach X x₀ a) {p : List (X.E × Bool)}
    (hp : IsPath X.src X.tgt p a b) : Reach X x₀ b := by
  obtain ⟨q, hq⟩ := h
  exact ⟨q ++ p, hq.append hp⟩

theorem Reach.map (f : Hom X Y) {x₀ v : X.V} (h : Reach X x₀ v) :
    Reach Y (f.onV x₀) (f.onV v) := by
  obtain ⟨p, hp⟩ := h
  exact ⟨mapPath f p, isPath_mapPath f hp⟩

theorem Reach.tgt_of_src {x₀ : X.V} {e : X.E} (h : Reach X x₀ (X.src e)) :
    Reach X x₀ (X.tgt e) :=
  h.trans_path (p := [(e, true)]) ⟨rfl, rfl⟩

theorem Reach.src_of_tgt {x₀ : X.V} {e : X.E} (h : Reach X x₀ (X.tgt e)) :
    Reach X x₀ (X.src e) :=
  h.trans_path (p := [(e, false)]) ⟨rfl, rfl⟩

theorem Reach.src_of_germSrc {x₀ : X.V} {eb : X.E × Bool}
    (h : Reach X x₀ (germSrc X.src X.tgt eb)) : Reach X x₀ (X.src eb.1) := by
  obtain ⟨e, b⟩ := eb
  cases b with
  | true => exact h
  | false => exact Reach.src_of_tgt h

theorem Reach.germSrc_of_src {x₀ : X.V} {eb : X.E × Bool}
    (h : Reach X x₀ (X.src eb.1)) : Reach X x₀ (germSrc X.src X.tgt eb) := by
  obtain ⟨e, b⟩ := eb
  cases b with
  | true => exact h
  | false => exact Reach.tgt_of_src h

/-- Every edge of a path issued from a reachable vertex is reachable. -/
theorem reach_of_mem_path {x₀ : X.V} :
    ∀ {l : List (X.E × Bool)} {a b : X.V}, IsPath X.src X.tgt l a b → Reach X x₀ a →
      ∀ eb ∈ l, Reach X x₀ (X.src eb.1)
  | [], _, _, _, _, _, hm => absurd hm List.not_mem_nil
  | eb :: t, a, b, hl, ha, eb', hm => by
      have ha' : Reach X x₀ (germSrc X.src X.tgt eb) := hl.1 ▸ ha
      have htail : Reach X x₀ (germTgt X.src X.tgt eb) :=
        ha'.trans_path (p := [eb]) ⟨rfl, rfl⟩
      rcases List.mem_cons.mp hm with h | h
      · subst h; exact ha'.src_of_germSrc
      · exact reach_of_mem_path hl.2 htail eb' h

/-! ### The cells of the component -/

variable (X) in
/-- The vertices of the component of `x₀`. -/
def CV (x₀ : X.V) : Type u := {v : X.V // Reach X x₀ v}

variable (X) in
/-- The edges of the component of `x₀`. -/
def CE (x₀ : X.V) : Type u := {e : X.E // Reach X x₀ (X.src e)}

variable (X) in
/-- The two-cells of the component of `x₀`. -/
def CF (x₀ : X.V) : Type u := {f : X.F // Reach X x₀ (X.base f)}

variable {x₀ : X.V}

/-- The initial vertex of an edge of the component. -/
def cSrc (e : CE X x₀) : CV X x₀ := ⟨X.src e.1, e.2⟩

/-- The terminal vertex of an edge of the component. -/
def cTgt (e : CE X x₀) : CV X x₀ := ⟨X.tgt e.1, e.2.tgt_of_src⟩

open Classical in
/-- The list of oriented edges of the component carried by a list of oriented edges of the
ambient complex: unreachable edges are dropped (they never occur in the lists we lift). -/
noncomputable def liftGerms (X : Complex2.{u}) (x₀ : X.V) (l : List (X.E × Bool)) :
    List (CE X x₀ × Bool) :=
  l.filterMap fun eb => if h : Reach X x₀ (X.src eb.1) then some (⟨eb.1, h⟩, eb.2) else none

@[simp] theorem liftGerms_nil (X : Complex2.{u}) (x₀ : X.V) : liftGerms X x₀ [] = [] := rfl

@[simp] theorem liftGerms_append (X : Complex2.{u}) (x₀ : X.V) (l l' : List (X.E × Bool)) :
    liftGerms X x₀ (l ++ l') = liftGerms X x₀ l ++ liftGerms X x₀ l' := by
  simp [liftGerms, List.filterMap_append]

theorem liftGerms_cons {eb : X.E × Bool} (h : Reach X x₀ (X.src eb.1))
    (l : List (X.E × Bool)) :
    liftGerms X x₀ (eb :: l) = ((⟨eb.1, h⟩ : CE X x₀), eb.2) :: liftGerms X x₀ l := by
  classical
  simp [liftGerms, h]

/-- The forgetful map on oriented edges of the component. -/
def cForget (eb : CE X x₀ × Bool) : X.E × Bool := (eb.1.1, eb.2)

@[simp] theorem liftGerms_map_cForget (L : List (CE X x₀ × Bool)) :
    liftGerms X x₀ (L.map cForget) = L := by
  induction L with
  | nil => rfl
  | cons eb L ih =>
      rw [List.map_cons, liftGerms_cons (eb := cForget eb) eb.1.2, ih]
      rfl

theorem map_cForget_liftGerms {l : List (X.E × Bool)}
    (h : ∀ eb ∈ l, Reach X x₀ (X.src eb.1)) :
    (liftGerms X x₀ l).map cForget = l := by
  induction l with
  | nil => rfl
  | cons eb l ih =>
      rw [liftGerms_cons (h eb List.mem_cons_self), List.map_cons,
        ih fun e he => h e (List.mem_cons_of_mem _ he)]
      rfl

@[simp] theorem cGermSrc (eb : CE X x₀ × Bool) :
    germSrc cSrc cTgt eb = ⟨germSrc X.src X.tgt (cForget eb), (eb.1.2).germSrc_of_src⟩ := by
  obtain ⟨e, b⟩ := eb
  cases b <;> rfl

@[simp] theorem cGermTgt (eb : CE X x₀ × Bool) :
    germTgt cSrc cTgt eb = ⟨germTgt X.src X.tgt (cForget eb), by
      obtain ⟨e, b⟩ := eb
      cases b
      · exact e.2
      · exact e.2.tgt_of_src⟩ := by
  obtain ⟨e, b⟩ := eb
  cases b <;> rfl

/-- A path of the ambient complex issued from a reachable vertex lifts to a path of the
component. -/
theorem isPath_liftGerms :
    ∀ {l : List (X.E × Bool)} {a b : X.V} (ha : Reach X x₀ a) (hb : Reach X x₀ b),
      IsPath X.src X.tgt l a b →
        IsPath (cSrc (X := X) (x₀ := x₀)) cTgt (liftGerms X x₀ l) ⟨a, ha⟩ ⟨b, hb⟩
  | [], a, b, ha, hb, hl => by
      show (⟨a, ha⟩ : CV X x₀) = ⟨b, hb⟩
      exact Subtype.ext hl
  | eb :: t, a, b, ha, hb, hl => by
      have hsrc : Reach X x₀ (X.src eb.1) := (hl.1 ▸ ha).src_of_germSrc
      have htgt : Reach X x₀ (germTgt X.src X.tgt eb) :=
        (hl.1 ▸ ha).trans_path (p := [eb]) ⟨rfl, rfl⟩
      rw [liftGerms_cons hsrc]
      refine ⟨?_, ?_⟩
      · rw [cGermSrc]
        exact Subtype.ext hl.1
      · have := isPath_liftGerms htgt hb hl.2
        rw [cGermTgt]
        exact this

/-! ### The component -/

variable (X) in
/-- **The connected component** of a vertex: the subcomplex of all cells reachable from
`x₀`. -/
noncomputable def component (x₀ : X.V) : Complex2.{u} where
  V := CV X x₀
  E := CE X x₀
  F := CF X x₀
  src := cSrc
  tgt := cTgt
  base f := ⟨X.base f.1, f.2⟩
  att f := liftGerms X x₀ (X.att f.1)
  att_isLoop f := isPath_liftGerms f.2 f.2 (X.att_isLoop f.1)

@[simp] theorem component_V (x₀ : X.V) : (component X x₀).V = CV X x₀ := rfl
@[simp] theorem component_E (x₀ : X.V) : (component X x₀).E = CE X x₀ := rfl
@[simp] theorem component_F (x₀ : X.V) : (component X x₀).F = CF X x₀ := rfl
@[simp] theorem component_src (x₀ : X.V) : (component X x₀).src = cSrc := rfl
@[simp] theorem component_tgt (x₀ : X.V) : (component X x₀).tgt = cTgt := rfl
@[simp] theorem component_att (x₀ : X.V) (f : CF X x₀) :
    (component X x₀).att f = liftGerms X x₀ (X.att f.1) := rfl

instance (x₀ : X.V) [Finite X.E] : Finite (component X x₀).E := by
  show Finite (CE X x₀); unfold CE; infer_instance

instance (x₀ : X.V) [Finite X.F] : Finite (component X x₀).F := by
  show Finite (CF X x₀); unfold CF; infer_instance

/-- The component is connected. -/
theorem component_isConnected (x₀ : X.V) : IsConnected (component X x₀) := by
  rintro ⟨a, p, hp⟩ ⟨b, q, hq⟩
  refine ⟨liftGerms X x₀ (revPath p ++ q), ?_⟩
  exact isPath_liftGerms _ _ ((isPath_revPath hp).append hq)

variable (X) in
/-- The inclusion of the component into the complex. -/
noncomputable def componentIncl (x₀ : X.V) : Hom (component X x₀) X where
  onV := Subtype.val
  onE := Subtype.val
  onF := Subtype.val
  src_onE _ := rfl
  tgt_onE _ := rfl
  base_onF _ := rfl
  att_onF f := by
    refine (map_cForget_liftGerms ?_).symm
    exact reach_of_mem_path (X.att_isLoop f.1) f.2

@[simp] theorem componentIncl_onV (x₀ : X.V) (v : (component X x₀).V) :
    (componentIncl X x₀).onV v = v.1 := rfl

@[simp] theorem componentIncl_onE (x₀ : X.V) (e : (component X x₀).E) :
    (componentIncl X x₀).onE e = e.1 := rfl

@[simp] theorem componentIncl_onF (x₀ : X.V) (f : (component X x₀).F) :
    (componentIncl X x₀).onF f = f.1 := rfl

theorem componentIncl_injective_onV (x₀ : X.V) :
    Function.Injective (componentIncl X x₀).onV := fun _ _ h => Subtype.ext h

theorem componentIncl_injective_onE (x₀ : X.V) :
    Function.Injective (componentIncl X x₀).onE := fun _ _ h => Subtype.ext h

theorem componentIncl_injective_onF (x₀ : X.V) :
    Function.Injective (componentIncl X x₀).onF := fun _ _ h => Subtype.ext h

/-! ### Corestriction of a cellular map to a component -/

/-- Two cellular maps agreeing on cells of every dimension are equal. -/
theorem Hom.ext' {f g : Hom X Y} (hV : f.onV = g.onV) (hE : f.onE = g.onE)
    (hF : f.onF = g.onF) : f = g := by
  cases f; cases g; cases hV; cases hE; cases hF; rfl

/-- **The corestriction of a cellular map** whose image is reachable from `x₀`. -/
noncomputable def Hom.toComponent (f : Hom A X) (x₀ : X.V)
    (h : ∀ v : A.V, Reach X x₀ (f.onV v)) : Hom A (component X x₀) where
  onV v := ⟨f.onV v, h v⟩
  onE e := ⟨f.onE e, by rw [f.src_onE]; exact h _⟩
  onF c := ⟨f.onF c, by rw [f.base_onF]; exact h _⟩
  src_onE e := Subtype.ext (f.src_onE e)
  tgt_onE e := Subtype.ext (f.tgt_onE e)
  base_onF c := Subtype.ext (f.base_onF c)
  att_onF c := by
    have hL : X.att (f.onF c)
        = ((A.att c).map fun eb => ((⟨f.onE eb.1, by rw [f.src_onE]; exact h _⟩ : CE X x₀),
            eb.2)).map cForget := by
      rw [f.att_onF, List.map_map]
      rfl
    show liftGerms X x₀ (X.att (f.onF c)) = _
    rw [hL, liftGerms_map_cForget]

@[simp] theorem toComponent_onV (f : Hom A X) (x₀ : X.V)
    (h : ∀ v : A.V, Reach X x₀ (f.onV v)) (v : A.V) :
    (f.toComponent x₀ h).onV v = ⟨f.onV v, h v⟩ := rfl

theorem componentIncl_comp_toComponent (f : Hom A X) (x₀ : X.V)
    (h : ∀ v : A.V, Reach X x₀ (f.onV v)) :
    (componentIncl X x₀).comp (f.toComponent x₀ h) = f :=
  Hom.ext' rfl rfl rfl

theorem toComponent_injective_onV {f : Hom A X} {x₀ : X.V}
    (h : ∀ v : A.V, Reach X x₀ (f.onV v)) (hf : Function.Injective f.onV) :
    Function.Injective (f.toComponent x₀ h).onV :=
  fun _ _ hx => hf (congrArg Subtype.val hx)

theorem toComponent_injective_onE {f : Hom A X} {x₀ : X.V}
    (h : ∀ v : A.V, Reach X x₀ (f.onV v)) (hf : Function.Injective f.onE) :
    Function.Injective (f.toComponent x₀ h).onE :=
  fun _ _ hx => hf (congrArg Subtype.val hx)

theorem toComponent_injective_onF {f : Hom A X} {x₀ : X.V}
    (h : ∀ v : A.V, Reach X x₀ (f.onV v)) (hf : Function.Injective f.onF) :
    Function.Injective (f.toComponent x₀ h).onF :=
  fun _ _ hx => hf (congrArg Subtype.val hx)

/-! ### Homotopies take place inside the component -/

/-- An elementary homotopy of the ambient complex between paths issued from a reachable
vertex lifts to the component. -/
theorem step_liftGerms {a b : X.V} (ha : Reach X x₀ a) (hb : Reach X x₀ b)
    {l l' : List (X.E × Bool)} (hstep : Step X a b l l') :
    Htpy (component X x₀) ⟨a, ha⟩ ⟨b, hb⟩ (liftGerms X x₀ l) (liftGerms X x₀ l') := by
  obtain ⟨hl, hl', hc⟩ := hstep
  have hPl : IsPath (component X x₀).src (component X x₀).tgt (liftGerms X x₀ l)
      ⟨a, ha⟩ ⟨b, hb⟩ := isPath_liftGerms ha hb hl
  have hPl' : IsPath (component X x₀).src (component X x₀).tgt (liftGerms X x₀ l')
      ⟨a, ha⟩ ⟨b, hb⟩ := isPath_liftGerms ha hb hl'
  rcases hc with ⟨p, q, eb, hlEq, hl'Eq⟩ | ⟨p, q, f, hlEq, hl'Eq⟩
  · have hmem : eb ∈ l := by
      rw [hlEq]; exact List.mem_append_right _ List.mem_cons_self
    have hsrc : Reach X x₀ (X.src eb.1) := reach_of_mem_path hl ha eb hmem
    refine Htpy.of_step ⟨hPl, hPl', Or.inl ⟨liftGerms X x₀ p, liftGerms X x₀ q,
      (⟨eb.1, hsrc⟩, eb.2), ?_, ?_⟩⟩
    · rw [hlEq, liftGerms_append, liftGerms_cons hsrc,
        liftGerms_cons (eb := revGerm eb) hsrc]
      rfl
    · rw [hl'Eq, liftGerms_append]
  · by_cases hatt : X.att f = []
    · have : liftGerms X x₀ l = liftGerms X x₀ l' := by
        rw [hlEq, hl'Eq, hatt]
        simp
      rw [this]
      exact Htpy.refl _
    · obtain ⟨eb, t, hsplit⟩ : ∃ eb t, X.att f = eb :: t := by
        cases hx : X.att f with
        | nil => exact absurd hx hatt
        | cons eb t => exact ⟨eb, t, rfl⟩
      have hmem : eb ∈ l := by
        rw [hlEq, hsplit]
        simp
      have hsrc : Reach X x₀ (X.src eb.1) := reach_of_mem_path hl ha eb hmem
      have hbase : Reach X x₀ (X.base f) := by
        have hloop := X.att_isLoop f
        rw [hsplit] at hloop
        rw [hloop.1]
        exact hsrc.germSrc_of_src
      refine Htpy.of_step ⟨hPl, hPl', Or.inr ⟨liftGerms X x₀ p, liftGerms X x₀ q,
        ⟨f, hbase⟩, ?_, ?_⟩⟩
      · rw [hlEq, liftGerms_append, liftGerms_append]
        rfl
      · rw [hl'Eq, liftGerms_append]

/-- **A homotopy of the ambient complex between paths issued from a reachable vertex already
takes place inside the component.** -/
theorem htpy_liftGerms {a b : X.V} (ha : Reach X x₀ a) (hb : Reach X x₀ b)
    {l l' : List (X.E × Bool)} (h : Htpy X a b l l') :
    Htpy (component X x₀) ⟨a, ha⟩ ⟨b, hb⟩ (liftGerms X x₀ l) (liftGerms X x₀ l') := by
  induction h with
  | refl => exact Htpy.refl _
  | tail _ hstep ih =>
      refine (ih).trans ?_
      rcases hstep with hs | hs
      · exact step_liftGerms ha hb hs
      · exact (step_liftGerms ha hb hs).symm

/-! ### The universal cover of a component -/

theorem mapPath_componentIncl (x₀ : X.V) (l : List ((component X x₀).E × Bool)) :
    mapPath (componentIncl X x₀) l = l.map cForget := rfl

/-- **The inclusion of a component is injective on universal covers**: two edge paths of the
component which become homotopic in the ambient complex are homotopic in the component. -/
theorem univLiftV_componentIncl_injective (c₀ : (component X x₀).V) :
    Function.Injective (univLiftV c₀ (componentIncl X x₀)) := by
  intro cP cQ hPQ
  induction cP using UV.ind with
  | h P =>
    induction cQ using UV.ind with
    | h Q =>
      have hx : Htpy X c₀.1 (endpt X c₀.1 (mapPath (componentIncl X x₀) P.1))
          (mapPath (componentIncl X x₀) P.1) (mapPath (componentIncl X x₀) Q.1) :=
        Quotient.exact hPQ
      have hd : endpt X c₀.1 (mapPath (componentIncl X x₀) P.1)
          = (endpt (component X x₀) c₀ P.1).1 :=
        endpt_mapPath (componentIncl X x₀) P.1 c₀
      rw [hd] at hx
      have hlift := htpy_liftGerms (x₀ := x₀) c₀.2 (endpt (component X x₀) c₀ P.1).2 hx
      rw [mapPath_componentIncl, mapPath_componentIncl, liftGerms_map_cForget,
        liftGerms_map_cForget] at hlift
      exact Quotient.sound hlift

/-- The inclusion of a component is injective on the two-cells of the universal covers. -/
theorem univLift_componentIncl_injective_onF (c₀ : (component X x₀).V) :
    Function.Injective (univLift (component X x₀) (componentIncl X x₀) c₀).onF := by
  intro F G h
  have h' : univLiftF c₀ (componentIncl X x₀) F = univLiftF c₀ (componentIncl X x₀) G := h
  have h1 : univLiftV c₀ (componentIncl X x₀) F.1.1
      = univLiftV c₀ (componentIncl X x₀) G.1.1 := congrArg (fun z => z.1.1) h'
  have h2 : (componentIncl X x₀).onF F.1.2 = (componentIncl X x₀).onF G.1.2 :=
    congrArg (fun z => z.1.2) h'
  refine Subtype.ext (Prod.ext ?_ ?_)
  · exact univLiftV_componentIncl_injective c₀ h1
  · exact componentIncl_injective_onF x₀ h2

/-! ### Functoriality of the lift to universal covers -/

theorem univLiftV_comp (g : Hom Y Z) (f : Hom X Y) (x₀ : X.V) (c : UV X x₀) :
    univLiftV (f.onV x₀) g (univLiftV x₀ f c) = univLiftV x₀ (g.comp f) c := by
  induction c using UV.ind with
  | h p =>
      refine Quotient.sound ?_
      have hlist : mapPath g (mapPath f p.1) = mapPath (g.comp f) p.1 := by
        simp only [mapPath, List.map_map]
        rfl
      show Htpy Z (g.onV (f.onV x₀)) _ (mapPath g (mapPath f p.1)) (mapPath (g.comp f) p.1)
      rw [hlist]
      exact Htpy.refl _

theorem univLiftF_comp (g : Hom Y Z) (f : Hom X Y) (x₀ : X.V) (F : UF X x₀) :
    univLiftF (f.onV x₀) g (univLiftF x₀ f F) = univLiftF x₀ (g.comp f) F :=
  Subtype.ext (Prod.ext (univLiftV_comp g f x₀ F.1.1) rfl)

theorem univLiftV_toComponent (f : Hom A X) (x₀ : X.V) (h : ∀ v : A.V, Reach X x₀ (f.onV v))
    (y₀ : A.V) (c : UV A y₀) :
    univLiftV ((f.toComponent x₀ h).onV y₀) (componentIncl X x₀)
        (univLiftV y₀ (f.toComponent x₀ h) c) = univLiftV y₀ f c := by
  induction c using UV.ind with
  | h p =>
      refine Quotient.sound ?_
      have hlist : mapPath (componentIncl X x₀) (mapPath (f.toComponent x₀ h) p.1)
          = mapPath f p.1 := by
        simp only [mapPath, List.map_map]
        rfl
      show Htpy X (f.onV y₀) _
        (mapPath (componentIncl X x₀) (mapPath (f.toComponent x₀ h) p.1)) (mapPath f p.1)
      rw [hlist]
      exact Htpy.refl _

theorem univLiftF_toComponent (f : Hom A X) (x₀ : X.V) (h : ∀ v : A.V, Reach X x₀ (f.onV v))
    (y₀ : A.V) (F : UF A y₀) :
    univLiftF ((f.toComponent x₀ h).onV y₀) (componentIncl X x₀)
        (univLiftF y₀ (f.toComponent x₀ h) F) = univLiftF y₀ f F :=
  Subtype.ext (Prod.ext (univLiftV_toComponent f x₀ h y₀ F.1.1) rfl)

/-! ### Zero on `π₂` passes to components -/

/-- **Precomposition preserves being zero on `π₂`.** -/
theorem zeroPi2_comp_right (g : Hom Y Z) (f : Hom X Y) (hz : ZeroPi2 g) :
    ZeroPi2 (g.comp f) := by
  intro x₀ c hc
  have hcycle : chain2 (univLift X f x₀) c ∈ Pi2 Y (f.onV x₀) :=
    mem_pi2_chain2_univLift f hc
  have hg := hz (f.onV x₀) (chain2 (univLift X f x₀) c) hcycle
  have hfun : ∀ F : UF X x₀, (univLift Y g (f.onV x₀)).onF ((univLift X f x₀).onF F)
      = (univLift X (g.comp f) x₀).onF F := fun F => univLiftF_comp g f x₀ F
  have : Finsupp.mapDomain (univLift X (g.comp f) x₀).onF c
      = Finsupp.mapDomain (univLift Y g (f.onV x₀)).onF
        (Finsupp.mapDomain (univLift X f x₀).onF c) := by
    rw [← Finsupp.mapDomain_comp]
    exact Finsupp.mapDomain_congr fun F _ => (hfun F).symm
  show Finsupp.mapDomain (univLift X (g.comp f) x₀).onF c = 0
  rw [this]
  exact hg

/-- **The corestriction to a component of a map which is zero on `π₂` is zero on `π₂`.** -/
theorem zeroPi2_toComponent {f : Hom A X} {x₀ : X.V} (h : ∀ v : A.V, Reach X x₀ (f.onV v))
    (hz : ZeroPi2 f) : ZeroPi2 (f.toComponent x₀ h) := by
  intro y₀ c hc
  have hz' : Finsupp.mapDomain (univLift A f y₀).onF c = 0 := hz y₀ c hc
  have hcomp : Finsupp.mapDomain
      (univLift (component X x₀) (componentIncl X x₀) ((f.toComponent x₀ h).onV y₀)).onF
      (Finsupp.mapDomain (univLift A (f.toComponent x₀ h) y₀).onF c) = 0 := by
    rw [← Finsupp.mapDomain_comp]
    rw [show ((univLift (component X x₀) (componentIncl X x₀)
        ((f.toComponent x₀ h).onV y₀)).onF ∘ (univLift A (f.toComponent x₀ h) y₀).onF)
        = (univLift A f y₀).onF from funext fun F => univLiftF_toComponent f x₀ h y₀ F]
    exact hz'
  have hinj := univLift_componentIncl_injective_onF (X := X) (x₀ := x₀)
    ((f.toComponent x₀ h).onV y₀)
  show Finsupp.mapDomain (univLift A (f.toComponent x₀ h) y₀).onF c = 0
  refine Finsupp.mapDomain_injective hinj ?_
  rw [hcomp, Finsupp.mapDomain_zero]

end Comb
end FiniteChains
