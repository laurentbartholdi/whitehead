module

public import RequestProject.CombCoveringLift
public import RequestProject.CombPi2
public import RequestProject.MinimalGap

@[expose] public section

/-!
# The universal cover maps to every covering, and acyclic covers force the Cockcroft property

Let `p : D → K` be a combinatorial covering and let `d₀` be a vertex of `D` over the base
vertex `x₀` of `K`.  The universal cover of `K` is built in
`RequestProject/CombUniversalCover.lean` out of homotopy classes of edge paths issued from
`x₀`; sending such a class to the endpoint of the lift of any of its representatives at `d₀`
is well defined by the homotopy lifting property of
`RequestProject/CombCoveringLift.lean`, and extends to a cellular map

`FiniteChains.Comb.coverHom : Hom (uCover K x₀) D`  with  `p ∘ coverHom = univProj`.

* `FiniteChains.Comb.coverV`, `coverE`, `coverF` — the map on vertices, edges and two-cells;
* `FiniteChains.Comb.onV_coverV`, `onE_coverE`, `onF_coverF` — the lift covers the projection
  of the universal cover;
* `FiniteChains.Comb.isCockcroft_of_isAcyclicCover` — **a two-complex with a connected acyclic
  regular cover is Cockcroft**: a spherical class of `K` lifts to a two-cycle of `D`, which
  vanishes because `D` is acyclic.  This is the step "`(2)` implies that `K` is Cockcroft" of
  the paper, and it was previously carried as a hypothesis.
-/

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains
namespace Comb

universe u

variable {D K : Complex2.{u}} {p : Hom D K} {x₀ : K.V} {d₀ : D.V}

/-! ### Endpoints of lifted paths -/

variable (p d₀) in
/-- `LiftsTo p d₀ q v`: the edge path `q` of the base lifts to an edge path from `d₀` to `v`. -/
def LiftsTo (q : List (K.E × Bool)) (v : D.V) : Prop :=
  ∃ m : List (D.E × Bool), IsPath D.src D.tgt m d₀ v ∧ mapPath p m = q

theorem exists_liftsTo (hcov : IsCovering p) (hd : p.onV d₀ = x₀) (q : PathFrom K x₀) :
    ∃ v, LiftsTo p d₀ q.1 v := by
  obtain ⟨m, c, hm, hmap⟩ :=
    exists_liftPathAt hcov q.1 d₀ (endpt K x₀ q.1) (by rw [hd]; exact q.2)
  exact ⟨c, m, hm, hmap⟩

theorem liftsTo_unique (hcov : IsCovering p) {q : List (K.E × Bool)} {v w : D.V}
    (hv : LiftsTo p d₀ q v) (hw : LiftsTo p d₀ q w) : v = w := by
  obtain ⟨m, hm, hmap⟩ := hv
  obtain ⟨m', hm', hmap'⟩ := hw
  have hmm : m = m' := liftPath_unique hcov m m' d₀ v w hm hm' (by rw [hmap, hmap'])
  subst hmm
  exact isPath_endpoint_eq hm hm'

/-- The endpoint of a lift only depends on the homotopy class of the path. -/
theorem liftsTo_htpy (hcov : IsCovering p) (hd : p.onV d₀ = x₀) {q q' : List (K.E × Bool)}
    {v : D.V} (hv : LiftsTo p d₀ q v) (h : Htpy K x₀ (endpt K x₀ q) q q') :
    LiftsTo p d₀ q' v := by
  obtain ⟨m, hm, hmap⟩ := hv
  have hpath : IsPath K.src K.tgt (mapPath p m) (p.onV d₀) (p.onV v) := isPath_mapPath p hm
  rw [hmap, hd] at hpath
  have hb : endpt K x₀ q = p.onV v := endpt_eq_of_isPath hpath
  rw [hb, ← hd] at h
  obtain ⟨m', hm', hmap', -⟩ := lift_htpy hcov hm (by rw [hmap]; exact h)
  exact ⟨m', hm', hmap'⟩

/-! ### The lift on vertices -/

/-- The lift of the universal cover on vertices: the class of a path from `x₀` goes to the
endpoint of the lift of that path at `d₀`. -/
noncomputable def coverV (hcov : IsCovering p) (hd : p.onV d₀ = x₀) (c : UV K x₀) : D.V :=
  Quotient.liftOn c (fun q => Classical.choose (exists_liftsTo hcov hd q)) (by
    intro q q' hqq'
    exact liftsTo_unique hcov
      (liftsTo_htpy hcov hd (Classical.choose_spec (exists_liftsTo hcov hd q)) hqq')
      (Classical.choose_spec (exists_liftsTo hcov hd q')))

theorem coverV_spec (hcov : IsCovering p) (hd : p.onV d₀ = x₀) (q : PathFrom K x₀) :
    LiftsTo p d₀ q.1 (coverV hcov hd (UV.mk q)) :=
  Classical.choose_spec (exists_liftsTo hcov hd q)

theorem coverV_eq (hcov : IsCovering p) (hd : p.onV d₀ = x₀) {q : PathFrom K x₀} {v : D.V}
    (h : LiftsTo p d₀ q.1 v) : coverV hcov hd (UV.mk q) = v :=
  liftsTo_unique hcov (coverV_spec hcov hd q) h

theorem coverV_base (hcov : IsCovering p) (hd : p.onV d₀ = x₀) :
    coverV hcov hd (UV.base K x₀) = d₀ :=
  coverV_eq hcov hd ⟨[], rfl, rfl⟩

/-- The lift covers the projection of the universal cover. -/
theorem onV_coverV (hcov : IsCovering p) (hd : p.onV d₀ = x₀) (c : UV K x₀) :
    p.onV (coverV hcov hd c) = endV c := by
  induction c using UV.ind with
  | h q =>
      obtain ⟨m, hm, hmap⟩ := coverV_spec hcov hd q
      have hpath : IsPath K.src K.tgt (mapPath p m) (p.onV d₀) (p.onV (coverV hcov hd (UV.mk q))) :=
        isPath_mapPath p hm
      rw [hmap, hd] at hpath
      exact (endpt_eq_of_isPath hpath).symm

/-- Extending a class by an oriented edge moves the lift along the lifted edge. -/
theorem coverV_extend (hcov : IsCovering p) (hd : p.onV d₀ = x₀) {c : UV K x₀}
    {eb : K.E × Bool} (h : endV c = germSrc K.src K.tgt eb) {x : D.E × Bool}
    (hx1 : germSrc D.src D.tgt x = coverV hcov hd c) (hx2 : (p.onE x.1, x.2) = eb) :
    coverV hcov hd (extend eb c) = germTgt D.src D.tgt x := by
  induction c using UV.ind with
  | h q =>
      have h' : endpt K x₀ q.1 = germSrc K.src K.tgt eb := h
      obtain ⟨m, hm, hmap⟩ := coverV_spec hcov hd q
      rw [extend_mk]
      refine coverV_eq hcov hd ⟨m ++ [x], hm.append ⟨hx1.symm, rfl⟩, ?_⟩
      rw [extendP_pos h', mapPath_append, hmap]
      show q.1 ++ [(p.onE x.1, x.2)] = q.1 ++ [eb]
      rw [hx2]

/-! ### The lift on edges -/

theorem coverE_cond (hcov : IsCovering p) (hd : p.onV d₀ = x₀) (ce : UE K x₀) :
    germSrc K.src K.tgt (ce.1.2, true) = p.onV (coverV hcov hd ce.1.1) := by
  rw [onV_coverV]
  exact ce.2.symm

/-- The lift, at the image of its initial vertex, of the oriented edge underlying an edge of
the universal cover. -/
noncomputable def coverGerm (hcov : IsCovering p) (hd : p.onV d₀ = x₀) (ce : UE K x₀) :
    D.E × Bool :=
  Classical.choose (exists_unique_liftGerm hcov (coverV hcov hd ce.1.1) (coverE_cond hcov hd ce))

theorem coverGerm_spec (hcov : IsCovering p) (hd : p.onV d₀ = x₀) (ce : UE K x₀) :
    germSrc D.src D.tgt (coverGerm hcov hd ce) = coverV hcov hd ce.1.1 ∧
      (p.onE (coverGerm hcov hd ce).1, (coverGerm hcov hd ce).2) = (ce.1.2, true) :=
  (Classical.choose_spec
    (exists_unique_liftGerm hcov (coverV hcov hd ce.1.1) (coverE_cond hcov hd ce))).1

theorem coverGerm_snd (hcov : IsCovering p) (hd : p.onV d₀ = x₀) (ce : UE K x₀) :
    (coverGerm hcov hd ce).2 = true :=
  congrArg Prod.snd (coverGerm_spec hcov hd ce).2

/-- The lift of the universal cover on edges. -/
noncomputable def coverE (hcov : IsCovering p) (hd : p.onV d₀ = x₀) (ce : UE K x₀) : D.E :=
  (coverGerm hcov hd ce).1

theorem onE_coverE (hcov : IsCovering p) (hd : p.onV d₀ = x₀) (ce : UE K x₀) :
    p.onE (coverE hcov hd ce) = ce.1.2 :=
  congrArg Prod.fst (coverGerm_spec hcov hd ce).2

theorem coverGerm_eq (hcov : IsCovering p) (hd : p.onV d₀ = x₀) (ce : UE K x₀) :
    coverGerm hcov hd ce = (coverE hcov hd ce, true) := by
  rw [coverE, ← coverGerm_snd hcov hd ce]

theorem src_coverE (hcov : IsCovering p) (hd : p.onV d₀ = x₀) (ce : UE K x₀) :
    D.src (coverE hcov hd ce) = coverV hcov hd ce.1.1 := by
  have h := (coverGerm_spec hcov hd ce).1
  rwa [coverGerm_eq hcov hd ce, germSrc_true] at h

theorem tgt_coverE (hcov : IsCovering p) (hd : p.onV d₀ = x₀) (ce : UE K x₀) :
    D.tgt (coverE hcov hd ce) = coverV hcov hd (extend (ce.1.2, true) ce.1.1) := by
  have hcond : endV ce.1.1 = germSrc K.src K.tgt (ce.1.2, true) := ce.2
  have h := coverV_extend hcov hd (c := ce.1.1) (eb := (ce.1.2, true)) hcond
    (x := coverGerm hcov hd ce) (coverGerm_spec hcov hd ce).1 (coverGerm_spec hcov hd ce).2
  rw [h, coverGerm_eq hcov hd ce, germTgt_true]

/-! ### The lift on two-cells -/

theorem coverF_cond (hcov : IsCovering p) (hd : p.onV d₀ = x₀) (cf : UF K x₀) :
    K.base cf.1.2 = p.onV (coverV hcov hd cf.1.1) := by
  rw [onV_coverV]
  exact cf.2.symm

/-- The lift of the universal cover on two-cells. -/
noncomputable def coverF (hcov : IsCovering p) (hd : p.onV d₀ = x₀) (cf : UF K x₀) : D.F :=
  Classical.choose (exists_unique_liftCell hcov cf.1.2 (coverF_cond hcov hd cf))

theorem onF_coverF (hcov : IsCovering p) (hd : p.onV d₀ = x₀) (cf : UF K x₀) :
    p.onF (coverF hcov hd cf) = cf.1.2 :=
  (Classical.choose_spec (exists_unique_liftCell hcov cf.1.2 (coverF_cond hcov hd cf))).1.1

theorem base_coverF (hcov : IsCovering p) (hd : p.onV d₀ = x₀) (cf : UF K x₀) :
    D.base (coverF hcov hd cf) = coverV hcov hd cf.1.1 :=
  (Classical.choose_spec (exists_unique_liftCell hcov cf.1.2 (coverF_cond hcov hd cf))).1.2

/-! ### Paths -/

/-- The image of an edge path of the universal cover. -/
noncomputable def mapUP (hcov : IsCovering p) (hd : p.onV d₀ = x₀) (L : List (UE K x₀ × Bool)) :
    List (D.E × Bool) :=
  L.map (fun x => (coverE hcov hd x.1, x.2))

theorem germSrc_mapUP (hcov : IsCovering p) (hd : p.onV d₀ = x₀) (x : UE K x₀ × Bool) :
    germSrc D.src D.tgt (coverE hcov hd x.1, x.2)
      = coverV hcov hd (germSrc (uCover K x₀).src (uCover K x₀).tgt x) := by
  obtain ⟨ce, b⟩ := x
  cases b with
  | true => exact src_coverE hcov hd ce
  | false => exact tgt_coverE hcov hd ce

theorem germTgt_mapUP (hcov : IsCovering p) (hd : p.onV d₀ = x₀) (x : UE K x₀ × Bool) :
    germTgt D.src D.tgt (coverE hcov hd x.1, x.2)
      = coverV hcov hd (germTgt (uCover K x₀).src (uCover K x₀).tgt x) := by
  obtain ⟨ce, b⟩ := x
  cases b with
  | true => exact tgt_coverE hcov hd ce
  | false => exact src_coverE hcov hd ce

theorem isPath_mapUP (hcov : IsCovering p) (hd : p.onV d₀ = x₀) :
    ∀ (L : List (UE K x₀ × Bool)) (a b : UV K x₀),
      IsPath (uCover K x₀).src (uCover K x₀).tgt L a b →
        IsPath D.src D.tgt (mapUP hcov hd L) (coverV hcov hd a) (coverV hcov hd b) := by
  intro L
  induction L with
  | nil => intro a b h; exact congrArg (coverV hcov hd) h
  | cons x L ih =>
      intro a b h
      refine ⟨?_, ?_⟩
      · rw [germSrc_mapUP hcov hd x, h.1]
      · have := ih (germTgt (uCover K x₀).src (uCover K x₀).tgt x) b h.2
        rwa [← germTgt_mapUP hcov hd x] at this

theorem mapPath_mapUP (hcov : IsCovering p) (hd : p.onV d₀ = x₀) (L : List (UE K x₀ × Bool)) :
    mapPath p (mapUP hcov hd L) = mapPath (univProj K x₀) L := by
  simp only [mapPath, mapUP, List.map_map, Function.comp_def, onE_coverE]
  rfl

/-! ### The cellular lift -/

/-- **The universal cover maps to every covering.**  The lift of `univProj : uCover K x₀ → K`
along the covering `p : D → K` determined by the choice of a vertex `d₀` over `x₀`. -/
noncomputable def coverHom (hcov : IsCovering p) (hd : p.onV d₀ = x₀) :
    Hom (uCover K x₀) D where
  onV := coverV hcov hd
  onE := coverE hcov hd
  onF := coverF hcov hd
  src_onE := fun ce => src_coverE hcov hd ce
  tgt_onE := fun ce => tgt_coverE hcov hd ce
  base_onF := fun cf => base_coverF hcov hd cf
  att_onF := fun cf => by
    have hloop := uAtt_isLoop (X := K) (x₀ := x₀) cf
    have hA : IsPath D.src D.tgt (mapUP hcov hd (uAtt cf)) (coverV hcov hd cf.1.1)
        (coverV hcov hd cf.1.1) := isPath_mapUP hcov hd _ _ _ hloop
    have hproj : mapPath p (mapUP hcov hd (uAtt cf)) = K.att (p.onF (coverF hcov hd cf)) := by
      rw [mapPath_mapUP, onF_coverF]
      exact ((univProj K x₀).att_onF cf).symm
    exact (eq_att_of_lift hcov hA (base_coverF hcov hd cf) hproj).symm

theorem coverHom_onV (hcov : IsCovering p) (hd : p.onV d₀ = x₀) :
    (coverHom hcov hd).onV = coverV hcov hd := rfl

/-- The lift really is a lift: composing with the covering gives the projection of the
universal cover. -/
theorem onF_comp_coverHom (hcov : IsCovering p) (hd : p.onV d₀ = x₀) :
    p.onF ∘ (coverHom hcov hd).onF = (univProj K x₀).onF :=
  funext fun cf => onF_coverF hcov hd cf

/-! ### Acyclic covers force the Cockcroft property -/

/-- **A two-complex with an acyclic covering is Cockcroft.**  A spherical class of `K` is a
two-cycle of the universal cover; it maps to a two-cycle of the acyclic total space `D`,
which must vanish, and the Hurewicz image of the class is its further image in `K`. -/
theorem isCockcroft_of_isCovering_of_isAcyclic (hcov : IsCovering p) (hD : IsAcyclic D) :
    IsCockcroft K := by
  intro x₀ c hc
  obtain ⟨d₀, hd⟩ := hcov.surjV x₀
  set F := coverHom hcov hd with hF
  have hcycle : bdry2 D (chain2 F c) = 0 := by
    rw [bdry2_chain2 F c]
    have : bdry2 (uCover K x₀) c = 0 := hc
    rw [this, map_zero]
  have hzero : chain2 F c = 0 := by
    refine hD.h2 ?_
    rw [hcycle, map_zero]
  have hcomp : hurewicz K x₀ c = chain2 p (chain2 F c) := by
    show Finsupp.mapDomain (univProj K x₀).onF c
      = Finsupp.mapDomain p.onF (Finsupp.mapDomain F.onF c)
    rw [← Finsupp.mapDomain_comp, onF_comp_coverHom hcov hd]
  rw [hcomp, hzero, map_zero]

/-- **A two-complex with a connected acyclic regular cover is Cockcroft.**  This is the step
of the paper which deduces the Cockcroft property of `K` from condition `(2)` of Theorem A;
it used to be a hypothesis of the interface of Section 3. -/
theorem isCockcroft_of_isAcyclicCover {D K : Complex2.{u}} (h : IsAcyclicCover D K) :
    IsCockcroft K := by
  obtain ⟨Q, hQ, p, A, hcov, -, -, hacyc⟩ := h
  exact isCockcroft_of_isCovering_of_isAcyclic hcov hacyc

/-- **Condition `(2)` of Theorem A implies the Cockcroft property.** -/
theorem isCockcroft_of_hasAcyclicRegularCover {K : Complex2.{u}} (h : HasAcyclicRegularCover K) :
    IsCockcroft K := by
  obtain ⟨D, hD⟩ := (hasAcyclicRegularCover_iff K).2 h
  exact isCockcroft_of_isAcyclicCover hD

end Comb
end FiniteChains
