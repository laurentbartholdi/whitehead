module

public import RequestProject.UniversalToCover
public import RequestProject.PushoutChain

@[expose] public section

/-!
# The inclusion of the base into the pushout is zero on `π₂`

This file proves the first of the three homotopy-theoretic assertions of Proposition 3.11
(step 3 of its proof in the paper): *the arrow `K → E₁ = K ∪_p L` is zero on `π₂`.*  The
argument of the paper is: "the map `K → E₁` lifts, after passing to the acyclic cover `D`, to
a map `D → Ẽ₁`; its map on `π₂` factors through `H₂(D) = 0`, and is zero."  Making that
precise in the combinatorial model needs three things, all proved here from scratch.

* `FiniteChains.Comb.lift_onF_eq` (and its companions for vertices and edges) — **uniqueness
  of lifts**: two cellular maps of a connected complex into a covering which have the same
  composite with the covering and agree at one vertex agree everywhere;
* `FiniteChains.Comb.liftHom` — **the lifting criterion**: a cellular map `f : D → Y` of a
  connected complex which kills `π₁` lifts to the universal cover of `Y`, i.e. there is a
  cellular `f̃ : D → Ỹ` with `univProj ∘ f̃ = f` and `f̃ d₀ = ` the base vertex;
* `FiniteChains.Comb.zeroPi2_of_pi1Trivial_comp` — **the homotopy statement**: if `K` has a
  connected acyclic covering `p : D → K` and `f : K → Y` is such that `f ∘ p` kills `π₁`,
  then `f` is zero on `π₂`.  Indeed the lift `K̃ → D` of the universal covering along `p`
  composed with the lift `D → Ỹ` is, by uniqueness of lifts, the lift of `f` itself, and a
  spherical class of `K` already dies in `D` because `D` is acyclic.

Applying this to the cellular pushout of `RequestProject/CombPushout.lean` gives

* `FiniteChains.Comb.zeroPi2_pushoutInl` — for a connected acyclic covering `p : D → K` and a
  connected complex `L ⊇ D` in which `π₁(D)` dies, the inclusion `K ⊆ K ∪_p L` is zero on
  `π₂`;
* `FiniteChains.Comb.zeroPi2_descentChain_zero` — the same statement for the first arrow
  `E₀ = K → E₁` of the descended chain of `RequestProject/PushoutChain.lean`.
-/

namespace FiniteChains
namespace Comb

universe u

/-! ### Uniqueness of lifts along a covering -/

section Unique

variable {X Z W : Complex2.{u}}

theorem mapPath_comp (g : Hom Z W) (h : Hom X Z) (l : List (X.E × Bool)) :
    mapPath g (mapPath h l) = mapPath (g.comp h) l := by
  simp [mapPath, List.map_map, Function.comp_def, Hom.comp]

variable {q : Hom Z W} {A B : Hom X Z}

/-- **Uniqueness of lifts, on vertices.**  Two cellular maps of a connected complex into a
covering with the same composite with the covering which agree at one vertex agree on all
vertices. -/
theorem lift_onV_eq (hq : IsCovering q) (hX : IsConnected X)
    (hE : ∀ e, q.onE (A.onE e) = q.onE (B.onE e)) {x : X.V} (hx : A.onV x = B.onV x) :
    ∀ v, A.onV v = B.onV v := by
  intro v
  obtain ⟨m, hm⟩ := hX x v
  have hA : IsPath Z.src Z.tgt (mapPath A m) (A.onV x) (A.onV v) := isPath_mapPath A hm
  have hB : IsPath Z.src Z.tgt (mapPath B m) (A.onV x) (B.onV v) := by
    rw [hx]; exact isPath_mapPath B hm
  have hmap : mapPath q (mapPath A m) = mapPath q (mapPath B m) := by
    simp only [mapPath, List.map_map, Function.comp_def]
    exact List.map_congr_left fun eb _ => by rw [hE eb.1]
  have hlists := liftPath_unique hq (mapPath A m) (mapPath B m) (A.onV x) _ _ hA hB hmap
  rw [← hlists] at hB
  exact isPath_endpoint_eq hA hB

/-- **Uniqueness of lifts, on edges.** -/
theorem lift_onE_eq (hq : IsCovering q) (hE : ∀ e, q.onE (A.onE e) = q.onE (B.onE e))
    (hV : ∀ v, A.onV v = B.onV v) : ∀ e, A.onE e = B.onE e := by
  intro e
  have h1 : germSrc Z.src Z.tgt (A.onE e, true) = A.onV (X.src e) := A.src_onE e
  have h2 : germSrc Z.src Z.tgt (B.onE e, true) = A.onV (X.src e) := by
    rw [germSrc_true, B.src_onE e, hV]
  have h3 : (q.onE (A.onE e, true).1, (A.onE e, true).2)
      = (q.onE (B.onE e, true).1, (B.onE e, true).2) := by rw [hE e]
  exact congrArg Prod.fst (liftGerm_unique hq h1 h2 h3)

/-- **Uniqueness of lifts, on two-cells.** -/
theorem lift_onF_eq (hq : IsCovering q) (hF : ∀ f, q.onF (A.onF f) = q.onF (B.onF f))
    (hV : ∀ v, A.onV v = B.onV v) : ∀ f, A.onF f = B.onF f := by
  intro f
  have hv : W.base (q.onF (A.onF f)) = q.onV (A.onV (X.base f)) := by
    rw [q.base_onF, A.base_onF]
  obtain ⟨g, -, huniq⟩ := exists_unique_liftCell hq (q.onF (A.onF f)) hv
  rw [huniq (A.onF f) ⟨rfl, A.base_onF f⟩,
    huniq (B.onF f) ⟨(hF f).symm, by rw [B.base_onF f, hV]⟩]

end Unique

/-! ### The lifting criterion -/

section Lift

variable {D Y : Complex2.{u}}

theorem mapPath_revPath (f : Hom D Y) (m : List (D.E × Bool)) :
    mapPath f (revPath m) = revPath (mapPath f m) := by
  simp [mapPath, revPath, revGerm, List.map_map, Function.comp_def, List.map_reverse]

/-- A map which kills `π₁` sends any two paths with the same endpoints to homotopic paths. -/
theorem htpy_mapPath_of_pi1Trivial {f : Hom D Y} (htriv : Pi1Trivial f)
    {m m' : List (D.E × Bool)} {a b : D.V} (hm : IsPath D.src D.tgt m a b)
    (hm' : IsPath D.src D.tgt m' a b) :
    Htpy Y (f.onV a) (f.onV b) (mapPath f m) (mapPath f m') := by
  have hP : IsPath Y.src Y.tgt (mapPath f m) (f.onV a) (f.onV b) := isPath_mapPath f hm
  have hQ : IsPath Y.src Y.tgt (mapPath f m') (f.onV a) (f.onV b) := isPath_mapPath f hm'
  have hQrev : IsPath Y.src Y.tgt (revPath (mapPath f m')) (f.onV b) (f.onV a) :=
    isPath_revPath hQ
  have h0 : Htpy Y (f.onV a) (f.onV a) (mapPath f m ++ revPath (mapPath f m')) [] := by
    have hloop : IsPath D.src D.tgt (m ++ revPath m') a a :=
      isPath_append_iff.mpr ⟨b, hm, isPath_revPath hm'⟩
    have h := htriv a (m ++ revPath m') hloop
    rwa [mapPath_append, mapPath_revPath] at h
  have hrev : Htpy Y (f.onV b) (f.onV b) (revPath (mapPath f m') ++ mapPath f m') [] :=
    htpy_revPath_append hQ
  have step1 : Htpy Y (f.onV a) (f.onV b)
      (mapPath f m ++ (revPath (mapPath f m') ++ mapPath f m')) (mapPath f m ++ []) :=
    Htpy.append_congr hP (isPath_append_iff.mpr ⟨f.onV a, hQrev, hQ⟩) (Htpy.refl _) hrev
  have step2 : Htpy Y (f.onV a) (f.onV b)
      (mapPath f m ++ revPath (mapPath f m') ++ mapPath f m') ([] ++ mapPath f m') :=
    Htpy.append_congr (isPath_append_iff.mpr ⟨f.onV b, hP, hQrev⟩) hQ h0 (Htpy.refl _)
  have hcomb : Htpy Y (f.onV a) (f.onV b) (mapPath f m ++ []) ([] ++ mapPath f m') := by
    refine step1.symm.trans ?_
    rw [← List.append_assoc]
    exact step2
  simpa using hcomb

variable (f : Hom D Y) (hconn : IsConnected D) (d₀ : D.V)

/-- A chosen edge path from the base vertex. -/
noncomputable def cPath (v : D.V) : List (D.E × Bool) := (hconn d₀ v).choose

theorem cPath_isPath (v : D.V) : IsPath D.src D.tgt (cPath hconn d₀ v) d₀ v :=
  (hconn d₀ v).choose_spec

/-- The image of a path issued from `d₀`, as a path of `Y` issued from `f d₀`. -/
def pathFromMap {v : D.V} {m : List (D.E × Bool)} (hm : IsPath D.src D.tgt m d₀ v) :
    PathFrom Y (f.onV d₀) :=
  ⟨mapPath f m, by
    have h := isPath_mapPath f hm
    rw [endpt_eq_of_isPath h]
    exact h⟩

/-- **The lift of a `π₁`-trivial map to the universal cover, on vertices**: send `v` to the
class of the image of any path from `d₀` to `v`. -/
noncomputable def liftV (v : D.V) : UV Y (f.onV d₀) :=
  UV.mk (pathFromMap f d₀ (cPath_isPath hconn d₀ v))

variable {f d₀}

theorem liftV_eq (htriv : Pi1Trivial f) {v : D.V} {m : List (D.E × Bool)}
    (hm : IsPath D.src D.tgt m d₀ v) :
    liftV f hconn d₀ v = UV.mk (pathFromMap f d₀ hm) := by
  refine UV.sound ?_
  show Htpy Y (f.onV d₀) (endpt Y (f.onV d₀) (mapPath f (cPath hconn d₀ v)))
    (mapPath f (cPath hconn d₀ v)) (mapPath f m)
  rw [endpt_eq_of_isPath (isPath_mapPath f (cPath_isPath hconn d₀ v))]
  exact htpy_mapPath_of_pi1Trivial htriv (cPath_isPath hconn d₀ v) hm

@[simp] theorem endV_liftV (v : D.V) : endV (liftV f hconn d₀ v) = f.onV v :=
  endpt_eq_of_isPath (isPath_mapPath f (cPath_isPath hconn d₀ v))

theorem liftV_base (htriv : Pi1Trivial f) : liftV f hconn d₀ d₀ = UV.base Y (f.onV d₀) :=
  liftV_eq hconn htriv (m := []) rfl

/-- Extending the lift along an oriented edge. -/
theorem liftV_extend (htriv : Pi1Trivial f) (eb : D.E × Bool) :
    liftV f hconn d₀ (germTgt D.src D.tgt eb)
      = extend (f.onE eb.1, eb.2) (liftV f hconn d₀ (germSrc D.src D.tgt eb)) := by
  set v := germSrc D.src D.tgt eb with hv
  have hm : IsPath D.src D.tgt (cPath hconn d₀ v) d₀ v := cPath_isPath hconn d₀ v
  have hstep : IsPath D.src D.tgt (cPath hconn d₀ v ++ [eb]) d₀ (germTgt D.src D.tgt eb) :=
    isPath_append_iff.mpr ⟨v, hm, isPath_single eb⟩
  rw [liftV_eq hconn htriv hstep, liftV_eq hconn htriv hm, extend_mk]
  refine congrArg UV.mk (Subtype.ext ?_)
  have hend : endpt Y (f.onV d₀) (mapPath f (cPath hconn d₀ v))
      = germSrc Y.src Y.tgt (f.onE eb.1, eb.2) := by
    rw [endpt_eq_of_isPath (isPath_mapPath f hm), germSrc_onE f eb]
  show mapPath f (cPath hconn d₀ v ++ [eb])
    = (extendP (f.onE eb.1, eb.2) (pathFromMap f d₀ hm)).1
  rw [extendP_pos hend]
  simp [mapPath, pathFromMap]

variable (f d₀)

/-- The lift of a `π₁`-trivial map to the universal cover, on edges. -/
noncomputable def liftE (e : D.E) : UE Y (f.onV d₀) :=
  ⟨(liftV f hconn d₀ (D.src e), f.onE e), by rw [endV_liftV, f.src_onE]⟩

/-- The lift of a `π₁`-trivial map to the universal cover, on two-cells. -/
noncomputable def liftF (g : D.F) : UF Y (f.onV d₀) :=
  ⟨(liftV f hconn d₀ (D.base g), f.onF g), by rw [endV_liftV, f.base_onF]⟩

variable {f d₀}

theorem uSrc_liftE (e : D.E) : uSrc (liftE f hconn d₀ e) = liftV f hconn d₀ (D.src e) := rfl

theorem uTgt_liftE (htriv : Pi1Trivial f) (e : D.E) :
    uTgt (liftE f hconn d₀ e) = liftV f hconn d₀ (D.tgt e) :=
  (liftV_extend hconn htriv (e, true)).symm

/-- The lift sends edge paths to edge paths of the universal cover. -/
theorem isPath_map_liftE (htriv : Pi1Trivial f) :
    ∀ (m : List (D.E × Bool)) (a b : D.V), IsPath D.src D.tgt m a b →
      IsPath (uCover Y (f.onV d₀)).src (uCover Y (f.onV d₀)).tgt
        (m.map fun eb => (liftE f hconn d₀ eb.1, eb.2))
        (liftV f hconn d₀ a) (liftV f hconn d₀ b) := by
  intro m
  induction m with
  | nil => intro a b hab; exact congrArg _ hab
  | cons eb t ih =>
      intro a b hab
      obtain ⟨ha, hrest⟩ := hab
      refine ⟨?_, ?_⟩
      · obtain ⟨e, s⟩ := eb
        cases s with
        | true => rw [ha]; rfl
        | false =>
            show liftV f hconn d₀ a = uTgt (liftE f hconn d₀ e)
            rw [uTgt_liftE hconn htriv, ha]
            rfl
      · have hgerm : germTgt (uCover Y (f.onV d₀)).src (uCover Y (f.onV d₀)).tgt
            (liftE f hconn d₀ eb.1, eb.2) = liftV f hconn d₀ (germTgt D.src D.tgt eb) := by
          obtain ⟨e, s⟩ := eb
          cases s with
          | true => exact uTgt_liftE hconn htriv e
          | false => rfl
        rw [hgerm]
        exact ih _ b hrest

/-- **The lifting criterion.**  A cellular map of a connected complex which kills `π₁` lifts
to the universal cover of its target. -/
noncomputable def liftHom (htriv : Pi1Trivial f) : Hom D (uCover Y (f.onV d₀)) where
  onV := liftV f hconn d₀
  onE := liftE f hconn d₀
  onF := liftF f hconn d₀
  src_onE := fun _ => rfl
  tgt_onE := fun e => uTgt_liftE hconn htriv e
  base_onF := fun _ => rfl
  att_onF := fun g => by
    have hbase : endV (liftV f hconn d₀ (D.base g)) = Y.base (f.onF g) := by
      rw [endV_liftV, f.base_onF]
    have hpath : IsPath (uCover Y (f.onV d₀)).src (uCover Y (f.onV d₀)).tgt
        ((D.att g).map fun eb => (liftE f hconn d₀ eb.1, eb.2))
        (liftV f hconn d₀ (D.base g)) (liftV f hconn d₀ (D.base g)) :=
      isPath_map_liftE hconn htriv (D.att g) _ _ (D.att_isLoop g)
    have hproj : mapPath (univProj Y (f.onV d₀))
        ((D.att g).map fun eb => (liftE f hconn d₀ eb.1, eb.2)) = Y.att (f.onF g) := by
      rw [f.att_onF g]
      simp [mapPath, List.map_map, Function.comp_def, univProj, liftE]
    have := eq_uLiftPath_of_isPath _ _ _ hpath
    rw [hproj] at this
    exact this.symm

theorem liftHom_onV (htriv : Pi1Trivial f) (v : D.V) :
    (liftHom hconn htriv).onV v = liftV f hconn d₀ v := rfl

theorem univProj_liftHom_onV (htriv : Pi1Trivial f) (v : D.V) :
    (univProj Y (f.onV d₀)).onV ((liftHom hconn htriv).onV v) = f.onV v := endV_liftV hconn v

theorem univProj_liftHom_onE (htriv : Pi1Trivial f) (e : D.E) :
    (univProj Y (f.onV d₀)).onE ((liftHom hconn htriv).onE e) = f.onE e := rfl

theorem univProj_liftHom_onF (htriv : Pi1Trivial f) (g : D.F) :
    (univProj Y (f.onV d₀)).onF ((liftHom hconn htriv).onF g) = f.onF g := rfl

theorem liftHom_base (htriv : Pi1Trivial f) :
    (liftHom hconn htriv).onV d₀ = UV.base Y (f.onV d₀) := liftV_base hconn htriv

end Lift

/-! ### Maps that are zero on `π₂` -/

variable {D K Y : Complex2.{u}}

/-- Composing on the left preserves the triviality of the induced map on `π₁`. -/
theorem Pi1Trivial.comp_left {X Z W : Complex2.{u}} {h : Hom X Z} (g : Hom Z W)
    (hh : Pi1Trivial h) : Pi1Trivial (g.comp h) := by
  intro a m hm
  have := mapPath_htpy g (hh a m hm)
  rwa [mapPath_comp, mapPath_nil] at this

/-- **A map of a complex with a connected acyclic cover which kills `π₁` upstairs is zero on
`π₂`.**  This is step 3 of the proof of Proposition 3.11: the composite `D → K → Y` lifts to
the universal cover of `Y`, so the lift `K̃ → Ỹ` factors through the acyclic complex `D`,
where every two-cycle vanishes. -/
theorem zeroPi2_of_pi1Trivial_comp {p : Hom D K} (hcov : IsCovering p) (hD : IsAcyclic D)
    (hconnD : IsConnected D) (hconnY : IsConnected Y) (f : Hom K Y)
    (htriv : Pi1Trivial (f.comp p)) : ZeroPi2 f := by
  intro x₀ c hc
  obtain ⟨d₀, hd⟩ := hcov.surjV x₀
  subst hd
  set F : Hom (uCover K (p.onV d₀)) D := coverHom hcov rfl
  set psi : Hom D (uCover Y (f.onV (p.onV d₀))) := liftHom hconnD htriv with hpsi
  set A : Hom (uCover K (p.onV d₀)) (uCover Y (f.onV (p.onV d₀))) :=
    univLift K f (p.onV d₀)
  set B : Hom (uCover K (p.onV d₀)) (uCover Y (f.onV (p.onV d₀))) := psi.comp F
  have hq : IsCovering (univProj Y (f.onV (p.onV d₀))) := isCovering_univProj hconnY
  have hqE : ∀ e, (univProj Y (f.onV (p.onV d₀))).onE (A.onE e)
      = (univProj Y (f.onV (p.onV d₀))).onE (B.onE e) := by
    intro e
    show f.onE e.1.2 = f.onE (p.onE (coverE hcov rfl e))
    rw [onE_coverE hcov rfl e]
  have hqF : ∀ g, (univProj Y (f.onV (p.onV d₀))).onF (A.onF g)
      = (univProj Y (f.onV (p.onV d₀))).onF (B.onF g) := by
    intro g
    show f.onF g.1.2 = f.onF (p.onF (coverF hcov rfl g))
    rw [onF_coverF hcov rfl g]
  have hbase : A.onV (UV.base K (p.onV d₀)) = B.onV (UV.base K (p.onV d₀)) := by
    have hFbase : F.onV (UV.base K (p.onV d₀)) = d₀ := coverV_base hcov rfl
    show UV.mk (mapPathFrom (p.onV d₀) f ⟨[], rfl⟩) = psi.onV (F.onV (UV.base K (p.onV d₀)))
    rw [hFbase, hpsi, liftHom_base hconnD htriv]
    rfl
  have hV := lift_onV_eq hq isConnected_univCover hqE hbase
  have hFeq := lift_onF_eq hq hqF hV
  have hcycle : bdry2 D (chain2 F c) = 0 := by
    rw [bdry2_chain2 F c]
    have h : bdry2 (uCover K (p.onV d₀)) c = 0 := hc
    rw [h, map_zero]
  have hzero : chain2 F c = 0 := hD.h2 (by rw [hcycle, map_zero])
  have hcomp : chain2 A c = chain2 psi (chain2 F c) := by
    show Finsupp.mapDomain A.onF c = Finsupp.mapDomain psi.onF (Finsupp.mapDomain F.onF c)
    rw [← Finsupp.mapDomain_comp]
    exact congrArg (fun m => Finsupp.mapDomain m c) (funext hFeq)
  rw [hcomp, hzero, map_zero]

/-! ### Maps out of an acyclic complex -/

/-- **A `π₁`-trivial map out of a connected acyclic complex is zero on `π₂`.**  Take the
identity covering of `D` in `FiniteChains.Comb.zeroPi2_of_pi1Trivial_comp`: the map lifts to
the universal cover of its target, so on `π₂` it factors through `H₂(D) = 0`. -/
theorem zeroPi2_of_isAcyclic_of_pi1Trivial {f : Hom D Y} (hD : IsAcyclic D)
    (hconnD : IsConnected D) (hconnY : IsConnected Y) (htriv : Pi1Trivial f) : ZeroPi2 f :=
  zeroPi2_of_pi1Trivial_comp (isCovering_id D) hD hconnD hconnY f htriv

/-- The same statement in the interface of Theorem A: over a connected acyclic complex `D`,
the field `zero` of a relative chain at its first step is a **consequence** of the field
`pi1`. -/
theorem combData_zeroPi2_of_isAcyclic (hD : IsAcyclic D) (hconnD : IsConnected D)
    (hconnY : IsConnected Y) (hpi1 : combData.Pi1Trivial D Y) : combData.ZeroPi2 D Y :=
  fun h hV hE hF => zeroPi2_of_isAcyclic_of_pi1Trivial hD hconnD hconnY (hpi1 h hV hE hF)

/-- **One condition less in a relative chain.**  To build a relative chain over a connected
acyclic complex `D` one no longer has to check that the first inclusion `D = c₀ ⊆ c₁` is zero
on `π₂`: that follows from the triviality of `π₁(D)` in `c₁`. -/
theorem isRelativeChain_of_zero_succ {D : Complex2.{u}} {c : ℕ → Complex2.{u}} {n : ℕ}
    (hD : IsAcyclic D) (hconnD : IsConnected D) (hconn : ∀ i, i ≤ n → IsConnected (c i))
    (hsub : ∀ i < n, Sub (c i) (c (i + 1))) (hstrict : ∀ i < n, c i ≠ c (i + 1))
    (hzero : ∀ i, 1 ≤ i → i < n → combData.ZeroPi2 (c i) (c (i + 1))) (hbase : c 0 = D)
    (hcock : ∀ i ≤ n, IsCockcroft (c i))
    (hpi1 : ∀ i, 1 ≤ i → i ≤ n → combData.Pi1Trivial D (c i)) :
    IsRelativeChain combData D c n where
  sub := hsub
  strict := hstrict
  zero := by
    intro i hi
    rcases Nat.eq_zero_or_pos i with rfl | h1
    · rw [hbase]
      exact combData_zeroPi2_of_isAcyclic hD hconnD (hconn 1 hi) (hpi1 1 le_rfl hi)
    · exact hzero i h1 hi
  base := hbase
  cockcroft := hcock
  pi1 := hpi1

/-! ### The inclusion of the base into the cellular pushout -/

variable {L : Complex2.{u}}

/-- **The inclusion `K ⊆ K ∪_p L` is zero on `π₂`.**  Here `p : D → K` is a connected acyclic
covering, `D ⊆ L` with `π₁(D)` dying in `L`, and `L` is connected. -/
theorem zeroPi2_pushoutInl {p : Hom D K} (i : Hom D L) (hiV : Function.Injective i.onV)
    (hiE : Function.Injective i.onE) (hiF : Function.Injective i.onF) (hcov : IsCovering p)
    (hD : IsAcyclic D) (hconnD : IsConnected D) (hconnK : IsConnected K)
    (hconnL : IsConnected L) (hpi1 : Pi1Trivial i) :
    ZeroPi2 (pushoutInl p i hiV hiE) := by
  intro x₀ c hc
  obtain ⟨d₀, -⟩ := hcov.surjV x₀
  have hconnE : IsConnected (pushoutComplex p i hiV hiE) :=
    isConnected_pushoutComplex p i hiV hiE hconnK hconnL d₀
  have hcomm : (pushoutInl p i hiV hiE).comp p = (pushoutMap p i hiV hiE hiF).comp i :=
    (pushout_comm p i hiV hiE hiF).symm
  have htriv : Pi1Trivial ((pushoutInl p i hiV hiE).comp p) := by
    rw [hcomm]
    exact Pi1Trivial.comp_left _ hpi1
  exact zeroPi2_of_pi1Trivial_comp hcov hD hconnD hconnE _ htriv x₀ c hc

/-! ### The first arrow of the descended chain -/

variable {c : ℕ → Complex2.{u}}

/-- **The inclusion of `K` into any stage of the descended chain is zero on `π₂`**: the arrow
`E₀ = K → Eᵢ₊₁ = K ∪_p Lᵢ₊₁` of `RequestProject/PushoutChain.lean` kills `π₂`, as soon as
`π₁(L₀) = π₁(D)` dies in `Lᵢ₊₁`.  For `i = 0` this is the first arrow of the chain of
Proposition 3.11. -/
theorem zeroPi2_descentChain_inl {K : Complex2.{u}} (p : Hom (c 0) K)
    (hsub : ∀ i, Sub (c i) (c (i + 1))) (hcov : IsCovering p) (hD : IsAcyclic (c 0))
    (hconnD : IsConnected (c 0)) (hconnK : IsConnected K) (i : ℕ)
    (hconnL : IsConnected (c (i + 1))) (hpi1 : Pi1Trivial (chainIncl c hsub (i + 1))) :
    ZeroPi2 (pushoutInl p (chainIncl c hsub (i + 1)) (chainIncl_injV hsub (i + 1))
      (chainIncl_injE hsub (i + 1))) :=
  zeroPi2_pushoutInl _ _ _ (chainIncl_injF hsub (i + 1)) hcov hD hconnD hconnK hconnL hpi1

/-- The complex the previous statement speaks about really is the `(i+1)`-st term of the
descended chain. -/
theorem descentChain_eq_pushout {K : Complex2.{u}} (p : Hom (c 0) K)
    (hsub : ∀ i, Sub (c i) (c (i + 1))) (i : ℕ) :
    descentChain K p hsub (i + 1) =
      pushoutComplex p (chainIncl c hsub (i + 1)) (chainIncl_injV hsub (i + 1))
        (chainIncl_injE hsub (i + 1)) := rfl

end Comb
end FiniteChains
