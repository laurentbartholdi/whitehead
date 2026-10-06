import RequestProject.CombUniversalCover
import RequestProject.UnivCoverIncl

/-!
# `π₂` of a combinatorial two-complex, the Hurewicz map and the Cockcroft property

With the universal cover of `RequestProject/CombUniversalCover.lean` at hand, the second
homotopy module of a two-complex is available in the usual combinatorial form: a two-complex
has no three-cells, so

  `π₂(X) = H₂(X̃) = ker ∂₂(X̃)`.

This file introduces that module, the Hurewicz map (push a two-cycle of the cover down to the
complex), the **Cockcroft** property ("the Hurewicz map is zero"), the functorial lift of a
cellular map to the universal covers, and the property "the map is zero on `π₂`" used in
condition (1) of Theorem A.

* `FiniteChains.Comb.univLift` — the lift of a cellular map to the universal covers;
* `FiniteChains.Comb.Pi2` — the second homotopy module, as the two-cycles of the cover;
* `FiniteChains.Comb.bdry2_hurewicz` — the Hurewicz image of a two-cycle of the cover is a
  two-cycle of `X`, that is, an element of `H₂(X)`;
* `FiniteChains.Comb.IsCockcroft` — the Cockcroft property: the Hurewicz map is zero;
* `FiniteChains.Comb.ZeroPi2` — a cellular map is zero on `π₂`.
-/

namespace FiniteChains
namespace Comb

universe u

variable {X Y Z : Complex2.{u}}

/-! ### Functoriality of the universal cover -/

theorem endpt_mapPath (h : Hom X Y) : ∀ (q : List (X.E × Bool)) (a : X.V),
    endpt Y (h.onV a) (mapPath h q) = h.onV (endpt X a q) := by
  intro q
  induction q with
  | nil => intro a; rfl
  | cons eb t ih =>
      intro a
      show endpt Y (germTgt Y.src Y.tgt (h.onE eb.1, eb.2)) (mapPath h t) = _
      rw [germTgt_onE h eb]
      exact ih (germTgt X.src X.tgt eb)

variable (x₀ : X.V)

/-- The image of a path from `x₀` under a cellular map. -/
def mapPathFrom (h : Hom X Y) (p : PathFrom X x₀) : PathFrom Y (h.onV x₀) :=
  ⟨mapPath h p.1, by
    rw [endpt_mapPath h p.1 x₀]
    exact isPath_mapPath h p.2⟩

theorem endpt_mapPathFrom (h : Hom X Y) (p : PathFrom X x₀) :
    endpt Y (h.onV x₀) (mapPathFrom x₀ h p).1 = h.onV (endpt X x₀ p.1) :=
  endpt_mapPath h p.1 x₀

/-- The map of universal covers induced by a cellular map, on vertices. -/
def univLiftV (h : Hom X Y) (c : UV X x₀) : UV Y (h.onV x₀) :=
  Quotient.map (mapPathFrom x₀ h) (by
    intro p q hpq
    show Htpy Y (h.onV x₀) (endpt Y (h.onV x₀) (mapPathFrom x₀ h p).1)
      (mapPathFrom x₀ h p).1 (mapPathFrom x₀ h q).1
    rw [endpt_mapPathFrom]
    exact mapPath_htpy h hpq) c

@[simp] theorem univLiftV_mk (h : Hom X Y) (p : PathFrom X x₀) :
    univLiftV x₀ h (UV.mk p) = UV.mk (mapPathFrom x₀ h p) := rfl

@[simp] theorem endV_univLiftV (h : Hom X Y) (c : UV X x₀) :
    endV (univLiftV x₀ h c) = h.onV (endV c) := by
  induction c using UV.ind with
  | h p => exact endpt_mapPathFrom x₀ h p

/-- On germs issued from the endpoint, the lift commutes with extension of classes. -/
theorem univLiftV_extend (h : Hom X Y) {eb : X.E × Bool} {c : UV X x₀}
    (hc : endV c = germSrc X.src X.tgt eb) :
    univLiftV x₀ h (extend eb c) = extend (h.onE eb.1, eb.2) (univLiftV x₀ h c) := by
  induction c using UV.ind with
  | h p =>
      have hpos : endpt X x₀ p.1 = germSrc X.src X.tgt eb := hc
      have hgerm : germSrc Y.src Y.tgt (h.onE eb.1, eb.2) = h.onV (germSrc X.src X.tgt eb) :=
        germSrc_onE h eb
      have hpos' : endpt Y (h.onV x₀) (mapPathFrom x₀ h p).1
          = germSrc Y.src Y.tgt (h.onE eb.1, eb.2) := by
        rw [endpt_mapPathFrom, hgerm, hpos]
      have hl : (mapPathFrom x₀ h (extendP eb p)).1
          = (extendP (h.onE eb.1, eb.2) (mapPathFrom x₀ h p)).1 := by
        rw [extendP_pos hpos']
        show mapPath h (extendP eb p).1 = mapPath h p.1 ++ [(h.onE eb.1, eb.2)]
        rw [extendP_pos hpos]
        simp [mapPath]
      refine Quotient.sound ?_
      show Htpy Y (h.onV x₀) (endpt Y (h.onV x₀) (mapPathFrom x₀ h (extendP eb p)).1)
        (mapPathFrom x₀ h (extendP eb p)).1 (extendP (h.onE eb.1, eb.2) (mapPathFrom x₀ h p)).1
      rw [hl]
      exact Htpy.refl _

/-- The map of universal covers induced by a cellular map, on edges. -/
def univLiftE (h : Hom X Y) (E : UE X x₀) : UE Y (h.onV x₀) :=
  ⟨(univLiftV x₀ h E.1.1, h.onE E.1.2), by
    rw [endV_univLiftV, E.2, h.src_onE]⟩

/-- The map of universal covers induced by a cellular map, on two-cells. -/
def univLiftF (h : Hom X Y) (F : UF X x₀) : UF Y (h.onV x₀) :=
  ⟨(univLiftV x₀ h F.1.1, h.onF F.1.2), by
    rw [endV_univLiftV, F.2, h.base_onF]⟩

theorem univLiftV_liftGerm (h : Hom X Y) {c : UV X x₀} {eb : X.E × Bool}
    (hc : endV c = germSrc X.src X.tgt eb)
    (hc' : endV (univLiftV x₀ h c) = germSrc Y.src Y.tgt (h.onE eb.1, eb.2)) :
    liftGerm (univLiftV x₀ h c) (h.onE eb.1, eb.2) hc'
      = (univLiftE x₀ h (liftGerm c eb hc).1, (liftGerm c eb hc).2) := by
  obtain ⟨e, b⟩ := eb
  cases b with
  | true => rfl
  | false =>
      refine Prod.ext ?_ rfl
      refine Subtype.ext (Prod.ext ?_ rfl)
      exact (univLiftV_extend x₀ h (eb := (e, false)) hc).symm

theorem uLiftPath_univLiftV (h : Hom X Y) : ∀ (q : List (X.E × Bool)) (c : UV X x₀) (w : X.V),
    IsPath X.src X.tgt q (endV c) w →
      uLiftPath (mapPath h q) (univLiftV x₀ h c)
        = (uLiftPath q c).map (fun Eb => (univLiftE x₀ h Eb.1, Eb.2)) := by
  intro q
  induction q with
  | nil => intro c w _; rfl
  | cons eb t ih =>
      intro c w hq
      have hc : endV c = germSrc X.src X.tgt eb := hq.1
      have hc' : endV (univLiftV x₀ h c) = germSrc Y.src Y.tgt (h.onE eb.1, eb.2) := by
        rw [endV_univLiftV, germSrc_onE h eb, hc]
      have hnext : IsPath X.src X.tgt t (endV (extend eb c)) w := by
        rw [endV_extend hc]; exact hq.2
      show uLiftPath ((h.onE eb.1, eb.2) :: mapPath h t) (univLiftV x₀ h c) = _
      rw [uLiftPath_cons hc', uLiftPath_cons hc, List.map_cons,
        univLiftV_liftGerm x₀ h hc hc', ← univLiftV_extend x₀ h hc,
        ih (extend eb c) w hnext]

variable (X) in
/-- **The lift of a cellular map to the universal covers.** -/
noncomputable def univLift (h : Hom X Y) (x₀ : X.V) :
    Hom (uCover X x₀) (uCover Y (h.onV x₀)) where
  onV := univLiftV x₀ h
  onE := univLiftE x₀ h
  onF := univLiftF x₀ h
  src_onE := fun _ => rfl
  tgt_onE := by
    intro E
    show extend (h.onE E.1.2, true) (univLiftV x₀ h E.1.1)
      = univLiftV x₀ h (extend (E.1.2, true) E.1.1)
    exact (univLiftV_extend x₀ h (eb := (E.1.2, true)) E.2).symm
  base_onF := fun _ => rfl
  att_onF := by
    intro F
    have hbase : endV F.1.1 = X.base F.1.2 := F.2
    have hatt : IsPath X.src X.tgt (X.att F.1.2) (endV F.1.1) (X.base F.1.2) := by
      rw [hbase]; exact X.att_isLoop F.1.2
    show uLiftPath (Y.att (h.onF F.1.2)) (univLiftV x₀ h F.1.1) = _
    rw [h.att_onF F.1.2]
    exact uLiftPath_univLiftV x₀ h (X.att F.1.2) F.1.1 (X.base F.1.2) hatt

/-! ### `π₂`, the Hurewicz map and the Cockcroft property -/

variable (X) in
/-- **The second homotopy module** of a two-complex at a base vertex: the two-cycles of its
universal cover.  (A two-complex has no three-cells, so `π₂ = H₂` of the universal cover is
the kernel of `∂₂`.) -/
noncomputable def Pi2 (x₀ : X.V) : Submodule ℤ ((uCover X x₀).F →₀ ℤ) :=
  LinearMap.ker (bdry2 (uCover X x₀))

variable (X) in
/-- **The Hurewicz map** `π₂(X) → H₂(X)`: push a two-cycle of the universal cover down to the
complex. -/
noncomputable def hurewicz (x₀ : X.V) : ((uCover X x₀).F →₀ ℤ) →ₗ[ℤ] (X.F →₀ ℤ) :=
  chain2 (univProj X x₀)

/-- The Hurewicz image of an element of `π₂` is a two-cycle of `X`, i.e. an element of
`H₂(X) = ker ∂₂`. -/
theorem bdry2_hurewicz {x₀ : X.V} {c : (uCover X x₀).F →₀ ℤ} (hc : c ∈ Pi2 X x₀) :
    bdry2 X (hurewicz X x₀ c) = 0 := by
  have h := bdry2_chain2 (univProj X x₀) c
  rw [hurewicz, h]
  have : bdry2 (uCover X x₀) c = 0 := hc
  rw [this, map_zero]

variable (X) in
/-- **The Cockcroft property**: the Hurewicz map `π₂(X) → H₂(X)` vanishes. -/
def IsCockcroft : Prop :=
  ∀ (x₀ : X.V) (c : (uCover X x₀).F →₀ ℤ), c ∈ Pi2 X x₀ → hurewicz X x₀ c = 0

/-- **A cellular map is zero on `π₂`**: the induced map of two-chains of the universal covers
kills every two-cycle. -/
def ZeroPi2 (h : Hom X Y) : Prop :=
  ∀ (x₀ : X.V) (c : (uCover X x₀).F →₀ ℤ), c ∈ Pi2 X x₀ → chain2 (univLift X h x₀) c = 0

/-- The lift of a cellular map carries `π₂` into `π₂`. -/
theorem mem_pi2_chain2_univLift (h : Hom X Y) {x₀ : X.V} {c : (uCover X x₀).F →₀ ℤ}
    (hc : c ∈ Pi2 X x₀) : chain2 (univLift X h x₀) c ∈ Pi2 Y (h.onV x₀) := by
  have hchain := bdry2_chain2 (univLift X h x₀) c
  have hzero : bdry2 (uCover X x₀) c = 0 := hc
  show bdry2 (uCover Y (h.onV x₀)) (chain2 (univLift X h x₀) c) = 0
  rw [hchain, hzero, map_zero]

end Comb
end FiniteChains
