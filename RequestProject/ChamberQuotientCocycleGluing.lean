import RequestProject.BlockSpinePres
import RequestProject.OrderCocycleChains
import RequestProject.OrderCocyclePotential
import RequestProject.GenusSurfaceMonodromyExt
import RequestProject.GenusChainCollapse

/-! Explicit nonabelian cocycle gluing on the actual quotient Q.

The transition function comes from the marked surface theorem, not an assumed
presentation of its fundamental group. This is the geometric construction
needed for the reverse substituted-group comparison.
-/

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains.Comb.OrdCocycle
universe u v w
variable {P Q : Type u} [Preorder P] [Preorder Q]
  {G : Type v} [Group G] {H : Type w} [Group H]

theorem eq_of_val_eq {c d : OrdCocycle P G} (h : ∀ a b, c.val a b = d.val a b) :
    c = d := by
  cases c with
  | mk cv cc =>
    cases d with
    | mk dv dc =>
      have he : cv = dv := funext (fun a => funext (h a))
      cases he
      rfl

theorem comap_readPath (c : OrdCocycle Q G) (f : P → Q) (hf : Monotone f)
    (p : List ((orderCx P).E × Bool)) :
    (c.comap f hf).readPath p = c.readPath (mapPath (orderCxMap f hf) p) := by
  induction p with
  | nil => rfl
  | cons e p ih =>
    simp only [mapPath, List.map_cons]
    rw [readPath_cons, readPath_cons, ih]
    congr 1

def postcompose (c : OrdCocycle P G) (φ : G →* H) : OrdCocycle P H where
  val a b := φ (c.val a b)
  comp hab hbc := by rw [← map_mul, c.comp hab hbc]

theorem postcompose_readPath (c : OrdCocycle P G) (φ : G →* H)
    (p : List ((orderCx P).E × Bool)) :
    (c.postcompose φ).readPath p = φ (c.readPath p) := by
  induction p with
  | nil => exact (map_one φ).symm
  | cons e p ih =>
    rw [readPath_cons, readPath_cons, map_mul, ih]
    congr 1
    obtain ⟨e, b⟩ := e
    cases b <;> simp [readGerm, postcompose]

end FiniteChains.Comb.OrdCocycle

namespace FiniteChains.Davis
open RACG Mirror Comb
open scoped Classical
universe u v
variable {V : Type u} [DecidableEq V] {A : CommRel V}
  {X : Type u} [Preorder X] {att : NeSpx A →o X}
  {G : Type v} [Group G]

def positiveOldSimplex (d : QOld A) (hd : d.1.sgn = 0) : NeSpx A :=
  ⟨d.1.spx, Finset.nonempty_iff_ne_empty.mpr (fun h => d.2 ⟨h, hd⟩),
    d.1.isSimplex⟩

theorem posQCube_positiveOldSimplex (d : QOld A) (hd : d.1.sgn = 0) :
    posQCube (positiveOldSimplex d hd) = d := by
  apply Subtype.ext
  apply QCube.ext'
  · rfl
  · intro z _
    exact (congrFun hd z).symm

omit [DecidableEq V] in
theorem positiveOldSimplex_posQCube (s : NeSpx A) :
    positiveOldSimplex (posQCube s) rfl = s := by
  apply Subtype.ext
  rfl

theorem positiveOld_upward {d e : QOld A} (hde : d ≤ e) (hd : d.1.sgn = 0) :
    e.1.sgn = 0 := by
  funext z
  change e.1.sgn z = 0
  by_cases hz : z ∈ e.1.spx
  · exact e.1.sgn_eq_zero z hz
  · rw [← hde.2 z hz]
    exact congrFun hd z

theorem positiveOldSimplex_monotone {d e : QOld A} (hde : d ≤ e)
    (hd : d.1.sgn = 0) (he : e.1.sgn = 0) :
    positiveOldSimplex d hd ≤ positiveOldSimplex e he := hde.1

theorem new_le_positiveOld {x : X} {d : QOld A}
    (h : qNew (A := A) (att := att) x ≤ qOldIncl d) :
    x ≤ att (positiveOldSimplex d h.1) := by
  obtain ⟨_, hn, hx⟩ := h
  exact hx

variable (old : OrdCocycle (QOld A) G) (base : OrdCocycle X G)
  (k : NeSpx A → G)

noncomputable def quotientCocycleValue : Qpos A X att → Qpos A X att → G
  | .inl d, .inl e => old.val d e
  | .inl _, .inr _ => 1
  | .inr x, .inl e => if he : e.1.sgn = 0 then
      base.val x (att (positiveOldSimplex e he)) * (k (positiveOldSimplex e he))⁻¹
    else 1
  | .inr x, .inr y => base.val x y

theorem quotientCocycleValue_mixed (x : X) (e : QOld A) (he : e.1.sgn = 0) :
    quotientCocycleValue (att := att) old base k (.inr x) (.inl e) =
      base.val x (att (positiveOldSimplex e he)) * (k (positiveOldSimplex e he))⁻¹ := by
  classical
  simp only [quotientCocycleValue, dif_pos he]

variable (hk : ∀ {s t : NeSpx A}, s ≤ t →
  old.val (posQCube s) (posQCube t) * k t = k s * base.val (att s) (att t))

include hk in
theorem quotientCocycleValue_comp {a b c : Qpos A X att} (hab : a ≤ b) (hbc : b ≤ c) :
    quotientCocycleValue old base k a b * quotientCocycleValue old base k b c =
      quotientCocycleValue old base k a c := by
  classical
  cases a with
  | inl d =>
    cases b with
    | inl e =>
      cases c with
      | inl f => exact old.comp hab hbc
      | inr z => exact False.elim hbc
    | inr y => exact False.elim hab
  | inr x =>
    cases b with
    | inl e =>
      cases c with
      | inr z => exact False.elim hbc
      | inl f =>
        have he : e.1.sgn = 0 := hab.1
        have hf : f.1.sgn = 0 := positiveOld_upward hbc he
        have hef : positiveOldSimplex e he ≤ positiveOldSimplex f hf := hbc.1
        have hx : x ≤ att (positiveOldSimplex e he) := new_le_positiveOld hab
        have hg := hk hef
        rw [posQCube_positiveOldSimplex, posQCube_positiveOldSimplex] at hg
        have ht : (k (positiveOldSimplex e he))⁻¹ * old.val e f =
            base.val (att (positiveOldSimplex e he)) (att (positiveOldSimplex f hf)) *
              (k (positiveOldSimplex f hf))⁻¹ := by
          calc
            _ = (k (positiveOldSimplex e he))⁻¹ *
                (old.val e f * k (positiveOldSimplex f hf)) *
                  (k (positiveOldSimplex f hf))⁻¹ := by group
            _ = _ := by rw [hg]; group
        rw [quotientCocycleValue_mixed old base k x e he,
          quotientCocycleValue_mixed old base k x f hf]
        change (base.val x (att (positiveOldSimplex e he)) *
            (k (positiveOldSimplex e he))⁻¹) * old.val e f = _
        rw [mul_assoc, ht, ← mul_assoc, base.comp hx (att.monotone hef)]
    | inr y =>
      cases c with
      | inr z => exact base.comp hab hbc
      | inl f =>
        have hf : f.1.sgn = 0 := hbc.1
        have hy : y ≤ att (positiveOldSimplex f hf) := new_le_positiveOld hbc
        rw [quotientCocycleValue_mixed old base k y f hf,
          quotientCocycleValue_mixed old base k x f hf]
        change base.val x y * (base.val y (att (positiveOldSimplex f hf)) * _) = _
        rw [← mul_assoc, base.comp hab hy]

noncomputable def gluedQuotientCocycle : OrdCocycle (Qpos A X att) G where
  val := quotientCocycleValue old base k
  comp := quotientCocycleValue_comp old base k hk

theorem gluedQuotientCocycle_old (d e : QOld A) :
    (gluedQuotientCocycle old base k hk).val
      (qOldIncl (att := att) d) (qOldIncl e) = old.val d e := rfl

theorem gluedQuotientCocycle_base (x y : X) :
    (gluedQuotientCocycle old base k hk).val
      (qNew (att := att) x) (qNew y) = base.val x y := rfl

theorem gluedQuotientCocycle_cylinder (s : NeSpx A) :
    (gluedQuotientCocycle old base k hk).val
      (qNew (att := att) (att s)) (qOldIncl (posQCube s)) = (k s)⁻¹ := by
  change quotientCocycleValue old base k (.inr (att s)) (.inl (posQCube s)) = _
  rw [quotientCocycleValue_mixed old base k (att s) (posQCube s) rfl,
    positiveOldSimplex_posQCube, base.val_refl, one_mul]

theorem gluedQuotientCocycle_read_old (p : List ((orderCx (QOld A)).E × Bool)) :
    (gluedQuotientCocycle old base k hk).readPath
      (mapPath (orderCxMap (qOldIncl (att := att)) qOldIncl_monotone) p) =
      old.readPath p := by
  rw [← OrdCocycle.comap_readPath]
  rfl

theorem gluedQuotientCocycle_read_base (p : List ((orderCx X).E × Bool)) :
    (gluedQuotientCocycle old base k hk).readPath
      (mapPath (orderCxMap (qNew (A := A) (att := att)) qNew_monotone) p) =
      base.readPath p := by
  rw [← OrdCocycle.comap_readPath]
  rfl

def quotientOldBasedInclusion (s : NeSpx A) :
    Pi1 (orderCx (QOld A)) (posQCube s) →*
      Pi1 (orderCx (Qpos A X att)) (qNew (att := att) (att s)) :=
  (pi1Conj (isPath_ordPos (qNew_att_le_qOldIncl (att := att) s))).comp
    (pi1Map (orderCxMap (qOldIncl (att := att)) qOldIncl_monotone) (posQCube s))

/-- The normalized cylinder edge makes the reverse reading on the based old
inclusion equal to the original old reading, without a conjugation factor. -/
theorem monodromy_quotientOldBasedInclusion (s : NeSpx A)
    (c : OrdCocycle (Qpos A X att) G) (χ : Pi1 (orderCx (QOld A)) (posQCube s) →* G)
    (hcyl : c.val (qNew (att s)) (qOldIncl (posQCube s)) = 1)
    (hread : ∀ p : Loop (orderCx (QOld A)) (posQCube s),
      c.readPath (mapPath (orderCxMap (qOldIncl (att := att)) qOldIncl_monotone) p.1) =
        χ (Pi1.mk p)) :
    (c.monodromy (qNew (att s))).comp (quotientOldBasedInclusion (att := att) s) = χ := by
  apply MonoidHom.ext
  intro z
  refine Quotient.inductionOn z ?_
  intro p
  change c.readPath
    (([ordPos (qNew_att_le_qOldIncl (att := att) s)] ++
      mapPath (orderCxMap (qOldIncl (att := att)) qOldIncl_monotone) p.1) ++
      revPath [ordPos (qNew_att_le_qOldIncl (att := att) s)]) = _
  simp only [OrdCocycle.readPath_append, OrdCocycle.readPath_revPath,
    OrdCocycle.readPath_cons, OrdCocycle.readPath_nil,
    OrdCocycle.readGerm_ordPos, hcyl, one_mul, mul_one, inv_one]
  exact hread p

theorem monodromy_quotientBaseInclusion (x : X)
    (c : OrdCocycle (Qpos A X att) G) (d : OrdCocycle X G)
    (hd : ∀ a b, c.val (qNew a) (qNew b) = d.val a b) :
    (c.monodromy (qNew x)).comp
      (pi1Map (orderCxMap (qNew (A := A) (att := att)) qNew_monotone) x) =
        d.monodromy x := by
  have he : c.comap (qNew (A := A) (att := att)) qNew_monotone = d :=
    OrdCocycle.eq_of_val_eq hd
  apply MonoidHom.ext
  intro z
  refine Quotient.inductionOn z ?_
  intro p
  change c.readPath (mapPath (orderCxMap (qNew (A := A) (att := att)) qNew_monotone) p.1) = _
  rw [← OrdCocycle.comap_readPath, he]
  rfl

end FiniteChains.Davis

namespace FiniteChains.Davis.Genus
open RACG Mirror Comb
universe v
variable (q : ℕ) [NeZero q] {X : Type} [Preorder X]
  (att : NeSpx (cmpRel (GenusVertex q)) →o X) {G : Type v} [Group G]
  (old : OrdCocycle (QOld (cmpRel (GenusVertex q))) G) (base : OrdCocycle X G)

/-- The actual standard marked equalities suffice to glue on Q, preserving
both original cocycles and giving value 1 to the base cylinder edge. -/
theorem exists_quotientCocycle_of_marked
    (hm : ∀ x : Fin q × Bool,
      old.readPath (mapPath (surfCx (cmpRel (GenusVertex q)))
        (gSig q (x.1.val, x.2))) =
      base.readPath (mapPath (orderCxMap att att.monotone) (gSig q (x.1.val, x.2)))) :
    ∃ c : OrdCocycle (Qpos (cmpRel (GenusVertex q)) X att) G,
      (∀ d e, c.val (qOldIncl d) (qOldIncl e) = old.val d e) ∧
      (∀ x y, c.val (qNew x) (qNew y) = base.val x y) ∧
      c.val (qNew (att (gBase q))) (qOldIncl (posQCube (gBase q))) = 1 := by
  have hm' : ∀ x : Fin q × Bool,
      (old.comap posQCube posQCube_monotone).readPath (gSig q (x.1.val, x.2)) =
      (base.comap att att.monotone).readPath (gSig q (x.1.val, x.2)) := by
    intro x
    simpa only [OrdCocycle.comap_readPath, surfCx] using hm x
  obtain ⟨k, hb, hk⟩ := genus_cocycle_gauge_of_marked q
    (old.comap posQCube posQCube_monotone) (base.comap att att.monotone) hm'
  refine ⟨gluedQuotientCocycle old base k hk, ?_, ?_, ?_⟩
  · exact gluedQuotientCocycle_old old base k hk
  · exact gluedQuotientCocycle_base old base k hk
  · rw [gluedQuotientCocycle_cylinder, hb, inv_one]

end FiniteChains.Davis.Genus
