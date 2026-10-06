module

public import RequestProject.CombData

@[expose] public section

/-!
# The cellular pushout `E = K ∪_p L` of Proposition 3.11

Proposition 3.11 of the paper descends a chain of complexes over an acyclic regular cover
`p : D → K` to a chain over `K` by forming, for every term `L` of the chain upstairs, the
cellular pushout

  `E = K ∪_p L = (K ⊔ L)/(d ∼ p d  for every cell d of D)`.

So far the project used this construction only as a black box (the field `descent` of
`FiniteChains.Comb.Gap`).  This file builds it honestly inside the combinatorial model of
`RequestProject/CellComplex.lean` and proves everything about it that does not involve
homotopy groups:

* `FiniteChains.Comb.pushoutComplex` — the complex `E`: its cells are the cells of `K`
  together with the cells of `L` which do not come from `D`;
* `FiniteChains.Comb.pushoutInl` — the cellular map `K → E`, injective on all cells, so
  `FiniteChains.Comb.sub_pushoutComplex : Sub K E`;
* `FiniteChains.Comb.pushoutMap` — the cellular map `L → E`;
* `FiniteChains.Comb.pushout_comm` — the square commutes: `L → E` precomposed with `D → L`
  is `K → E` precomposed with `p`;
* `FiniteChains.Comb.pushout_universal` — the **universal property**: any pair of cellular
  maps out of `K` and `L` agreeing on `D` factors uniquely through `E`;
* `FiniteChains.Comb.pushoutComplex_finite_*` — `E` has finitely many cells as soon as `K`
  has and `L` has only finitely many cells off `D`.

Only the injectivity of the inclusion `D ⊆ L` is used; `p` is an arbitrary cellular map.
-/

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains
namespace Comb

universe u

variable {K D L : Complex2.{u}}

/-! ### Transport of edge paths along a map of graphs -/

/-- A map of graphs takes edge paths to edge paths. -/
theorem isPath_map {V E V' E' : Type*} {src tgt : E → V} {src' tgt' : E' → V'}
    (fV : V → V') (fE : E → E') (hs : ∀ e, src' (fE e) = fV (src e))
    (ht : ∀ e, tgt' (fE e) = fV (tgt e)) :
    ∀ {q : List (E × Bool)} {a b : V}, IsPath src tgt q a b →
      IsPath src' tgt' (q.map fun eb => (fE eb.1, eb.2)) (fV a) (fV b) := by
  intro q
  induction q with
  | nil => intro a b h; exact congrArg fV h
  | cons eb q ih =>
      rintro a b ⟨h1, h2⟩
      refine ⟨?_, ?_⟩
      · obtain ⟨e, s⟩ := eb
        cases s <;> simp [germSrc, hs, ht] at h1 ⊢ <;> exact congrArg fV h1
      · obtain ⟨e, s⟩ := eb
        cases s
        · simpa [germTgt, hs, ht] using ih h2
        · simpa [germTgt, hs, ht] using ih h2

/-! ### The cells of `L` off `D` -/

/-- The vertices of `L` which do not come from `D`. -/
def OffV (i : Hom D L) : Type u := {v : L.V // ∀ d, i.onV d ≠ v}

/-- The edges of `L` which do not come from `D`. -/
def OffE (i : Hom D L) : Type u := {e : L.E // ∀ d, i.onE d ≠ e}

/-- The two-cells of `L` which do not come from `D`. -/
def OffF (i : Hom D L) : Type u := {f : L.F // ∀ d, i.onF d ≠ f}

open Classical in
/-- The vertex map `L → E`: a vertex coming from `D` goes to its image in `K`, any other
vertex survives. -/
noncomputable def pushV (p : Hom D K) (i : Hom D L) (v : L.V) : K.V ⊕ OffV i :=
  if h : ∃ d, i.onV d = v then Sum.inl (p.onV h.choose) else Sum.inr ⟨v, fun d hd => h ⟨d, hd⟩⟩

open Classical in
/-- The edge map `L → E`. -/
noncomputable def pushE (p : Hom D K) (i : Hom D L) (e : L.E) : K.E ⊕ OffE i :=
  if h : ∃ d, i.onE d = e then Sum.inl (p.onE h.choose) else Sum.inr ⟨e, fun d hd => h ⟨d, hd⟩⟩

open Classical in
/-- The two-cell map `L → E`. -/
noncomputable def pushF (p : Hom D K) (i : Hom D L) (f : L.F) : K.F ⊕ OffF i :=
  if h : ∃ d, i.onF d = f then Sum.inl (p.onF h.choose) else Sum.inr ⟨f, fun d hd => h ⟨d, hd⟩⟩

theorem pushV_of_mem (p : Hom D K) {i : Hom D L} (hi : Function.Injective i.onV) (d : D.V) :
    pushV p i (i.onV d) = Sum.inl (p.onV d) := by
  have h : ∃ d', i.onV d' = i.onV d := ⟨d, rfl⟩
  rw [pushV, dif_pos h, hi h.choose_spec]

theorem pushE_of_mem (p : Hom D K) {i : Hom D L} (hi : Function.Injective i.onE) (d : D.E) :
    pushE p i (i.onE d) = Sum.inl (p.onE d) := by
  have h : ∃ d', i.onE d' = i.onE d := ⟨d, rfl⟩
  rw [pushE, dif_pos h, hi h.choose_spec]

theorem pushF_of_mem (p : Hom D K) {i : Hom D L} (hi : Function.Injective i.onF) (d : D.F) :
    pushF p i (i.onF d) = Sum.inl (p.onF d) := by
  have h : ∃ d', i.onF d' = i.onF d := ⟨d, rfl⟩
  rw [pushF, dif_pos h, hi h.choose_spec]

theorem pushV_of_off (p : Hom D K) (i : Hom D L) (v : OffV i) :
    pushV p i v.1 = Sum.inr v := by
  rw [pushV, dif_neg (by rintro ⟨d, hd⟩; exact v.2 d hd)]
  rfl

theorem pushE_of_off (p : Hom D K) (i : Hom D L) (e : OffE i) :
    pushE p i e.1 = Sum.inr e := by
  rw [pushE, dif_neg (by rintro ⟨d, hd⟩; exact e.2 d hd)]
  rfl

theorem pushF_of_off (p : Hom D K) (i : Hom D L) (f : OffF i) :
    pushF p i f.1 = Sum.inr f := by
  rw [pushF, dif_neg (by rintro ⟨d, hd⟩; exact f.2 d hd)]
  rfl

/-- Every vertex of the pushout is either a vertex of `K` or the image of a vertex of `L`. -/
theorem pushV_surjective_or (p : Hom D K) (i : Hom D L) (x : K.V ⊕ OffV i) :
    (∃ a, x = Sum.inl a) ∨ ∃ v, x = pushV p i v := by
  cases x with
  | inl a => exact Or.inl ⟨a, rfl⟩
  | inr v => exact Or.inr ⟨v.1, (pushV_of_off p i v).symm⟩

/-! ### The pushout complex -/

section

variable (p : Hom D K) (i : Hom D L)
  (hiV : Function.Injective i.onV) (hiE : Function.Injective i.onE)

noncomputable def psrc : K.E ⊕ OffE i → K.V ⊕ OffV i :=
  Sum.elim (fun e => Sum.inl (K.src e)) (fun e => pushV p i (L.src e.1))

noncomputable def ptgt : K.E ⊕ OffE i → K.V ⊕ OffV i :=
  Sum.elim (fun e => Sum.inl (K.tgt e)) (fun e => pushV p i (L.tgt e.1))

include hiV hiE in
theorem psrc_pushE (e : L.E) : psrc p i (pushE p i e) = pushV p i (L.src e) := by
  by_cases h : ∃ d, i.onE d = e
  · obtain ⟨d, rfl⟩ := h
    rw [pushE_of_mem p hiE d]
    show Sum.inl (K.src (p.onE d)) = _
    rw [p.src_onE, i.src_onE, pushV_of_mem p hiV]
  · have he : (⟨e, fun d hd => h ⟨d, hd⟩⟩ : OffE i).1 = e := rfl
    rw [pushE_of_off p i ⟨e, fun d hd => h ⟨d, hd⟩⟩]
    show pushV p i (L.src e) = pushV p i (L.src e)
    rfl

include hiV hiE in
theorem ptgt_pushE (e : L.E) : ptgt p i (pushE p i e) = pushV p i (L.tgt e) := by
  by_cases h : ∃ d, i.onE d = e
  · obtain ⟨d, rfl⟩ := h
    rw [pushE_of_mem p hiE d]
    show Sum.inl (K.tgt (p.onE d)) = _
    rw [p.tgt_onE, i.tgt_onE, pushV_of_mem p hiV]
  · rw [pushE_of_off p i ⟨e, fun d hd => h ⟨d, hd⟩⟩]
    rfl

/-- **The cellular pushout `E = K ∪_p L`.**  Its vertices, edges and two-cells are those of
`K` together with those of `L` which do not come from `D`; a cell of `L` coming from `D` is
identified with its image under `p`. -/
noncomputable def pushoutComplex : Complex2.{u} where
  V := K.V ⊕ OffV i
  E := K.E ⊕ OffE i
  F := K.F ⊕ OffF i
  src := psrc p i
  tgt := ptgt p i
  base := Sum.elim (fun f => Sum.inl (K.base f)) (fun f => pushV p i (L.base f.1))
  att := Sum.elim (fun f => (K.att f).map fun eb => (Sum.inl eb.1, eb.2))
    (fun f => (L.att f.1).map fun eb => (pushE p i eb.1, eb.2))
  att_isLoop := by
    rintro (f | f)
    · exact isPath_map (src := K.src) (tgt := K.tgt) Sum.inl Sum.inl (fun _ => rfl) (fun _ => rfl)
        (K.att_isLoop f)
    · exact isPath_map (src := L.src) (tgt := L.tgt) (pushV p i) (pushE p i)
        (psrc_pushE p i hiV hiE) (ptgt_pushE p i hiV hiE) (L.att_isLoop f.1)

@[simp] theorem pushoutComplex_src_inl (e : K.E) :
    (pushoutComplex p i hiV hiE).src (Sum.inl e) = Sum.inl (K.src e) := rfl

@[simp] theorem pushoutComplex_tgt_inl (e : K.E) :
    (pushoutComplex p i hiV hiE).tgt (Sum.inl e) = Sum.inl (K.tgt e) := rfl

theorem pushoutComplex_src_pushE (e : L.E) :
    (pushoutComplex p i hiV hiE).src (pushE p i e) = pushV p i (L.src e) :=
  psrc_pushE p i hiV hiE e

theorem pushoutComplex_tgt_pushE (e : L.E) :
    (pushoutComplex p i hiV hiE).tgt (pushE p i e) = pushV p i (L.tgt e) :=
  ptgt_pushE p i hiV hiE e

/-- The inclusion `K ⊆ E`. -/
noncomputable def pushoutInl : Hom K (pushoutComplex p i hiV hiE) where
  onV := Sum.inl
  onE := Sum.inl
  onF := Sum.inl
  src_onE := fun _ => rfl
  tgt_onE := fun _ => rfl
  base_onF := fun _ => rfl
  att_onF := fun _ => rfl

/-- `K` is a subcomplex of the pushout. -/
theorem sub_pushoutComplex : Sub K (pushoutComplex p i hiV hiE) :=
  ⟨pushoutInl p i hiV hiE, fun _ _ h => Sum.inl_injective h, fun _ _ h => Sum.inl_injective h,
    fun _ _ h => Sum.inl_injective h⟩

include hiV hiE in
theorem att_pushF (hiF : Function.Injective i.onF) (f : L.F) :
    (pushoutComplex p i hiV hiE).att (pushF p i f) =
      (L.att f).map fun eb => (pushE p i eb.1, eb.2) := by
  by_cases h : ∃ d, i.onF d = f
  · obtain ⟨d, rfl⟩ := h
    rw [pushF_of_mem p hiF d]
    show (K.att (p.onF d)).map (fun eb => (Sum.inl eb.1, eb.2)) = _
    rw [p.att_onF, i.att_onF]
    simp [Function.comp, pushE_of_mem p hiE]
  · rw [pushF_of_off p i ⟨f, fun d hd => h ⟨d, hd⟩⟩]
    rfl

include hiV hiE in
theorem base_pushF (hiF : Function.Injective i.onF) (f : L.F) :
    (pushoutComplex p i hiV hiE).base (pushF p i f) = pushV p i (L.base f) := by
  by_cases h : ∃ d, i.onF d = f
  · obtain ⟨d, rfl⟩ := h
    rw [pushF_of_mem p hiF d]
    show Sum.inl (K.base (p.onF d)) = _
    rw [p.base_onF, i.base_onF, pushV_of_mem p hiV]
  · rw [pushF_of_off p i ⟨f, fun d hd => h ⟨d, hd⟩⟩]
    rfl

/-- The cellular map `L → E`. -/
noncomputable def pushoutMap (hiF : Function.Injective i.onF) :
    Hom L (pushoutComplex p i hiV hiE) where
  onV := pushV p i
  onE := pushE p i
  onF := pushF p i
  src_onE := pushoutComplex_src_pushE p i hiV hiE
  tgt_onE := pushoutComplex_tgt_pushE p i hiV hiE
  base_onF := base_pushF p i hiV hiE hiF
  att_onF := att_pushF p i hiV hiE hiF

/-- **The pushout square commutes**: a cell of `D` has the same image in `E` whether it is
pushed into `L` or mapped into `K`. -/
theorem pushout_comm (hiF : Function.Injective i.onF) :
    (pushoutMap p i hiV hiE hiF).comp i = (pushoutInl p i hiV hiE).comp p := by
  have hV : ∀ d, pushV p i (i.onV d) = Sum.inl (p.onV d) := pushV_of_mem p hiV
  have hE : ∀ d, pushE p i (i.onE d) = Sum.inl (p.onE d) := pushE_of_mem p hiE
  have hF : ∀ d, pushF p i (i.onF d) = Sum.inl (p.onF d) := pushF_of_mem p hiF
  have : ∀ (X Y : Complex2.{u}) (f g : Hom X Y), f.onV = g.onV → f.onE = g.onE →
      f.onF = g.onF → f = g := by
    rintro X Y ⟨a, b, c, _, _, _, _⟩ ⟨a', b', c', _, _, _, _⟩ h1 h2 h3
    cases h1; cases h2; cases h3; rfl
  exact this _ _ _ _ (funext hV) (funext hE) (funext hF)

/-! ### The universal property -/

variable {M : Complex2.{u}}

/-- The map out of the pushout induced by a compatible pair of maps. -/
noncomputable def pushoutLift (f : Hom K M) (g : Hom L M)
    (hV : ∀ d, g.onV (i.onV d) = f.onV (p.onV d))
    (hE : ∀ d, g.onE (i.onE d) = f.onE (p.onE d)) : Hom (pushoutComplex p i hiV hiE) M := by
  have lV : ∀ v : L.V, Sum.elim f.onV (fun w : OffV i => g.onV w.1) (pushV p i v) = g.onV v := by
    intro v
    by_cases h : ∃ d, i.onV d = v
    · obtain ⟨d, rfl⟩ := h
      rw [pushV_of_mem p hiV d]
      exact (hV d).symm
    · rw [pushV_of_off p i ⟨v, fun d hd => h ⟨d, hd⟩⟩]
      rfl
  have lE : ∀ e : L.E, Sum.elim f.onE (fun w : OffE i => g.onE w.1) (pushE p i e) = g.onE e := by
    intro e
    by_cases h : ∃ d, i.onE d = e
    · obtain ⟨d, rfl⟩ := h
      rw [pushE_of_mem p hiE d]
      exact (hE d).symm
    · rw [pushE_of_off p i ⟨e, fun d hd => h ⟨d, hd⟩⟩]
      rfl
  exact
    { onV := Sum.elim f.onV (fun w : OffV i => g.onV w.1)
      onE := Sum.elim f.onE (fun w : OffE i => g.onE w.1)
      onF := Sum.elim f.onF (fun w : OffF i => g.onF w.1)
      src_onE := by
        rintro (e | e)
        · exact f.src_onE e
        · show M.src (g.onE e.1) = Sum.elim f.onV _ (pushV p i (L.src e.1))
          rw [lV, g.src_onE]
      tgt_onE := by
        rintro (e | e)
        · exact f.tgt_onE e
        · show M.tgt (g.onE e.1) = Sum.elim f.onV _ (pushV p i (L.tgt e.1))
          rw [lV, g.tgt_onE]
      base_onF := by
        rintro (c | c)
        · exact f.base_onF c
        · show M.base (g.onF c.1) = Sum.elim f.onV _ (pushV p i (L.base c.1))
          rw [lV, g.base_onF]
      att_onF := by
        rintro (c | c)
        · show M.att (f.onF c) = ((K.att c).map fun eb => (Sum.inl eb.1, eb.2)).map _
          rw [f.att_onF]
          simp
        · show M.att (g.onF c.1) = ((L.att c.1).map fun eb => (pushE p i eb.1, eb.2)).map _
          rw [g.att_onF]
          simp only [List.map_map]
          exact List.map_congr_left (fun eb _ => by simp [Function.comp, lE eb.1]) }

@[simp] theorem pushoutLift_onV (f : Hom K M) (g : Hom L M)
    (hV : ∀ d, g.onV (i.onV d) = f.onV (p.onV d))
    (hE : ∀ d, g.onE (i.onE d) = f.onE (p.onE d)) :
    (pushoutLift p i hiV hiE f g hV hE).onV = Sum.elim f.onV (fun w : OffV i => g.onV w.1) := rfl

@[simp] theorem pushoutLift_onE (f : Hom K M) (g : Hom L M)
    (hV : ∀ d, g.onV (i.onV d) = f.onV (p.onV d))
    (hE : ∀ d, g.onE (i.onE d) = f.onE (p.onE d)) :
    (pushoutLift p i hiV hiE f g hV hE).onE = Sum.elim f.onE (fun w : OffE i => g.onE w.1) := rfl

@[simp] theorem pushoutLift_onF (f : Hom K M) (g : Hom L M)
    (hV : ∀ d, g.onV (i.onV d) = f.onV (p.onV d))
    (hE : ∀ d, g.onE (i.onE d) = f.onE (p.onE d)) :
    (pushoutLift p i hiV hiE f g hV hE).onF = Sum.elim f.onF (fun w : OffF i => g.onF w.1) := rfl

/-- **The universal property of the pushout.**  A pair of cellular maps `K → M`, `L → M`
agreeing on `D` factors through `E = K ∪_p L`, and the factorization is unique. -/
theorem pushout_universal (hiF : Function.Injective i.onF) (f : Hom K M) (g : Hom L M)
    (hV : ∀ d, g.onV (i.onV d) = f.onV (p.onV d))
    (hE : ∀ d, g.onE (i.onE d) = f.onE (p.onE d))
    (hF : ∀ d, g.onF (i.onF d) = f.onF (p.onF d)) :
    ∃! u : Hom (pushoutComplex p i hiV hiE) M,
      u.comp (pushoutInl p i hiV hiE) = f ∧ u.comp (pushoutMap p i hiV hiE hiF) = g := by
  classical
  have ext : ∀ (X Y : Complex2.{u}) (a b : Hom X Y), a.onV = b.onV → a.onE = b.onE →
      a.onF = b.onF → a = b := by
    rintro X Y ⟨a1, a2, a3, _, _, _, _⟩ ⟨b1, b2, b3, _, _, _, _⟩ h1 h2 h3
    cases h1; cases h2; cases h3; rfl
  refine ⟨pushoutLift p i hiV hiE f g hV hE, ⟨?_, ?_⟩, ?_⟩
  · exact ext _ _ _ _ rfl rfl rfl
  · refine ext _ _ _ _ (funext fun v => ?_) (funext fun e => ?_) (funext fun c => ?_)
    · show Sum.elim f.onV (fun w : OffV i => g.onV w.1) (pushV p i v) = g.onV v
      by_cases h : ∃ d, i.onV d = v
      · obtain ⟨d, rfl⟩ := h
        rw [pushV_of_mem p hiV d]
        exact (hV d).symm
      · rw [pushV_of_off p i ⟨v, fun d hd => h ⟨d, hd⟩⟩]
        rfl
    · show Sum.elim f.onE (fun w : OffE i => g.onE w.1) (pushE p i e) = g.onE e
      by_cases h : ∃ d, i.onE d = e
      · obtain ⟨d, rfl⟩ := h
        rw [pushE_of_mem p hiE d]
        exact (hE d).symm
      · rw [pushE_of_off p i ⟨e, fun d hd => h ⟨d, hd⟩⟩]
        rfl
    · show Sum.elim f.onF (fun w : OffF i => g.onF w.1) (pushF p i c) = g.onF c
      by_cases h : ∃ d, i.onF d = c
      · obtain ⟨d, rfl⟩ := h
        rw [pushF_of_mem p hiF d]
        exact (hF d).symm
      · rw [pushF_of_off p i ⟨c, fun d hd => h ⟨d, hd⟩⟩]
        rfl
  · rintro u ⟨hu1, hu2⟩
    refine ext _ _ _ _ (funext fun x => ?_) (funext fun x => ?_) (funext fun x => ?_)
    · cases x with
      | inl a => exact congrFun (congrArg Hom.onV hu1) a
      | inr w =>
          have := congrFun (congrArg Hom.onV hu2) w.1
          show u.onV (Sum.inr w) = g.onV w.1
          rw [← this]
          show u.onV (Sum.inr w) = u.onV (pushV p i w.1)
          rw [pushV_of_off p i w]
    · cases x with
      | inl a => exact congrFun (congrArg Hom.onE hu1) a
      | inr w =>
          have := congrFun (congrArg Hom.onE hu2) w.1
          show u.onE (Sum.inr w) = g.onE w.1
          rw [← this]
          show u.onE (Sum.inr w) = u.onE (pushE p i w.1)
          rw [pushE_of_off p i w]
    · cases x with
      | inl a => exact congrFun (congrArg Hom.onF hu1) a
      | inr w =>
          have := congrFun (congrArg Hom.onF hu2) w.1
          show u.onF (Sum.inr w) = g.onF w.1
          rw [← this]
          show u.onF (Sum.inr w) = u.onF (pushF p i w.1)
          rw [pushF_of_off p i w]

/-! ### Finiteness -/

theorem pushoutComplex_finite_V (h₁ : Finite K.V) (h₂ : Finite (OffV i)) :
    Finite (pushoutComplex p i hiV hiE).V :=
  inferInstanceAs (Finite (K.V ⊕ OffV i))

theorem pushoutComplex_finite_E (h₁ : Finite K.E) (h₂ : Finite (OffE i)) :
    Finite (pushoutComplex p i hiV hiE).E :=
  inferInstanceAs (Finite (K.E ⊕ OffE i))

theorem pushoutComplex_finite_F (h₁ : Finite K.F) (h₂ : Finite (OffF i)) :
    Finite (pushoutComplex p i hiV hiE).F :=
  inferInstanceAs (Finite (K.F ⊕ OffF i))

end

/-! ### Functoriality in the term upstairs -/

section Functor

variable {L' : Complex2.{u}}

theorem functor_hV (p : Hom D K) (j : Hom D L) (j' : Hom D L') (k : Hom L L')
    (hj'V : Function.Injective j'.onV) (hj'E : Function.Injective j'.onE)
    (hj'F : Function.Injective j'.onF) (hkj : k.comp j = j') (d : D.V) :
    ((pushoutMap p j' hj'V hj'E hj'F).comp k).onV (j.onV d) =
      (pushoutInl p j' hj'V hj'E).onV (p.onV d) := by
  show pushV p j' (k.onV (j.onV d)) = Sum.inl (p.onV d)
  rw [show k.onV (j.onV d) = j'.onV d from congrFun (congrArg Hom.onV hkj) d,
    pushV_of_mem p hj'V]

theorem functor_hE (p : Hom D K) (j : Hom D L) (j' : Hom D L') (k : Hom L L')
    (hj'V : Function.Injective j'.onV) (hj'E : Function.Injective j'.onE)
    (hj'F : Function.Injective j'.onF) (hkj : k.comp j = j') (d : D.E) :
    ((pushoutMap p j' hj'V hj'E hj'F).comp k).onE (j.onE d) =
      (pushoutInl p j' hj'V hj'E).onE (p.onE d) := by
  show pushE p j' (k.onE (j.onE d)) = Sum.inl (p.onE d)
  rw [show k.onE (j.onE d) = j'.onE d from congrFun (congrArg Hom.onE hkj) d,
    pushE_of_mem p hj'E]

/-- The map of pushouts induced by an inclusion `L ⊆ L'` of terms over `D`. -/
noncomputable def pushoutFunctor (p : Hom D K) (j : Hom D L) (j' : Hom D L') (k : Hom L L')
    (hjV : Function.Injective j.onV) (hjE : Function.Injective j.onE)
    (hj'V : Function.Injective j'.onV) (hj'E : Function.Injective j'.onE)
    (hj'F : Function.Injective j'.onF) (hkj : k.comp j = j') :
    Hom (pushoutComplex p j hjV hjE) (pushoutComplex p j' hj'V hj'E) :=
  pushoutLift p j hjV hjE (pushoutInl p j' hj'V hj'E) ((pushoutMap p j' hj'V hj'E hj'F).comp k)
    (functor_hV p j j' k hj'V hj'E hj'F hkj) (functor_hE p j j' k hj'V hj'E hj'F hkj)

/-- A cell of `L` off `D` stays off `D` in a larger term `L'`. -/
theorem off_map_V {j : Hom D L} {j' : Hom D L'} {k : Hom L L'}
    (hkV : Function.Injective k.onV) (hkj : k.comp j = j') (w : OffV j) :
    ∀ d, j'.onV d ≠ k.onV w.1 := by
  intro d hd
  refine w.2 d (hkV ?_)
  rw [show k.onV (j.onV d) = j'.onV d from congrFun (congrArg Hom.onV hkj) d, hd]

theorem off_map_E {j : Hom D L} {j' : Hom D L'} {k : Hom L L'}
    (hkE : Function.Injective k.onE) (hkj : k.comp j = j') (w : OffE j) :
    ∀ d, j'.onE d ≠ k.onE w.1 := by
  intro d hd
  refine w.2 d (hkE ?_)
  rw [show k.onE (j.onE d) = j'.onE d from congrFun (congrArg Hom.onE hkj) d, hd]

theorem off_map_F {j : Hom D L} {j' : Hom D L'} {k : Hom L L'}
    (hkF : Function.Injective k.onF) (hkj : k.comp j = j') (w : OffF j) :
    ∀ d, j'.onF d ≠ k.onF w.1 := by
  intro d hd
  refine w.2 d (hkF ?_)
  rw [show k.onF (j.onF d) = j'.onF d from congrFun (congrArg Hom.onF hkj) d, hd]

/-- **The induced map of pushouts is again a subcomplex inclusion.**  If `L ⊆ L'` are two
terms over `D`, then `K ∪_p L` is a subcomplex of `K ∪_p L'`. -/
theorem sub_pushout_of_sub (p : Hom D K) (j : Hom D L) (j' : Hom D L') (k : Hom L L')
    (hjV : Function.Injective j.onV) (hjE : Function.Injective j.onE)
    (hj'V : Function.Injective j'.onV) (hj'E : Function.Injective j'.onE)
    (hj'F : Function.Injective j'.onF) (hkV : Function.Injective k.onV)
    (hkE : Function.Injective k.onE) (hkF : Function.Injective k.onF) (hkj : k.comp j = j') :
    Sub (pushoutComplex p j hjV hjE) (pushoutComplex p j' hj'V hj'E) := by
  set F := pushoutFunctor p j j' k hjV hjE hj'V hj'E hj'F hkj
  refine ⟨F, ?_, ?_, ?_⟩
  · have hinl : ∀ a : K.V, F.onV (Sum.inl a) = Sum.inl a := fun _ => rfl
    have hinr : ∀ w : OffV j, F.onV (Sum.inr w) = Sum.inr ⟨k.onV w.1, off_map_V hkV hkj w⟩ :=
      fun w => pushV_of_off p j' ⟨k.onV w.1, off_map_V hkV hkj w⟩
    rintro (a | w) (b | w') h
    · rw [hinl, hinl] at h
      exact congrArg Sum.inl (Sum.inl_injective h)
    · rw [hinl, hinr] at h
      simp at h
    · rw [hinr, hinl] at h
      simp at h
    · rw [hinr, hinr] at h
      exact congrArg Sum.inr (Subtype.ext (hkV (congrArg Subtype.val (Sum.inr_injective h))))
  · have hinl : ∀ a : K.E, F.onE (Sum.inl a) = Sum.inl a := fun _ => rfl
    have hinr : ∀ w : OffE j, F.onE (Sum.inr w) = Sum.inr ⟨k.onE w.1, off_map_E hkE hkj w⟩ :=
      fun w => pushE_of_off p j' ⟨k.onE w.1, off_map_E hkE hkj w⟩
    rintro (a | w) (b | w') h
    · rw [hinl, hinl] at h
      exact congrArg Sum.inl (Sum.inl_injective h)
    · rw [hinl, hinr] at h
      simp at h
    · rw [hinr, hinl] at h
      simp at h
    · rw [hinr, hinr] at h
      exact congrArg Sum.inr (Subtype.ext (hkE (congrArg Subtype.val (Sum.inr_injective h))))
  · have hinl : ∀ a : K.F, F.onF (Sum.inl a) = Sum.inl a := fun _ => rfl
    have hinr : ∀ w : OffF j, F.onF (Sum.inr w) = Sum.inr ⟨k.onF w.1, off_map_F hkF hkj w⟩ :=
      fun w => pushF_of_off p j' ⟨k.onF w.1, off_map_F hkF hkj w⟩
    rintro (a | w) (b | w') h
    · rw [hinl, hinl] at h
      exact congrArg Sum.inl (Sum.inl_injective h)
    · rw [hinl, hinr] at h
      simp at h
    · rw [hinr, hinl] at h
      simp at h
    · rw [hinr, hinr] at h
      exact congrArg Sum.inr (Subtype.ext (hkF (congrArg Subtype.val (Sum.inr_injective h))))

end Functor

/-! ### Connectivity -/

section Connected

/-- **The pushout of connected complexes is connected.** -/
theorem isConnected_pushoutComplex (p : Hom D K) (i : Hom D L)
    (hiV : Function.Injective i.onV) (hiE : Function.Injective i.onE)
    (hK : IsConnected K) (hL : IsConnected L) (d₀ : D.V) :
    IsConnected (pushoutComplex p i hiV hiE) := by
  set E := pushoutComplex p i hiV hiE
  set b : E.V := Sum.inl (p.onV d₀)
  have key : ∀ x : E.V, (∃ q, IsPath E.src E.tgt q x b) ∧ ∃ q, IsPath E.src E.tgt q b x := by
    rintro (a | w)
    · obtain ⟨q₁, hq₁⟩ := hK a (p.onV d₀)
      obtain ⟨q₂, hq₂⟩ := hK (p.onV d₀) a
      exact ⟨⟨_, isPath_map (src := K.src) (tgt := K.tgt) Sum.inl Sum.inl (fun _ => rfl)
          (fun _ => rfl) hq₁⟩,
        ⟨_, isPath_map (src := K.src) (tgt := K.tgt) Sum.inl Sum.inl (fun _ => rfl)
          (fun _ => rfl) hq₂⟩⟩
    · have hw : pushV p i w.1 = Sum.inr w := pushV_of_off p i w
      have hd : pushV p i (i.onV d₀) = b := pushV_of_mem p hiV d₀
      obtain ⟨q₁, hq₁⟩ := hL w.1 (i.onV d₀)
      obtain ⟨q₂, hq₂⟩ := hL (i.onV d₀) w.1
      have h₁ := isPath_map (src := L.src) (tgt := L.tgt) (pushV p i) (pushE p i)
        (pushoutComplex_src_pushE p i hiV hiE) (pushoutComplex_tgt_pushE p i hiV hiE) hq₁
      have h₂ := isPath_map (src := L.src) (tgt := L.tgt) (pushV p i) (pushE p i)
        (pushoutComplex_src_pushE p i hiV hiE) (pushoutComplex_tgt_pushE p i hiV hiE) hq₂
      rw [hw, hd] at h₁
      rw [hw, hd] at h₂
      exact ⟨⟨_, h₁⟩, ⟨_, h₂⟩⟩
  intro x y
  obtain ⟨⟨q₁, hq₁⟩, -⟩ := key x
  obtain ⟨-, ⟨q₂, hq₂⟩⟩ := key y
  exact ⟨q₁ ++ q₂, hq₁.append hq₂⟩

end Connected

end Comb
end FiniteChains
