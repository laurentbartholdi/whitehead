import RequestProject.Pi2GenerationDescent

/-!
# The copies of `L̃` cover the universal cover of the pushout

Step 2 of the proof of Proposition 3.11 computes `π₂(E)` for the cellular pushout
`E = K ∪_p L` from the short exact sequence of chain complexes

  `0 → ⊕_Λ C_*(D) → (⊕_{Λ/H} C_*(D)) ⊕ (⊕_{Λ/J} C_*(L̃)) → C_*(Ẽ) → 0`.

This file proves the **surjectivity of the right-hand map in degree two** (and in the two
lower degrees) in the combinatorial model, from scratch:

* `FiniteChains.Comb.pi1Trivial_of_simplyConnected` — a cellular map out of a simply connected
  complex kills `π₁`;
* `FiniteChains.Comb.exists_lift_univCover` — **every copy of `L̃` is available**: for a
  cellular map `ι : L → E` and a vertex `c` of `Ẽ` over `ι l₀` there is a lift
  `φ : L̃(l₀) → Ẽ(x₀)` of `ι` to the universal covers which sends the base vertex of `L̃(l₀)`
  to `c`;
* `FiniteChains.Comb.exists_lift_onF_eq` — consequently, if `ι` is onto on two-cells, **every
  two-cell of `Ẽ` lies in a copy of `L̃`**; likewise for edges and vertices;
* `FiniteChains.Comb.span_chainsFromSub_eq_top` — hence the chains of `Ẽ` in degree two are
  spanned by the chains coming from the copies of `L̃`
  (`FiniteChains.Comb.ChainsFromSub`, the degree-two part of the middle term above);
* `FiniteChains.Comb.surjective_onF_of_isCovering`, `surjective_onE_of_isCovering` — a
  combinatorial covering is onto on cells, hence `FiniteChains.Comb.surjective_pushF` etc.:
  the map `L → K ∪_p L` of Proposition 3.11 is onto on cells of every dimension;
* `FiniteChains.Comb.span_chainsFromSub_pushoutMap_eq_top` — the resulting statement for the
  pushout of Proposition 3.11.
-/

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains
namespace Comb

universe u

/-! ### Maps out of a simply connected complex -/

/-- A cellular map out of a simply connected complex kills `π₁`. -/
theorem pi1Trivial_of_simplyConnected {X Y : Complex2.{u}} (hX : SimplyConnected X)
    (h : Hom X Y) : Pi1Trivial h := by
  intro a p hp
  simpa using mapPath_htpy h (hX a p hp)

/-! ### Lifting a cellular map to the universal covers, with a prescribed base image -/

section Lifts

variable {L E : Complex2.{u}}

/-- **Every copy of `L̃` inside `Ẽ` is available.**  Given a cellular map `ι : L → E`, a
vertex `l₀` of `L` and a vertex `c` of the universal cover of `E` lying over `ι l₀`, there is
a lift of `ι` to the universal covers taking the base vertex of `L̃(l₀)` to `c`.  (The
universal cover of `L` is simply connected, so the composite `L̃ → L → E` lifts; a change of
base vertex moves the image of the base point to `c`.) -/
theorem exists_lift_univCover (ι : Hom L E) {x₀ : E.V} (l₀ : L.V) (c : UV E x₀)
    (hc : endV c = ι.onV l₀) :
    ∃ φ : Hom (uCover L l₀) (uCover E x₀),
      (∀ v, endV (φ.onV v) = ι.onV (endV v)) ∧
      (∀ e : UE L l₀, ((φ.onE e).1).2 = ι.onE (e.1.2)) ∧
      (∀ f : UF L l₀, ((φ.onF f).1).2 = ι.onF (f.1.2)) ∧
      φ.onV (UV.base L l₀) = c := by
  classical
  set f : Hom (uCover L l₀) E := ι.comp (univProj L l₀)
  have htriv : Pi1Trivial f := pi1Trivial_of_simplyConnected simplyConnected_univCover f
  set psi : Hom (uCover L l₀) (uCover E (ι.onV l₀)) :=
    liftHom (f := f) (d₀ := UV.base L l₀) isConnected_univCover htriv
  -- a path representing `c`
  obtain ⟨tp, htp⟩ := Quotient.exists_rep c
  have hend : endpt E x₀ tp.1 = ι.onV l₀ := by rw [← hc, ← htp]; rfl
  have hq : IsPath E.src E.tgt tp.1 x₀ (ι.onV l₀) := by
    have h := tp.2
    rwa [hend] at h
  refine ⟨(shiftHom hq).comp psi, ?_, ?_, ?_, ?_⟩
  · intro v
    show endV (shiftV hq (psi.onV v)) = ι.onV (endV v)
    rw [endV_shiftV]
    exact univProj_liftHom_onV (f := f) (d₀ := UV.base L l₀) isConnected_univCover htriv v
  · intro e
    show ((shiftE hq (psi.onE e)).1).2 = ι.onE (e.1.2)
    exact univProj_liftHom_onE (f := f) (d₀ := UV.base L l₀) isConnected_univCover htriv e
  · intro g
    show ((shiftF hq (psi.onF g)).1).2 = ι.onF (g.1.2)
    exact univProj_liftHom_onF (f := f) (d₀ := UV.base L l₀) isConnected_univCover htriv g
  · show shiftV hq (psi.onV (UV.base L l₀)) = c
    have h1 : psi.onV (UV.base L l₀) = UV.base E (ι.onV l₀) :=
      liftHom_base (f := f) (d₀ := UV.base L l₀) isConnected_univCover htriv
    rw [h1, shiftV_base, ← htp]
    exact congrArg UV.mk (Subtype.ext rfl)

/-- **Every two-cell of `Ẽ` lies in a copy of `L̃`**, as soon as `ι : L → E` is onto on
two-cells. -/
theorem exists_lift_onF_eq (ι : Hom L E) (hsurj : Function.Surjective ι.onF) {x₀ : E.V}
    (Φ : UF E x₀) :
    ∃ (l₀ : L.V) (φ : Hom (uCover L l₀) (uCover E x₀)),
      (∀ v, endV (φ.onV v) = ι.onV (endV v)) ∧
      (∀ e : UE L l₀, ((φ.onE e).1).2 = ι.onE (e.1.2)) ∧
      (∀ f : UF L l₀, ((φ.onF f).1).2 = ι.onF (f.1.2)) ∧
      ∃ F : UF L l₀, φ.onF F = Φ := by
  obtain ⟨fL, hfL⟩ := hsurj Φ.1.2
  refine ⟨L.base fL, ?_⟩
  have hc : endV Φ.1.1 = ι.onV (L.base fL) := by
    rw [Φ.2, ← hfL, ι.base_onF]
  obtain ⟨φ, hV, hE, hF, hbase⟩ := exists_lift_univCover ι (L.base fL) Φ.1.1 hc
  refine ⟨φ, hV, hE, hF, ⟨(UV.base L (L.base fL), fL), rfl⟩, ?_⟩
  refine Subtype.ext (Prod.ext ?_ ?_)
  · have := φ.base_onF ⟨(UV.base L (L.base fL), fL), rfl⟩
    show (φ.onF ⟨(UV.base L (L.base fL), fL), rfl⟩).1.1 = Φ.1.1
    rw [show (φ.onF ⟨(UV.base L (L.base fL), fL), rfl⟩).1.1
        = (uCover E x₀).base (φ.onF ⟨(UV.base L (L.base fL), fL), rfl⟩) from rfl, this]
    exact hbase
  · show (φ.onF ⟨(UV.base L (L.base fL), fL), rfl⟩).1.2 = Φ.1.2
    rw [hF ⟨(UV.base L (L.base fL), fL), rfl⟩]
    exact hfL

/-- **Every edge of `Ẽ` lies in a copy of `L̃`**, as soon as `ι : L → E` is onto on edges. -/
theorem exists_lift_onE_eq (ι : Hom L E) (hsurj : Function.Surjective ι.onE) {x₀ : E.V}
    (Φ : UE E x₀) :
    ∃ (l₀ : L.V) (φ : Hom (uCover L l₀) (uCover E x₀)),
      (∀ v, endV (φ.onV v) = ι.onV (endV v)) ∧
      (∀ e : UE L l₀, ((φ.onE e).1).2 = ι.onE (e.1.2)) ∧
      (∀ f : UF L l₀, ((φ.onF f).1).2 = ι.onF (f.1.2)) ∧
      ∃ e : UE L l₀, φ.onE e = Φ := by
  obtain ⟨eL, heL⟩ := hsurj Φ.1.2
  refine ⟨L.src eL, ?_⟩
  have hc : endV Φ.1.1 = ι.onV (L.src eL) := by
    rw [Φ.2, ← heL, ι.src_onE]
  obtain ⟨φ, hV, hE, hF, hbase⟩ := exists_lift_univCover ι (L.src eL) Φ.1.1 hc
  refine ⟨φ, hV, hE, hF, ⟨(UV.base L (L.src eL), eL), rfl⟩, ?_⟩
  refine Subtype.ext (Prod.ext ?_ ?_)
  · have := φ.src_onE ⟨(UV.base L (L.src eL), eL), rfl⟩
    show (φ.onE ⟨(UV.base L (L.src eL), eL), rfl⟩).1.1 = Φ.1.1
    rw [show (φ.onE ⟨(UV.base L (L.src eL), eL), rfl⟩).1.1
        = (uCover E x₀).src (φ.onE ⟨(UV.base L (L.src eL), eL), rfl⟩) from rfl, this]
    exact hbase
  · show (φ.onE ⟨(UV.base L (L.src eL), eL), rfl⟩).1.2 = Φ.1.2
    rw [hE ⟨(UV.base L (L.src eL), eL), rfl⟩]
    exact heL

/-- **Every vertex of `Ẽ` lies in a copy of `L̃`**, as soon as `ι : L → E` is onto on
vertices. -/
theorem exists_lift_onV_eq (ι : Hom L E) (hsurj : Function.Surjective ι.onV) {x₀ : E.V}
    (c : UV E x₀) :
    ∃ (l₀ : L.V) (φ : Hom (uCover L l₀) (uCover E x₀)),
      (∀ v, endV (φ.onV v) = ι.onV (endV v)) ∧
      (∀ e : UE L l₀, ((φ.onE e).1).2 = ι.onE (e.1.2)) ∧
      (∀ f : UF L l₀, ((φ.onF f).1).2 = ι.onF (f.1.2)) ∧
      ∃ v : UV L l₀, φ.onV v = c := by
  obtain ⟨l₀, hl₀⟩ := hsurj (endV c)
  obtain ⟨φ, hV, hE, hF, hbase⟩ := exists_lift_univCover ι l₀ c hl₀.symm
  exact ⟨l₀, φ, hV, hE, hF, UV.base L l₀, hbase⟩

/-! ### The degree-two chains coming from the copies -/

/-- The two-chains of `Ẽ` **coming from `L`** along `ι : L → E`: the images of the two-chains
of the universal cover of `L` under all lifts of `ι`.  This is the degree-two part of the
term `⊕_{Λ/J} C_*(L̃)` of the exact sequence of step 2 of Proposition 3.11; the spherical
classes of `FiniteChains.Comb.Pi2FromSub` are the elements coming from two-*cycles*. -/
def ChainsFromSub (ι : Hom L E) (x₀ : E.V) : Set ((uCover E x₀).F →₀ ℤ) :=
  {d | ∃ (l₀ : L.V) (φ : Hom (uCover L l₀) (uCover E x₀)),
      (∀ v, endV (φ.onV v) = ι.onV (endV v)) ∧
      (∀ e : UE L l₀, ((φ.onE e).1).2 = ι.onE (e.1.2)) ∧
      (∀ f : UF L l₀, ((φ.onF f).1).2 = ι.onF (f.1.2)) ∧
      ∃ w : (uCover L l₀).F →₀ ℤ, d = chain2 φ w}

theorem pi2FromSub_subset_chainsFromSub (ι : Hom L E) (x₀ : E.V) :
    Pi2FromSub ι x₀ ⊆ ChainsFromSub ι x₀ := by
  rintro d ⟨l₀, φ, hV, hE, hF, z, -, rfl⟩
  exact ⟨l₀, φ, hV, hE, hF, z, rfl⟩

/-- The classes coming from a subcomplex really are spherical classes: the image of a
two-cycle of a copy of `L̃` is a two-cycle of `Ẽ`. -/
theorem pi2FromSub_subset_pi2 (ι : Hom L E) (x₀ : E.V) :
    Pi2FromSub ι x₀ ⊆ (Pi2 E x₀ : Set ((uCover E x₀).F →₀ ℤ)) := by
  rintro d ⟨l₀, φ, -, -, -, z, hz, rfl⟩
  have h : bdry2 (uCover L l₀) z = 0 := hz
  show bdry2 (uCover E x₀) (chain2 φ z) = 0
  rw [bdry2_chain2 φ z, h, map_zero]

/-- **The two-chains of `Ẽ` are spanned by the chains coming from the copies of `L̃`.**  This
is the surjectivity, in degree two, of the right-hand map of the exact sequence of step 2 of
Proposition 3.11. -/
theorem span_chainsFromSub_eq_top (ι : Hom L E) (hsurj : Function.Surjective ι.onF)
    (x₀ : E.V) : Submodule.span ℤ (ChainsFromSub ι x₀) = ⊤ := by
  classical
  refine Submodule.eq_top_iff'.2 fun u => ?_
  refine Finsupp.induction u (Submodule.zero_mem _) ?_
  intro Φ a v _ _ hv
  refine Submodule.add_mem _ ?_ hv
  obtain ⟨l₀, φ, hV, hE, hF, F, hFΦ⟩ := exists_lift_onF_eq ι hsurj Φ
  refine Submodule.subset_span ⟨l₀, φ, hV, hE, hF, Finsupp.single F a, ?_⟩
  show Finsupp.single Φ a = Finsupp.mapDomain φ.onF (Finsupp.single F a)
  rw [Finsupp.mapDomain_single, hFΦ]

end Lifts

/-! ### Coverings are onto on cells -/

section Covering

variable {D K : Complex2.{u}} {p : Hom D K}

/-- A combinatorial covering is onto on two-cells. -/
theorem surjective_onF_of_isCovering (hp : IsCovering p) : Function.Surjective p.onF := by
  intro g
  obtain ⟨a, ha⟩ := hp.surjV (K.base g)
  obtain ⟨d, hd⟩ := hp.cell.2 ⟨(g, a), ha.symm⟩
  exact ⟨d, congrArg (fun z => (z.1).1) hd⟩

/-- A combinatorial covering is onto on edges. -/
theorem surjective_onE_of_isCovering (hp : IsCovering p) : Function.Surjective p.onE := by
  intro e
  obtain ⟨a, ha⟩ := hp.surjV (K.src e)
  obtain ⟨g, hg⟩ := (hp.germ a).2 ⟨(e, true), ha.symm⟩
  exact ⟨g.1.1, congrArg (fun z => (z.1).1) hg⟩

end Covering

/-! ### The map `L → K ∪_p L` of Proposition 3.11 is onto on cells -/

section Pushout

variable {D K L : Complex2.{u}} (p : Hom D K) (i : Hom D L)
  (hiV : Function.Injective i.onV) (hiE : Function.Injective i.onE)
  (hiF : Function.Injective i.onF)

include hiF in
/-- The map `L → K ∪_p L` is onto on two-cells as soon as `p` is. -/
theorem surjective_pushF (hp : Function.Surjective p.onF) :
    Function.Surjective (pushF p i) := by
  rintro (k | w)
  · obtain ⟨d, rfl⟩ := hp k
    exact ⟨i.onF d, pushF_of_mem p hiF d⟩
  · exact ⟨w.1, pushF_of_off p i w⟩

include hiE in
/-- The map `L → K ∪_p L` is onto on edges as soon as `p` is. -/
theorem surjective_pushE (hp : Function.Surjective p.onE) :
    Function.Surjective (pushE p i) := by
  rintro (k | w)
  · obtain ⟨d, rfl⟩ := hp k
    exact ⟨i.onE d, pushE_of_mem p hiE d⟩
  · exact ⟨w.1, pushE_of_off p i w⟩

include hiV in
/-- The map `L → K ∪_p L` is onto on vertices as soon as `p` is. -/
theorem surjective_pushV (hp : Function.Surjective p.onV) :
    Function.Surjective (pushV p i) := by
  rintro (k | w)
  · obtain ⟨d, rfl⟩ := hp k
    exact ⟨i.onV d, pushV_of_mem p hiV d⟩
  · exact ⟨w.1, pushV_of_off p i w⟩

/-- **The two-chains of the universal cover of the pushout `E = K ∪_p L` are spanned by the
chains coming from the copies of `L̃`.**  This is the degree-two surjectivity used in step 2
of the proof of Proposition 3.11; `p : D → K` is the covering of the proposition. -/
theorem span_chainsFromSub_pushoutMap_eq_top (hcov : IsCovering p)
    (x₀ : (pushoutComplex p i hiV hiE).V) :
    Submodule.span ℤ (ChainsFromSub (pushoutMap p i hiV hiE hiF) x₀) = ⊤ :=
  span_chainsFromSub_eq_top _ (surjective_pushF p i hiF (surjective_onF_of_isCovering hcov)) x₀

end Pushout

end Comb
end FiniteChains
