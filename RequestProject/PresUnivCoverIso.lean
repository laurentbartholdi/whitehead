import RequestProject.CombPi2
import RequestProject.CombPresPi1
import RequestProject.UnivCoverIncl

/-!
# The two models of the universal cover of a presentation complex agree

Two universal covers of the presentation complex `K = presComplex ρ` occur in this
development.

* The *homotopy-theoretic* one, `FiniteChains.Comb.uCover (presComplex ρ) PUnit.unit`, built in
  `RequestProject/CombUniversalCover.lean` out of homotopy classes of edge paths.  It is the one
  that defines `π₂` and the condition "a cellular map is zero on `π₂`"
  (`FiniteChains.Comb.Pi2`, `FiniteChains.Comb.ZeroPi2`) in the interface `combData` of
  Theorem A.
* The *algebraic* one, `FiniteChains.Comb.univCover ρ`, built in
  `RequestProject/CoverComplex.lean` out of the group `G = F/R`: vertices `G`, edges `G × α`,
  two-cells `G × J`.  It is the one whose chain complex is the Fox complex, and therefore the
  one all of Section 2 speaks about.

This file constructs an isomorphism between them and deduces that the two readings of
condition (1) of Theorem A coincide.
-/

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains
namespace Comb

universe u

variable {α J : Type u} [DecidableEq α] (ρ : J → FreeGroup α)

/-! ### The vertices: homotopy classes of edge paths are elements of `G` -/

/-- The class in `G = F/R` of the word spelled by (any representative of) a vertex of the
homotopy-theoretic universal cover. -/
def uvWord : UV (presComplex ρ) PUnit.unit → PresGroup ρ :=
  Quotient.lift (fun p : PathFrom (presComplex ρ) PUnit.unit => presWord ρ p.1)
    (fun _ _ h => presWord_htpy ρ h)

@[simp] theorem uvWord_mk (p : PathFrom (presComplex ρ) PUnit.unit) :
    uvWord ρ (UV.mk p) = presWord ρ p.1 := rfl

/-- Every list of oriented edges is a path of the presentation complex. -/
def presPath (l : List (α × Bool)) : PathFrom (presComplex ρ) PUnit.unit :=
  ⟨l, isPath_of_subsingleton _ _ _ _ _⟩

theorem uvWord_surjective : Function.Surjective (uvWord ρ) := by
  intro g
  induction g using QuotientGroup.induction_on with
  | H w =>
      refine ⟨UV.mk (presPath ρ w.toWord), ?_⟩
      show presWord ρ w.toWord = _
      unfold presWord
      rw [FreeGroup.mk_toWord]

theorem uvWord_injective : Function.Injective (uvWord ρ) := by
  intro c d h
  induction c using UV.ind with
  | h p =>
    induction d using UV.ind with
    | h q =>
      have hl : pi1ToPres ρ (Pi1.mk ⟨p.1, isPath_of_subsingleton _ _ _ _ _⟩)
          = pi1ToPres ρ (Pi1.mk ⟨q.1, isPath_of_subsingleton _ _ _ _ _⟩) := h
      have hpi : (Pi1.mk ⟨p.1, isPath_of_subsingleton _ _ _ _ _⟩ :
            Pi1 (presComplex ρ) PUnit.unit)
          = Pi1.mk ⟨q.1, isPath_of_subsingleton _ _ _ _ _⟩ :=
        (pi1PresEquiv ρ).injective hl
      exact Quotient.sound (Quotient.exact hpi)

theorem uvWord_bijective : Function.Bijective (uvWord ρ) :=
  ⟨uvWord_injective ρ, uvWord_surjective ρ⟩

/-- The identification of the vertices of the two universal covers. -/
noncomputable def uvEquiv : UV (presComplex ρ) PUnit.unit ≃ PresGroup ρ :=
  Equiv.ofBijective _ (uvWord_bijective ρ)

@[simp] theorem uvEquiv_apply (c : UV (presComplex ρ) PUnit.unit) :
    uvEquiv ρ c = uvWord ρ c := rfl

/-! ### Extending a class by an edge multiplies its word by a generator -/

theorem uvWord_extend_true (i : α) (c : UV (presComplex ρ) PUnit.unit) :
    uvWord ρ (extend (i, true) c) = uvWord ρ c * qof (relSub ρ) i := by
  induction c using UV.ind with
  | h p =>
      have h : endpt (presComplex ρ) PUnit.unit p.1
          = germSrc (presComplex ρ).src (presComplex ρ).tgt (i, true) := Subsingleton.elim _ _
      rw [extend_mk, uvWord_mk, extendP_pos h, uvWord_mk, presWord_append]
      rfl

theorem uvWord_extend_false (i : α) (c : UV (presComplex ρ) PUnit.unit) :
    uvWord ρ (extend (i, false) c) = uvWord ρ c * (qof (relSub ρ) i)⁻¹ := by
  induction c using UV.ind with
  | h p =>
      have h : endpt (presComplex ρ) PUnit.unit p.1
          = germSrc (presComplex ρ).src (presComplex ρ).tgt (i, false) := Subsingleton.elim _ _
      rw [extend_mk, uvWord_mk, extendP_pos h, uvWord_mk, presWord_append]
      congr 1

/-! ### The isomorphism of complexes -/

/-- The map of edges: an edge of the homotopy-theoretic cover is a class `c` together with a
generator, and it goes to the edge `(uvWord c, i)` of the algebraic cover. -/
def uvEdge (E : UE (presComplex ρ) PUnit.unit) : (univCover ρ).E := (uvWord ρ E.1.1, E.1.2)

/-- The map of two-cells. -/
def uvFace (F : UF (presComplex ρ) PUnit.unit) : (univCover ρ).F := (uvWord ρ F.1.1, F.1.2)

/-- **The lift of a word in the two models agree.** -/
theorem map_uLiftPath_pres : ∀ (L : List (α × Bool)) (c : UV (presComplex ρ) PUnit.unit),
    (uLiftPath L c).map (fun Eb => (uvEdge ρ Eb.1, Eb.2)) = liftPath L (uvWord ρ c) := by
  intro L
  induction L with
  | nil => intro _; rfl
  | cons eb t ih =>
      intro c
      obtain ⟨i, b⟩ := eb
      have h : endV c = germSrc (presComplex ρ).src (presComplex ρ).tgt (i, b) :=
        Subsingleton.elim _ _
      rw [uLiftPath_cons h]
      cases b
      · rw [liftPath_cons_false, List.map_cons, ih (extend (i, false) c),
          uvWord_extend_false]
        have hhead : (uvEdge ρ (liftGerm c (i, false) h).1, (liftGerm c (i, false) h).2)
            = (((uvWord ρ c * (qof (relSub ρ) i)⁻¹, i) : (univCover ρ).E), false) := by
          show ((uvWord ρ (extend (i, false) c), i), false) = _
          rw [uvWord_extend_false]
        rw [hhead]
      · rw [liftPath_cons_true, List.map_cons, ih (extend (i, true) c), uvWord_extend_true]
        rfl

/-- **The homotopy-theoretic universal cover of a presentation complex is the algebraic
one.**  The cellular map sending the class of a path to the element of `G = F/R` it spells. -/
noncomputable def presUnivHom : Hom (uCover (presComplex ρ) PUnit.unit) (univCover ρ) where
  onV := uvWord ρ
  onE := uvEdge ρ
  onF := uvFace ρ
  src_onE _ := rfl
  tgt_onE E := by
    show uvWord ρ E.1.1 * qof (relSub ρ) E.1.2 = uvWord ρ (extend (E.1.2, true) E.1.1)
    rw [uvWord_extend_true]
  base_onF _ := rfl
  att_onF F := by
    show liftPath (FreeGroup.toWord (ρ F.1.2)) (uvWord ρ F.1.1)
      = (uLiftPath ((presComplex ρ).att F.1.2) F.1.1).map (fun Eb => (uvEdge ρ Eb.1, Eb.2))
    rw [map_uLiftPath_pres]

/-! ### The cellular map is an isomorphism -/

theorem uvEdge_bijective : Function.Bijective (uvEdge ρ) := by
  constructor
  · rintro ⟨⟨c, i⟩, hc⟩ ⟨⟨d, i'⟩, hd⟩ hEq
    have h1 : uvWord ρ c = uvWord ρ d := congrArg Prod.fst hEq
    have h2 : i = i' := congrArg Prod.snd hEq
    subst h2
    exact Subtype.ext (Prod.ext (uvWord_injective ρ h1) rfl)
  · rintro ⟨q, i⟩
    obtain ⟨c, hc⟩ := uvWord_surjective ρ q
    exact ⟨⟨(c, i), Subsingleton.elim _ _⟩, by simp [uvEdge, hc]⟩

theorem uvFace_bijective : Function.Bijective (uvFace ρ) := by
  constructor
  · rintro ⟨⟨c, j⟩, hc⟩ ⟨⟨d, j'⟩, hd⟩ hEq
    have h1 : uvWord ρ c = uvWord ρ d := congrArg Prod.fst hEq
    have h2 : j = j' := congrArg Prod.snd hEq
    subst h2
    exact Subtype.ext (Prod.ext (uvWord_injective ρ h1) rfl)
  · rintro ⟨q, j⟩
    obtain ⟨c, hc⟩ := uvWord_surjective ρ q
    exact ⟨⟨(c, j), Subsingleton.elim _ _⟩, by simp [uvFace, hc]⟩

/-- The two-chains of the two models are identified. -/
theorem chain2_presUnivHom_surjective :
    Function.Surjective (chain2 (presUnivHom ρ)) := by
  intro v
  classical
  obtain ⟨u, hu⟩ := Finsupp.mapDomain_surjective (M := ℤ) (uvFace_bijective ρ).2 v
  exact ⟨u, hu⟩

/-- **A two-chain of the homotopy-theoretic universal cover is a cycle exactly when its image
in the algebraic model is.** -/
theorem mem_pi2_iff_bdry2_eq_zero (u : (uCover (presComplex ρ) PUnit.unit).F →₀ ℤ) :
    u ∈ Pi2 (presComplex ρ) PUnit.unit ↔ bdry2 (univCover ρ) (chain2 (presUnivHom ρ) u) = 0 := by
  rw [bdry2_chain2]
  constructor
  · intro hu
    have : bdry2 (uCover (presComplex ρ) PUnit.unit) u = 0 := hu
    rw [this, map_zero]
  · intro hu
    show bdry2 (uCover (presComplex ρ) PUnit.unit) u = 0
    have hinj : Function.Injective (chain1 (presUnivHom ρ)) :=
      Finsupp.mapDomain_injective (uvEdge_bijective ρ).1
    exact hinj (by rw [hu, map_zero])

@[simp] theorem presUnivHom_onV : (presUnivHom ρ).onV = uvWord ρ := rfl
@[simp] theorem presUnivHom_onE : (presUnivHom ρ).onE = uvEdge ρ := rfl
@[simp] theorem presUnivHom_onF : (presUnivHom ρ).onF = uvFace ρ := rfl

/-! ### Naturality in an inclusion of presentations -/

section Incl

variable {β K : Type u} [DecidableEq β] {σ : K → FreeGroup β}
variable (f : α → β) (hf : Function.Injective f) (g : J → K)
  (hg : ∀ j, σ (g j) = FreeGroup.map f (ρ j))

/-- The word spelled by the image of a path is the image of the word it spells. -/
theorem uvWord_univLiftV (c : UV (presComplex ρ) PUnit.unit) :
    uvWord σ (univLiftV PUnit.unit (presInclHom f hf ρ σ g hg) c)
      = presInclGroupHom f ρ σ g hg (uvWord ρ c) := by
  induction c using UV.ind with
  | h p =>
      show presWord σ (mapPath (presInclHom f hf ρ σ g hg) p.1)
        = presInclGroupHom f ρ σ g hg (presWord ρ p.1)
      rw [show presWord ρ p.1 = QuotientGroup.mk (FreeGroup.mk p.1) from rfl,
        presInclGroupHom_mk]
      rfl

/-- The identification of the two models is natural: it carries the lift of an inclusion of
presentation complexes to the universal covers to the algebraic one. -/
theorem uvFace_univLiftF (F : UF (presComplex ρ) PUnit.unit) :
    uvFace σ (univLiftF (x₀ := PUnit.unit) (presInclHom f hf ρ σ g hg) F)
      = (univCoverInclHom f hf ρ σ g hg).onF (uvFace ρ F) := by
  show ((uvWord σ (univLiftV PUnit.unit (presInclHom f hf ρ σ g hg) F.1.1), g F.1.2) :
      (univCover σ).F) = Prod.map (presInclGroupHom f ρ σ g hg) g (uvWord ρ F.1.1, F.1.2)
  rw [uvWord_univLiftV]
  rfl

/-- The two lifts agree on two-chains. -/
theorem chain2_presUnivHom_square (u : (uCover (presComplex ρ) PUnit.unit).F →₀ ℤ) :
    chain2 (presUnivHom σ)
        (chain2 (univLift (presComplex ρ) (presInclHom f hf ρ σ g hg) PUnit.unit) u)
      = chain2 (univCoverInclHom f hf ρ σ g hg) (chain2 (presUnivHom ρ) u) := by
  classical
  show Finsupp.mapDomain (uvFace σ)
      (Finsupp.mapDomain ((univLift (presComplex ρ) (presInclHom f hf ρ σ g hg) PUnit.unit).onF) u)
    = Finsupp.mapDomain (univCoverInclHom f hf ρ σ g hg).onF
      (Finsupp.mapDomain (uvFace ρ) u)
  rw [← Finsupp.mapDomain_comp, ← Finsupp.mapDomain_comp]
  refine congrArg (fun h => Finsupp.mapDomain h u) ?_
  funext F
  exact uvFace_univLiftF ρ f hf g hg F

/-- **The topological and the algebraic readings of "the inclusion is zero on `π₂`" agree.**
On the left the definition used by the interface of Theorem A (the induced map of two-chains of
the homotopy-theoretic universal covers kills every two-cycle); on the right the condition
carried by `FiniteChains.PresChain`, stated in the algebraic model whose chain complex is the
Fox complex. -/
theorem zeroPi2_presInclHom_iff :
    ZeroPi2 (presInclHom f hf ρ σ g hg) ↔
      ∀ v : (univCover ρ).F →₀ ℤ, bdry2 (univCover ρ) v = 0 →
        chain2 (univCoverInclHom f hf ρ σ g hg) v = 0 := by
  constructor
  · intro hzero v hv
    obtain ⟨u, rfl⟩ := chain2_presUnivHom_surjective ρ v
    have hu : u ∈ Pi2 (presComplex ρ) PUnit.unit := (mem_pi2_iff_bdry2_eq_zero ρ u).2 hv
    rw [← chain2_presUnivHom_square ρ f hf g hg u, hzero PUnit.unit u hu, map_zero]
  · intro hzero x₀ u hu
    have hinj : Function.Injective (chain2 (presUnivHom σ)) :=
      Finsupp.mapDomain_injective (uvFace_bijective σ).1
    refine hinj ?_
    rw [map_zero, chain2_presUnivHom_square ρ f hf g hg u]
    exact hzero _ ((mem_pi2_iff_bdry2_eq_zero ρ u).1 hu)

/-! ### The same for the fundamental group -/

/-- The word spelled by the image of an edge path. -/
theorem presWord_mapPath (l : List (α × Bool)) :
    presWord σ (mapPath (presInclHom f hf ρ σ g hg) l)
      = presInclGroupHom f ρ σ g hg (presWord ρ l) := by
  rw [show presWord ρ l = QuotientGroup.mk (FreeGroup.mk l) from rfl, presInclGroupHom_mk]
  rfl

/-- An edge loop of a presentation complex spelling the trivial element of the presented group
is null-homotopic. -/
theorem htpy_of_presWord_eq_one {l : List (β × Bool)} (h : presWord σ l = 1) :
    Htpy (presComplex σ) PUnit.unit PUnit.unit l [] := by
  have hone :
      (Pi1.mk ⟨l, isPath_of_subsingleton _ _ _ _ _⟩ : Pi1 (presComplex σ) PUnit.unit) = 1 := by
    refine (pi1PresEquiv σ).injective ?_
    rw [map_one]
    exact h
  exact Quotient.exact hone

/-- **The topological and the algebraic readings of "the inclusion kills `π₁`" agree.**  The
inclusion of presentation complexes is trivial on fundamental groups exactly when the induced
homomorphism of presented groups is trivial. -/
theorem pi1Trivial_presInclHom_iff :
    Pi1Trivial (presInclHom f hf ρ σ g hg) ↔
      ∀ w : PresGroup ρ, presInclGroupHom f ρ σ g hg w = 1 := by
  constructor
  · intro hpi w
    induction w using QuotientGroup.induction_on with
    | H x =>
        have hht := hpi PUnit.unit x.toWord (isPath_of_subsingleton _ _ _ _ _)
        have hw := presWord_htpy σ hht
        rw [presWord_mapPath, presWord_nil] at hw
        rw [← hw]
        congr 1
        show (QuotientGroup.mk x : PresGroup ρ) = QuotientGroup.mk (FreeGroup.mk x.toWord)
        rw [FreeGroup.mk_toWord]
  · intro hw _ p _
    refine htpy_of_presWord_eq_one (σ := σ) ?_
    rw [presWord_mapPath]
    exact hw _

end Incl

end Comb
end FiniteChains
