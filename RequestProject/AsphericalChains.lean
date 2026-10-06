import RequestProject.Pi2ExtensionInjective
import RequestProject.MapChainDescent
import RequestProject.PresUnivCoverIso
import RequestProject.UniversalCoverPi2
import RequestProject.PresentationConsistency
import RequestProject.TorsionFreeGroupRing
import RequestProject.GenerationIterate
import RequestProject.Pi2ExtensionExample

/-!
# Strictly increasing chains over an aspherical presentation complex

Condition (1) of Theorem A asks for **strictly increasing** chains
`K = E₀ ⊊ E₁ ⊊ ⋯ ⊊ Eₙ` of finite two-complexes whose inclusions are zero on `π₂`.  This
file proves condition (1), for every length and with no unproved hypothesis, for the
presentation complex of a finite presentation with vanishing `π₂` — that is, one with no
nonzero Fox cycles.

The chain is obtained by adjoining cancelling generator–relator pairs `⟨…, z | …, z⟩`.  Such a
Tietze extension does not change the fundamental group, and it creates no new elements of
`π₂`; so every stage again has vanishing `π₂` and every inclusion is zero on `π₂` for the
trivial reason that its source has no spherical classes at all.  The point of the
construction is that the stages *grow*: each step adds one edge and one two-cell.

The same padding works over any complex which admits **one** strictly larger finite
aspherical extension — the inclusion into an aspherical complex is automatically zero on
`π₂` — so such a complex also satisfies condition (1), and therefore, by the implication
`(1) ⇒ (2)` proved in this project, has a connected acyclic regular cover.

* `FiniteChains.Aspherical` — the presentation has no nonzero Fox cycle;
* `FiniteChains.aspherical_iff_pi2_eq_zero` — this is the vanishing of `π₂` of the
  presentation complex in the homotopy-theoretic model;
* `FiniteChains.aspherical_cancelExt` — a cancelling pair preserves asphericity (the induced
  map of fundamental groups is proved bijective);
* `FiniteChains.extStrictTopChain`, `FiniteChains.hasMapChains_of_asphericalExtension`,
  `FiniteChains.hasAcyclicRegularCover_of_asphericalExtension` — condition (1), and hence
  condition (2), for a complex with one strictly larger finite aspherical extension;
* `FiniteChains.hasMapChains_of_aspherical`, `FiniteChains.theoremA_maps_of_aspherical` —
  **Theorem A, unconditionally, for the complex of a finite aspherical presentation**, with
  condition (1) in its faithful, map-carrying form.
-/

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains

open MonoidAlgebra

universe u

variable {α J : Type u}

/-! ### Aspherical presentations -/

/-- **An aspherical presentation**: its presentation complex has no spherical classes, i.e.
the only Fox cycle is zero.  (By `FiniteChains.Comb.univCover_bdry2_eq_zero_iff` this says
that the universal cover of the presentation complex has no two-cycles.) -/
def Aspherical [DecidableEq α] [Fintype J] (ρ : J → FreeGroup α) : Prop :=
  ∀ v : J → MonoidAlgebra ℤ (PresGroup ρ), IsFoxCycle ρ v → v = 0

/-! ### Adjoining a cancelling generator–relator pair -/

/-- The presentation obtained by adjoining one new generator `z` together with the relator
`z`. -/
def cancelExt (ρ : J → FreeGroup α) : Option J → FreeGroup (Option α) :=
  extRel ρ (tietzeWord (1 : FreeGroup α))

theorem cancelExt_none (ρ : J → FreeGroup α) :
    cancelExt ρ none = FreeGroup.of (none : Option α) := by
  show tietzeWord (1 : FreeGroup α) = _
  rw [tietzeWord, map_one, inv_one, mul_one]

/-- The class of the new generator is trivial in the enlarged group. -/
theorem mk_of_none_eq_one (ρ : J → FreeGroup α) :
    (QuotientGroup.mk (FreeGroup.of (none : Option α)) :
      PresGroup (extRel ρ (tietzeWord (1 : FreeGroup α)))) = 1 := by
  refine (QuotientGroup.eq_one_iff _).2 ?_
  have h : FreeGroup.of (none : Option α) = extRel ρ (tietzeWord (1 : FreeGroup α)) none :=
    (cancelExt_none ρ).symm
  rw [h]
  exact Subgroup.subset_normalClosure (Set.mem_range_self none)

/-- **A cancelling pair does not change the fundamental group.**  The map of presented groups
induced by the extension is onto; it is injective by
`FiniteChains.extHom_tietze_injective`. -/
theorem extHom_cancel_surjective (ρ : J → FreeGroup α) :
    Function.Surjective (extHom ρ (tietzeWord (1 : FreeGroup α))) := by
  have hcomp : ((extHom ρ (tietzeWord (1 : FreeGroup α))).comp
      ((QuotientGroup.mk' (relSub ρ)).comp (tietzeLift (1 : FreeGroup α))))
      = QuotientGroup.mk' (relSub (extRel ρ (tietzeWord (1 : FreeGroup α)))) := by
    refine FreeGroup.ext_hom _ _ fun o => ?_
    cases o with
    | none =>
        show extHom ρ _ (QuotientGroup.mk (tietzeLift (1 : FreeGroup α) (FreeGroup.of none)))
          = QuotientGroup.mk (FreeGroup.of none)
        rw [tietzeLift_of_none]
        rw [mk_of_none_eq_one ρ]
        show extHom ρ _ (QuotientGroup.mk 1) = 1
        simp
    | some a =>
        show extHom ρ _ (QuotientGroup.mk (tietzeLift (1 : FreeGroup α) (FreeGroup.of (some a))))
          = QuotientGroup.mk (FreeGroup.of (some a))
        have hl : tietzeLift (1 : FreeGroup α) (FreeGroup.of (some a)) = FreeGroup.of a := by
          simp [tietzeLift]
        rw [hl, extHom_mk]
        simp
  intro y
  obtain ⟨w, rfl⟩ := QuotientGroup.mk_surjective y
  exact ⟨QuotientGroup.mk (tietzeLift (1 : FreeGroup α) w),
    congrArg (fun f : FreeGroup (Option α) →* _ => f w) hcomp⟩

theorem extHom_cancel_bijective [Fintype α] [DecidableEq α] [Fintype J] [DecidableEq J]
    (ρ : J → FreeGroup α) :
    Function.Bijective (extHom ρ (tietzeWord (1 : FreeGroup α))) :=
  ⟨extHom_tietze_injective ρ 1, extHom_cancel_surjective ρ⟩

theorem extRingHom_cancel_bijective [Fintype α] [DecidableEq α] [Fintype J] [DecidableEq J]
    (ρ : J → FreeGroup α) :
    Function.Bijective (extRingHom ρ (tietzeWord (1 : FreeGroup α))) := by
  classical
  set e : PresGroup ρ ≃ PresGroup (extRel ρ (tietzeWord (1 : FreeGroup α))) :=
    Equiv.ofBijective _ (extHom_cancel_bijective ρ) with he
  have hmap : ∀ x : MonoidAlgebra ℤ (PresGroup ρ),
      (extRingHom ρ (tietzeWord (1 : FreeGroup α)) x).coeff = Finsupp.equivMapDomain e x.coeff := by
    intro x
    show Finsupp.mapDomain (extHom ρ (tietzeWord (1 : FreeGroup α))) x.coeff = _
    rw [Finsupp.equivMapDomain_eq_mapDomain]
    rfl
  constructor
  · intro x y hxy
    apply MonoidAlgebra.coeff_injective
    have := hmap x ▸ hmap y ▸ congrArg MonoidAlgebra.coeff hxy
    exact (Finsupp.equivCongrLeft e).injective (by simpa [Finsupp.equivCongrLeft] using this)
  · intro y
    refine ⟨MonoidAlgebra.ofCoeff (Finsupp.equivMapDomain e.symm y.coeff), ?_⟩
    apply MonoidAlgebra.coeff_injective
    rw [hmap]
    ext g
    simp [Finsupp.equivMapDomain_apply]

/-! ### A cancelling pair creates no new elements of `π₂` -/

/-- **Asphericity is inherited by the cancelling-pair extension.** -/
theorem aspherical_cancelExt [Fintype α] [DecidableEq α] [Fintype J] [DecidableEq J]
    {ρ : J → FreeGroup α} (h : Aspherical ρ) :
    Aspherical (extRel ρ (tietzeWord (1 : FreeGroup α))) := by
  classical
  intro v hv
  have hreg : ∀ x : MonoidAlgebra ℤ (PresGroup (extRel ρ (tietzeWord (1 : FreeGroup α)))),
      x * foxMatrixPres (extRel ρ (tietzeWord (1 : FreeGroup α))) none none = 0 → x = 0 := by
    intro x hx
    rwa [foxNew_tietze ρ 1, mul_one] at hx
  obtain ⟨hnone, hold⟩ := extCycle_old ρ _ hreg hv
  set φ := extRingHom ρ (tietzeWord (1 : FreeGroup α)) with hφ
  set e := RingEquiv.ofBijective φ (extRingHom_cancel_bijective ρ) with he
  have hsymm : ∀ x : MonoidAlgebra ℤ (PresGroup ρ), e.symm (φ x) = x := fun x =>
    e.symm_apply_apply x
  set u : J → MonoidAlgebra ℤ (PresGroup ρ) := fun j => e.symm (v (some j)) with hu
  have hcyc : IsFoxCycle ρ u := by
    intro i
    have h0 := hold i
    have := congrArg (fun z => e.symm z) h0
    simp only [map_sum, map_mul, map_zero] at this
    rw [← this]
    exact Finset.sum_congr rfl fun j _ => by rw [hsymm]
  have hu0 : u = 0 := h u hcyc
  funext jo
  cases jo with
  | none => exact hnone
  | some j =>
      have hz : e.symm (v (some j)) = 0 := congrFun hu0 j
      have he0 : e (e.symm (v (some j))) = e 0 := congrArg (fun z => e z) hz
      rw [e.apply_symm_apply, map_zero] at he0
      simpa using he0

/-! ### Asphericity in the homotopy-theoretic model -/

/-- **An aspherical presentation is one whose presentation complex has no `π₂`.**  The
algebraic condition "no nonzero Fox cycle" agrees with the vanishing of the second homotopy
module of `RequestProject/CombPi2.lean`. -/
theorem aspherical_iff_pi2_eq_zero [Fintype α] [DecidableEq α] [Fintype J] [DecidableEq J]
    (ρ : J → FreeGroup α) :
    Aspherical ρ ↔ ∀ u : (Comb.uCover (Comb.presComplex ρ) PUnit.unit).F →₀ ℤ,
      u ∈ Comb.Pi2 (Comb.presComplex ρ) PUnit.unit → u = 0 := by
  classical
  constructor
  · intro h u hu
    have hv : Comb.bdry2 (Comb.univCover ρ) (Comb.chain2 (Comb.presUnivHom ρ) u) = 0 :=
      (Comb.mem_pi2_iff_bdry2_eq_zero ρ u).1 hu
    have hcyc : IsFoxCycle ρ
        (Comb.coords (relSub ρ) J (Comb.chain2 (Comb.presUnivHom ρ) u)) :=
      (Comb.univCover_bdry2_eq_zero_iff ρ _).1 hv
    have hzero : Comb.chain2 (Comb.presUnivHom ρ) u = 0 := by
      refine (Comb.coords (relSub ρ) J).injective ?_
      rw [h _ hcyc, map_zero]
    refine Finsupp.mapDomain_injective (Comb.uvFace_bijective ρ).1 ?_
    rw [Finsupp.mapDomain_zero]
    exact hzero
  · intro h v hv
    set c := (Comb.coords (relSub ρ) J).symm v with hc
    have hcv : Comb.coords (relSub ρ) J c = v := by
      rw [hc, LinearEquiv.apply_symm_apply]
    have hb : Comb.bdry2 (Comb.univCover ρ) c = 0 :=
      (Comb.univCover_bdry2_eq_zero_iff ρ c).2 (by rw [hcv]; exact hv)
    obtain ⟨u, hu⟩ := Comb.chain2_presUnivHom_surjective ρ c
    have hmem : u ∈ Comb.Pi2 (Comb.presComplex ρ) PUnit.unit :=
      (Comb.mem_pi2_iff_bdry2_eq_zero ρ u).2 (by rw [hu]; exact hb)
    have hu0 : c = 0 := by rw [← hu, h u hmem, map_zero]
    rw [← hcv, hu0, map_zero]

/-- **The inclusion of an aspherical presentation complex into any larger presentation
complex is zero on `π₂`** — for the trivial reason that the source has no spherical
classes. -/
theorem zeroPi2_presInclHom_of_aspherical [Fintype α] [DecidableEq α] [Fintype J]
    [DecidableEq J] {ρ : J → FreeGroup α} (h : Aspherical ρ) {β K : Type u} [DecidableEq β]
    {σ : K → FreeGroup β} (f : α → β) (hf : Function.Injective f) (g : J → K)
    (hg : ∀ j, σ (g j) = FreeGroup.map f (ρ j)) :
    Comb.ZeroPi2 (Comb.presInclHom f hf ρ σ g hg) := by
  classical
  refine (Comb.zeroPi2_presInclHom_iff ρ f hf g hg).2 fun v hv => ?_
  have hcyc : IsFoxCycle ρ (Comb.coords (relSub ρ) J v) :=
    (Comb.univCover_bdry2_eq_zero_iff ρ v).1 hv
  have hv0 : v = 0 := by
    refine (Comb.coords (relSub ρ) J).injective ?_
    rw [h _ hcyc, map_zero]
  rw [hv0, map_zero]

/-- **An inclusion into an aspherical presentation complex is zero on `π₂`** — the target has
no spherical classes, and the image of a spherical class is one. -/
theorem zeroPi2_presInclHom_of_aspherical_target [DecidableEq α] {ρ : J → FreeGroup α}
    {β Kc : Type u} [Fintype β] [DecidableEq β] [Fintype Kc] [DecidableEq Kc]
    {σ : Kc → FreeGroup β} (hσ : Aspherical σ) (f : α → β) (hf : Function.Injective f)
    (g : J → Kc) (hg : ∀ j, σ (g j) = FreeGroup.map f (ρ j)) :
    Comb.ZeroPi2 (Comb.presInclHom f hf ρ σ g hg) := by
  classical
  refine (Comb.zeroPi2_presInclHom_iff ρ f hf g hg).2 fun v hv => ?_
  have hw : Comb.bdry2 (Comb.univCover σ)
      (Comb.chain2 (Comb.univCoverInclHom f hf ρ σ g hg) v) = 0 := by
    rw [Comb.bdry2_chain2, hv, map_zero]
  have hcyc : IsFoxCycle σ (Comb.coords (relSub σ) Kc
      (Comb.chain2 (Comb.univCoverInclHom f hf ρ σ g hg) v)) :=
    (Comb.univCover_bdry2_eq_zero_iff σ _).1 hw
  refine (Comb.coords (relSub σ) Kc).injective ?_
  rw [hσ _ hcyc, map_zero]

/-! ### Iterating the cancelling pairs -/

/-- The relators adjoined at the successive stages: at every stage the new relator is the new
generator itself. -/
def cancelWords (β : Type u) (n : ℕ) : FreeGroup (Option (optIter β n)) :=
  tietzeWord (1 : FreeGroup (optIter β n))

/-- **The `n`-th stage of the chain**: the presentation `ρ` with `n` cancelling
generator–relator pairs adjoined. -/
def iterCancel (ρ : J → FreeGroup α) : ∀ n, optIter J n → FreeGroup (optIter α n) :=
  iterPres ρ (cancelWords α)

theorem iterCancel_succ_some (ρ : J → FreeGroup α) (n : ℕ) (j : optIter J n) :
    iterCancel ρ (n + 1) (some j) = FreeGroup.map Option.some (iterCancel ρ n j) := rfl

/-- **Every stage is again aspherical.** -/
theorem aspherical_iterCancel [Fintype α] [DecidableEq α] [Fintype J] [DecidableEq J]
    {ρ : J → FreeGroup α} (h : Aspherical ρ) : ∀ n, Aspherical (iterCancel ρ n)
  | 0 => h
  | n + 1 => aspherical_cancelExt (ρ := iterCancel ρ n) (aspherical_iterCancel h n)

/-! ### The chain -/

/-- Adjoining a cell changes the complex: the larger presentation has one two-cell more. -/
theorem presComplex_ne_of_option {β K : Type u} [DecidableEq β] [Fintype K]
    (σ : K → FreeGroup β) {β' : Type u} [DecidableEq β'] (τ : Option K → FreeGroup β') :
    Comb.presComplex σ ≠ Comb.presComplex τ := by
  intro h
  have hF : K = Option K := congrArg Comb.Complex2.F h
  have hcard := Fintype.card_congr (Equiv.cast hF)
  simp only [Fintype.card_option] at hcard
  omega

variable [Fintype α] [DecidableEq α] [Fintype J] [DecidableEq J]

/-- The inclusion of one stage into the next. -/
def iterCancelInc (ρ : J → FreeGroup α) (n : ℕ) :
    Comb.Hom (Comb.presComplex (iterCancel ρ n)) (Comb.presComplex (iterCancel ρ (n + 1))) :=
  Comb.presInclHom Option.some (Option.some_injective _) (iterCancel ρ n)
    (iterCancel ρ (n + 1)) Option.some (iterCancel_succ_some ρ n)

/-- **Condition (1) of Theorem A from one aspherical extension.**  Suppose the presentation
complex `K` of `ρ` sits inside the presentation complex `X₀` of an *aspherical* presentation
`σ`, strictly and with the inclusion zero on `π₂`.  Padding `X₀` with cancelling
generator–relator pairs then produces a strictly increasing chain
`K ⊊ X₀ ⊊ ⋯ ⊊ Xₙ` of finite two-complexes, all of whose inclusions are zero on `π₂`. -/
def extStrictTopChain {β Kc : Type u} [Fintype β] [DecidableEq β] [Fintype Kc] [DecidableEq Kc]
    {ρ : J → FreeGroup α} {σ : Kc → FreeGroup β} (f : α → β) (hf : Function.Injective f)
    (g : J → Kc) (hgi : Function.Injective g) (hg : ∀ j, σ (g j) = FreeGroup.map f (ρ j))
    (hσ : Aspherical σ) (hne : Comb.presComplex ρ ≠ Comb.presComplex σ) (n : ℕ) :
    Comb.StrictTopChain (Comb.presComplex ρ) n where
  X r := Comb.presComplex (iterCancel σ r)
  inc r := iterCancelInc σ r
  incV := fun _ _ _ _ => Subsingleton.elim (α := PUnit.{u + 1}) _ _
  incE := fun _ => Option.some_injective _
  incF := fun _ => Option.some_injective _
  finE := fun _ => Finite.of_fintype _
  finF := fun _ => Finite.of_fintype _
  base := Comb.presInclHom f hf ρ σ g hg
  baseV := fun _ _ _ => Subsingleton.elim (α := PUnit.{u + 1}) _ _
  baseE := hf
  baseF := hgi
  zero_pi2 r _ :=
    zeroPi2_presInclHom_of_aspherical (aspherical_iterCancel hσ r) _ _ _ _
  baseStrict := hne
  strict r _ := presComplex_ne_of_option (iterCancel σ r) _

omit [Fintype α] [Fintype J] [DecidableEq J] in
/-- **The very first arrow of the chain is zero on `π₂` as well.**  The structure
`FiniteChains.Comb.StrictTopChain` only demands this of the arrows between the stages; here it
holds for the inclusion of `K` into the first stage too, so all `n + 1` inclusions of the
chain are zero on `π₂`, exactly as condition (1) of the paper asks. -/
theorem zeroPi2_base_extStrictTopChain {β Kc : Type u} [Fintype β] [DecidableEq β]
    [Fintype Kc] [DecidableEq Kc] {ρ : J → FreeGroup α} {σ : Kc → FreeGroup β} (f : α → β)
    (hf : Function.Injective f) (g : J → Kc) (hgi : Function.Injective g)
    (hg : ∀ j, σ (g j) = FreeGroup.map f (ρ j)) (hσ : Aspherical σ)
    (hne : Comb.presComplex ρ ≠ Comb.presComplex σ) (n : ℕ) :
    Comb.ZeroPi2 (extStrictTopChain f hf g hgi hg hσ hne n).base :=
  zeroPi2_presInclHom_of_aspherical_target hσ f hf g hg

omit [Fintype α] [Fintype J] [DecidableEq J] in
/-- **Condition (1) of Theorem A for a complex with one finite aspherical extension which is
zero on `π₂`.** -/
theorem hasMapChains_of_asphericalExtension {β Kc : Type u} [Fintype β] [DecidableEq β]
    [Fintype Kc] [DecidableEq Kc] {ρ : J → FreeGroup α} {σ : Kc → FreeGroup β} (f : α → β)
    (hf : Function.Injective f) (g : J → Kc) (hgi : Function.Injective g)
    (hg : ∀ j, σ (g j) = FreeGroup.map f (ρ j)) (hσ : Aspherical σ)
    (hne : Comb.presComplex ρ ≠ Comb.presComplex σ) :
    Comb.HasMapChains (Comb.presComplex ρ) :=
  fun n => ⟨extStrictTopChain f hf g hgi hg hσ hne n⟩

/-- **Condition (1) of Theorem A for an aspherical presentation complex**: a strictly
increasing chain `K ⊊ X₀ ⊊ ⋯ ⊊ Xₙ` of finite two-complexes whose inclusions are zero on
`π₂`, of every length and with no unproved hypothesis.  Here the first extension is the
complex itself with one cancelling pair adjoined. -/
def asphericalStrictTopChain {ρ : J → FreeGroup α} (h : Aspherical ρ) (n : ℕ) :
    Comb.StrictTopChain (Comb.presComplex ρ) n :=
  extStrictTopChain (σ := iterCancel ρ 1) Option.some (Option.some_injective _) Option.some
    (Option.some_injective _) (iterCancel_succ_some ρ 0) (aspherical_iterCancel h 1)
    (presComplex_ne_of_option ρ _) n

/-- **Condition (1) of Theorem A holds, in its faithful map-carrying form, for the
presentation complex of every finite aspherical presentation.** -/
theorem hasMapChains_of_aspherical {ρ : J → FreeGroup α} (h : Aspherical ρ) :
    Comb.HasMapChains (Comb.presComplex ρ) := fun n => ⟨asphericalStrictTopChain h n⟩

omit [Fintype α] [Fintype J] [DecidableEq J] in
theorem isConnected_presComplex_aspherical (ρ : J → FreeGroup α) :
    Comb.IsConnected (Comb.presComplex ρ) :=
  fun _ _ => ⟨[], Comb.isPath_of_subsingleton _ _ _ _ _⟩

/-! ### Arbitrary two-complexes inside an aspherical one -/

/-- A two-complex **without spherical classes**: no two-cycle in its universal cover, at any
base vertex. -/
def Pi2Trivial (Y : Comb.Complex2.{u}) : Prop :=
  ∀ (y₀ : Y.V) (c : (Comb.uCover Y y₀).F →₀ ℤ), c ∈ Comb.Pi2 Y y₀ → c = 0

/-- **Any cellular map into a complex without spherical classes is zero on `π₂`**: the image
of a two-cycle is a two-cycle. -/
theorem zeroPi2_of_pi2Trivial_target {X Y : Comb.Complex2.{u}} (hY : Pi2Trivial Y)
    (h : Comb.Hom X Y) : Comb.ZeroPi2 h :=
  fun _ _ hc => hY _ _ (Comb.mem_pi2_chain2_univLift h hc)

omit [Fintype α] [DecidableEq α] [Fintype J] [DecidableEq J] in
/-- An aspherical presentation complex has no spherical classes. -/
theorem pi2Trivial_presComplex_of_aspherical {β Kc : Type u} [Fintype β] [DecidableEq β]
    [Fintype Kc] [DecidableEq Kc] {σ : Kc → FreeGroup β} (hσ : Aspherical σ) :
    Pi2Trivial (Comb.presComplex σ) := by
  intro y₀ c hc
  cases y₀
  exact (aspherical_iff_pi2_eq_zero σ).1 hσ c hc

omit [Fintype α] [DecidableEq α] [Fintype J] [DecidableEq J] in
/-- **Condition (1) of Theorem A for an arbitrary two-complex inside a finite aspherical
presentation complex.**  If a two-complex `K` embeds — cellularly and injectively, and
strictly — into the presentation complex of a finite aspherical presentation, then over `K`
there are strictly increasing chains of finite two-complexes of every length whose inclusions
are zero on `π₂`.  The inclusion of `K` into the first stage is zero on `π₂` as well, by
`FiniteChains.zeroPi2_of_pi2Trivial_target`. -/
def homStrictTopChain {K : Comb.Complex2.{u}} {β Kc : Type u} [Fintype β] [DecidableEq β]
    [Fintype Kc] [DecidableEq Kc] {σ : Kc → FreeGroup β} (hσ : Aspherical σ)
    (b : Comb.Hom K (Comb.presComplex σ)) (hbV : Function.Injective b.onV)
    (hbE : Function.Injective b.onE) (hbF : Function.Injective b.onF)
    (hne : K ≠ Comb.presComplex σ) (n : ℕ) : Comb.StrictTopChain K n where
  X r := Comb.presComplex (iterCancel σ r)
  inc r := iterCancelInc σ r
  incV := fun _ _ _ _ => Subsingleton.elim (α := PUnit.{u + 1}) _ _
  incE := fun _ => Option.some_injective _
  incF := fun _ => Option.some_injective _
  finE := fun _ => Finite.of_fintype _
  finF := fun _ => Finite.of_fintype _
  base := b
  baseV := hbV
  baseE := hbE
  baseF := hbF
  zero_pi2 r _ :=
    zeroPi2_presInclHom_of_aspherical (aspherical_iterCancel hσ r) _ _ _ _
  baseStrict := hne
  strict r _ := presComplex_ne_of_option (iterCancel σ r) _

omit [Fintype α] [DecidableEq α] [Fintype J] [DecidableEq J] in
/-- **Condition (1) of Theorem A for a two-complex embedded strictly in a finite aspherical
presentation complex.** -/
theorem hasMapChains_of_hom_to_aspherical {K : Comb.Complex2.{u}} {β Kc : Type u} [Fintype β]
    [DecidableEq β] [Fintype Kc] [DecidableEq Kc] {σ : Kc → FreeGroup β} (hσ : Aspherical σ)
    (b : Comb.Hom K (Comb.presComplex σ)) (hbV : Function.Injective b.onV)
    (hbE : Function.Injective b.onE) (hbF : Function.Injective b.onF)
    (hne : K ≠ Comb.presComplex σ) : Comb.HasMapChains K :=
  fun n => ⟨homStrictTopChain hσ b hbV hbE hbF hne n⟩

omit [Fintype α] [DecidableEq α] [Fintype J] [DecidableEq J] in
/-- **A finite connected two-complex embedded strictly in a finite aspherical presentation
complex has a connected acyclic regular cover** — condition (2) of Theorem A, through the
implication `(1) ⇒ (2)` proved in the project. -/
theorem hasAcyclicRegularCover_of_hom_to_aspherical {K : Comb.Complex2.{u}} [Finite K.E]
    [Finite K.F] {β Kc : Type u} [Fintype β] [DecidableEq β] [Fintype Kc] [DecidableEq Kc]
    {σ : Kc → FreeGroup β} (hσ : Aspherical σ) (b : Comb.Hom K (Comb.presComplex σ))
    (hbV : Function.Injective b.onV) (hbE : Function.Injective b.onE)
    (hbF : Function.Injective b.onF) (hne : K ≠ Comb.presComplex σ)
    (hconn : Comb.IsConnected K) (x₀ : K.V) : Comb.HasAcyclicRegularCover K :=
  Comb.hasAcyclicRegularCover_of_topChainsDisc hconn x₀
    fun n => ⟨(homStrictTopChain hσ b hbV hbE hbF hne n).toTopChainDisc⟩

omit [DecidableEq J] in
/-- **A finite presentation complex with a strictly larger finite aspherical extension has a
connected acyclic regular cover** — condition (2) of Theorem A, obtained from the chains just
built through the implication `(1) ⇒ (2)` proved in the project. -/
theorem hasAcyclicRegularCover_of_asphericalExtension {β Kc : Type u} [Fintype β]
    [DecidableEq β] [Fintype Kc] [DecidableEq Kc]
    {ρ : J → FreeGroup α} {σ : Kc → FreeGroup β} (f : α → β)
    (hf : Function.Injective f) (g : J → Kc) (hgi : Function.Injective g)
    (hg : ∀ j, σ (g j) = FreeGroup.map f (ρ j)) (hσ : Aspherical σ)
    (hne : Comb.presComplex ρ ≠ Comb.presComplex σ) :
    Comb.HasAcyclicRegularCover (Comb.presComplex ρ) := by
  haveI : Finite (Comb.presComplex ρ).E := Finite.of_fintype α
  haveI : Finite (Comb.presComplex ρ).F := Finite.of_fintype J
  exact Comb.hasAcyclicRegularCover_of_topChainsDisc (isConnected_presComplex_aspherical ρ)
    PUnit.unit fun n => ⟨(extStrictTopChain f hf g hgi hg hσ hne n).toTopChainDisc⟩

/-- **Condition (2) of Theorem A for an aspherical presentation complex**: it has a connected
acyclic regular cover.  This is the implication `(1) ⇒ (2)`, proved in the project without
hypotheses, applied to the chains just constructed. -/
theorem hasAcyclicRegularCover_of_aspherical {ρ : J → FreeGroup α} (h : Aspherical ρ) :
    Comb.HasAcyclicRegularCover (Comb.presComplex ρ) := by
  haveI : Finite (Comb.presComplex ρ).E := Finite.of_fintype α
  haveI : Finite (Comb.presComplex ρ).F := Finite.of_fintype J
  exact Comb.hasAcyclicRegularCover_of_topChainsDisc (isConnected_presComplex_aspherical ρ)
    PUnit.unit fun n => ⟨(asphericalStrictTopChain h n).toTopChainDisc⟩

/-- **Theorem A for an aspherical presentation complex, unconditionally**, with condition (1)
in its faithful, map-carrying form: both conditions hold. -/
theorem theoremA_maps_of_aspherical {ρ : J → FreeGroup α} (h : Aspherical ρ) :
    Comb.HasMapChains (Comb.presComplex ρ) ↔
      Comb.HasAcyclicRegularCover (Comb.presComplex ρ) :=
  ⟨fun _ => hasAcyclicRegularCover_of_aspherical h, fun _ => hasMapChains_of_aspherical h⟩

/-! ### Examples of aspherical presentations -/

omit [Fintype α] [DecidableEq J] in
/-- A presentation without relators — the complex is a wedge of circles — is aspherical. -/
theorem aspherical_of_isEmpty [IsEmpty J] (ρ : J → FreeGroup α) : Aspherical ρ :=
  fun _ _ => funext fun j => isEmptyElim j

omit [Fintype α] [DecidableEq J] in
/-- **A one-relator presentation is aspherical as soon as its group ring has no zero divisors
and one Fox derivative of the relator is nonzero.**  (For a torsion-free abelian presented
group the group ring is a domain by
`FiniteChains.intMonoidAlgebra_isDomain`.) -/
theorem aspherical_of_unique_relator [Subsingleton J] {ρ : J → FreeGroup α}
    [NoZeroDivisors (MonoidAlgebra ℤ (PresGroup ρ))] {i : α} {j₀ : J}
    (hne : foxMatrixPres ρ i j₀ ≠ 0) : Aspherical ρ := by
  intro v hv
  have h := hv i
  have huniv : (Finset.univ : Finset J) = {j₀} :=
    Finset.eq_singleton_iff_unique_mem.2 ⟨Finset.mem_univ _, fun x _ => Subsingleton.elim _ _⟩
  rw [huniv, Finset.sum_singleton] at h
  have hv0 : v j₀ = 0 := by
    rcases mul_eq_zero.1 h with h1 | h1
    · exact h1
    · exact absurd h1 hne
  funext j
  rw [Subsingleton.elim j j₀]
  simpa using hv0

/-- The presentation `⟨x | x⟩` is aspherical: its Fox matrix is the unit of the group ring. -/
theorem aspherical_presRho : Aspherical presRho := by
  intro v hv
  have h := hv ()
  rw [foxMatrixPres_presRho] at h
  simp only [unitB, mul_one, Finset.univ_unique, Finset.sum_singleton] at h
  funext j
  cases j
  simpa using h

/-- Consequently the construction is not vacuous: over the presentation complex of `⟨x | x⟩`
there are strictly increasing chains of every length whose inclusions are zero on `π₂`. -/
theorem hasMapChains_presRho : Comb.HasMapChains (Comb.presComplex presRho) :=
  hasMapChains_of_aspherical aspherical_presRho

/-! ### The torus: an aspherical example with infinite fundamental group -/

/-- **The standard presentation complex of the torus is aspherical.**  This is
`FiniteChains.torus_isFoxCycle_eq_zero` of `RequestProject/Pi2ExtensionExample.lean`, read in
the present terminology. -/
theorem aspherical_torus : Aspherical (extRel rhoZ (hnnWord xZ xZ)) :=
  torus_isFoxCycle_eq_zero

/-- **The fundamental group of the torus complex is infinite**: the image of `x` has infinite
order, because the presented group of `⟨x |⟩` embeds into it. -/
theorem not_isOfFinOrder_torus_x :
    ¬ IsOfFinOrder (extHom rhoZ (hnnWord xZ xZ) (QuotientGroup.mk xZ)) :=
  not_isOfFinOrder_map_of_injective
    (extHom_hnn_injective rhoZ xZ xZ not_isOfFinOrder_xZ not_isOfFinOrder_xZ)
    not_isOfFinOrder_xZ

/-- **Condition (1) of Theorem A for the torus, of every length and unconditionally**: over
the standard presentation complex of the torus — an aspherical complex with infinite
fundamental group — there are strictly increasing chains of finite two-complexes of every
length whose inclusions are zero on `π₂`. -/
theorem hasMapChains_torus :
    Comb.HasMapChains (Comb.presComplex (extRel rhoZ (hnnWord xZ xZ))) :=
  hasMapChains_of_aspherical aspherical_torus

/-- **Theorem A for the torus, unconditionally**, with condition (1) in its faithful,
map-carrying form. -/
theorem theoremA_maps_torus :
    Comb.HasMapChains (Comb.presComplex (extRel rhoZ (hnnWord xZ xZ))) ↔
      Comb.HasAcyclicRegularCover (Comb.presComplex (extRel rhoZ (hnnWord xZ xZ))) :=
  theoremA_maps_of_aspherical aspherical_torus

end FiniteChains
