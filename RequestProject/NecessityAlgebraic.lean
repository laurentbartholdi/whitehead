import RequestProject.ChainFormula
import RequestProject.FinitelyDeterminedInf
import RequestProject.Pigeonhole
import RequestProject.CoverAcyclic

/-!
# `(1) ⇒ (2)` of Theorem A, algebraically complete

Section 2 of the paper derives condition (2) from condition (1) in four steps:

1. formula (2.3): a chain of `n` inclusions, all zero on `π₂`, supplies `n + 1` normal
   subgroups `M_r = ker (G → π₁(X_r))` of `G = π₁(K)` at which every requirement can fail
   at most once (`ChainInput.foxSat_of_not_foxSat`, proved in
   `RequestProject/ChainFormula.lean`);
2. the one-violation principle, giving a single normal subgroup for any finite family of
   requirements (`exists_stage_satisfying_all`);
3. compactness and minimality, giving a minimal normal subgroup satisfying *all* the
   requirements (`exists_normal_subgroup_forall`, `exists_minimal_normal_sat`, with the
   intersection step supplied by `sat_sInf_of_finitelyDetermined`);
4. Lemma 2.1, which makes that minimal subgroup perfect
   (`foxSat_commutator_forall`).

All four steps are theorems in this development.  The present file chains them together,
so that the implication `(1) ⇒ (2)` is *unconditionally* proved for the algebraic model of
the paper: the input is the cell-level data of the chains (the structure `ChainInput`),
and the output is a perfect normal subgroup satisfying all requirements (2.2), which by
`RequestProject/CoverAcyclic.lean` means exactly that the chain complex of the cover `K_N`
is acyclic.

The only hypothesis that is not proved here is the torsion freeness of `N/[N, N]`, the
universal-coefficient input of the paper; it enters as `htf` and is analysed in
`RequestProject/UniversalCoefficients.lean`.
-/

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains

open MonoidAlgebra

universe u

variable {G : Type u} [Group G] {I J : Type u}

/-- **Condition (1) of Theorem A at cell level**: for every `n` there is a chain
`K = X₀ ⊂ ⋯ ⊂ Xₙ` of two-complexes, all of whose inclusions are zero on `π₂`, described by
the data of `ChainInput`. -/
def HasCellChains (b : I → J → MonoidAlgebra ℤ G) : Prop :=
  ∀ n : ℕ, ∃ (Fund : ℕ → Type u) (_ : ∀ r, Group (Fund r)) (Gen Cell : ℕ → Type u),
    Nonempty (ChainInput b n Fund Gen Cell)

variable {b : I → J → MonoidAlgebra ℤ G}

/-- **Step 1–2 of Section 2.**  Any finite family of requirements (2.2) is satisfied by a
single normal subgroup of `G`. -/
theorem exists_normal_forall_finset (hchains : HasCellChains b)
    (S : Finset (J →₀ MonoidAlgebra ℤ G)) :
    ∃ N : Subgroup G, N.Normal ∧ ∀ v ∈ S, FoxSat b v N := by
  classical
  obtain ⟨Fund, inst, Gen, Cell, ⟨h⟩⟩ := hchains S.card
  letI := inst
  obtain ⟨r, -, hr⟩ :=
    exists_stage_satisfying_all S le_rfl (fun r v => FoxSat b v (h.phi r).ker)
      (fun r v hv => h.foxSat_of_not_foxSat v r hv)
  exact ⟨(h.phi r).ker, inferInstance, hr⟩

/-- **The conclusion of Section 2.**  If the chains of condition (1) exist for every
length, then `G = π₁(K)` has a perfect normal subgroup satisfying all the requirements
(2.2). -/
theorem exists_perfect_normal_foxSat (hchains : HasCellChains b)
    (hfin : ∀ v : J →₀ MonoidAlgebra ℤ G, {i : I | foxBoundary b v i ≠ 0}.Finite)
    (hcol : ∀ j, {i : I | b i j ≠ 0}.Finite)
    (htf : ∀ (N : Subgroup G) [N.Normal], (∀ v : J →₀ MonoidAlgebra ℤ G, FoxSat b v N) →
      IsMulTorsionFree (N.map (QuotientGroup.mk' ⁅N, N⁆))) :
    ∃ N : Subgroup G, N.Normal ∧ (∀ v : J →₀ MonoidAlgebra ℤ G, FoxSat b v N) ∧
      ⁅N, N⁆ = N := by
  classical
  have hdet : FinitelyDetermined (fun N (v : J →₀ MonoidAlgebra ℤ G) => FoxSat b v N) :=
    fun v => foxSat_finitelyDetermined b v (hfin v)
  obtain ⟨M, hMnormal, hM⟩ :=
    exists_normal_subgroup_forall (fun N v => FoxSat b v N) hdet
      (exists_normal_forall_finset hchains)
  obtain ⟨N, -, hNnormal, hN, hNmin⟩ :=
    exists_minimal_normal_sat (fun N => ∀ v : J →₀ MonoidAlgebra ℤ G, FoxSat b v N)
      (fun C hchain hne hC =>
        sat_sInf_of_finitelyDetermined (fun N v => FoxSat b v N) hdet hchain hne
          (fun N hNmem => (hC N hNmem).2))
      M hMnormal hM
  haveI := hNnormal
  haveI := htf N hN
  have hcomm : (⁅N, N⁆ : Subgroup G).Normal := inferInstance
  have hsatcomm : ∀ v : J →₀ MonoidAlgebra ℤ G, FoxSat b v ⁅N, N⁆ :=
    foxSat_commutator b hcol N hN
  exact ⟨N, hNnormal, hN, hNmin ⁅N, N⁆ (Subgroup.commutator_le_left N N) hcomm hsatcomm⟩

/-! ### The acyclic cover produced by Section 2

For a finite presentation `⟨x_1, …, x_n | r_1, …, r_m⟩` the requirements (2.2) attached to
the subgroups of the free group are exactly the injectivity of the boundary `∂₂` of the
chain complex of the cover, and a perfect normal subgroup satisfying them yields an acyclic
cover; this is `RequestProject/CoverAcyclic.lean`.  The statement below is the
corresponding end-to-end conclusion, for the free group itself.
-/

/-- Membership in the preimage of `N` can be read on the image: reduction along `q` and
reduction modulo `N.comap q` vanish together. -/
theorem vanishesMod_comap_iff {H : Type*} [Group H] (q : G →* H) (N : Subgroup H) [N.Normal]
    (x : MonoidAlgebra ℤ G) :
    VanishesMod (N.comap q) x.coeff ↔ VanishesMod N (MonoidAlgebra.mapDomainRingHom ℤ q x).coeff := by
  have hker : ((QuotientGroup.mk' N).comp q).ker = N.comap q := by
    ext g
    simp [MonoidHom.mem_ker, QuotientGroup.eq_one_iff]
  rw [← hker, vanishesMod_ker_iff, vanishesMod_iff_quotRingHom_eq_zero,
    ← mapDomainRingHom_comp_apply]
  rfl

/-- **The requirements descend along a quotient.**  If every requirement (2.2) holds for a
normal subgroup `N` of a quotient `H` of `G`, with the boundary matrix read in `ℤ[H]`, then
every requirement holds for the preimage of `N` in `G`, with the boundary matrix read in
`ℤ[G]`. -/
theorem foxSat_comap {H : Type*} [Group H] (q : G →* H) (N : Subgroup H) [N.Normal]
    (b : I → J → MonoidAlgebra ℤ G)
    (hsat : ∀ w : J →₀ MonoidAlgebra ℤ H,
      FoxSat (fun i j => MonoidAlgebra.mapDomainRingHom ℤ q (b i j)) w N)
    (v : J →₀ MonoidAlgebra ℤ G) : FoxSat b v (N.comap q) := by
  classical
  set qr := MonoidAlgebra.mapDomainRingHom ℤ q with hqr
  set w : J →₀ MonoidAlgebra ℤ H := Finsupp.mapRange qr (map_zero _) v with hw
  have hwapp : ∀ j, w j = qr (v j) := fun j => rfl
  have hwsupp : w.support ⊆ v.support := by
    intro j hj
    simp only [hw, Finsupp.mapRange_apply, Finsupp.mem_support_iff] at hj ⊢
    exact fun hv => hj (by rw [hv, map_zero])
  have hbdry : ∀ i : I,
      foxBoundary (fun i j => qr (b i j)) w i = qr (foxBoundary b v i) := by
    intro i
    rw [foxBoundary, foxBoundary, map_sum]
    refine (Finset.sum_subset hwsupp ?_).trans
      (Finset.sum_congr rfl fun j _ => by rw [hwapp, map_mul])
    intro j _ hj
    simp only [Finsupp.mem_support_iff, not_not] at hj
    rw [hj, zero_mul]
  intro hv j
  have hvw : ∀ i : I, VanishesMod N (foxBoundary (fun i j => qr (b i j)) w i).coeff := by
    intro i
    rw [hbdry i]
    exact (vanishesMod_comap_iff q N _).1 (hv i)
  exact (vanishesMod_comap_iff q N (v j)).2 (by simpa [hwapp, hqr] using hsat w hvw j)

variable {α : Type u} [Fintype α] [DecidableEq α] {JJ : Type u} [Fintype JJ]

/-- **From chains to an acyclic cover.**  Let `F` be the free group on the generators of a
finite presentation `⟨x_1, …, x_n | ρ⟩`, let `R` be the normal closure of the relators and
`G = F/R = π₁(K)`.  If the chains of condition (1) exist for every length, then there is a
normal subgroup `Ñ ◁ F` containing the relators whose associated cover `K_N` has an acyclic
chain complex: `∂₂` is injective (`H₂(K_N) = 0`), every `∂₁`-cycle is a `∂₂`-boundary
(`H₁(K_N) = 0`) and the image of `∂₁` is the augmentation ideal (`H̃₀(K_N) = 0`). -/
theorem exists_acyclic_cover_of_cellChains (ρ : JJ → FreeGroup α)
    (hchains : HasCellChains (I := α) (J := JJ)
      (fun i j => MonoidAlgebra.mapDomainRingHom ℤ
        (QuotientGroup.mk' (Subgroup.normalClosure (Set.range ρ))) (fox i (ρ j))))
    (htf : ∀ (N : Subgroup (FreeGroup α ⧸ Subgroup.normalClosure (Set.range ρ))) [N.Normal],
      (∀ v : JJ →₀ MonoidAlgebra ℤ (FreeGroup α ⧸ Subgroup.normalClosure (Set.range ρ)),
          FoxSat (fun i j => MonoidAlgebra.mapDomainRingHom ℤ
            (QuotientGroup.mk' (Subgroup.normalClosure (Set.range ρ))) (fox i (ρ j))) v N) →
      IsMulTorsionFree (N.map (QuotientGroup.mk' ⁅N, N⁆))) :
    ∃ Nsub : Subgroup (FreeGroup α), ∃ _ : Nsub.Normal,
      Subgroup.normalClosure (Set.range ρ) ≤ Nsub ∧
      (∀ u : JJ → CoverRing Nsub, bdry1 Nsub (bdry2 Nsub ρ u) = 0) ∧
        (∀ u : JJ → CoverRing Nsub, bdry2 Nsub ρ u = 0 → u = 0) ∧
        (∀ c : α → CoverRing Nsub, bdry1 Nsub c = 0 →
          ∃ u : JJ → CoverRing Nsub, bdry2 Nsub ρ u = c) ∧
        (∀ z : CoverRing Nsub, augQ Nsub z = 0 → ∃ c : α → CoverRing Nsub, bdry1 Nsub c = z) ∧
        (∀ c : α → CoverRing Nsub, augQ Nsub (bdry1 Nsub c) = 0) := by
  classical
  set R := Subgroup.normalClosure (Set.range ρ) with hR
  set q := QuotientGroup.mk' R with hq
  set bG : α → JJ → MonoidAlgebra ℤ (FreeGroup α ⧸ R) :=
    fun i j => MonoidAlgebra.mapDomainRingHom ℤ q (fox i (ρ j)) with hbG
  obtain ⟨N, hNnormal, hNsat, hNperf⟩ :=
    exists_perfect_normal_foxSat hchains (fun _ => Set.toFinite _) (fun _ => Set.toFinite _) htf
  haveI := hNnormal
  refine ⟨N.comap q, inferInstance, ?_, ?_⟩
  · intro x hx
    have : q x = 1 := by
      simpa [hq, QuotientGroup.eq_one_iff] using hx
    simp [Subgroup.mem_comap, this]
  · have hsat : ∀ v : JJ →₀ FreeGroupRing α, FoxSat (foxMatrix ρ) v (N.comap q) := by
      intro v
      exact foxSat_comap q N (foxMatrix ρ) (fun w => hNsat w) v
    have hρ : ∀ j, ρ j ∈ N.comap q := by
      intro j
      have : q (ρ j) = 1 := by
        have : ρ j ∈ R := Subgroup.subset_normalClosure (Set.mem_range_self j)
        simpa [hq, QuotientGroup.eq_one_iff] using this
      simp [Subgroup.mem_comap, this]
    have hperf : N.comap q ≤ R ⊔ ⁅N.comap q, N.comap q⁆ := by
      have h := comap_le_ker_sup_commutator q (QuotientGroup.mk'_surjective R) hNperf
      rwa [hq, QuotientGroup.ker_mk'] at h
    exact cover_acyclic_of_foxSat (N.comap q) ρ hρ hsat hperf

end FiniteChains
