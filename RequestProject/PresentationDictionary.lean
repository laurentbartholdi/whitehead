import RequestProject.HurewiczDictionary
import RequestProject.CoverAcyclic
import RequestProject.FrameworkNecessityTF
import RequestProject.NecessityLocallyFinite

/-!
# The Hurewicz input for a presented complex is a theorem

Let `K` be the two-complex of a finite presentation `⟨x_1, …, x_n | r_1, …, r_m⟩`, let `F`
be the free group on the generators, `R = ⟪r_1, …, r_m⟫` the relator subgroup and
`G = π₁(K) = F/R`.  The requirements (2.2) of Section 2 are attached to the Fox matrix
`b i j = ∂r_j/∂x_i` read in `ℤ[G]`.

`RequestProject/HurewiczDictionary.lean` proves, for a normal subgroup `Ñ ◁ F` containing
the relators, that the Fox vector of `w ∈ Ñ` is a boundary of the chain complex of the
cover exactly when `w ∈ R·[Ñ, Ñ]`, and deduces that `Ñ/(R·[Ñ, Ñ])` is torsion free as soon
as the Fox boundary is injective modulo every prime.

This file transports that statement across the identification `G/N ≅ F/Ñ`
(`FiniteChains.quotQuotEquivPres`) and obtains the Hurewicz input of Section 2 as a
theorem: for every normal subgroup `N ◁ G` satisfying the requirements (2.2) modulo every
prime, the abelianization `N/[N, N]` is torsion free
(`FiniteChains.isMulTorsionFree_of_foxSatMod_pres`).

Consequently the implication `(1) ⇒ (2)` of Theorem A holds for a presented complex with
only two topological inputs left: the cell data of the chains and the construction of the
cover (`FiniteChains.hasAcyclicRegularCover_of_cellDataMod_pres`).
-/

namespace FiniteChains

open MonoidAlgebra

universe u

/-! ### Transport of the lifting property along isomorphisms -/

/-- `LiftsMod` transfers along additive isomorphisms intertwining the two maps. -/
theorem liftsMod_of_addEquiv {U V U' V' : Type*} [AddCommGroup U] [AddCommGroup V]
    [AddCommGroup U'] [AddCommGroup V'] (f : U →+ V) (f' : U' →+ V')
    (eU : U ≃+ U') (eV : V ≃+ V') (hcomm : ∀ u, f' (eU u) = eV (f u)) (n : ℕ)
    (h : LiftsMod f n) : LiftsMod f' n := by
  intro u' ⟨w', hw'⟩
  obtain ⟨u, rfl⟩ : ∃ u, eU u = u' := ⟨eU.symm u', eU.apply_symm_apply u'⟩
  have hfu : eV (f u) = n • w' := by rw [← hcomm u]; exact hw'
  have : f u = n • eV.symm w' := by
    apply eV.injective
    rw [hfu, map_nsmul, eV.apply_symm_apply]
  obtain ⟨u₀, hu₀⟩ := h u ⟨eV.symm w', this⟩
  exact ⟨eU u₀, by rw [hu₀, map_nsmul]⟩

/-! ### A torsion-freeness criterion -/

/-- If, in a normal subgroup `N`, a power of an element lying in `[N, N]` forces the element
itself into `[N, N]`, then the abelian group `N/[N, N]` is torsion free. -/
theorem isMulTorsionFree_map_commutator_of_pow {G : Type*} [Group G] (N : Subgroup G)
    [N.Normal] (hkey : ∀ g ∈ N, ∀ n : ℕ, n ≠ 0 → g ^ n ∈ ⁅N, N⁆ → g ∈ ⁅N, N⁆) :
    IsMulTorsionFree (N.map (QuotientGroup.mk' ⁅N, N⁆)) := by
  haveI hcomm : IsMulCommutative (N.map (QuotientGroup.mk' ⁅N, N⁆)) :=
    isMulCommutative_map_commutator N
  constructor
  intro n hn a b hab
  have hab' : a ^ n = b ^ n := hab
  have hcab : Commute a b⁻¹ := hcomm.is_comm.comm a b⁻¹
  have hone : (a * b⁻¹) ^ n = 1 := by
    rw [hcab.mul_pow, hab', inv_pow, mul_inv_cancel]
  obtain ⟨z, hz, hzeq⟩ := (a * b⁻¹).2
  have hzn : z ^ n ∈ ⁅N, N⁆ := by
    have hz1 : (QuotientGroup.mk' ⁅N, N⁆) (z ^ n) = 1 := by
      rw [map_pow, hzeq]
      exact congrArg Subtype.val hone
    rwa [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hz1
  have hzmem : z ∈ ⁅N, N⁆ := hkey z hz n hn hzn
  have hab1 : (a * b⁻¹) = 1 := by
    apply Subtype.ext
    show ((a * b⁻¹ : N.map (QuotientGroup.mk' ⁅N, N⁆)) : G ⧸ ⁅N, N⁆)
      = ((1 : N.map (QuotientGroup.mk' ⁅N, N⁆)) : G ⧸ ⁅N, N⁆)
    rw [Subgroup.coe_one, ← hzeq, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    exact hzmem
  exact mul_inv_eq_one.1 hab1

/-! ### The presented complex -/

variable {α : Type*} [Fintype α] [DecidableEq α] {J : Type*} [Fintype J] (ρ : J → FreeGroup α)

/-- The relator subgroup `R = ⟪r_1, …, r_m⟫ ◁ F`. -/
def relSub : Subgroup (FreeGroup α) := Subgroup.normalClosure (Set.range ρ)

instance relSub_normal : (relSub ρ).Normal := Subgroup.normalClosure_normal

/-- The fundamental group `G = π₁(K) = F/R` of the presented complex. -/
abbrev PresGroup : Type _ := FreeGroup α ⧸ relSub ρ

/-- The Fox boundary matrix of the presentation, read in `ℤ[G]`. -/
noncomputable def foxMatrixPres (i : α) (j : J) : MonoidAlgebra ℤ (PresGroup ρ) :=
  quotRingHom ℤ (relSub ρ) (fox i (ρ j))

omit [Fintype α] [Fintype J] in
theorem foxMatrixPres_col_finite (j : J) : {i : α | foxMatrixPres ρ i j ≠ 0}.Finite :=
  (fox_generator_support_finite (ρ j)).subset (by
    intro i hi
    by_contra hz
    simp only [Set.mem_setOf_eq, not_not] at hz
    exact hi (by simp only [foxMatrixPres, hz, map_zero]))

omit [Fintype α] [Fintype J] in
theorem foxBoundaryPres_finite (v : J →₀ MonoidAlgebra ℤ (PresGroup ρ)) :
    {i : α | foxBoundary (foxMatrixPres ρ) v i ≠ 0}.Finite :=
  foxBoundary_support_finite (foxMatrixPres ρ) (foxMatrixPres_col_finite ρ) v

section Subgroups

variable (Nt : Subgroup (FreeGroup α)) [Nt.Normal] (hR : relSub ρ ≤ Nt)

/-- The normal subgroup `N = Ñ/R ◁ G` attached to `Ñ ◁ F`. -/
def presSub : Subgroup (PresGroup ρ) := Nt.map (QuotientGroup.mk' (relSub ρ))

instance presSub_normal : (presSub ρ Nt).Normal :=
  Subgroup.Normal.map ‹Nt.Normal› _ (QuotientGroup.mk'_surjective _)

/-- The identification `G/N ≅ F/Ñ` of the deck group of the cover. -/
noncomputable def quotQuotEquivPres :
    (PresGroup ρ ⧸ presSub ρ Nt) ≃* (FreeGroup α ⧸ Nt) :=
  QuotientGroup.quotientQuotientEquivQuotient (relSub ρ) Nt hR

omit [Fintype α] [DecidableEq α] [Fintype J] in
theorem quotQuotEquivPres_mk (w : FreeGroup α) :
    quotQuotEquivPres ρ Nt hR
        (QuotientGroup.mk (QuotientGroup.mk w : PresGroup ρ) : PresGroup ρ ⧸ presSub ρ Nt)
      = (QuotientGroup.mk w : FreeGroup α ⧸ Nt) :=
  (MulEquiv.eq_symm_apply (quotQuotEquivPres ρ Nt hR)).mp rfl

/-- The induced isomorphism of group rings `ℤ[G/N] ≅ ℤ[F/Ñ]`. -/
noncomputable def ringEquivPres :
    MonoidAlgebra ℤ (PresGroup ρ ⧸ presSub ρ Nt) ≃ₐ[ℤ] MonoidAlgebra ℤ (FreeGroup α ⧸ Nt) :=
  MonoidAlgebra.domCongr ℤ ℤ (quotQuotEquivPres ρ Nt hR)

omit [Fintype α] [DecidableEq α] [Fintype J] in
/-- The reduction of the group ring of the free group to `ℤ[F/Ñ]` factors through the two
successive quotients. -/
theorem ringEquivPres_quot (x : MonoidAlgebra ℤ (FreeGroup α)) :
    ringEquivPres ρ Nt hR (quotRingHom ℤ (presSub ρ Nt) (quotRingHom ℤ (relSub ρ) x))
      = proj Nt x := by
  induction x using MonoidAlgebra.induction_linear with
  | zero => simp
  | add x y hx hy => rw [map_add, map_add, map_add, hx, hy, map_add]
  | single g n =>
      rw [quotRingHom_single, quotRingHom_single, proj_single]
      show MonoidAlgebra.domCongr ℤ ℤ (quotQuotEquivPres ρ Nt hR) (single _ n) = _
      rw [MonoidAlgebra.domCongr_single, quotQuotEquivPres_mk]

include hR in
omit [Fintype α] in
/-- The boundary `∂₂` of the cover, transported to the presentation side. -/
theorem bdry2_ringEquivPres (u : J →₀ MonoidAlgebra ℤ (PresGroup ρ ⧸ presSub ρ Nt)) (i : α) :
    bdry2 Nt ρ (fun j => ringEquivPres ρ Nt hR (u j)) i
      = ringEquivPres ρ Nt hR (boundaryMap (foxMatrixPres ρ) (foxMatrixPres_col_finite ρ)
          (presSub ρ Nt) u i) := by
  classical
  rw [boundaryMap_apply_coord, bdry2]
  have hfull : ∑ j ∈ u.support, u j *
        quotRingHom ℤ (presSub ρ Nt) (foxMatrixPres ρ i j)
      = ∑ j : J, u j * quotRingHom ℤ (presSub ρ Nt) (foxMatrixPres ρ i j) := by
    refine Finset.sum_subset (Finset.subset_univ _) fun j _ hj => ?_
    have : u j = 0 := by simpa using hj
    rw [this, zero_mul]
  rw [hfull, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_mul]
  congr 1
  exact (ringEquivPres_quot ρ Nt hR (fox i (ρ j))).symm

include hR in
/-- Transport of the lifting property from the presentation side to the cover complex. -/
theorem liftsMod_bdry2Hom_of_liftsMod (n : ℕ)
    (h : LiftsMod (boundaryMap (foxMatrixPres ρ) (foxMatrixPres_col_finite ρ)
      (presSub ρ Nt)).toAddMonoidHom n) :
    LiftsMod (bdry2Hom Nt ρ) n := by
  classical
  set E := ringEquivPres ρ Nt hR with hE
  refine liftsMod_of_addEquiv _ _
    (((Finsupp.linearEquivFunOnFinite ℤ _ J).toAddEquiv.trans
      (AddEquiv.piCongrRight (fun _ : J => E.toAddEquiv))))
    (((Finsupp.linearEquivFunOnFinite ℤ _ α).toAddEquiv.trans
      (AddEquiv.piCongrRight (fun _ : α => E.toAddEquiv)))) ?_ n h
  intro u
  funext i
  show bdry2 Nt ρ (fun j => E (u j)) i = E (boundaryMap _ _ (presSub ρ Nt) u i)
  exact bdry2_ringEquivPres ρ Nt hR u i

include hR in
/-- **The key step towards torsion freeness of `N/[N, N]` for a presented complex.**  If the
requirements (2.2) hold modulo every prime for `N = Ñ/R`, then a power of an element of `N`
lying in `[N, N]` forces the element itself into `[N, N]`. -/
theorem hkey_presSub
    (hmod : ∀ p : ℕ, p.Prime → ∀ v : J →₀ MonoidAlgebra ℤ (PresGroup ρ),
      FoxSatMod p (foxMatrixPres ρ) v (presSub ρ Nt))
    (hρ : ∀ j, ρ j ∈ Nt) :
    ∀ g ∈ presSub ρ Nt, ∀ n : ℕ, n ≠ 0 →
      g ^ n ∈ ⁅presSub ρ Nt, presSub ρ Nt⁆ → g ∈ ⁅presSub ρ Nt, presSub ρ Nt⁆ := by
  classical
  set N := presSub ρ Nt with hN
  -- the lifting property for the boundary of the cover
  have hlift : ∀ p : ℕ, p.Prime → LiftsMod (bdry2Hom Nt ρ) p := fun p hp =>
    liftsMod_bdry2Hom_of_liftsMod ρ Nt hR p
      (liftsMod_of_foxSatMod (foxMatrixPres ρ) (foxMatrixPres_col_finite ρ) N p (hmod p hp))
  -- the key group-theoretic statement, transported from `Ñ`
  show ∀ g ∈ N, ∀ n : ℕ, n ≠ 0 → g ^ n ∈ ⁅N, N⁆ → g ∈ ⁅N, N⁆
  · rintro _ ⟨w, hw, rfl⟩ n hn hpow
    have hcommmap : ⁅N, N⁆ = ⁅Nt, Nt⁆.map (QuotientGroup.mk' (relSub ρ)) := by
      rw [hN, presSub, ← Subgroup.map_commutator]
    have hcomap : w ^ n ∈ relComm Nt ρ := by
      have hmem : (QuotientGroup.mk' (relSub ρ)) (w ^ n) ∈
          ⁅Nt, Nt⁆.map (QuotientGroup.mk' (relSub ρ)) := by
        rw [← hcommmap, map_pow]
        exact hpow
      have := Subgroup.comap_map_eq (QuotientGroup.mk' (relSub ρ)) ⁅Nt, Nt⁆
      have hmem' : w ^ n ∈ ⁅Nt, Nt⁆ ⊔ (QuotientGroup.mk' (relSub ρ)).ker := by
        rw [← this]
        exact hmem
      rw [QuotientGroup.ker_mk'] at hmem'
      rw [relComm, sup_comm]
      exact hmem'
    have hw' : w ∈ relComm Nt ρ :=
      mem_relComm_of_pow_mem Nt ρ hρ hlift hw hn hcomap
    rw [relComm, sup_comm] at hw'
    have : w ∈ ⁅Nt, Nt⁆ ⊔ (QuotientGroup.mk' (relSub ρ)).ker := by
      rw [QuotientGroup.ker_mk']
      exact hw'
    rw [← Subgroup.comap_map_eq] at this
    rw [hcommmap]
    exact this
end Subgroups

/-- **The Hurewicz input of Section 2, for a presented complex, as a theorem.**  For every
normal subgroup `N` of `G = π₁(K)` satisfying the requirements (2.2) modulo every prime,
the abelianization `N/[N, N]` is torsion free. -/
theorem isMulTorsionFree_of_foxSatMod_pres (N : Subgroup (PresGroup ρ)) [N.Normal]
    (hmod : ∀ p : ℕ, p.Prime → ∀ v : J →₀ MonoidAlgebra ℤ (PresGroup ρ),
      FoxSatMod p (foxMatrixPres ρ) v N) :
    IsMulTorsionFree (N.map (QuotientGroup.mk' ⁅N, N⁆)) := by
  set Nt := N.comap (QuotientGroup.mk' (relSub ρ)) with hNt
  have hR : relSub ρ ≤ Nt := by
    intro r hr
    show (QuotientGroup.mk' (relSub ρ)) r ∈ N
    rw [QuotientGroup.mk'_apply, (QuotientGroup.eq_one_iff r).2 hr]
    exact Subgroup.one_mem _
  have hNeq : presSub ρ Nt = N :=
    Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective _) N
  have hρ : ∀ j, ρ j ∈ Nt := fun j =>
    hR (Subgroup.subset_normalClosure (Set.mem_range_self j))
  have hmod' : ∀ p : ℕ, p.Prime → ∀ v : J →₀ MonoidAlgebra ℤ (PresGroup ρ),
      FoxSatMod p (foxMatrixPres ρ) v (presSub ρ Nt) := by
    rw [hNeq]; exact hmod
  have hkey' := hkey_presSub ρ Nt hR hmod' hρ
  refine isMulTorsionFree_map_commutator_of_pow N ?_
  rwa [hNeq] at hkey'

/-- **`(1) ⇒ (2)` of Theorem A for a presented complex.**  Only two topological inputs are
left: the cell data of the chains and the construction of the cover from a perfect normal
subgroup.  The Hurewicz dictionary and the universal-coefficient input are theorems. -/
theorem hasAcyclicRegularCover_of_cellDataMod_pres {β : Type u} [Fintype β] [DecidableEq β]
    {I : Type u} [Fintype I] (σ : I → FreeGroup β) {W : TwoComplexData.{u}} {K : W.Cx}
    (cellData : ∀ (c : ℕ → W.Cx) (n : ℕ), c 0 = K → IsZeroChain W c n →
      ∃ (Fund : ℕ → Type u) (_ : ∀ r, Group (Fund r)) (Gen Cell : ℕ → Type u)
        (h : ChainInput (foxMatrixPres σ) n Fund Gen Cell), ∀ m : ℕ, CycleLiftsMod h m)
    (cover : ∀ N : Subgroup (PresGroup σ), N.Normal →
      (∀ v : I →₀ MonoidAlgebra ℤ (PresGroup σ), FoxSat (foxMatrixPres σ) v N) →
      ⁅N, N⁆ = N → HasAcyclicRegularCover W K)
    (h : HasZeroChains W K) : HasAcyclicRegularCover W K :=
  hasAcyclicRegularCover_of_cellDataMod_tf (foxMatrixPres σ) (foxBoundaryPres_finite σ)
    (foxMatrixPres_col_finite σ) cellData
    (fun N _ hmod => isMulTorsionFree_of_foxSatMod_pres σ N hmod) cover h

end FiniteChains
