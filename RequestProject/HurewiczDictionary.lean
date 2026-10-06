module

public import RequestProject.MagnusKernel
public import RequestProject.CoverHomologyOne
public import RequestProject.UniversalCoefficients

@[expose] public section

/-!
# The Hurewicz dictionary `H₁(K_N) = N/[N, N]`, proved

For a finite presentation `⟨x_1, …, x_n | r_1, …, r_m⟩` with free group `F`, relator
subgroup `R = ⟪r_1, …, r_m⟫` and a normal subgroup `Ñ ◁ F` containing the relators, the
chain complex of the cover `K_N` was built in `RequestProject/CoverChainComplex.lean`:

* its cycles are the Fox vectors of the elements of `Ñ` (Crowell);
* its boundaries are the Fox vectors of the elements of `R`
  (`RequestProject/CoverHomologyOne.lean`).

With the Magnus/Blanchfield theorem of `RequestProject/MagnusKernel.lean` (the Fox vector
map has kernel exactly `[Ñ, Ñ]`) this identifies the first homology of the cover:

`H₁(K_N) = Ñ / (R·[Ñ, Ñ]) = N/[N, N]`,  where `N = Ñ/R`.

The two statements proved here are

* `FiniteChains.foxVec_mem_range_bdry2_iff` — for `w ∈ Ñ` the Fox vector of `w` is a
  boundary exactly when `w ∈ R·[Ñ, Ñ]`; this is the injectivity half of the dictionary, the
  surjectivity half being the Crowell sequence;
* `FiniteChains.mem_relComm_of_pow_mem` — the resulting torsion freeness of `N/[N, N]`:
  if the Fox boundary of the cover is injective modulo every prime, then `wⁿ ∈ R·[Ñ, Ñ]`
  with `n ≠ 0` forces `w ∈ R·[Ñ, Ñ]`.

Up to the passage from `Ñ ◁ F` to `N = Ñ/R ◁ G = F/R`, this is exactly the input that
Section 2 of the paper takes from the Hurewicz theorem and the universal coefficient
theorem.
-/

namespace FiniteChains

open MonoidAlgebra

variable {α : Type*} [Fintype α] [DecidableEq α]
variable (Nsub : Subgroup (FreeGroup α)) [Nsub.Normal]
variable {J : Type*} [Fintype J] (ρ : J → FreeGroup α)

/-- The subgroup `R·[Ñ, Ñ]` of `Ñ`; the quotient `Ñ/(R·[Ñ, Ñ])` is `N/[N, N]`. -/
def relComm : Subgroup (FreeGroup α) :=
  Subgroup.normalClosure (Set.range ρ) ⊔ ⁅Nsub, Nsub⁆

omit [Fintype α] [DecidableEq α] [Fintype J] in
theorem normalClosure_le (hρ : ∀ j, ρ j ∈ Nsub) :
    Subgroup.normalClosure (Set.range ρ) ≤ Nsub := by
  refine Subgroup.normalClosure_le_normal ?_
  rintro _ ⟨j, rfl⟩
  exact hρ j

omit [Fintype α] [DecidableEq α] [Fintype J] in
theorem relComm_le (hρ : ∀ j, ρ j ∈ Nsub) : relComm Nsub ρ ≤ Nsub :=
  sup_le (normalClosure_le Nsub ρ hρ) (Subgroup.commutator_le_left _ _)

/-- The subgroup of `F` consisting of the elements of `Ñ` whose Fox vector is a boundary of
the chain complex of the cover. -/
def bdrySubgroup : Subgroup (FreeGroup α) where
  carrier := {v | v ∈ Nsub ∧ ∃ u : J → CoverRing Nsub, bdry2 Nsub ρ u = foxVec Nsub v}
  one_mem' := ⟨Subgroup.one_mem _, 0, by rw [bdry2_zero, foxVec_one]⟩
  mul_mem' := by
    rintro v w ⟨hv, u₁, hu₁⟩ ⟨hw, u₂, hu₂⟩
    exact ⟨Subgroup.mul_mem _ hv hw, u₁ + u₂, by rw [bdry2_add, hu₁, hu₂, foxVec_mul hv]⟩
  inv_mem' := by
    rintro w ⟨hw, u, hu⟩
    exact ⟨Subgroup.inv_mem _ hw, -u, by rw [bdry2_neg, hu, foxVec_inv hw]⟩

omit [Fintype α] in
theorem mem_bdrySubgroup_iff {w : FreeGroup α} :
    w ∈ bdrySubgroup Nsub ρ ↔
      w ∈ Nsub ∧ ∃ u : J → CoverRing Nsub, bdry2 Nsub ρ u = foxVec Nsub w := Iff.rfl

omit [Fintype α] in
/-- **The injectivity half of the Hurewicz dictionary.**  For `w ∈ Ñ`, the Fox vector of `w`
is a boundary of the chain complex of the cover exactly when `w ∈ R·[Ñ, Ñ]`.  Together with
the Crowell sequence (the cycles are the Fox vectors of `Ñ`) this says
`H₁(K_N) = Ñ/(R·[Ñ, Ñ]) = N/[N, N]`. -/
theorem foxVec_mem_range_bdry2_iff (hρ : ∀ j, ρ j ∈ Nsub) {w : FreeGroup α} (hw : w ∈ Nsub) :
    (∃ u : J → CoverRing Nsub, bdry2 Nsub ρ u = foxVec Nsub w) ↔ w ∈ relComm Nsub ρ := by
  constructor
  · intro hu
    obtain ⟨r, hr, hre⟩ := (bdry2_mem_range_iff Nsub ρ hρ (foxVec Nsub w)).1 hu
    have hrN : r ∈ Nsub := normalClosure_le Nsub ρ hρ hr
    have hmem : w * r⁻¹ ∈ Nsub := Subgroup.mul_mem _ hw (Subgroup.inv_mem _ hrN)
    have hzero : foxVec Nsub (w * r⁻¹) = 0 := by
      rw [foxVec_mul hw, foxVec_inv hrN, ← hre]
      abel
    have hcomm : w * r⁻¹ ∈ ⁅Nsub, Nsub⁆ := (foxVec_eq_zero_iff Nsub hmem).1 hzero
    have : w = (w * r⁻¹) * r := by group
    rw [this]
    exact Subgroup.mul_mem _ ((le_sup_right : ⁅Nsub, Nsub⁆ ≤ relComm Nsub ρ) hcomm)
      ((le_sup_left : Subgroup.normalClosure (Set.range ρ) ≤ relComm Nsub ρ) hr)
  · intro hw'
    have hle : relComm Nsub ρ ≤ bdrySubgroup Nsub ρ := by
      refine sup_le ?_ ?_
      · intro r hr
        exact ⟨normalClosure_le Nsub ρ hρ hr,
          exists_bdry2_of_mem_normalClosure Nsub ρ hρ hr⟩
      · intro v hv
        have hvN : v ∈ Nsub := Subgroup.commutator_le_left Nsub Nsub hv
        refine ⟨hvN, 0, ?_⟩
        rw [bdry2_zero, (foxVec_eq_zero_iff Nsub hvN).2 hv]
    exact (hle hw').2

/-- The boundary `∂₂` of the cover as a homomorphism of additive groups. -/
noncomputable def bdry2Hom : (J → CoverRing Nsub) →+ (α → CoverRing Nsub) where
  toFun := bdry2 Nsub ρ
  map_zero' := bdry2_zero Nsub ρ
  map_add' := bdry2_add Nsub ρ

omit [Fintype α] in
theorem mem_range_bdry2Hom_iff (c : α → CoverRing Nsub) :
    c ∈ (bdry2Hom Nsub ρ).range ↔ ∃ u : J → CoverRing Nsub, bdry2 Nsub ρ u = c := Iff.rfl

omit [Fintype α] in
/-- **Torsion freeness of `N/[N, N]`.**  If the Fox boundary of the cover is injective
modulo every prime — the requirements (2.2) modulo `p`, for all `p` — then the quotient
`Ñ/(R·[Ñ, Ñ]) = N/[N, N]` is torsion free. -/
theorem mem_relComm_of_pow_mem (hρ : ∀ j, ρ j ∈ Nsub)
    (hmod : ∀ p : ℕ, p.Prime → LiftsMod (bdry2Hom Nsub ρ) p)
    {w : FreeGroup α} (hw : w ∈ Nsub) {n : ℕ} (hn : n ≠ 0)
    (hpow : w ^ n ∈ relComm Nsub ρ) : w ∈ relComm Nsub ρ := by
  have hpowN : w ^ n ∈ Nsub := Subgroup.pow_mem _ hw n
  have hvec : foxVec Nsub (w ^ n) = (n : ℤ) • foxVec Nsub w := by
    have := foxVec_zpow (Nsub := Nsub) hw (n : ℤ)
    simpa using this
  have hmemrange : ((n : ℕ) • foxVec Nsub w) ∈ (bdry2Hom Nsub ρ).range := by
    obtain ⟨u, hu⟩ := (foxVec_mem_range_bdry2_iff Nsub ρ hρ hpowN).2 hpow
    refine ⟨u, ?_⟩
    rw [show (bdry2Hom Nsub ρ) u = bdry2 Nsub ρ u from rfl, hu, hvec]
    simp
  have hrange : foxVec Nsub w ∈ (bdry2Hom Nsub ρ).range :=
    mem_range_of_nsmul_mem_range (bdry2Hom Nsub ρ) hmod n hn _ hmemrange
  exact (foxVec_mem_range_bdry2_iff Nsub ρ hρ hw).1 hrange

end FiniteChains
