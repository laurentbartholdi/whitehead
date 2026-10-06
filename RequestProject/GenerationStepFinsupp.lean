import RequestProject.GenerationStep
import RequestProject.FoxFinsupp

/-! Structural maps and equation (3.3) with actual finite-support chains.

The generator and relator sets are arbitrary. This is the algebra used when
the fixed-core induction replaces all its positive stages simultaneously;
it does not assert an inclusion of a stage in its own replacement.

-/

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains

universe u

variable {α J α' J' α'' J'' : Type u}
  [DecidableEq α] [DecidableEq α'] [DecidableEq α'']

/-- The genuine second Fox cycle condition for an arbitrary presentation. -/
def FSIsFoxCycle (ρ : J → FreeGroup α)
    (y : J →₀ MonoidAlgebra ℤ (PresGroup ρ)) : Prop :=
  coverSecondBoundary (relSub ρ) ρ y = 0

/-- Vanishing of the Hurewicz image, with finite support in both coordinates. -/
def FSIsCockcroft (ρ : J → FreeGroup α) : Prop :=
  ∀ y : J →₀ MonoidAlgebra ℤ (PresGroup ρ), FSIsFoxCycle ρ y →
    ∀ j, augPres ρ (y j) = 0

/-- A structural map of presentation chain modules, without finiteness of
the set of cells. Its coefficient homomorphism is part of the data. -/
structure PresMorFS (ρ : J → FreeGroup α) (τ : J' → FreeGroup α') where
  hom : PresGroup ρ →* PresGroup τ
  cells : (J →₀ MonoidAlgebra ℤ (PresGroup ρ)) →
    (J' →₀ MonoidAlgebra ℤ (PresGroup τ))
  cells_add : ∀ y z, cells (y + z) = cells y + cells z
  cells_smul : ∀ (a : MonoidAlgebra ℤ (PresGroup ρ)) y,
    cells (a • y) = MonoidAlgebra.mapDomainRingHom ℤ hom a • cells y
  cells_cycle : ∀ y, FSIsFoxCycle ρ y → FSIsFoxCycle τ (cells y)
  cells_aug : ∀ y, (∀ j, augPres ρ (y j) = 0) →
    ∀ j', augPres τ (cells y j') = 0

namespace PresMorFS

variable {ρ : J → FreeGroup α} {τ : J' → FreeGroup α'}
  {υ : J'' → FreeGroup α''}

@[simp] theorem cells_zero (f : PresMorFS ρ τ) : f.cells 0 = 0 := by
  have h := f.cells_smul 0 0
  rw [zero_smul, map_zero, zero_smul] at h
  exact h

@[simp] theorem cells_neg (f : PresMorFS ρ τ)
    (x : J →₀ MonoidAlgebra ℤ (PresGroup ρ)) : f.cells (-x) = -f.cells x := by
  have h := f.cells_smul (-1) x
  simpa only [neg_one_smul, map_neg, map_one] using h

theorem cells_sub (f : PresMorFS ρ τ)
    (x y : J →₀ MonoidAlgebra ℤ (PresGroup ρ)) :
    f.cells (x - y) = f.cells x - f.cells y := by
  rw [sub_eq_add_neg, f.cells_add, f.cells_neg, sub_eq_add_neg]

def id (ρ : J → FreeGroup α) : PresMorFS ρ ρ where
  hom := MonoidHom.id _
  cells := fun y => y
  cells_add := fun _ _ => rfl
  cells_smul := by
    intro a y
    have h : MonoidAlgebra.mapDomainRingHom ℤ (MonoidHom.id (PresGroup ρ)) a = a := by
      change MonoidAlgebra.mapDomain (fun g : PresGroup ρ => g) a = a
      exact MonoidAlgebra.mapDomain_id a
    rw [h]
  cells_cycle := fun _ h => h
  cells_aug := fun _ h => h

def comp (g : PresMorFS τ υ) (f : PresMorFS ρ τ) : PresMorFS ρ υ where
  hom := g.hom.comp f.hom
  cells := fun y => g.cells (f.cells y)
  cells_add := fun y z => by rw [f.cells_add, g.cells_add]
  cells_smul := by
    intro a y
    rw [f.cells_smul, g.cells_smul, PresMor.mapDomainRingHom_comp]
  cells_cycle := fun y hy => g.cells_cycle _ (f.cells_cycle y hy)
  cells_aug := fun y hy => g.cells_aug _ (f.cells_aug y hy)

@[simp] theorem comp_cells (g : PresMorFS τ υ) (f : PresMorFS ρ τ)
    (y : J →₀ MonoidAlgebra ℤ (PresGroup ρ)) :
    (g.comp f).cells y = g.cells (f.cells y) := rfl

def castTarget {τ' : J' → FreeGroup α'} (f : PresMorFS ρ τ) (h : τ = τ') :
    PresMorFS ρ τ' := h ▸ f

/-- A semilinear structural map sends a span into the span of its image. -/
theorem cells_mem_span (g : PresMorFS τ υ)
    {S : Set (J' →₀ MonoidAlgebra ℤ (PresGroup τ))}
    {y : J' →₀ MonoidAlgebra ℤ (PresGroup τ)}
    (hy : y ∈ Submodule.span (MonoidAlgebra ℤ (PresGroup τ)) S) :
    g.cells y ∈ Submodule.span (MonoidAlgebra ℤ (PresGroup υ)) (g.cells '' S) := by
  induction hy using Submodule.span_induction with
  | mem y hy => exact Submodule.subset_span ⟨y, hy, rfl⟩
  | zero => simp
  | add y z _ _ hy hz => rw [g.cells_add]; exact Submodule.add_mem _ hy hz
  | smul a y _ hy => rw [g.cells_smul]; exact Submodule.smul_mem _ _ hy

end PresMorFS

/-- Equation (3.3), retaining finite support even for an infinite core. -/
def FSGenerates {ρ : J → FreeGroup α} {τ : J' → FreeGroup α'}
    (f : PresMorFS ρ τ) : Prop :=
  ∀ y, FSIsFoxCycle τ y →
    y ∈ Submodule.span (MonoidAlgebra ℤ (PresGroup τ))
      {z | ∃ x, FSIsFoxCycle ρ x ∧ z = f.cells x}

variable {ρ : J → FreeGroup α} {τ : J' → FreeGroup α'}
  {υ : J'' → FreeGroup α''}

theorem FSGenerates.id (ρ : J → FreeGroup α) : FSGenerates (PresMorFS.id ρ) := by
  intro y hy
  exact Submodule.subset_span ⟨y, hy, rfl⟩

/-- Arbitrarily large individual presentations cause no problem with
composition: every element of the generated module is still a finite sum. -/
theorem FSGenerates.comp {g : PresMorFS τ υ} {f : PresMorFS ρ τ}
    (hg : FSGenerates g) (hf : FSGenerates f) : FSGenerates (g.comp f) := by
  intro y hy
  refine Submodule.span_le.2 ?_ (hg y hy)
  rintro _ ⟨z, hz, rfl⟩
  refine Submodule.span_le.2 ?_ (g.cells_mem_span (hf z hz))
  rintro _ ⟨_, ⟨x, hx, rfl⟩, rfl⟩
  exact Submodule.subset_span ⟨x, hx, rfl⟩

theorem FSGenerates.castTarget {τ' : J' → FreeGroup α'} {f : PresMorFS ρ τ}
    (hf : FSGenerates f) (h : τ = τ') : FSGenerates (f.castTarget h) := by
  cases h
  exact hf

/-- Equation (3.3) transports Cockcroftness for arbitrary presentations. -/
theorem fsIsCockcroft_of_generates (f : PresMorFS ρ τ) (hf : FSGenerates f)
    (hρ : FSIsCockcroft ρ) : FSIsCockcroft τ := by
  intro y hy
  have hspan := hf y hy
  clear hy
  induction hspan using Submodule.span_induction with
  | mem z hz =>
      obtain ⟨x, hx, rfl⟩ := hz
      exact f.cells_aug x (hρ x hx)
  | zero => intro j; simp
  | add x z _ _ hx hz =>
      intro j
      rw [Finsupp.add_apply, map_add, hx j, hz j, add_zero]
  | smul a x _ hx =>
      intro j
      rw [Finsupp.smul_apply, smul_eq_mul, map_mul, hx j, mul_zero]

/-- The terminal use of (3.3): killing the original cycle images suffices
to kill every cycle of the replacement. -/
theorem fsCells_eq_zero_of_generates_comp (f : PresMorFS ρ τ) (g : PresMorFS τ υ)
    (hf : FSGenerates f)
    (hcomp : ∀ x, FSIsFoxCycle ρ x → g.cells (f.cells x) = 0)
    {y : J' →₀ MonoidAlgebra ℤ (PresGroup τ)} (hy : FSIsFoxCycle τ y) :
    g.cells y = 0 := by
  have hspan := hf y hy
  clear hy
  induction hspan using Submodule.span_induction with
  | mem z hz =>
      obtain ⟨x, hx, rfl⟩ := hz
      exact hcomp x hx
  | zero => exact g.cells_zero
  | add x z _ _ hx hz => rw [g.cells_add, hx, hz, add_zero]
  | smul a x _ hx => rw [g.cells_smul, hx, smul_zero]

/-- The fixed-core induction transports each old zero arrow through a
commuting replacement square. It does not require `P` to include in `T(P)`. -/
theorem fsCells_eq_zero_of_generates {β K β' K' : Type u}
    [DecidableEq β] [DecidableEq β']
    {σ : K → FreeGroup β} {σ' : K' → FreeGroup β'}
    (eta : PresMorFS ρ σ) (eta' : PresMorFS τ σ')
    (j : PresMorFS ρ τ) (Tj : PresMorFS σ σ')
    (hsq : ∀ x, Tj.cells (eta.cells x) = eta'.cells (j.cells x))
    (hzero : ∀ x, FSIsFoxCycle ρ x → j.cells x = 0)
    (hgen : FSGenerates eta)
    {y : K →₀ MonoidAlgebra ℤ (PresGroup σ)} (hy : FSIsFoxCycle σ y) :
    Tj.cells y = 0 := by
  apply fsCells_eq_zero_of_generates_comp eta Tj hgen ?_ hy
  intro x hx
  rw [hsq x, hzero x hx, eta'.cells_zero]

section FiniteDictionary

variable [Fintype J] [Fintype J']

/-- With finitely many relators, the supported and ordinary Fox-cycle
conditions are identical, not merely related by a chosen homology map. -/
theorem fsIsFoxCycle_iff (y : J →₀ MonoidAlgebra ℤ (PresGroup ρ)) :
    FSIsFoxCycle ρ y ↔ IsFoxCycle ρ y := by
  have happ (i : α) : coverSecondBoundary (relSub ρ) ρ y i =
      ∑ j : J, y j * foxMatrixPres ρ i j := by
    simp only [coverSecondBoundary, Finsupp.linearCombination_apply, Finsupp.sum,
      Finsupp.finset_sum_apply, Finsupp.smul_apply, smul_eq_mul]
    change y.sum (fun j a => a * foxMatrixPres ρ i j) = _
    exact Finsupp.sum_fintype _ _ (fun _ => zero_mul _)
  change coverSecondBoundary (relSub ρ) ρ y = 0 ↔
    ∀ i, ∑ j : J, y j * foxMatrixPres ρ i j = 0
  constructor
  · intro h i
    rw [← happ, h, Finsupp.zero_apply]
  · intro h
    apply Finsupp.ext
    intro i
    exact (happ i).trans (h i)

/-- Forget only the redundant finite support when all cell sets are finite.
This connects the supported construction to the earlier `TPath` machinery. -/
def PresMorFS.toPresMor (f : PresMorFS ρ τ) : PresMor ρ τ where
  hom := f.hom
  cells := fun y => f.cells
    ((Finsupp.linearEquivFunOnFinite
      (MonoidAlgebra ℤ (PresGroup ρ)) (MonoidAlgebra ℤ (PresGroup ρ)) J).symm y)
  cells_add := by
    intro y z
    rw [map_add, f.cells_add]
    rfl
  cells_smul := by
    intro a y
    rw [map_smul, f.cells_smul]
    rfl
  cells_cycle := by
    intro y hy
    apply (fsIsFoxCycle_iff _).mp
    apply f.cells_cycle
    exact (fsIsFoxCycle_iff _).mpr hy
  cells_aug := by
    intro y hy
    exact f.cells_aug _ hy

@[simp] theorem PresMorFS.toPresMor_cells_coe (f : PresMorFS ρ τ)
    (y : J →₀ MonoidAlgebra ℤ (PresGroup ρ)) :
    f.toPresMor.cells y = (f.cells y : J' → MonoidAlgebra ℤ (PresGroup τ)) := by
  simp only [PresMorFS.toPresMor, Finsupp.linearEquivFunOnFinite_symm_coe]

/-- The actual supported generation equation supplies the original finite
`Generates` input, hence can be composed with the proved rules 1 and 2. -/
theorem FSGenerates.toGenerates {f : PresMorFS ρ τ} (hf : FSGenerates f) :
    Generates f.toPresMor := by
  intro y hy
  let z : J' →₀ MonoidAlgebra ℤ (PresGroup τ) :=
    (Finsupp.linearEquivFunOnFinite
      (MonoidAlgebra ℤ (PresGroup τ)) (MonoidAlgebra ℤ (PresGroup τ)) J').symm y
  have hz : FSIsFoxCycle τ z := (fsIsFoxCycle_iff z).mpr hy
  have hspan := hf z hz
  change (z : J' → MonoidAlgebra ℤ (PresGroup τ)) ∈
    Submodule.span (MonoidAlgebra ℤ (PresGroup τ))
      {w | ∃ x, IsFoxCycle ρ x ∧ w = f.toPresMor.cells x}
  clear hy hz
  generalize z = z' at hspan ⊢
  induction hspan using Submodule.span_induction with
  | mem w hw =>
      obtain ⟨x, hx, rfl⟩ := hw
      apply Submodule.subset_span
      exact ⟨x, (fsIsFoxCycle_iff x).mp hx, (f.toPresMor_cells_coe x).symm⟩
  | zero => exact Submodule.zero_mem _
  | add x w _ _ hx hw => exact Submodule.add_mem _ hx hw
  | smul a x _ hx => exact Submodule.smul_mem _ a hx

end FiniteDictionary

end FiniteChains
