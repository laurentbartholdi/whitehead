import RequestProject.ConeModel
import RequestProject.CubeMedianGraph

/-!
# The CAT(0) input of the capping argument: `H₂ = 0` from a cube-complex universal cover

`RequestProject/ConeModel.lean` reduced property (B3) of Theorem 3.2 to one hypothesis about
the cone model `C_q`: the vanishing of the second homology of its universal cover,

  `hH2 : ∀ x, M.IsCycle2 x → ∃ s c, ∀ g, x g = ∑ t ∈ s, c t * M.bdry t g`,

that is, every equivariant two-cycle over the group ring is an equivariant combination of the
boundaries of the three-cells.  The paper obtains it from the Cartan–Hadamard theorem: the
universal cover of `C_q` is a CAT(0) cube complex, hence contractible.

The project already contains the *combinatorial* form of that input, proved from scratch: in a
three-dimensional cube complex whose descending links satisfy the cube condition — in
particular in a cube complex with median one-skeleton — every cellular two-cycle with integer
coefficients is a boundary (`FiniteChains.DescCubeStr.exists_d₃_eq`,
`FiniteChains.MedianGraph.ker_d₂_eq_range_d₃`).

What was missing is the passage between the two statements: the chains of
`FiniteChains.DescCubeStr` are ordinary integral chains on the cells of the cover, while the
chains of a `FiniteChains.ConeModel` are group-ring chains on the cells of the model.  This
file supplies it, and thereby replaces the homological hypothesis of the capping argument by
the geometric input of the paper.

## The object

`FiniteChains.ConeModel.CubeCover M` is the datum of a realisation of the universal cover of
the model as a three-dimensional cube complex:

* a cube complex `S : DescCubeStr Vx`, whose `ker d₂ = im d₃` is the CAT(0) input (available as
  soon as the one-skeleton is a median graph, `FiniteChains.MedianGraph.toDescCubeStr`);
* an injection `cell₂` of the deck translates of the two-cells of the model into the squares of
  the complex and a bijection `cell₃` of the deck translates of its three-cells with the cubes
  of the complex: the cells of the cover are the translates of the cells of the model, the deck
  group acting freely;
* orientations `sgn₂`, `sgn₃` comparing the cellular orientation of a cell of the complex with
  the equivariant one of the model (the identification of two cellular chain complexes is only
  defined up to a sign on each cell; `sgn₂` is required to be invertible, i.e. non-zero);
* `bdry₃`: the cellular boundary of the cube `cell₃ (g, t)` is, up to its sign, the translate by
  `g` of the boundary of the three-cell `t` of the model, read through `cell₂`;
* `cycle`: a two-cycle of the model is read by `cell₂` as a cellular two-cycle of the complex.
  (Both chain complexes compute the homology of the same cover: the model is the cover of the
  two-skeleton after the collapse of a tree, which changes the cells only in degrees `0`
  and `1`.)

## What is proved

* `FiniteChains.ConeModel.toChain_injective` — the reading of group-ring chains as integral
  cellular chains is injective;
* `FiniteChains.ConeModel.CubeCover.exists_sum_bdry` — **`H₂ = 0` in the equivariant form**:
  every two-cycle of the model is a group-ring combination of the boundaries of its three-cells.
  The proof reads the cycle as an integral cellular two-cycle, applies the combinatorial
  Cartan–Hadamard theorem of `RequestProject/CubeCartanHadamard.lean`, and reads the resulting
  integral three-chain back as a group-ring vector of coefficients;
* `FiniteChains.ConeModel.CubeCover.isCockcroft`,
  `FiniteChains.isCockcroft_cappedBlock_of_cubeCover` — **property (B3) with the homological
  hypothesis replaced by the cube complex**, and
  `FiniteChains.ConeModel.isCockcroft_of_medianCover` — the same with the CAT(0) input in its
  proved combinatorial form: it suffices that the one-skeleton of the cover is a median graph;
* `FiniteChains.lemma_terminal_of_cubeCovers` — Lemma 3.10 with the blocks given by cone models
  whose universal covers are cube complexes.
-/

namespace FiniteChains

universe u

/-! ### Rescaling the coefficients of an integral chain cell by cell -/

/-- Multiply the coefficient at each cell by the orientation `σ` of that cell. -/
noncomputable def signScale {β : Type*} (σ : β → ℤ) (z : β →₀ ℤ) : β →₀ ℤ :=
  Finsupp.onFinset z.support (fun b => σ b * z b) (by
    intro b hb
    by_contra hbs
    exact hb (by simp [Finsupp.notMem_support_iff.1 hbs]))

@[simp] theorem signScale_apply {β : Type*} (σ : β → ℤ) (z : β →₀ ℤ) (b : β) :
    signScale σ z b = σ b * z b := rfl

theorem signScale_add {β : Type*} (σ : β → ℤ) (z w : β →₀ ℤ) :
    signScale σ (z + w) = signScale σ z + signScale σ w := by
  ext b; simp [mul_add]

theorem signScale_zero {β : Type*} (σ : β → ℤ) : signScale σ (0 : β →₀ ℤ) = 0 := by
  ext b; simp

theorem signScale_finset_sum {β ι : Type*} (σ : β → ℤ) (s : Finset ι) (z : ι → β →₀ ℤ) :
    signScale σ (∑ i ∈ s, z i) = ∑ i ∈ s, signScale σ (z i) := by
  classical
  induction s using Finset.induction with
  | empty => simp [signScale_zero]
  | insert a s ha ih => rw [Finset.sum_insert ha, signScale_add, ih, Finset.sum_insert ha]

theorem signScale_zsmul {β : Type*} (σ : β → ℤ) (a : ℤ) (z : β →₀ ℤ) :
    signScale σ (a • z) = a • signScale σ z := by
  ext b
  simp [mul_left_comm]

namespace ConeModel

variable {α J : Type u} [DecidableEq α] [Fintype J] {ρ : J → FreeGroup α}

section Chains

variable (M : ConeModel ρ) {Vx : Type u} [LinearOrder Vx] {S : DescCubeStr Vx}

/-- An equivariant two-chain of the model, read as an integral cellular two-chain of the cube
complex: the coefficient at the square `cell₂ (g, f)` is the coefficient of `g` in the
group-ring coordinate `x f`, times the orientation of that square. -/
noncomputable def toChain (cell₂ : PresGroup ρ × (J ⊕ M.Coll) → S.SqC) (sgn₂ : S.SqC → ℤ)
    (x : J ⊕ M.Coll → MonoidAlgebra ℤ (PresGroup ρ)) : S.SqC →₀ ℤ :=
  signScale sgn₂ (∑ f : J ⊕ M.Coll, Finsupp.mapDomain (fun g => cell₂ (g, f)) (x f).coeff)

variable {M}

omit [DecidableEq α] in
theorem injective_cell₂_fixed {cell₂ : PresGroup ρ × (J ⊕ M.Coll) → S.SqC}
    (hinj : Function.Injective cell₂) (f : J ⊕ M.Coll) :
    Function.Injective fun g => cell₂ (g, f) := by
  intro g₁ g₂ h
  exact congrArg Prod.fst (hinj h)

omit [DecidableEq α] in
/-- The coefficient of the integral chain at a cell of the cover. -/
theorem toChain_apply {cell₂ : PresGroup ρ × (J ⊕ M.Coll) → S.SqC} {sgn₂ : S.SqC → ℤ}
    (hinj : Function.Injective cell₂) (x : J ⊕ M.Coll → MonoidAlgebra ℤ (PresGroup ρ))
    (g : PresGroup ρ) (f : J ⊕ M.Coll) :
    M.toChain cell₂ sgn₂ x (cell₂ (g, f)) = sgn₂ (cell₂ (g, f)) * (x f).coeff g := by
  classical
  rw [toChain, signScale_apply]
  congr 1
  rw [Finsupp.finset_sum_apply, Finset.sum_eq_single f]
  · exact Finsupp.mapDomain_apply_of_injective (injective_cell₂_fixed hinj f) (x f).coeff g
  · intro f' _ hne
    refine Finsupp.mapDomain_notin_range _ _ ?_
    rintro ⟨g', hg'⟩
    exact hne (congrArg Prod.snd (hinj hg'))
  · intro h
    exact absurd (Finset.mem_univ f) h

omit [DecidableEq α] in
/-- Reading group-ring chains as integral cellular chains is injective. -/
theorem toChain_injective {cell₂ : PresGroup ρ × (J ⊕ M.Coll) → S.SqC} {sgn₂ : S.SqC → ℤ}
    (hinj : Function.Injective cell₂) (hsgn : ∀ Q, sgn₂ Q ≠ 0) :
    Function.Injective (M.toChain cell₂ sgn₂) := by
  intro x y hxy
  funext f
  ext g
  have h := congrArg (fun z => z (cell₂ (g, f))) hxy
  simp only [toChain_apply hinj] at h
  exact mul_left_cancel₀ (hsgn (cell₂ (g, f))) h

omit [DecidableEq α] in
theorem toChain_finset_sum {cell₂ : PresGroup ρ × (J ⊕ M.Coll) → S.SqC} {sgn₂ : S.SqC → ℤ}
    {ι : Type*} (s : Finset ι) (F : ι → J ⊕ M.Coll → MonoidAlgebra ℤ (PresGroup ρ)) :
    M.toChain cell₂ sgn₂ (fun f => ∑ p ∈ s, F p f)
      = ∑ p ∈ s, M.toChain cell₂ sgn₂ (F p) := by
  classical
  simp only [toChain, MonoidAlgebra.coeff_sum]
  rw [← signScale_finset_sum]
  congr 1
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun f _ => ?_
  exact Finsupp.mapDomain_finset_sum

omit [DecidableEq α] in
theorem toChain_zsmul {cell₂ : PresGroup ρ × (J ⊕ M.Coll) → S.SqC} {sgn₂ : S.SqC → ℤ} (a : ℤ)
    (x : J ⊕ M.Coll → MonoidAlgebra ℤ (PresGroup ρ)) :
    M.toChain cell₂ sgn₂ (fun f => a • x f) = a • M.toChain cell₂ sgn₂ x := by
  classical
  simp only [toChain, MonoidAlgebra.coeff_smul, ← signScale_zsmul]
  congr 1
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun f _ => ?_
  exact Finsupp.mapDomain_smul a (x f).coeff

end Chains

/-- **The universal cover of the cone model, realised as a cube complex.**  See the module
docstring for the meaning of the fields. -/
structure CubeCover (M : ConeModel ρ) where
  /-- The vertices of the cube complex realising the universal cover of the model. -/
  Vx : Type u
  [vxOrder : LinearOrder Vx]
  /-- The descending-cube structure: the combinatorial CAT(0) input. -/
  S : DescCubeStr Vx
  /-- The deck translates of the two-cells of the model, as squares of the complex. -/
  cell₂ : PresGroup ρ × (J ⊕ M.Coll) → S.SqC
  cell₂_inj : Function.Injective cell₂
  /-- The comparison of the orientation of a square with the equivariant one of the model. -/
  sgn₂ : S.SqC → ℤ
  sgn₂_ne : ∀ Q, sgn₂ Q ≠ 0
  /-- The deck translates of the three-cells of the model are exactly the cubes. -/
  cell₃ : PresGroup ρ × M.Three ≃ S.CbC
  /-- The comparison of the orientation of a cube with the equivariant one of the model. -/
  sgn₃ : PresGroup ρ × M.Three → ℤ
  /-- The boundary of a cube is the translated boundary of the three-cell of the model. -/
  bdry₃ : ∀ p : PresGroup ρ × M.Three, S.d₃ (Finsupp.single (cell₃ p) 1)
    = sgn₃ p • M.toChain cell₂ sgn₂ fun f => MonoidAlgebra.single p.1 (1 : ℤ) * M.bdry p.2 f
  /-- A two-cycle of the model is a cellular two-cycle of the complex. -/
  cycle : ∀ x, M.IsCycle2 x → S.d₂ (M.toChain cell₂ sgn₂ x) = 0

attribute [instance] CubeCover.vxOrder

namespace CubeCover

variable {M : ConeModel ρ}

/-- **`H₂ = 0` in the equivariant form.**  If the universal cover of the cone model is realised
as a three-dimensional cube complex satisfying the descending-cube condition — the combinatorial
form of the CAT(0) input of the paper — then every two-cycle of the model is a group-ring
combination of the boundaries of its three-cells. -/
theorem exists_sum_bdry (C : CubeCover M) {x : J ⊕ M.Coll → MonoidAlgebra ℤ (PresGroup ρ)}
    (hx : M.IsCycle2 x) :
    ∃ c : M.Three → MonoidAlgebra ℤ (PresGroup ρ), ∀ f, x f = ∑ t, c t * M.bdry t f := by
  classical
  obtain ⟨η, hη⟩ := C.S.exists_d₃_eq (M.toChain C.cell₂ C.sgn₂ x) (C.cycle x hx)
  set ν : (PresGroup ρ × M.Three) →₀ ℤ := Finsupp.equivMapDomain C.cell₃.symm η with hν
  have hηsum : η = ∑ p ∈ ν.support, Finsupp.single (C.cell₃ p) (ν p) := by
    have hmap : Finsupp.equivMapDomain C.cell₃ ν = η := by
      ext Q
      simp [hν, Finsupp.equivMapDomain_apply]
    calc
      η = Finsupp.mapDomain C.cell₃ ν := by
            rw [← hmap, Finsupp.equivMapDomain_eq_mapDomain]
      _ = ∑ p ∈ ν.support, Finsupp.single (C.cell₃ p) (ν p) := by
            rw [Finsupp.mapDomain]
            rfl
  refine ⟨fun t => ∑ p ∈ ν.support.filter fun p => p.2 = t,
    (ν p * C.sgn₃ p) • MonoidAlgebra.single p.1 (1 : ℤ), ?_⟩
  have key : M.toChain C.cell₂ C.sgn₂ x
      = M.toChain C.cell₂ C.sgn₂ fun f =>
          ∑ t, (∑ p ∈ ν.support.filter fun p => p.2 = t,
            (ν p * C.sgn₃ p) • MonoidAlgebra.single p.1 (1 : ℤ)) * M.bdry t f := by
    rw [← hη, hηsum, map_sum]
    have hstep : ∀ p ∈ ν.support, C.S.d₃ (Finsupp.single (C.cell₃ p) (ν p))
        = M.toChain C.cell₂ C.sgn₂ fun f =>
            (ν p * C.sgn₃ p) • (MonoidAlgebra.single p.1 (1 : ℤ) * M.bdry p.2 f) := by
      intro p _
      have h1 : Finsupp.single (C.cell₃ p) (ν p) = ν p • Finsupp.single (C.cell₃ p) (1 : ℤ) := by
        rw [Finsupp.smul_single, smul_eq_mul, mul_one]
      rw [h1, map_zsmul, C.bdry₃ p, smul_smul, ← toChain_zsmul]
    rw [Finset.sum_congr rfl hstep, ← toChain_finset_sum]
    congr 1
    funext f
    symm
    calc
      ∑ t, (∑ p ∈ ν.support.filter fun p => p.2 = t,
            (ν p * C.sgn₃ p) • MonoidAlgebra.single p.1 (1 : ℤ)) * M.bdry t f
          = ∑ t, ∑ p ∈ ν.support.filter fun p => p.2 = t,
              (ν p * C.sgn₃ p) • (MonoidAlgebra.single p.1 (1 : ℤ) * M.bdry p.2 f) := by
            refine Finset.sum_congr rfl fun t _ => ?_
            rw [Finset.sum_mul]
            refine Finset.sum_congr rfl fun p hp => ?_
            have hp2 : p.2 = t := (Finset.mem_filter.1 hp).2
            rw [smul_mul_assoc, hp2]
      _ = ∑ p ∈ ν.support, (ν p * C.sgn₃ p) •
            (MonoidAlgebra.single p.1 (1 : ℤ) * M.bdry p.2 f) :=
            Finset.sum_fiberwise _ _ _
  have := toChain_injective C.cell₂_inj C.sgn₂_ne key
  intro f
  exact congrFun this f

/-- **Property (B3) from a cube-complex cover.**  A presentation carrying a cone model whose
universal cover is realised as a three-dimensional cube complex with the descending-cube
property is Cockcroft: the homological hypothesis of `FiniteChains.ConeModel.isCockcroft` is now
a theorem. -/
theorem isCockcroft (C : CubeCover M) : IsCockcroft ρ := by
  refine M.isCockcroft ?_
  intro x hx
  obtain ⟨c, hc⟩ := C.exists_sum_bdry hx
  exact ⟨Finset.univ, c, hc⟩

end CubeCover

/-- **Property (B3) with the CAT(0) input in its proved combinatorial form.**  It suffices that
the one-skeleton of the universal cover of the cone model is a median graph: the descending-cube
structure is then `FiniteChains.MedianGraph.toDescCubeStr`. -/
theorem isCockcroft_of_medianCover {M : ConeModel ρ} {Vx : Type u} [LinearOrder Vx]
    (G : MedianGraph Vx)
    (cell₂ : PresGroup ρ × (J ⊕ M.Coll) → (G.toDescCubeStr).SqC)
    (cell₂_inj : Function.Injective cell₂)
    (sgn₂ : (G.toDescCubeStr).SqC → ℤ) (sgn₂_ne : ∀ Q, sgn₂ Q ≠ 0)
    (cell₃ : PresGroup ρ × M.Three ≃ (G.toDescCubeStr).CbC)
    (sgn₃ : PresGroup ρ × M.Three → ℤ)
    (bdry₃ : ∀ p : PresGroup ρ × M.Three, (G.toDescCubeStr).d₃ (Finsupp.single (cell₃ p) 1)
      = sgn₃ p • M.toChain cell₂ sgn₂ fun f => MonoidAlgebra.single p.1 (1 : ℤ) * M.bdry p.2 f)
    (cycle : ∀ x, M.IsCycle2 x → (G.toDescCubeStr).d₂ (M.toChain cell₂ sgn₂ x) = 0) :
    IsCockcroft ρ :=
  CubeCover.isCockcroft
    { Vx := Vx, S := G.toDescCubeStr, cell₂ := cell₂, cell₂_inj := cell₂_inj, sgn₂ := sgn₂,
      sgn₂_ne := sgn₂_ne, cell₃ := cell₃, sgn₃ := sgn₃, bdry₃ := bdry₃, cycle := cycle }

end ConeModel

/-! ### Property (B3) for the capped block, and Lemma 3.10 -/

variable {α J : Type u} [DecidableEq α] [Fintype J] {ρ : J → FreeGroup α}

variable {Kb D : Type u} [Fintype Kb] [Fintype D]

/-- **Property (B3) for the capped block, with the CAT(0) input replaced by the cube
complex.**  Compare `FiniteChains.isCockcroft_cappedBlock_of_coneModel`, where the vanishing of
the second homology of the universal cover is still a hypothesis. -/
theorem isCockcroft_cappedBlock_of_cubeCover (ρ : Kb ⊕ D → FreeGroup α) (M : ConeModel ρ)
    (C : ConeModel.CubeCover M) : IsCockcroft ρ :=
  C.isCockcroft

section Terminal

variable {P Q : PresPoint.{u}} {L : Type u} [Fintype L]
variable {S : Type u} [Fintype S] [DecidableEq S] {β K : S → Type u}
  [∀ s, DecidableEq (β s)] [∀ s, Fintype (K s)]

/-- **Lemma 3.10 with the blocks given by cube-complex cone models.**  The geometric input is
now only the cube complex structure on the universal cover of each block model; the vanishing of
its second homology is not assumed, it is proved. -/
theorem lemma_terminal_of_cubeCovers (t : TPath P Q) (ν : L → FreeGroup Q.gens)
    (hP : IsCockcroft P.rel)
    (hkill : ∀ a : P.gens,
      (addRelsMor Q.rel ν).hom (t.mor.hom (QuotientGroup.mk (FreeGroup.of a))) = 1)
    (blk : ∀ s, K s → FreeGroup (β s)) (M : ∀ s, ConeModel (blk s))
    (C : ∀ s, ConeModel.CubeCover (M s))
    (kappa : PresMor (addRels Q.rel ν) (sigmaWedgeRel blk))
    (hinj : ∀ v, IsFoxCycle (addRels Q.rel ν) v →
      (∀ p, augPres (sigmaWedgeRel blk) (kappa.cells v p) = 0) →
      ∀ m, augPres (addRels Q.rel ν) (v m) = 0) :
    IsCockcroft (addRels Q.rel ν) ∧
      (∀ v : Q.cells → MonoidAlgebra ℤ (PresGroup Q.rel), IsFoxCycle Q.rel v →
        (addRelsMor Q.rel ν).cells v = 0) ∧
      (∀ x : P.gens, (QuotientGroup.mk (FreeGroup.of x) : PresGroup P.rel) = 1 →
        t.mor.hom (QuotientGroup.mk (FreeGroup.of x)) = 1 ∧
          (addRelsMor Q.rel ν).hom (t.mor.hom (QuotientGroup.mk (FreeGroup.of x))) = 1) :=
  lemma_terminal_of_models t ν hP hkill blk M
    (fun s x hx => by
      obtain ⟨c, hc⟩ := (C s).exists_sum_bdry hx
      exact ⟨Finset.univ, c, hc⟩)
    kappa hinj

end Terminal

end FiniteChains
