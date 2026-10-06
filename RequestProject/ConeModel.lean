module

public import RequestProject.CappedBlock
public import RequestProject.CollapseChainMap

@[expose] public section

/-!
# The cone model `C_q` as a combinatorial object, and its dictionary with the Fox complex

This is the last link of the capping argument of property (B3) of Theorem 3.2.  Up to now the
argument used the cone model `C_q` of the paper through a *dictionary*, supplied as data: a
labelling of the two-cells of the model by the cells of the capped block, a way of reading a
Fox cycle as a two-chain of the model, and the compatibility of the two readings of the
boundary of the cone three-cell (`FiniteChains.exists_mul_coneChain_of_cubeModel`,
`FiniteChains.isCockcroft_cappedBlock_of_cubeModel`).

Here the model is *built* instead, as a combinatorial object over the presentation of its
spine, and the dictionary becomes a theorem.

## The object

A `FiniteChains.ConeModel ρ` for a presentation `ρ : J → FreeGroup α` consists of

* the two-cells removed by the collapse (`Coll`), each with its attaching word (`word`); the
  two-cells of the model are therefore `J ⊕ Coll`, those of the spine being `J`, attached
  along the relators of `ρ`;
* the requirement `word_mem` that each removed relator is a consequence of the relators of
  the spine.  This is what "the collapse does not change the fundamental group" means
  combinatorially; with it, `PresGroup ρ` *is* the fundamental group of the model and
  `MonoidAlgebra ℤ (PresGroup ρ)`-chains on the cells are the cellular chains of its
  universal cover (the cells of the cover are the cells of the model times the deck group).
  It is a well-definedness condition for reading the model's cover chains over `ℤ[G]`; the
  chain computations below do not use it;
* the three-cells (`Three`) with their equivariant boundaries (`bdry`), one of them being the
  cone cell (`cone`);
* a chain collapse (`steps`) which removes every three-cell except the cone cell
  (`collapsed`) and, as its free faces, only two-cells of `Coll` (`steps_faces`): this is
  Lemma 3.3 (ii), the collapse of `M_q` onto its two-dimensional spine, the surviving
  three-cell being the one created by coning the cut surface;
* the closedness condition `closed`: downstairs — i.e. after augmentation — the sum of the
  boundaries of all three-cells is zero.  The model `C_q` is the truncated cube complex
  `M_q` with the cone on its boundary surface `Σ_q` glued in, so it is a closed
  pseudo-manifold: every two-cell lies in exactly two three-cells, with opposite incidence
  numbers.

## The dictionary, proved

* `FiniteChains.ConeModel.isCycle2_chainOf` — **a Fox cycle of the spine presentation is a
  two-cycle of the model**: extended by zero over the collapsed cells, the Fox coordinates
  are precisely the coordinates of an equivariant two-chain of the universal cover, since the
  boundary of the two-cell `j` of the model is the Fox derivative row of the relator `ρ j`;
* `FiniteChains.ConeModel.augPres_coneBdry` — **the augmentation of the collapsed boundary of
  the cone cell vanishes**.  This is Lemma 3.3 (iii) in the form the capping argument needs
  it (the image of the fundamental class `[Σ_q]` in `H₂(M_q)` is zero) and it is here a
  consequence of closedness: downstairs the boundary of the cone cell is minus the sum of the
  boundaries of the three-cells of `M_q`, all of which are collapsed away, and a collapse
  kills the boundary of every cell it removes;
* `FiniteChains.ConeModel.exists_mul_coneBdry` — **asphericity in the form (B3) uses it**:
  if every two-cycle of the universal cover of the model bounds (`H₂ = 0`, the CAT(0) input,
  proved in the project for cube complexes with median one-skeleton), then every Fox cycle of
  the spine presentation is a group-ring multiple of the collapsed boundary of the cone cell;
* `FiniteChains.ConeModel.isCockcroft`, `FiniteChains.isCockcroft_cappedBlock_of_coneModel` —
  **property (B3)**: a presentation carrying a cone model with `H₂ = 0` is Cockcroft.  No
  dictionary is assumed any more: the only input is the vanishing of the second homology of
  the universal cover of the model;
* `FiniteChains.lemma_terminal_of_models` — Lemma 3.10 with the blocks presented by cone
  models.

A ring homomorphism commutes with the chain map of a collapse
(`FiniteChains.CollapseChain.map_cmap`), which is what lets the augmentation move the
computation from the universal cover to the complex itself.
-/

namespace FiniteChains

open MonoidAlgebra

/-! ### A ring homomorphism commutes with the chain map of a collapse -/

namespace CollapseChain

variable {T F R S : Type*} [Ring R] [Ring S]

theorem map_ring_inverse (φ : R →+* S) {u : R} (hu : IsUnit u) :
    φ (Ring.inverse u) = Ring.inverse (φ u) := by
  obtain ⟨v, rfl⟩ := hu
  have h1 : φ (v : R) = ((Units.map (φ : R →* S) v : Sˣ) : S) := rfl
  rw [Ring.inverse_unit, h1, Ring.inverse_unit]
  rfl

theorem map_retr (φ : R →+* S) (d : T → F → R) {t : T} {f : F} (hu : IsUnit (d t f))
    (x : F → R) (g : F) :
    φ (retr d t f x g) = retr (fun t f => φ (d t f)) t f (fun f => φ (x f)) g := by
  simp only [retr, map_sub, map_mul, map_ring_inverse φ hu]

/-- **A ring homomorphism commutes with the chain map of a collapse.**  Applied to the
augmentation `ℤ[G] → ℤ`, this transports a computation in the universal cover to the same
computation in the complex itself. -/
theorem map_cmap (φ : R →+* S) (d : T → F → R) :
    ∀ (l : List (T × F)), (∀ p ∈ l, IsUnit (d p.1 p.2)) → ∀ (x : F → R) (g : F),
      φ (cmap d l x g) = cmap (fun t f => φ (d t f)) l (fun f => φ (x f)) g
  | [], _, _, _ => rfl
  | (t, f) :: l, hu, x, g => by
      have hstep : (fun f' => φ (retr d t f x f'))
          = retr (fun t f => φ (d t f)) t f (fun f' => φ (x f')) := by
        funext f'
        exact map_retr φ d (hu (t, f) List.mem_cons_self) x f'
      show φ (cmap d l (retr d t f x) g) = cmap _ l (retr _ t f _) g
      rw [map_cmap φ d l (fun p hp => hu p (List.mem_cons_of_mem _ hp)) (retr d t f x) g, hstep]

/-- The image of a chain collapse under a ring homomorphism is a chain collapse. -/
theorem IsChainCollapse.map (φ : R →+* S) {d : T → F → R} :
    ∀ {l : List (T × F)}, IsChainCollapse d l → IsChainCollapse (fun t f => φ (d t f)) l
  | [], _ => trivial
  | (_, f) :: _, ⟨hunit, hfree, hrest⟩ =>
      ⟨hunit.map φ, fun p hp => show φ (d p.1 f) = 0 by rw [hfree p hp, map_zero],
        hrest.map φ⟩

theorem isUnit_of_mem_isChainCollapse {d : T → F → R} :
    ∀ {l : List (T × F)}, IsChainCollapse d l → ∀ p ∈ l, IsUnit (d p.1 p.2)
  | [], _, _, hp => absurd hp List.not_mem_nil
  | (t, f) :: l, ⟨hunit, _, hrest⟩, p, hp => by
      rcases List.mem_cons.1 hp with rfl | hpl
      · exact hunit
      · exact isUnit_of_mem_isChainCollapse hrest p hpl

end CollapseChain

/-! ### Fox coordinates of an arbitrary word -/

universe u

variable {α J : Type u} [DecidableEq α]

/-- The Fox coordinates of a word, read in the group ring of the presented group: the
coefficients of the boundary, in the universal cover, of a two-cell attached along `w`. -/
noncomputable def foxCoordPres (ρ : J → FreeGroup α) (w : FreeGroup α) (i : α) :
    MonoidAlgebra ℤ (PresGroup ρ) :=
  quotRingHom ℤ (relSub ρ) (fox i w)

theorem foxCoordPres_rel (ρ : J → FreeGroup α) (j : J) (i : α) :
    foxCoordPres ρ (ρ j) i = foxMatrixPres ρ i j := rfl

/-! ### The cone model -/

/-- **The cone model `C_q` as a combinatorial three-dimensional complex over the presentation
of its spine.**  See the module docstring for the meaning of the fields. -/
structure ConeModel [Fintype J] (ρ : J → FreeGroup α) where
  /-- The two-cells removed by the collapse. -/
  Coll : Type u
  [collFintype : Fintype Coll]
  /-- The three-cells. -/
  Three : Type u
  [threeFintype : Fintype Three]
  [threeDecEq : DecidableEq Three]
  /-- The attaching word of a removed two-cell. -/
  word : Coll → FreeGroup α
  /-- A removed relator is a consequence of the relators of the spine: the collapse does not
  change the fundamental group. -/
  word_mem : ∀ c, word c ∈ relSub ρ
  /-- The boundary of a three-cell of the universal cover, in the coordinates given by the
  two-cells of the model and the group ring of the deck group. -/
  bdry : Three → (J ⊕ Coll) → MonoidAlgebra ℤ (PresGroup ρ)
  /-- The three-cell created by coning the cut surface. -/
  cone : Three
  /-- The collapse of Lemma 3.3 (ii). -/
  steps : List (Three × (J ⊕ Coll))
  isCollapse : CollapseChain.IsChainCollapse bdry steps
  /-- Every three-cell but the cone cell is collapsed away. -/
  collapsed : ∀ t, t ≠ cone → ∃ f, (t, f) ∈ steps
  /-- The collapse removes only two-cells outside the spine. -/
  steps_faces : ∀ p ∈ steps, ∃ c, p.2 = Sum.inr c
  /-- Downstairs the model is closed: the sum of the boundaries of all three-cells is zero. -/
  closed : ∀ f, ∑ t, augPres ρ (bdry t f) = 0

namespace ConeModel

variable [Fintype J] {ρ : J → FreeGroup α} (M : ConeModel ρ)

attribute [instance] ConeModel.collFintype ConeModel.threeFintype ConeModel.threeDecEq

/-- The attaching word of a two-cell of the model: the relators of the spine on `J`, the
removed words on `Coll`. -/
def attach : J ⊕ M.Coll → FreeGroup α := Sum.elim ρ M.word

/-- The cellular boundary of an equivariant two-chain of the universal cover of the model: at
the one-cell `i` it is the sum of the coefficients times the Fox coordinates of the attaching
words. -/
noncomputable def bdry2 (x : J ⊕ M.Coll → MonoidAlgebra ℤ (PresGroup ρ)) (i : α) :
    MonoidAlgebra ℤ (PresGroup ρ) :=
  ∑ f, x f * foxCoordPres ρ (M.attach f) i

/-- A two-cycle of the universal cover of the model. -/
def IsCycle2 (x : J ⊕ M.Coll → MonoidAlgebra ℤ (PresGroup ρ)) : Prop :=
  ∀ i : α, M.bdry2 x i = 0

/-- **The dictionary**: a vector of Fox coordinates of the spine presentation, read as a
two-chain of the model by extending it by zero over the collapsed cells. -/
noncomputable def chainOf (v : J → MonoidAlgebra ℤ (PresGroup ρ)) :
    J ⊕ M.Coll → MonoidAlgebra ℤ (PresGroup ρ) :=
  Sum.elim v 0

omit [DecidableEq α] in
@[simp] theorem chainOf_inl (v : J → MonoidAlgebra ℤ (PresGroup ρ)) (j : J) :
    M.chainOf v (Sum.inl j) = v j := rfl

omit [DecidableEq α] in
@[simp] theorem chainOf_inr (v : J → MonoidAlgebra ℤ (PresGroup ρ)) (c : M.Coll) :
    M.chainOf v (Sum.inr c) = 0 := rfl

/-- **A Fox cycle of the spine presentation is a two-cycle of the model.**  This is the
identification of the cellular chains of the universal cover of the model with the Fox
coordinates: the boundary of the two-cell `j` is the `j`-th column of the Fox matrix. -/
theorem isCycle2_chainOf {v : J → MonoidAlgebra ℤ (PresGroup ρ)} (hv : IsFoxCycle ρ v) :
    M.IsCycle2 (M.chainOf v) := by
  intro i
  rw [bdry2, Fintype.sum_sum_type]
  have h1 : ∑ j : J, M.chainOf v (Sum.inl j) * foxCoordPres ρ (M.attach (Sum.inl j)) i
      = ∑ j : J, v j * foxMatrixPres ρ i j := rfl
  have h2 : ∑ c : M.Coll, M.chainOf v (Sum.inr c) * foxCoordPres ρ (M.attach (Sum.inr c)) i
      = 0 := Finset.sum_eq_zero fun c _ => by rw [chainOf_inr, zero_mul]
  rw [h1, h2, hv i, add_zero]

/-- The boundary of the cone three-cell after the collapse, read at the cells of the spine:
the chain of the two-skeleton which the capping argument uses. -/
noncomputable def coneBdry (j : J) : MonoidAlgebra ℤ (PresGroup ρ) :=
  CollapseChain.cmap M.bdry M.steps (M.bdry M.cone) (Sum.inl j)

omit [DecidableEq α] in
/-- **Lemma 3.3 (iii) in the model**: the ordinary (downstairs) boundary of the cone
three-cell vanishes after the collapse.  Since the model is closed, that boundary is minus the
sum of the boundaries of the three-cells of `M_q`; all of them are collapsed away, and the
chain map of a collapse kills the boundary of every cell it removes. -/
theorem augPres_coneBdry (j : J) : augPres ρ (M.coneBdry j) = 0 := by
  classical
  have hunits : ∀ p ∈ M.steps, IsUnit (M.bdry p.1 p.2) :=
    CollapseChain.isUnit_of_mem_isChainCollapse M.isCollapse
  have hmap := CollapseChain.map_cmap (augPres ρ) M.bdry M.steps hunits (M.bdry M.cone)
    (Sum.inl j)
  have hbound : ∀ g : J ⊕ M.Coll, augPres ρ (M.bdry M.cone g)
      = ∑ t ∈ Finset.univ.erase M.cone, (-1 : ℤ) * augPres ρ (M.bdry t g) := by
    intro g
    have h := M.closed g
    rw [← Finset.sum_erase_add Finset.univ _ (Finset.mem_univ M.cone)] at h
    have h' : ∑ t ∈ Finset.univ.erase M.cone, augPres ρ (M.bdry t g)
        = - augPres ρ (M.bdry M.cone g) := eq_neg_of_add_eq_zero_left h
    rw [← Finset.mul_sum, h', neg_one_mul, neg_neg]
  have hzero : CollapseChain.cmap (fun t f => augPres ρ (M.bdry t f)) M.steps
      (fun f => augPres ρ (M.bdry M.cone f)) = 0 :=
    CollapseChain.cmap_eq_zero_of_isBoundary (M.isCollapse.map (augPres ρ))
      (s := Finset.univ.erase M.cone) (c := fun _ => (-1 : ℤ))
      (fun t ht => M.collapsed t (Finset.ne_of_mem_erase ht)) hbound
  rw [coneBdry, hmap, hzero]
  rfl

/-- **Asphericity of the model, in the form the capping argument uses.**  If every two-cycle
of the universal cover of the model bounds — the vanishing of `H₂`, which for a CAT(0) cube
complex is the Cartan–Hadamard input of the paper — then every Fox cycle of the spine
presentation is a group-ring multiple of the collapsed boundary of the cone cell. -/
theorem exists_mul_coneBdry
    (hH2 : ∀ x, M.IsCycle2 x → ∃ (s : Finset M.Three) (c : M.Three → MonoidAlgebra ℤ (PresGroup ρ)),
      ∀ g, x g = ∑ t ∈ s, c t * M.bdry t g)
    {v : J → MonoidAlgebra ℤ (PresGroup ρ)} (hv : IsFoxCycle ρ v) :
    ∃ lam : MonoidAlgebra ℤ (PresGroup ρ), ∀ j, v j = lam * M.coneBdry j := by
  classical
  have hspine : ∀ p ∈ M.steps, M.chainOf v p.2 = 0 := by
    intro p hp
    obtain ⟨c, hc⟩ := M.steps_faces p hp
    rw [hc, chainOf_inr]
  obtain ⟨lam, hlam⟩ :=
    CollapseChain.exists_mul_bdry_of_cycles_bound M.isCollapse M.cone M.IsCycle2 hH2
      M.collapsed (M.isCycle2_chainOf hv) hspine
  exact ⟨lam, fun j => hlam (Sum.inl j)⟩

/-- **Property (B3) from a cone model.**  A presentation which carries a cone model whose
universal cover has vanishing second homology is Cockcroft.  Both geometric inputs of the
capping argument are now theorems of the model: the vanishing of the fundamental class of the
cut surface is `FiniteChains.ConeModel.augPres_coneBdry`, and asphericity enters only through
`H₂ = 0`. -/
theorem isCockcroft
    (hH2 : ∀ x, M.IsCycle2 x → ∃ (s : Finset M.Three) (c : M.Three → MonoidAlgebra ℤ (PresGroup ρ)),
      ∀ g, x g = ∑ t ∈ s, c t * M.bdry t g) :
    IsCockcroft ρ :=
  isCockcroft_of_single_threeCell M.coneBdry M.augPres_coneBdry
    fun _ hv => M.exists_mul_coneBdry hH2 hv

end ConeModel

/-! ### Property (B3) for the capped block -/

variable {Kb D : Type u} [Fintype Kb] [Fintype D]

/-- **Property (B3), with the dictionary discharged.**  The capped block `V_q` — the block
(`Kb`) together with the disks adjoined along the distinguished generators (`D`) — is
Cockcroft as soon as it carries a cone model of `C_q` whose universal cover has vanishing
second homology.  Compare `FiniteChains.isCockcroft_cappedBlock_of_cubeModel`, which needed in
addition the labelling of the cells of the model by the cells of the block and the two
readings of the boundary of the cone three-cell; here both are part of the model. -/
theorem isCockcroft_cappedBlock_of_coneModel (ρ : Kb ⊕ D → FreeGroup α) (M : ConeModel ρ)
    (hH2 : ∀ x, M.IsCycle2 x → ∃ (s : Finset M.Three) (c : M.Three → MonoidAlgebra ℤ (PresGroup ρ)),
      ∀ g, x g = ∑ t ∈ s, c t * M.bdry t g) :
    IsCockcroft ρ :=
  M.isCockcroft hH2

/-! ### Lemma 3.10 with the blocks presented by cone models -/

section Terminal

variable {P Q : PresPoint.{u}} {L : Type u} [Fintype L]
variable {S : Type u} [Fintype S] [DecidableEq S] {β K : S → Type u}
  [∀ s, DecidableEq (β s)] [∀ s, Fintype (K s)]

/-- **Lemma 3.10 with the cone models built.**  Each block factor is given with its cone
model, and (B3) for it is the theorem `FiniteChains.ConeModel.isCockcroft`; the geometry
enters only through the vanishing of the second homology of the universal cover of the
model. -/
theorem lemma_terminal_of_models (t : TPath P Q) (ν : L → FreeGroup Q.gens)
    (hP : IsCockcroft P.rel)
    (hkill : ∀ a : P.gens,
      (addRelsMor Q.rel ν).hom (t.mor.hom (QuotientGroup.mk (FreeGroup.of a))) = 1)
    (blk : ∀ s, K s → FreeGroup (β s)) (M : ∀ s, ConeModel (blk s))
    (hH2 : ∀ s, ∀ x, (M s).IsCycle2 x →
      ∃ (u : Finset (M s).Three) (c : (M s).Three → MonoidAlgebra ℤ (PresGroup (blk s))),
        ∀ g, x g = ∑ w ∈ u, c w * (M s).bdry w g)
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
  lemma_terminal_of_coneModels t ν hP hkill blk (fun s => (M s).coneBdry)
    (fun s => (M s).augPres_coneBdry)
    (fun s _ hv => (M s).exists_mul_coneBdry (hH2 s) hv) kappa hinj

end Terminal

end FiniteChains
