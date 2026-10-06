module

public import RequestProject.RACGSquareComplex
public import RequestProject.SquareComplexMonodromy
public import RequestProject.SquareComplexCoverExists

@[expose] public section

/-!
# The fundamental group of `C(L)` is the kernel of the parity map

The paper computes the fundamental group of the real moment-angle complex `C(L)`: it is the
kernel of the abelianisation `W_L → (ℤ/2)^{L⁰}` of the right-angled Coxeter group.  This file
proves that statement in the combinatorial category, for the edge-path group
`FiniteChains.SquareComplex.Pi1` of the square complex `C(L)`:

* `FiniteChains.RACG.kerPhi` — the kernel of the parity map, as a subgroup of `W_L`;
* `FiniteChains.RACG.liftEnd_deck` — the lift of a walk of `C(L)` is equivariant for the deck
  transformations, that is for left multiplication by elements of the kernel;
* `FiniteChains.RACG.pi1Equiv` — **the monodromy is a group isomorphism**
  `π₁(C(L)) ≃* ker(W_L → (ℤ/2)^{L⁰})`, and `FiniteChains.RACG.pi1_cubeCx_equiv` is the same
  statement with the base point written as the zero sign vector.

The proof uses the combinatorial covering theory of
`RequestProject/SquareComplexCovering.lean` (the parity map is a covering of square complexes,
`FiniteChains.RACG.isCovering_phi`), the simple connectivity of the Cayley complex and the
monodromy bijection of `RequestProject/SquareComplexMonodromy.lean`.
-/

namespace FiniteChains
namespace RACG

open SquareComplex

universe u

variable {V : Type u} [DecidableEq V] (A : CommRel V)

/-- The kernel of the parity homomorphism `W_L → (ℤ/2)^{L⁰}`, as a subgroup. -/
noncomputable def kerPhi : Subgroup (CayGroup A) where
  carrier := {x | phi A x = 0}
  mul_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq] at ha hb ⊢
    rw [phi_mul, ha, hb, add_zero]
  one_mem' := by simp [Set.mem_setOf_eq]
  inv_mem' := by
    intro a ha
    simp only [Set.mem_setOf_eq] at ha ⊢
    rw [phi_inv, ha]

@[simp] theorem mem_kerPhi {x : CayGroup A} : x ∈ kerPhi A ↔ phi A x = 0 := Iff.rfl

variable (hdim : ∀ t : Finset V, (∀ s ∈ t, ∀ r ∈ t, s ≠ r → A.rel s r) → t.card ≤ 3)

/-- The covering of square complexes given by the parity map. -/
noncomputable abbrev coveringPhi :
    SquareComplex.IsCovering ((cayleyMedianSimpleGraph A hdim).toSquareComplex) (cubeCx A)
      (phi A) := isCovering_phi A hdim

/-- Left multiplication by an element of the kernel commutes with lifting edges. -/
theorem edgeLift_deck {k x : CayGroup A} (hk : phi A k = 0) {v : V → ZMod 2}
    (h : (cubeCx A).adj (phi A x) v) :
    (coveringPhi A hdim).edgeLift (k * x) v = k * (coveringPhi A hdim).edgeLift x v := by
  have hp := coveringPhi A hdim
  obtain ⟨hxy, hpy⟩ := hp.edgeLift_spec h
  have hkx : phi A (k * x) = phi A x := phi_deck A hk
  have h' : (cubeCx A).adj (phi A (k * x)) v := by rw [hkx]; exact h
  obtain ⟨hxy', hpy'⟩ := hp.edgeLift_spec h'
  refine hp.edge_unique hxy' (deck_adj A k hxy) ?_
  rw [hpy', phi_deck A hk, hpy]

/-- **The lift of a walk is equivariant** for the deck transformations of the covering: left
multiplication by an element of the kernel of the parity map. -/
theorem liftEnd_deck {k : CayGroup A} (hk : phi A k = 0) :
    ∀ {b c : V → ZMod 2} (w : (toSimpleGraph (cubeCx A)).Walk b c) (x : CayGroup A),
      phi A x = b →
      (coveringPhi A hdim).liftEnd w (k * x) = k * (coveringPhi A hdim).liftEnd w x := by
  intro b c w
  induction w with
  | nil => intro x _; rfl
  | @cons b' v c' hadj q ih =>
      intro x hx
      have hadj' : (cubeCx A).adj (phi A x) v := by rw [hx]; exact hadj
      have hstep := edgeLift_deck A hdim hk hadj'
      rw [IsCovering.liftEnd_cons, IsCovering.liftEnd_cons, hstep]
      exact ih _ ((coveringPhi A hdim).edgeLift_spec hadj').2

/-- The monodromy of a closed walk of `C(L)` lies in the kernel of the parity map. -/
theorem monodromy_mem (g : (cubeCx A).Pi1 (phi A (1 : CayGroup A))) :
    (coveringPhi A hdim).monodromy 1 g ∈ kerPhi A := by
  have h := (coveringPhi A hdim).monodromy_mem_fibre 1 g
  simpa using h.trans (phi_one A)

/-- **The monodromy homomorphism** from the fundamental group of `C(L)` to the kernel of the
parity map. -/
noncomputable def monoHom :
    (cubeCx A).Pi1 (phi A (1 : CayGroup A)) →* kerPhi A where
  toFun g := ⟨(coveringPhi A hdim).monodromy 1 g, monodromy_mem A hdim g⟩
  map_one' := by
    refine Subtype.ext ?_
    simp
  map_mul' := by
    refine Quotient.ind fun w => Quotient.ind fun w' => ?_
    refine Subtype.ext ?_
    have hk : phi A ((coveringPhi A hdim).liftEnd w 1) = 0 := by
      have := monodromy_mem A hdim (Pi1.mk w)
      simpa using this
    show (coveringPhi A hdim).liftEnd (w.append w') 1
        = (coveringPhi A hdim).liftEnd w 1 * (coveringPhi A hdim).liftEnd w' 1
    rw [(coveringPhi A hdim).liftEnd_append]
    have hbase : phi A (1 : CayGroup A) = phi A (1 : CayGroup A) := rfl
    have := liftEnd_deck A hdim hk w' (1 : CayGroup A) (by rw [phi_one])
    rw [mul_one] at this
    exact this

/-- **The fundamental group of `C(L)` is the kernel of the parity map.**  The monodromy is a
group isomorphism from the edge-path group of the square complex `C(L)` onto
`ker(W_L → (ℤ/2)^{L⁰})`. -/
noncomputable def pi1Equiv :
    (cubeCx A).Pi1 (phi A (1 : CayGroup A)) ≃* kerPhi A := by
  refine MulEquiv.ofBijective (monoHom A hdim) ?_
  have hbij := (coveringPhi A hdim).monodromy_bijective (cayleyCx_walkConnected A hdim)
    ((cayleyMedianSimpleGraph A hdim).toSquareComplex_simplyConnectedW) (1 : CayGroup A)
  constructor
  · intro g g' h
    refine hbij.1 ?_
    exact Subtype.ext (congrArg Subtype.val h)
  · rintro ⟨z, hz⟩
    have hz' : phi A z = phi A (1 : CayGroup A) := by
      rw [phi_one]
      exact hz
    obtain ⟨g, hg⟩ := hbij.2 ⟨z, hz'⟩
    exact ⟨g, Subtype.ext (congrArg Subtype.val hg)⟩

include hdim in
/-- The same statement with the base point written as the zero sign vector, the base vertex of
`C(L)`. -/
theorem pi1_cubeCx_equiv :
    Nonempty ((cubeCx A).Pi1 (0 : V → ZMod 2) ≃* kerPhi A) :=
  ⟨(phi_one A) ▸ pi1Equiv A hdim⟩

include hdim in
/-- **Gromov's criterion for `C(L)`, applied to the universal cover constructed from homotopy
classes of walks**: the one-skeleton of the universal cover of `C(L)` is a median graph.  Here
the cover is no longer assumed to exist: it is the one built in
`RequestProject/SquareComplexCoverExists.lean`. -/
theorem univCover_cubeCx_median :
    ∃ M : MedianSimpleGraph (SquareComplex.UnivVx (cubeCx A) (0 : V → ZMod 2)),
      ∀ a b : SquareComplex.UnivVx (cubeCx A) (0 : V → ZMod 2),
        M.G.Adj a b ↔ (SquareComplex.univCover (cubeCx A) (0 : V → ZMod 2)).adj a b :=
  universal_cover_median A hdim (SquareComplex.isCovering_univProj (cubeCx A) 0)
    (SquareComplex.univCover_walkConnected (cubeCx A) 0)
    (SquareComplex.univCover_simplyConnectedW (cubeCx A) 0)
    (u₀ := SquareComplex.univBase (cubeCx A) 0) (x₀ := 1) (phi_one A).symm

end RACG
end FiniteChains
