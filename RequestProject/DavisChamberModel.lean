module

public import RequestProject.MirrorSimplyConnected

@[expose] public section

/-!
# The concrete chamber model of the Davis complex, and its chamber intersections

This file builds the complex `𝒟` of the chamber argument *as an explicit poset*, so that the
chamber intersection formula becomes a statement about actual subcomplexes rather than an
interface hypothesis.

The model is the poset of **spherical cosets**: pairs `(w W_T, T)` where `T` is a simplex of `L`
(a clique of the commutation graph) and `w W_T` is a coset of the special subgroup `W_T`, ordered
by inclusion of cosets.  Each coset is represented by its unique shortest element
(`FiniteChains.RACG.existsUnique_shortest_coset`), so no quotient construction is needed:

* `FiniteChains.Davis.Sph A` — the poset; `Sph.rep` is the shortest element, `Sph.spx` the
  simplex; the order is `p ≤ q ↔ p.spx ⊆ q.spx ∧ p.rep⁻¹ q.rep ∈ W_{q.spx}`.

The order complex of this poset is `𝒟`: its vertices are the spherical cosets, i.e. exactly the
cells `w W_T` of the Davis complex, and a chain of the poset is a simplex of the barycentric
subdivision.  Two functors of the project are available on any poset and are used here:
`FiniteChains.Comb.orderCx` (the two-skeleton, for `π₁`) and `FiniteChains.Nerve.Ch`
(the simplicial chain complex in *all* degrees, so that `∂₃` is kept and `H₂` is not disturbed
by truncation).

* `FiniteChains.Davis.Chamber A x` — the chamber `F_x`: the subposet of cosets containing `x`.
  It is isomorphic to the poset of all simplices of `L` (`FiniteChains.Davis.chamberOrderIso`),
  is a cone on its minimum `{x} = x W_∅`, hence its order complex is connected, simply connected
  (`chamber_simplyConnected`) and acyclic in all degrees (`chamber_exists_bdry_eq_of_cycle`).
* `FiniteChains.Davis.mem_earlier_chamber_iff` — **the chamber intersection formula for the
  actual subcomplexes**: a coset of the chamber `F_x` lies in some chamber `F_y` with `y ≠ x`
  and `ℓ(y) ≤ ℓ(x)` if and only if its simplex meets the descent set `D(x)`.  So
  `F_x ∩ ⋃_{earlier} F_y` is the subposet `ChamberInter A x`.
* `FiniteChains.Davis.chamberInterOrderIso` — that intersection is isomorphic to the poset
  `𝒫_{D(x)} = {σ ∈ L : σ ∩ D(x) ≠ ∅}` of `RequestProject/MirrorContraction.lean`; hence
  (`chamberInter_simplyConnected`, `chamberInter_exists_bdry_eq_of_cycle`,
  `chamberInter_isConnected`) it is nonempty, connected, simply connected and acyclic, by the
  contraction `ρ(σ) = σ ∩ D(x)` of the text, applied here directly inside the model.
-/

namespace FiniteChains
namespace Davis

open RACG Mirror

universe u

variable {V : Type u} [DecidableEq V]

/-! ### The poset of spherical cosets -/

/-- **A spherical coset** of the right-angled Coxeter group: a simplex `T` of `L` together with
a coset of `W_T`, represented by its unique shortest element. -/
def Sph (A : CommRel V) : Type u :=
  {p : CayGroup A × Finset V // IsSimplex A p.2 ∧ ∀ s ∈ p.2, ¬ IsRDesc A p.1 s}

variable {A : CommRel V}

/-- The shortest element of the coset. -/
def Sph.rep (p : Sph A) : CayGroup A := p.1.1

/-- The simplex of `L` carried by the coset: its mirror type. -/
def Sph.spx (p : Sph A) : Finset V := p.1.2

theorem Sph.isSimplex (p : Sph A) : IsSimplex A p.spx := p.2.1

theorem Sph.no_rdesc (p : Sph A) : ∀ s ∈ p.spx, ¬ IsRDesc A p.rep s := p.2.2

theorem Sph.ext' {p q : Sph A} (hr : p.rep = q.rep) (hs : p.spx = q.spx) : p = q := by
  obtain ⟨⟨a, s⟩, hp⟩ := p
  obtain ⟨⟨b, t⟩, hq⟩ := q
  simp only [Sph.rep, Sph.spx] at hr hs
  subst hr
  subst hs
  rfl

omit [DecidableEq V] in
/-- A simplex of `L` is a commuting set of generators. -/
theorem commuting_of_isSimplex {σ : Finset V} (h : IsSimplex A σ) : Commuting A (σ : Set V) :=
  fun _ hs _ hr hne => h _ (Finset.mem_coe.1 hs) _ (Finset.mem_coe.1 hr) hne

theorem specialSub_mono {S T : Set V} (h : S ⊆ T) : specialSub A S ≤ specialSub A T :=
  Subgroup.closure_mono (Set.image_mono h)

/-- **The order of the Davis poset**: inclusion of cosets. -/
instance : PartialOrder (Sph A) where
  le p q := p.spx ⊆ q.spx ∧ p.rep⁻¹ * q.rep ∈ specialSub A (q.spx : Set V)
  le_refl p := ⟨Finset.Subset.refl _, by rw [inv_mul_cancel]; exact Subgroup.one_mem _⟩
  le_trans p q r hpq hqr := by
    refine ⟨hpq.1.trans hqr.1, ?_⟩
    have h1 : p.rep⁻¹ * q.rep ∈ specialSub A (r.spx : Set V) :=
      specialSub_mono (by exact_mod_cast hqr.1) hpq.2
    have h2 : p.rep⁻¹ * r.rep = (p.rep⁻¹ * q.rep) * (q.rep⁻¹ * r.rep) := by group
    rw [h2]
    exact Subgroup.mul_mem _ h1 hqr.2
  le_antisymm p q hpq hqp := by
    have hspx : p.spx = q.spx := Finset.Subset.antisymm hpq.1 hqp.1
    have hT : Commuting A (p.spx : Set V) := commuting_of_isSimplex p.isSimplex
    have huniq := existsUnique_shortest_coset A hT p.rep
    have hp : p.rep⁻¹ * p.rep ∈ specialSub A (p.spx : Set V) ∧
        ∀ s ∈ (p.spx : Set V), ¬ IsRDesc A p.rep s := by
      refine ⟨by rw [inv_mul_cancel]; exact Subgroup.one_mem _, ?_⟩
      intro s hs
      exact p.no_rdesc s (Finset.mem_coe.1 hs)
    have hq : p.rep⁻¹ * q.rep ∈ specialSub A (p.spx : Set V) ∧
        ∀ s ∈ (p.spx : Set V), ¬ IsRDesc A q.rep s := by
      refine ⟨by rw [hspx]; exact hpq.2, ?_⟩
      intro s hs
      exact q.no_rdesc s (hspx ▸ Finset.mem_coe.1 hs)
    have h1 := huniq.unique hp hq
    exact Sph.ext' h1 hspx

theorem Sph.le_def {p q : Sph A} :
    p ≤ q ↔ p.spx ⊆ q.spx ∧ p.rep⁻¹ * q.rep ∈ specialSub A (q.spx : Set V) := Iff.rfl

/-! ### Chambers -/

/-- The coset `p` contains the group element `x`: the corresponding cell of the Davis complex
lies in the chamber `F_x`. -/
def InChamber (x : CayGroup A) (p : Sph A) : Prop :=
  p.rep⁻¹ * x ∈ specialSub A (p.spx : Set V)

/-- **The chamber `F_x`** as a subposet of the Davis poset. -/
def Chamber (A : CommRel V) (x : CayGroup A) : Type u := {p : Sph A // InChamber x p}

instance (x : CayGroup A) : PartialOrder (Chamber A x) := Subtype.partialOrder _

@[simp] theorem Chamber.le_def {x : CayGroup A} (p q : Chamber A x) :
    p ≤ q ↔ p.1 ≤ q.1 := Iff.rfl

/-- Inside one chamber the order is just inclusion of simplices. -/
theorem le_of_inChamber {x : CayGroup A} {p q : Sph A} (hp : InChamber x p) (hq : InChamber x q)
    (h : p.spx ⊆ q.spx) : p ≤ q := by
  refine ⟨h, ?_⟩
  have h1 : p.rep⁻¹ * x ∈ specialSub A (q.spx : Set V) :=
    specialSub_mono (by exact_mod_cast h) hp
  have h2 : x⁻¹ * q.rep ∈ specialSub A (q.spx : Set V) := by
    have := Subgroup.inv_mem _ hq
    rwa [mul_inv_rev, inv_inv] at this
  have h3 : p.rep⁻¹ * q.rep = (p.rep⁻¹ * x) * (x⁻¹ * q.rep) := by group
  rw [h3]
  exact Subgroup.mul_mem _ h1 h2

/-- The unique cell of the chamber `F_x` with a given mirror type. -/
noncomputable def chamberPt (x : CayGroup A) {σ : Finset V} (hσ : IsSimplex A σ) : Sph A :=
  ⟨((existsUnique_shortest_coset A (commuting_of_isSimplex hσ) x).choose, σ),
    hσ, fun s hs => (existsUnique_shortest_coset A (commuting_of_isSimplex hσ) x).choose_spec.1.2
      s (Finset.mem_coe.2 hs)⟩

@[simp] theorem chamberPt_spx (x : CayGroup A) {σ : Finset V} (hσ : IsSimplex A σ) :
    (chamberPt x hσ).spx = σ := rfl

theorem chamberPt_inChamber (x : CayGroup A) {σ : Finset V} (hσ : IsSimplex A σ) :
    InChamber x (chamberPt x hσ) := by
  have h := (existsUnique_shortest_coset A (commuting_of_isSimplex hσ) x).choose_spec.1.1
  have := Subgroup.inv_mem _ h
  rw [mul_inv_rev, inv_inv] at this
  exact this

/-- **Uniqueness of the cell of a given type in a chamber.** -/
theorem eq_chamberPt {x : CayGroup A} {p : Sph A} (hp : InChamber x p) :
    p = chamberPt x p.isSimplex := by
  have hT : Commuting A (p.spx : Set V) := commuting_of_isSimplex p.isSimplex
  have huniq := existsUnique_shortest_coset A hT x
  have h1 : x⁻¹ * p.rep ∈ specialSub A (p.spx : Set V) ∧
      ∀ s ∈ (p.spx : Set V), ¬ IsRDesc A p.rep s := by
    refine ⟨?_, fun s hs => p.no_rdesc s (Finset.mem_coe.1 hs)⟩
    have := Subgroup.inv_mem _ hp
    rwa [mul_inv_rev, inv_inv] at this
  have h2 := (existsUnique_shortest_coset A hT x).choose_spec.1
  refine Sph.ext' ?_ rfl
  exact huniq.unique h1 h2

/-! ### The chamber is a cone -/

omit [DecidableEq V] in
theorem isSimplex_empty : IsSimplex A (∅ : Finset V) := by
  intro s hs
  exact absurd hs (by simp)

/-- The apex of the chamber `F_x`: the cell `x W_∅ = {x}`. -/
noncomputable def chamberApex (x : CayGroup A) : Chamber A x :=
  ⟨chamberPt x (isSimplex_empty (A := A)), chamberPt_inChamber x _⟩

theorem chamberApex_le {x : CayGroup A} (p : Chamber A x) : chamberApex x ≤ p :=
  le_of_inChamber (chamberApex x).2 p.2 (Finset.empty_subset _)

/-- **The chamber is simply connected**: its order complex is a cone on the apex. -/
theorem chamber_simplyConnected (x : CayGroup A) :
    Comb.SimplyConnected (Comb.orderCx (Chamber A x)) :=
  Comb.simplyConnected_orderCx (chamberApex x) (fun _ => chamberApex x)
    (fun p => chamberApex_le p) (fun _ => le_refl _) (fun _ => le_refl _)

/-- The chamber is connected. -/
theorem chamber_isConnected (x : CayGroup A) :
    Comb.IsConnected (Comb.orderCx (Chamber A x)) :=
  Comb.isConnected_orderCx (chamberApex x) (fun _ => chamberApex x)
    (fun p => chamberApex_le p) (fun _ => le_refl _)

/-- **The chamber is acyclic in all degrees**: every increasing cycle of its simplicial chain
complex, in every degree including the augmentation degree, is a boundary. -/
theorem chamber_exists_bdry_eq_of_cycle (x : CayGroup A) {c : Nerve.Ch (Chamber A x)}
    (hc : c ∈ Nerve.Inc (Chamber A x)) (hcyc : Nerve.bdry c = 0) :
    ∃ y ∈ Nerve.Inc (Chamber A x), Nerve.bdry y = c :=
  Nerve.exists_bdry_eq_of_cycle (fun _ => chamberApex x) (chamberApex x)
    (fun _ _ _ => le_refl _) (fun p => chamberApex_le p) (fun _ => le_refl _) hc hcyc

/-- **The chamber is the poset of all simplices of `L`.** -/
noncomputable def chamberOrderIso (x : CayGroup A) :
    Chamber A x ≃o {σ : Finset V // IsSimplex A σ} where
  toFun p := ⟨p.1.spx, p.1.isSimplex⟩
  invFun σ := ⟨chamberPt x σ.2, chamberPt_inChamber x σ.2⟩
  left_inv p := Subtype.ext (eq_chamberPt p.2).symm
  right_inv _ := Subtype.ext rfl
  map_rel_iff' {p q} := by
    constructor
    · intro h
      exact le_of_inChamber p.2 q.2 h
    · intro h
      exact h.1

/-! ### The intersection with the earlier chambers -/

section Inter

variable [Fintype V]

/-- **The chamber intersection formula for the actual subcomplexes.**  A cell of the chamber
`F_x` lies in some strictly earlier chamber (`y ≠ x`, `ℓ(y) ≤ ℓ(x)`) exactly when its mirror
type meets the descent set `D(x)`; that is,
`F_x ∩ ⋃_{earlier} F_y = ⋃_{s ∈ D(x)} (F_s)_x`. -/
theorem mem_earlier_chamber_iff {x : CayGroup A} {p : Sph A} (hp : InChamber x p) :
    (∃ y : CayGroup A, y ≠ x ∧ RACG.clen A y ≤ RACG.clen A x ∧ InChamber y p) ↔
      (p.spx ∩ rdescFinset A x).Nonempty := by
  have hT : Commuting A (p.spx : Set V) := commuting_of_isSimplex p.isSimplex
  have hkey := exists_rdesc_iff_exists_earlier A hT x
  constructor
  · rintro ⟨y, hne, hlen, hy⟩
    have hxy : x⁻¹ * y ∈ specialSub A (p.spx : Set V) := by
      have h1 : x⁻¹ * p.rep ∈ specialSub A (p.spx : Set V) := by
        have := Subgroup.inv_mem _ hp
        rwa [mul_inv_rev, inv_inv] at this
      have h2 : x⁻¹ * y = (x⁻¹ * p.rep) * (p.rep⁻¹ * y) := by group
      rw [h2]
      exact Subgroup.mul_mem _ h1 hy
    obtain ⟨s, hs, hsd⟩ := hkey.1 ⟨y, hxy, hne, hlen⟩
    exact ⟨s, Finset.mem_inter.2 ⟨Finset.mem_coe.1 hs, (mem_rdescFinset A).2 hsd⟩⟩
  · rintro ⟨s, hs⟩
    obtain ⟨hsσ, hsd⟩ := Finset.mem_inter.1 hs
    obtain ⟨y, hxy, hne, hlen⟩ := hkey.2 ⟨s, Finset.mem_coe.2 hsσ, (mem_rdescFinset A).1 hsd⟩
    refine ⟨y, hne, hlen, ?_⟩
    have h1 : p.rep⁻¹ * y = (p.rep⁻¹ * x) * (x⁻¹ * y) := by group
    rw [InChamber, h1]
    exact Subgroup.mul_mem _ hp hxy

/-- **The attaching subcomplex of the chamber `F_x`**: the part of `F_x` contained in the union
of the earlier chambers, by `FiniteChains.Davis.mem_earlier_chamber_iff`. -/
def ChamberInter (A : CommRel V) (x : CayGroup A) : Type u :=
  {p : Sph A // InChamber x p ∧ (p.spx ∩ rdescFinset A x).Nonempty}

instance (x : CayGroup A) : PartialOrder (ChamberInter A x) := Subtype.partialOrder _

/-- **The attaching subcomplex is the order complex of `𝒫_{D(x)}`.**  This is the transfer of
the coset formula to the actual subcomplexes of the model. -/
noncomputable def chamberInterOrderIso (x : CayGroup A) :
    ChamberInter A x ≃o MeetPoset (IsSimplex A) (rdescFinset A x) where
  toFun p := ⟨p.1.spx, p.1.isSimplex, p.2.2⟩
  invFun σ := ⟨chamberPt x σ.2.1, chamberPt_inChamber x σ.2.1, σ.2.2⟩
  left_inv p := Subtype.ext (eq_chamberPt p.2.1).symm
  right_inv _ := Subtype.ext rfl
  map_rel_iff' {p q} := by
    constructor
    · intro h
      exact le_of_inChamber p.2.1 q.2.1 h
    · intro h
      exact h.1

variable {x : CayGroup A}

/-- The descent set itself is a cell of the attaching subcomplex: the top vertex `D(x)`. -/
noncomputable def interTop (hx : x ≠ 1) : ChamberInter A x :=
  ⟨chamberPt x (isSimplex_rdescFinset A x), chamberPt_inChamber x _, by
    simp only [chamberPt_spx, Finset.inter_self]
    exact rdescFinset_nonempty A hx⟩

theorem interTop_spx (hx : x ≠ 1) : (interTop hx).1.spx = rdescFinset A x := rfl

/-- The contraction `ρ(σ) = σ ∩ D(x)` of the text, inside the model. -/
noncomputable def interRho (p : ChamberInter A x) : ChamberInter A x :=
  let hsubset : p.1.spx ∩ rdescFinset A x ⊆ p.1.spx := Finset.inter_subset_left
  let hsimplex := isSimplex_subset A hsubset p.1.isSimplex
  ⟨chamberPt x hsimplex,
    chamberPt_inChamber x hsimplex, by
      have hspx : (chamberPt x hsimplex).spx = p.1.spx ∩ rdescFinset A x :=
        chamberPt_spx x hsimplex
      rw [hspx]
      rw [Finset.inter_assoc, Finset.inter_self]
      exact p.2.2⟩

theorem interRho_spx (p : ChamberInter A x) :
    (interRho p).1.spx = p.1.spx ∩ rdescFinset A x := by
  dsimp only [interRho]
  exact chamberPt_spx x _

theorem interRho_le (p : ChamberInter A x) : interRho p ≤ p := by
  refine le_of_inChamber (interRho p).2.1 p.2.1 ?_
  rw [interRho_spx]
  exact Finset.inter_subset_left

theorem interRho_le_top (hx : x ≠ 1) (p : ChamberInter A x) : interRho p ≤ interTop hx := by
  refine le_of_inChamber (interRho p).2.1 (interTop hx).2.1 ?_
  rw [interRho_spx, interTop_spx]
  exact Finset.inter_subset_right

theorem interRho_mono {p q : ChamberInter A x} (h : p ≤ q) : interRho p ≤ interRho q := by
  have h1 : p.1.spx ⊆ q.1.spx := h.1
  refine le_of_inChamber (interRho p).2.1 (interRho q).2.1 ?_
  rw [interRho_spx, interRho_spx]
  exact fun a ha => Finset.mem_inter.2
    ⟨h1 (Finset.mem_inter.1 ha).1, (Finset.mem_inter.1 ha).2⟩

/-- **The attaching subcomplex of a chamber is simply connected**, proved inside the model by
the path contraction of `RequestProject/MirrorSimplyConnected.lean`. -/
theorem chamberInter_simplyConnected (hx : x ≠ 1) :
    Comb.SimplyConnected (Comb.orderCx (ChamberInter A x)) :=
  Comb.simplyConnected_orderCx (interTop hx) interRho interRho_le (interRho_le_top hx)
    (fun h => interRho_mono h)

/-- The attaching subcomplex is connected. -/
theorem chamberInter_isConnected (hx : x ≠ 1) :
    Comb.IsConnected (Comb.orderCx (ChamberInter A x)) :=
  Comb.isConnected_orderCx (interTop hx) interRho interRho_le (interRho_le_top hx)

/-- **The attaching subcomplex is acyclic in all degrees.** -/
theorem chamberInter_exists_bdry_eq_of_cycle (hx : x ≠ 1)
    {c : Nerve.Ch (ChamberInter A x)} (hc : c ∈ Nerve.Inc (ChamberInter A x))
    (hcyc : Nerve.bdry c = 0) :
    ∃ y ∈ Nerve.Inc (ChamberInter A x), Nerve.bdry y = c :=
  Nerve.exists_bdry_eq_of_cycle interRho (interTop hx) (fun _ _ h => interRho_mono h)
    interRho_le (interRho_le_top hx) hc hcyc

end Inter

end Davis
end FiniteChains
