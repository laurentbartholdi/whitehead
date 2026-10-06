module

public import RequestProject.DavisSimplyConnected

@[expose] public section

/-!
# The attaching intersection of a chamber is `J_w`, not the whole outer boundary

This file records, inside the concrete model of `RequestProject/DavisChamberModel.lean`, the
**corrected** form of the intersection formula that the gluing argument uses, and proves that
the two candidate subcomplexes really are different objects.

Write `D(w) = {s | ℓ(w s) < ℓ(w)}` for the descent set of `w` (`FiniteChains.RACG.rdescFinset`).

* `FiniteChains.Davis.MarkedMirror w s` — the marked mirror `(F_s)_w`: the cells of the chamber
  `F_w` whose mirror type contains `s`;
* `FiniteChains.Davis.JSet w` — `J_w = ⋃_{s ∈ D(w)} (F_s)_w`;
* `FiniteChains.Davis.OuterBdry w` — the whole outer boundary of the chamber, i.e. the cells of
  `F_w` of nonempty mirror type (a copy of the whole nerve `L`);
* `FiniteChains.Davis.mem_earlier_chamber_iff_jSet` — **the correct intersection formula**:
  `F_w ∩ ⋃_{earlier} F_v = J_w`, in the sharp form with ties in word length allowed, and
  `FiniteChains.Davis.mem_shorter_chamber_iff_jSet` for strictly shorter chambers;
* `FiniteChains.Davis.jSet_imp_outerBdry` — `J_w ⊆ ∂F_w`, and
  `FiniteChains.Davis.exists_outerBdry_not_jSet`, `FiniteChains.Davis.jSet_ne_outerBdry` —
  the inclusion is **strict** as soon as some vertex of `L` is not a descent of `w`; for
  `w = 1` the set `J_1` is empty while the outer boundary is not.  Hence the attaching
  intersection cannot be identified with the outer end of the cylinder: the outer end is a
  copy of the whole of `L`, whereas `J_w` is the union of the descending mirrors only, and it
  is exactly the latter that is contractible by the mirror contraction
  (`FiniteChains.Davis.chamberInter_simplyConnected`,
  `FiniteChains.Davis.chamberInter_exists_bdry_eq_of_cycle`).
-/

namespace FiniteChains
namespace Davis

open RACG Mirror

universe u

variable {V : Type u} [DecidableEq V] [Fintype V] {A : CommRel V}

/-- **The marked mirror `(F_s)_w`** of the chamber `F_w`: the cells of `F_w` whose mirror type
contains the generator `s`. -/
def MarkedMirror (w : CayGroup A) (s : V) (p : Sph A) : Prop :=
  InChamber w p ∧ s ∈ p.spx

/-- **`J_w = ⋃_{s ∈ D(w)} (F_s)_w`**: the union of the *descending* marked mirrors of the
chamber `F_w`. -/
def JSet (w : CayGroup A) (p : Sph A) : Prop :=
  ∃ s ∈ rdescFinset A w, MarkedMirror w s p

/-- **The whole outer boundary of the chamber `F_w`**: the cells of `F_w` of nonempty mirror
type.  This is a copy of the whole nerve `L`, and is the outer end of the cylinder in the
modified chamber. -/
def OuterBdry (w : CayGroup A) (p : Sph A) : Prop :=
  InChamber w p ∧ p.spx.Nonempty

theorem jSet_iff {w : CayGroup A} {p : Sph A} :
    JSet w p ↔ (InChamber w p ∧ (p.spx ∩ rdescFinset A w).Nonempty) := by
  constructor
  · rintro ⟨s, hs, hp, hsp⟩
    exact ⟨hp, ⟨s, Finset.mem_inter.2 ⟨hsp, hs⟩⟩⟩
  · rintro ⟨hp, s, hs⟩
    obtain ⟨hsp, hsd⟩ := Finset.mem_inter.1 hs
    exact ⟨s, hsd, hp, hsp⟩

theorem jSet_imp_outerBdry {w : CayGroup A} {p : Sph A} (h : JSet w p) : OuterBdry w p := by
  obtain ⟨s, _, hp, hsp⟩ := h
  exact ⟨hp, ⟨s, hsp⟩⟩

/-- `J_w` is upward closed inside the chamber. -/
theorem jSet_up {w : CayGroup A} {p q : Sph A} (hpq : p ≤ q) (hp : JSet w p) : JSet w q := by
  obtain ⟨s, hs, hpc, hsp⟩ := hp
  exact ⟨s, hs, inChamber_of_le hpq hpc, hpq.1 hsp⟩

/-- **The corrected intersection formula.**  For a cell of the chamber `F_w`, lying in some
other chamber `F_v` with `ℓ(v) ≤ ℓ(w)` — ties included — is equivalent to lying in
`J_w = ⋃_{s ∈ D(w)} (F_s)_w`.  So
`F_w ∩ ⋃_{v earlier} F_v = J_w`, *not* the whole outer boundary. -/
theorem mem_earlier_chamber_iff_jSet {w : CayGroup A} {p : Sph A} (hp : InChamber w p) :
    (∃ v : CayGroup A, v ≠ w ∧ RACG.clen A v ≤ RACG.clen A w ∧ InChamber v p) ↔ JSet w p := by
  rw [jSet_iff]
  constructor
  · intro h
    exact ⟨hp, (mem_earlier_chamber_iff hp).1 h⟩
  · rintro ⟨-, h⟩
    exact (mem_earlier_chamber_iff hp).2 h

/-- The same formula with strictly shorter chambers. -/
theorem mem_shorter_chamber_iff_jSet {w : CayGroup A} {p : Sph A} (hp : InChamber w p) :
    (∃ v : CayGroup A, RACG.clen A v < RACG.clen A w ∧ InChamber v p) ↔ JSet w p := by
  rw [jSet_iff]
  constructor
  · intro h
    exact ⟨hp, (mem_shorter_chamber_iff hp).1 h⟩
  · rintro ⟨-, h⟩
    exact (mem_shorter_chamber_iff hp).2 h

/-! ### The apex of a chamber -/

omit [Fintype V] in
theorem specialSub_empty : specialSub A (∅ : Set V) = ⊥ := by
  rw [specialSub, Set.image_empty, Subgroup.closure_empty]

omit [Fintype V] in
/-- The apex of the chamber `F_g` is the cell `{g}`: its representative is `g` itself. -/
theorem chamberPt_empty_rep (g : CayGroup A) :
    (chamberPt g (isSimplex_empty (A := A))).rep = g := by
  have h := chamberPt_inChamber g (isSimplex_empty (A := A))
  have h1 : (chamberPt g (isSimplex_empty (A := A))).rep⁻¹ * g ∈
      specialSub A ((∅ : Finset V) : Set V) := h
  rw [Finset.coe_empty, specialSub_empty, Subgroup.mem_bot] at h1
  exact inv_mul_eq_one.1 h1

/-! ### The outer boundary is strictly bigger than `J_w` -/

omit [DecidableEq V] [Fintype V] in
theorem isSimplex_singleton (s : V) : IsSimplex A {s} := by
  intro a ha b hb hab
  rw [Finset.mem_singleton] at ha hb
  exact absurd (ha.trans hb.symm) hab

/-- **The two candidate attaching subcomplexes are different.**  If some generator `s` is not a
descent of `w`, then the vertex of the chamber `F_w` of mirror type `{s}` lies in the outer
boundary but not in `J_w`. -/
theorem exists_outerBdry_not_jSet {w : CayGroup A} {s : V} (hs : ¬ IsRDesc A w s) :
    ∃ p : Sph A, OuterBdry w p ∧ ¬ JSet w p := by
  classical
  refine ⟨chamberPt w (isSimplex_singleton (A := A) s), ⟨chamberPt_inChamber w _, ?_⟩, ?_⟩
  · exact ⟨s, by simp⟩
  · rintro ⟨t, ht, -, htp⟩
    rw [chamberPt_spx, Finset.mem_singleton] at htp
    subst htp
    exact hs ((mem_rdescFinset A).1 ht)

/-- The same statement as an inequality of predicates. -/
theorem jSet_ne_outerBdry {w : CayGroup A} {s : V} (hs : ¬ IsRDesc A w s) :
    JSet (A := A) w ≠ OuterBdry (A := A) w := by
  intro h
  obtain ⟨p, hout, hnot⟩ := exists_outerBdry_not_jSet hs
  exact hnot (by rw [h]; exact hout)

/-- For the initial chamber `J_1` is empty, while its outer boundary is not (as soon as `L` has
a vertex).  This is the extreme case of the previous statement. -/
theorem jSet_one (p : Sph A) : ¬ JSet (1 : CayGroup A) p := by
  rintro ⟨s, hs, -, -⟩
  have h2 : RACG.clen A (1 * gen A s) < RACG.clen A (1 : CayGroup A) := (mem_rdescFinset A).1 hs
  rw [clen_one] at h2
  omega

theorem exists_outerBdry_one [Nonempty V] :
    ∃ p : Sph A, OuterBdry (1 : CayGroup A) p ∧ ¬ JSet (1 : CayGroup A) p := by
  classical
  obtain ⟨s⟩ := ‹Nonempty V›
  exact ⟨chamberPt 1 (isSimplex_singleton (A := A) s),
    ⟨chamberPt_inChamber 1 _, ⟨s, by simp⟩⟩, jSet_one _⟩

end Davis
end FiniteChains
