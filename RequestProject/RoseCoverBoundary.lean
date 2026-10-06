module

public import RequestProject.RoseCoverIncidences

@[expose] public section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains.PresModel
open Comb
universe u
variable {α P : Type u} [PartialOrder P] (f : P → Rose α) (hf : IsPosetCover f)

/-- The midpoint boundary equation for the actual finite chain complex of a rose cover. -/
theorem roseCover_boundary_mid (v : P) (i : α) (hv : f v = Rose.mid i)
    (c : StrictOrdEdge P →₀ ℤ) :
    FiniteChains.Comb.bdry1 (strictOrderCx P) c v =
      -c (hf.strictEdgeLiftFrom (roseMidEdge i false) v hv) -
        c (hf.strictEdgeLiftFrom (roseMidEdge i true) v hv) := by
  classical
  let l := hf.strictEdgeLiftFrom (roseMidEdge i false) v hv
  let r := hf.strictEdgeLiftFrom (roseMidEdge i true) v hv
  have hl : l.1.1 = v := rfl
  have hr : r.1.1 = v := rfl
  have hne : l ≠ r := by
    intro h
    have hp := congrArg ((strictOrderCxMap f hf.strictMono).onE) h
    rw [hf.strictEdgeLiftFrom_projection, hf.strictEdgeLiftFrom_projection] at hp
    have hb := congrArg (fun e : StrictOrdEdge (Rose α) => e.1.2) hp
    cases hb
  change FiniteChains.Comb.bdry1 (strictOrderCx P) c v = -c l - c r
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd => simp only [map_add, Finsupp.add_apply, hc, hd]; ring
  | single e n =>
    rw [bdry1_single (X := strictOrderCx P)]
    have ht := roseCover_mid_no_incoming f hf v i hv e
    by_cases he : e = l
    · subst e
      simp [strictOrderCx, ht, hl, hne.symm]
    · by_cases her : e = r
      · subst e
        simp [strictOrderCx, ht, hr, hne]
      · have hs : e.1.1 ≠ v := by
          intro h
          exact (roseCover_mid_outgoing_edge_cases f hf v i hv e h).elim he her
        simp [strictOrderCx, ht, hs, he, her]

/-- The edge-end boundary equation for the actual finite chain complex of a rose cover. -/
theorem roseCover_boundary_end (q : P) (i : α) (b : Bool) (hq : f q = Rose.edg i b)
    (c : StrictOrdEdge P →₀ ℤ) :
    FiniteChains.Comb.bdry1 (strictOrderCx P) c q =
      c (hf.strictEdgeLiftTo (roseBaseEdge i b) q hq) +
        c (hf.strictEdgeLiftTo (roseMidEdge i b) q hq) := by
  classical
  let l := hf.strictEdgeLiftTo (roseBaseEdge i b) q hq
  let r := hf.strictEdgeLiftTo (roseMidEdge i b) q hq
  have hl : l.1.2 = q := rfl
  have hr : r.1.2 = q := rfl
  have hne : l ≠ r := by
    intro h
    have hp := congrArg ((strictOrderCxMap f hf.strictMono).onE) h
    rw [hf.strictEdgeLiftTo_projection, hf.strictEdgeLiftTo_projection] at hp
    have hb := congrArg (fun e : StrictOrdEdge (Rose α) => e.1.1) hp
    cases hb
  change FiniteChains.Comb.bdry1 (strictOrderCx P) c q = c l + c r
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd => simp only [map_add, Finsupp.add_apply, hc, hd]; ring
  | single e n =>
    rw [bdry1_single (X := strictOrderCx P)]
    have hs := roseCover_end_no_outgoing f hf q i b hq e
    by_cases he : e = l
    · subst e
      simp [strictOrderCx, hs, hl, hne.symm]
    · by_cases her : e = r
      · subst e
        simp [strictOrderCx, hs, hr, hne]
      · have ht : e.1.2 ≠ q := by
          intro h
          exact (roseCover_incoming_edge_cases f hf q i b hq e h).elim he her
        simp [strictOrderCx, ht, hs, he, her]

/-- A genuine finite one-cycle is determined by its midpoint-to-true-end incidences. -/
theorem roseCover_cycle_eq_zero (c : StrictOrdEdge P →₀ ℤ)
    (hc : FiniteChains.Comb.bdry1 (strictOrderCx P) c = 0)
    (hz : ∀ (e : StrictOrdEdge P) (i : α),
      (strictOrderCxMap f hf.strictMono).onE e = roseMidEdge i true → c e = 0) : c = 0 := by
  have hm : ∀ (e : StrictOrdEdge P) (i : α) (b : Bool),
      (strictOrderCxMap f hf.strictMono).onE e = roseMidEdge i b → c e = 0 := by
    intro e i b he
    cases b with
    | true => exact hz e i he
    | false =>
      have hv : f e.1.1 = Rose.mid i :=
        congrArg (fun r : StrictOrdEdge (Rose α) => r.1.1) he
      have hl := hf.strictEdgeLiftFrom_unique (roseMidEdge i false) e.1.1 hv e he rfl
      have hr := hz (hf.strictEdgeLiftFrom (roseMidEdge i true) e.1.1 hv) i
        (hf.strictEdgeLiftFrom_projection _ _ _)
      have hb := roseCover_boundary_mid f hf e.1.1 i hv c
      rw [hc, Finsupp.zero_apply, ← hl, hr] at hb
      omega
  ext e
  obtain ⟨i, b, he⟩ := rose_strict_edge_cases ((strictOrderCxMap f hf.strictMono).onE e)
  rcases he with he | he
  · have hq : f e.1.2 = Rose.edg i b :=
      congrArg (fun r : StrictOrdEdge (Rose α) => r.1.2) he
    have hl := hf.strictEdgeLiftTo_unique (roseBaseEdge i b) e.1.2 hq e he rfl
    have hr := hm (hf.strictEdgeLiftTo (roseMidEdge i b) e.1.2 hq) i b
      (hf.strictEdgeLiftTo_projection _ _ _)
    have hb := roseCover_boundary_end f hf e.1.2 i b hq c
    rw [hc, Finsupp.zero_apply, ← hl, hr] at hb
    simpa using hb.symm
  · exact hm e i b he

/-- Equality of the selected actual incidence coefficients detects equality of one-cycles. -/
theorem roseCover_cycle_ext (c d : StrictOrdEdge P →₀ ℤ)
    (hc : FiniteChains.Comb.bdry1 (strictOrderCx P) c = 0) (hd : FiniteChains.Comb.bdry1 (strictOrderCx P) d = 0)
    (h : ∀ (e : StrictOrdEdge P) (i : α),
      (strictOrderCxMap f hf.strictMono).onE e = roseMidEdge i true → c e = d e) :
    c = d := by
  apply sub_eq_zero.mp
  apply roseCover_cycle_eq_zero f hf (c - d)
  · rw [map_sub, hc, hd, sub_self]
  · intro e i he
    simp only [Finsupp.sub_apply, h e i he, sub_self]

end FiniteChains.PresModel
