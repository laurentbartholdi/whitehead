module

public import RequestProject.PresPosetPartialOrder
public import RequestProject.StrictOrderChains

@[expose] public section

namespace FiniteChains.PresModel
open Comb
universe u
variable {α J : Type u} (w : J → List (α × Bool))

/-- Valid attaching-circle positions are downward closed in the actual circle order. -/
theorem tCirc_valid_down {x y : TCirc w} (hxy : x ≤ y)
    (hy : y.2.1 < (w y.1).length) :
    x.1 = y.1 ∧ x.2.1 < (w y.1).length := by
  change x = y ∨ TCirc.lt w x y at hxy
  rcases hxy with rfl | hxy
  · exact ⟨rfl, hy⟩
  obtain ⟨j, k, t⟩ := x
  obtain ⟨j', k', t'⟩ := y
  obtain ⟨hj, hk', htags⟩ := hxy
  subst j'
  refine ⟨rfl, ?_⟩
  rcases htags with ⟨_, _, hk⟩ | ⟨_, _, hk⟩ | ⟨_, _, hk⟩ | ⟨_, _, hk⟩
  · exact hk ▸ hk'
  · exact hk ▸ hk'
  · exact hk ▸ hk'
  · rw [hk]
    exact Nat.mod_lt _ (by omega)

/-- The strict old interval below a relator apex consists exactly of its genuine
valid attaching-circle cells; no rose cell lies in that interval. -/
theorem presPos_le_apex_iff (j : J) (p : PresPos w) :
    p ≤ apexOf w j ↔ p = apexOf w j ∨
      ∃ k t, k < (w j).length ∧ p = iCirc w (TCirc.pt w j k t) := by
  constructor
  · intro h
    cases p with
    | inr j' => exact Or.inl (congrArg Sum.inr h)
    | inl p =>
      obtain ⟨r, ⟨k, t, hk, rfl⟩, hpr⟩ := h
      cases p with
      | inl r => exact hpr.elim
      | inr c =>
        have hc := tCirc_valid_down w hpr hk
        obtain ⟨j', k', t'⟩ := c
        change j' = j ∧ k' < (w j).length at hc
        obtain ⟨rfl, hc⟩ := hc
        exact Or.inr ⟨k', t', hc, rfl⟩
  · rintro (rfl | ⟨k, t, hk, rfl⟩)
    · exact le_refl _
    · exact iCirc_le_apexOf w t hk

theorem presPos_lt_apex_iff (j : J) (p : PresPos w) :
    p < apexOf w j ↔ ∃ k t, k < (w j).length ∧ p = iCirc w (TCirc.pt w j k t) := by
  constructor
  · intro h
    rcases (presPos_le_apex_iff w j p).mp h.le with he | he
    · exact ((ne_of_lt h) he).elim
    · exact he
  · rintro ⟨k, t, hk, rfl⟩
    apply lt_of_le_of_ne (iCirc_le_apexOf w t hk)
    exact Sum.inl_ne_inr

theorem iCirc_strictMono : StrictMono (iCirc w) := by
  intro x y h
  apply lt_of_le_of_ne ((iCirc_monotone w) h.le)
  intro he
  exact (ne_of_lt h) (Sum.inr.inj (Sum.inl.inj he))

/-- Actual cone triangles are the cones on valid attaching-circle edges. -/
def relatorConeTriangle (e : StrictOrdEdge (TCirc w))
    (hv : e.1.2.2.1 < (w e.1.2.1).length) : StrictOrdTri (PresPos w) :=
  ⟨(iCirc w e.1.1, iCirc w e.1.2, apexOf w e.1.2.1), iCirc_strictMono w e.2,
    (presPos_lt_apex_iff w e.1.2.1 (iCirc w e.1.2)).mpr
      ⟨e.1.2.2.1, e.1.2.2.2, hv, rfl⟩⟩

theorem exists_relatorConeTriangle (t : StrictOrdTri (PresPos w)) (j : J)
    (ht : t.1.2.2 = apexOf w j) :
    ∃ (e : StrictOrdEdge (TCirc w)) (hv : e.1.2.2.1 < (w e.1.2.1).length),
      relatorConeTriangle w e hv = t := by
  have h1 : t.1.2.1 < apexOf w j := ht ▸ t.2.2
  have h0 : t.1.1 < apexOf w j := t.2.1.trans h1
  obtain ⟨k0, s0, _, he0⟩ := (presPos_lt_apex_iff w j _).mp h0
  obtain ⟨k1, s1, hk1, he1⟩ := (presPos_lt_apex_iff w j _).mp h1
  have he : TCirc.pt w j k0 s0 < TCirc.pt w j k1 s1 := by
    have h := t.2.1
    rw [he0, he1] at h
    exact h
  let e : StrictOrdEdge (TCirc w) := ⟨(TCirc.pt w j k0 s0, TCirc.pt w j k1 s1), he⟩
  refine ⟨e, hk1, ?_⟩
  apply Subtype.ext
  exact Prod.ext he0.symm (Prod.ext he1.symm ht.symm)

/-- The only strict circle edges are the four incidences for a valid letter position. -/
theorem tCirc_strict_edge_cases (e : StrictOrdEdge (TCirc w)) :
    ∃ j k, k < (w j).length ∧
      (e.1 = (TCirc.pt w j k CPos.cor, TCirc.pt w j k CPos.cedgL) ∨
       e.1 = (TCirc.pt w j k CPos.cmid, TCirc.pt w j k CPos.cedgL) ∨
       e.1 = (TCirc.pt w j k CPos.cmid, TCirc.pt w j k CPos.cedgR) ∨
       e.1 = (TCirc.pt w j (TCirc.csucc w j k) CPos.cor, TCirc.pt w j k CPos.cedgR)) := by
  rcases e with ⟨⟨⟨j, k, s⟩, ⟨j', k', s'⟩⟩, h⟩
  have hn := ne_of_lt h
  have hl := h.le
  change (j, k, s) = (j', k', s') ∨ TCirc.lt w (j, k, s) (j', k', s') at hl
  rcases hl with he | hl
  · exact (hn he).elim
  obtain ⟨hj, hk', htags⟩ := hl
  subst j'
  refine ⟨j, k', hk', ?_⟩
  rcases htags with ⟨hs, hs', hk⟩ | ⟨hs, hs', hk⟩ | ⟨hs, hs', hk⟩ | ⟨hs, hs', hk⟩
  · subst s; subst s'; subst k
    exact Or.inl rfl
  · subst s; subst s'; subst k
    exact Or.inr (Or.inl rfl)
  · subst s; subst s'; subst k
    exact Or.inr (Or.inr (Or.inl rfl))
  · subst s; subst s'; subst k
    exact Or.inr (Or.inr (Or.inr rfl))

end FiniteChains.PresModel
