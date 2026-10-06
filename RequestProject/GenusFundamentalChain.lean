import RequestProject.SurfaceFundamentalChain
import RequestProject.GenusSurface

/-! The oriented fundamental chain of the concrete genus polygon. -/

namespace FiniteChains.Davis
open Genus
variable (q : ℕ) [NeZero q]

omit [NeZero q] in
theorem genus_paired_parity {p n : Fin (8 * q)} (hne : p ≠ n)
    (he : gec q p = gec q n) : p.val % 2 ≠ n.val % 2 := by
  obtain ⟨h1, h2, h3⟩ := (gec_eq_iff' q p n).mp he
  intro hp
  apply hne
  apply Fin.ext
  split_ifs at h3 <;> omega

theorem genus_next_parity (p : Fin (8 * q)) :
    (p + 1).val % 2 = (p.val + 1) % 2 := by
  rw [fin_succ_val]
  have hp := p.isLt
  rcases Nat.lt_or_ge (p.val + 1) (8 * q) with h | h
  · rw [Nat.mod_eq_of_lt h]
  · have he : p.val + 1 = 8 * q := by omega
    rw [he, Nat.mod_self]
    omega

/-- The two occurrences of a paired side have opposite endpoints, with their orientations
fixed by the actual polygon labels. -/
theorem genus_paired_endpoints {p n : Fin (8 * q)} (hne : p ≠ n)
    (he : gec q p = gec q n) :
    gvc q p = gvc q (n + 1) ∧ gvc q (p + 1) = gvc q n := by
  have hpar := genus_paired_parity q hne he
  have hpnext := genus_next_parity q p
  have hnnext := genus_next_parity q n
  obtain ⟨h1, h2, _⟩ := (gec_eq_iff' q p n).mp he
  have hp := p.isLt
  have hn := n.isLt
  have hpn := fin_succ_val p
  have hnn := fin_succ_val n
  by_cases hp0 : p.val % 2 = 0
  · have hn1 : n.val % 2 = 1 := by omega
    constructor
    · rw [gvc_even q hp0, gvc_even q (by omega)]
    · rw [gvc_odd q (by omega), gvc_odd q (by omega)]
      congr 1
      apply Prod.ext
      · apply Fin.ext
        have hlt : p.val + 1 < 8 * q := by omega
        rw [Nat.mod_eq_of_lt hlt] at hpn
        dsimp
        omega
      · have hlt : p.val + 1 < 8 * q := by omega
        rw [Nat.mod_eq_of_lt hlt] at hpn
        dsimp
        exact Bool.decide_congr (by omega)
  · have hp1 : p.val % 2 = 1 := by omega
    have hn0 : n.val % 2 = 0 := by omega
    constructor
    · rw [gvc_odd q (by omega), gvc_odd q (by omega)]
      congr 1
      apply Prod.ext
      · apply Fin.ext
        have hlt : n.val + 1 < 8 * q := by omega
        rw [Nat.mod_eq_of_lt hlt] at hnn
        dsimp
        omega
      · have hlt : n.val + 1 < 8 * q := by omega
        rw [Nat.mod_eq_of_lt hlt] at hnn
        dsimp
        exact Bool.decide_congr (by omega)
    · rw [gvc_even q (by omega), gvc_even q hn0]

/-- The other occurrence of a side is chosen from the proved two-occurrence property. -/
noncomputable def genusSidePartner (p : Fin (8 * q)) : Fin (8 * q) :=
  Classical.choose (genus_pairs q p)

theorem genusSidePartner_spec (p : Fin (8 * q)) :
    genusSidePartner q p ≠ p ∧ gec q (genusSidePartner q p) = gec q p ∧
      ∀ k, gec q k = gec q p → k = p ∨ k = genusSidePartner q p :=
  Classical.choose_spec (genus_pairs q p)

theorem genusSidePartner_involutive : Function.Involutive (genusSidePartner q) := by
  intro p
  have h1 := genusSidePartner_spec q p
  have h2 := genusSidePartner_spec q (genusSidePartner q p)
  rcases h1.2.2 _ (h2.2.1.trans h1.2.1) with h | h
  · exact h
  · exact False.elim (h2.1 h)

theorem genus_paired_flagEdge (p : Fin (8 * q)) :
    flagEdge (cV (gc q) p) (cV (gc q) (p + 1)) (cE (gc q) p) +
      flagEdge (cV (gc q) (genusSidePartner q p))
        (cV (gc q) (genusSidePartner q p + 1))
        (cE (gc q) (genusSidePartner q p)) = 0 := by
  have hs := genusSidePartner_spec q p
  obtain ⟨hv, hw⟩ := genus_paired_endpoints q hs.1 hs.2.1
  unfold flagEdge cV cE
  rw [hs.2.1, hv, hw]
  abel

/-- An explicit integral two-cycle of the concrete triangulated genus surface. -/
noncomputable def genusFundamentalChain := polygonFundamentalChain (gc q)

theorem genusFundamentalChain_cycle : Nerve.bdry (genusFundamentalChain q) = 0 := by
  rw [genusFundamentalChain, bdry_polygonFundamentalChain]
  exact Finset.sum_ninvolution (genusSidePartner q) (genus_paired_flagEdge q)
    (fun p _ => (genusSidePartner_spec q p).1)
    (fun _ => Finset.mem_univ _) (genusSidePartner_involutive q)

theorem genusFundamentalChain_mem_inc :
    genusFundamentalChain q ∈ Nerve.Inc (SCell (gvc q) (gec q) (gc q)) :=
  polygonFundamentalChain_mem_inc (gc q)

theorem genusFundamentalChain_degree :
    Nerve.lengthProjection 3 (genusFundamentalChain q) = genusFundamentalChain q :=
  polygonFundamentalChain_degree (gc q)

theorem genusFundamentalChain_ne_zero : genusFundamentalChain q ≠ 0 := by
  apply polygonFundamentalChain_ne_zero (gc q)
  have := Nat.pos_of_neZero q
  omega

end FiniteChains.Davis
