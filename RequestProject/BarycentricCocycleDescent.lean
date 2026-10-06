module

public import RequestProject.CmpNerve
public import RequestProject.OrderCocycleFlatSections

@[expose] public section

/-! Recover a nonabelian cocycle on a face poset from its actual subdivision. -/
namespace FiniteChains.Davis
open RACG Mirror Comb
open scoped Classical
universe u v w
variable {P : Type u} [PartialOrder P] [DecidableEq P]
  {G : Type v} [Group G] (c : OrdCocycle (NeSpx (cmpRel P)) G)

theorem edgeHop_comp_htpy {a b d : P} (hab : a ≤ b) (hbd : b ≤ d) :
    Htpy (orderCx (NeSpx (cmpRel P))) (spx1 a) (spx1 d)
      (edgeHop hab ++ edgeHop hbd) (edgeHop (hab.trans hbd)) := by
  apply htpy_of_loop_nil ((isPath_edgeHop hab).append (isPath_edgeHop hbd))
    (isPath_edgeHop (hab.trans hbd))
  apply htpy_nil_of_star d (starCh_spx1 (hab.trans hbd))
  · exact ((isPath_edgeHop hab).append (isPath_edgeHop hbd)).append
      (isPath_revPath (isPath_edgeHop (hab.trans hbd)))
  · exact pathIn_append
      (pathIn_append (pathIn_edgeHop hab (hab.trans hbd) hbd)
        (pathIn_edgeHop hbd hbd le_rfl))
      (pathIn_revPath (pathIn_edgeHop (hab.trans hbd) (hab.trans hbd) le_rfl))

noncomputable def barycentricCocycle : OrdCocycle P G where
  val a b := if h : a ≤ b then c.readPath (edgeHop h) else 1
  comp hab hbd := by
    simp only [dif_pos hab, dif_pos hbd, dif_pos (hab.trans hbd)]
    exact (c.readPath_append _ _).symm.trans (c.readPath_htpy (edgeHop_comp_htpy hab hbd))

theorem barycentricCocycle_val {a b : P} (h : a ≤ b) :
    (barycentricCocycle c).val a b = c.readPath (edgeHop h) := by
  simp only [barycentricCocycle, dif_pos h]

theorem edgeHop_read_via {a b : P} (hab : a ≤ b) (σ : NeSpx (cmpRel P))
    (ha : a ∈ σ.1) (hb : b ∈ σ.1) :
    c.readPath (edgeHop hab) = c.val (spx1 a) σ * (c.val (spx1 b) σ)⁻¹ := by
  have hσ : spx2 hab ≤ σ := by
    intro x hx
    simp only [spx2_val, Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    exacts [ha, hb]
  rw [← c.comp (spx1_le_spx2_left hab) hσ,
    ← c.comp (spx1_le_spx2_right hab) hσ]
  simp only [edgeHop, hop, OrdCocycle.readPath_cons, OrdCocycle.readPath_nil,
    OrdCocycle.readGerm_ordPos, OrdCocycle.readGerm_ordNeg, mul_one]
  group

variable {Ω : Type w} [MulAction G Ω]

noncomputable def barycentricSection (s : P → Ω) (σ : NeSpx (cmpRel P)) : Ω :=
  (c.val (spx1 (chainMax σ)) σ)⁻¹ • s (chainMax σ)

/-- A flat section on the original face poset gives a flat section on the
actual subdivision, not merely an agreement on selected generators. -/
theorem barycentricSection_flat (s : P → Ω)
    (hs : (barycentricCocycle c).IsFlatSection s) :
    c.IsFlatSection (barycentricSection c s) := by
  intro σ τ hστ
  have hm : spx1 (chainMax σ) ≤ σ := by
    intro x hx
    simp only [spx1_val, Finset.mem_singleton] at hx
    subst x
    exact chainMax_mem σ
  have hread := hs (chainMax_monotone hστ)
  rw [barycentricCocycle_val c (chainMax_monotone hστ),
    edgeHop_read_via c (chainMax_monotone hστ) τ
      (hστ (chainMax_mem σ)) (chainMax_mem τ)] at hread
  unfold barycentricSection
  rw [← c.comp hm hστ, mul_smul] at hread
  have he := congrArg (fun z => (c.val (spx1 (chainMax σ)) σ)⁻¹ • z) hread
  simpa only [mul_smul, inv_smul_smul] using he

theorem barycentricSection_spx1 (s : P → Ω) (a : P) :
    barycentricSection c s (spx1 a) = s a := by
  simp [barycentricSection]

end FiniteChains.Davis
