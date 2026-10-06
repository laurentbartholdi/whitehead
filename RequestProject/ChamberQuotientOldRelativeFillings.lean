module

public import RequestProject.ChamberQuotientOldGeneration
public import RequestProject.ChamberQuotientStarOneFillings
public import RequestProject.NerveRelativeIntersection
public import RequestProject.NerveBoundaryReflection

@[expose] public section

/-! Actual relative degree-two vanishing for the old/attaching pair in the Q cover. -/
namespace FiniteChains.Davis
open RACG Mirror Comb Nerve
universe u
variable {V : Type u} [DecidableEq V] [Fintype V] {A : CommRel V}
  {X : Type u} [PartialOrder X] {att : NeSpx A →o X}

/-- An old two-chain whose boundary is on the attaching locus is an attaching
two-chain modulo an old three-boundary, with exactly the same boundary.
In particular, the original chain is not assumed to be an absolute cycle. -/
theorem qUniversal_old_relative_filling (x : X) (hx : IsConnected (orderCx X))
    (z : Ch (UOrder (Qpos A X att) (qNew x)))
    (hz : z ∈ IncOn (fun p => InQOld (uOrderEnd p)))
    (hd : lengthProjection 3 z = z)
    (hdz : Nerve.bdry z ∈ IncOn
      (fun p => InQOld (uOrderEnd p) ∧ InQBaseStar (uOrderEnd p))) :
    ∃ t ∈ IncOn (fun p => InQOld (uOrderEnd p) ∧ InQBaseStar (uOrderEnd p)),
      lengthProjection 3 t = t ∧ Nerve.bdry t = Nerve.bdry z ∧
      ∃ y ∈ IncOn (fun p => InQOld (uOrderEnd p)),
        lengthProjection 4 y = y ∧ z = t + Nerve.bdry y := by
  have hgen : GeneratesDegreeIn (fun _ : UOrder (Qpos A X att) (qNew x) => True)
      (fun p => InQBaseStar (uOrderEnd p)) 3 := by
    intro c hc hdc hcyc
    obtain ⟨b, hb, y, hy, hbc, he⟩ := qUniversal_generatesDegreeIn_base x hx c hc hdc hcyc
    exact ⟨b, incOn_mono (fun _ h => inQBase_in_star h) hb, y, hy, hbc, he⟩
  exact relative_filling_intersection_of_ambient (n := 2)
    (fun _ _ => True.intro) (fun _ _ => True.intro)
    (fun a b hab _ _ => qOld_baseStar_unmixed _ _ (uOrderEnd_monotone hab))
    hgen (qUniversal_baseStar_fillsDegree_two x hx) z hz hd
    (incOn_mono (fun _ h => h.2) hdz)

/-- An attaching one-cycle which bounds in old cells already bounds in the
actual attaching preimage. This is derived from the relative chain construction. -/
theorem qUniversal_attaching_reflects_one_boundaries (x : X)
    (hx : IsConnected (orderCx X)) :
    ReflectsBoundsIn
      (fun p : UOrder (Qpos A X att) (qNew x) => InQOld (uOrderEnd p))
      (fun p => InQOld (uOrderEnd p) ∧ InQBaseStar (uOrderEnd p)) 2 := by
  intro c hc hd hbound
  obtain ⟨y, hy, hdy⟩ := hbound
  let z := lengthProjection 3 y
  have hz : z ∈ IncOn (fun p => InQOld (uOrderEnd p)) := lengthProjection_mem_incOn _ hy
  have hdz : Nerve.bdry z = c := by rw [← lengthProjection_bdry, hdy, hd]
  obtain ⟨t, ht, _, hdt, _⟩ := qUniversal_old_relative_filling x hx z hz
    (lengthProjection_idempotent _ _) (by rw [hdz]; exact hc)
  exact ⟨t, ht, hdt.trans hdz⟩

end FiniteChains.Davis
