import RequestProject.NerveDegree
import RequestProject.ChamberZChain

/-! The actual chamber relative homology theorem with witnesses in the required degrees. -/

namespace FiniteChains.Davis
open RACG Mirror Comb Nerve
universe u
variable {V : Type u} [DecidableEq V] [Fintype V] {A : CommRel V}
  {X : Type u} [Preorder X] {M : CayGroup A → Prop} {att : NeSpx A →o X}

/-- A degree-`n` cycle in the actual modified-chamber complex is a base cycle of the same
 degree plus a boundary of degree `n + 1`. Both witnesses remain increasing chains. -/
theorem exists_base_cycle_of_cycle_degree [Nonempty X] (n : ℕ)
    {z : Nerve.Ch (Zpos A X M att)} (hz : z ∈ Nerve.Inc (Zpos A X M att))
    (hcyc : Nerve.bdry z = 0) (hdegree : lengthProjection (n + 1) z = z) :
    ∃ c ∈ Nerve.IncOn (InZBase (A := A) (X := X) (M := M) (att := att)),
      ∃ y ∈ Nerve.Inc (Zpos A X M att),
        lengthProjection (n + 1) c = c ∧ lengthProjection (n + 2) y = y ∧
        Nerve.bdry c = 0 ∧ z = c + Nerve.bdry y := by
  obtain ⟨c, hc, y, hy, hdc, hzc⟩ := exists_base_cycle_of_cycle hz hcyc
  refine ⟨lengthProjection (n + 1) c, lengthProjection_mem_incOn _ hc,
    lengthProjection (n + 2) y, lengthProjection_mem_inc _ hy,
    lengthProjection_idempotent _ _, lengthProjection_idempotent _ _, ?_, ?_⟩
  · rw [← lengthProjection_bdry, hdc, map_zero]
  · have h := congrArg (lengthProjection (n + 1)) hzc
    simpa only [hdegree, map_add, lengthProjection_bdry, Nat.add_assoc] using h

end FiniteChains.Davis
