import RequestProject.ChamberZStrictCellular
import RequestProject.StrictSubposetChains

/-! The actual base-subcomplex chain map in modified-chamber generation. -/
namespace FiniteChains.Davis
open RACG Mirror Comb Nerve
universe u
variable {V : Type u} [DecidableEq V] [Fintype V] {A : CommRel V}
  {X : Type u} [PartialOrder X] {M : CayGroup A → Prop} {att : NeSpx A →o X}

/-- The union of the actual inserted base copies, with its induced order. -/
abbrev ZBase := {z : Zpos A X M att // InZBase (A := A) (X := X) (M := M) (att := att) z}

/-- The cellular inclusion of the actual base subcomplex. -/
def zBaseIncl : Hom (strictOrderCx (ZBase (A := A) (X := X) (M := M) (att := att)))
    (strictOrderCx (Zpos A X M att)) :=
  strictSubposetIncl {z | InZBase (A := A) (X := X) (M := M) (att := att) z}

def zBaseFaceIncl : StrictOrdTri (ZBase (A := A) (X := X) (M := M) (att := att)) →
    StrictOrdTri (Zpos A X M att) :=
  (zBaseIncl (A := A) (X := X) (M := M) (att := att)).onF

/-- Unconditional relative two-cycle generation for the actual pair of modified chambers
and its base subcomplex, expressed using the constructed cellular inclusion. -/
theorem exists_zBase_cycle [Nonempty X]
    (z : StrictOrdTri (Zpos A X M att) →₀ ℤ)
    (hz : Comb.bdry2 (strictOrderCx (Zpos A X M att)) z = 0) :
    ∃ d : (strictOrderCx (ZBase (A := A) (X := X) (M := M) (att := att))).F →₀ ℤ,
      Comb.bdry2 (strictOrderCx (ZBase (A := A) (X := X) (M := M) (att := att))) d = 0 ∧
      ∃ y : StrictOrdTet (Zpos A X M att) →₀ ℤ,
        z = Finsupp.mapDomain (zBaseFaceIncl (A := A) (X := X) (M := M) (att := att)) d +
          strictOrdBoundary3 y := by
  obtain ⟨c, hs, hc, y, hy⟩ := exists_base_strict_cellular_cycle z hz
  obtain ⟨d, hd, hcycle⟩ := exists_strictSubposet_cycle {z | InZBase z} c hs hc
  refine ⟨d, hcycle, y, ?_⟩
  have hmap : Finsupp.mapDomain
      (zBaseFaceIncl (A := A) (X := X) (M := M) (att := att)) d = c := hd
  rw [hmap]
  exact hy

end FiniteChains.Davis
