import RequestProject.ChamberZBaseSheets
import RequestProject.CombData

/-! Finite generation by actual base-copy cycles in the modified chambers. -/
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains.Davis
open RACG Mirror Comb
open scoped Classical
universe u
variable {V : Type u} [DecidableEq V] [Fintype V] {A : CommRel V}
  {X : Type u} [PartialOrder X] {M : CayGroup A → Prop} {att : NeSpx A →o X}

def zNewStrictCx (w : {w : CayGroup A // M w}) :
    Hom (strictOrderCx X) (strictOrderCx (Zpos A X M att)) :=
  zBaseIncl.comp (zBaseCopyCx w)

def zNewStrictFace (w : {w : CayGroup A // M w}) :
    StrictOrdTri X → StrictOrdTri (Zpos A X M att) := (zNewStrictCx w).onF

/-- Every actual modified-chamber two-cycle is, modulo an actual finite strict
three-boundary, a finite sum of images of cycles of the original base. -/
theorem exists_zNew_cycles_generate [Nonempty X]
    (z : StrictOrdTri (Zpos A X M att) →₀ ℤ)
    (hz : Comb.bdry2 (strictOrderCx (Zpos A X M att)) z = 0) :
    ∃ (s : Finset {w : CayGroup A // M w})
      (d : {w : CayGroup A // M w} → (StrictOrdTri X →₀ ℤ)),
      (∀ w, Comb.bdry2 (strictOrderCx X) (d w) = 0) ∧
      ∃ y : StrictOrdTet (Zpos A X M att) →₀ ℤ,
        z = (∑ w ∈ s, Finsupp.mapDomain (zNewStrictFace w) (d w)) +
          strictOrdBoundary3 y := by
  obtain ⟨c, hc, y, hy⟩ := exists_zBase_cycle z hz
  obtain ⟨s, d, hd, he⟩ := exists_zBase_cycle_decomposition c hc
  refine ⟨s, d, hd, y, ?_⟩
  have hm : Finsupp.mapDomain
      (zBaseFaceIncl (A := A) (X := X) (M := M) (att := att)) c =
      ∑ w ∈ s, Finsupp.mapDomain (zNewStrictFace w) (d w) := by
    rw (config := { transparency := .default }) [he, Finsupp.mapDomain_finset_sum]
    apply Finset.sum_congr rfl
    intro w _
    change Finsupp.mapDomain zBaseFaceIncl
      (Finsupp.mapDomain (zBaseCopyCx w).onF (d w)) = _
    rw (config := { transparency := .default }) [← Finsupp.mapDomain_comp]
    rfl
  rw (config := { transparency := .default }) [hy, hm]

end FiniteChains.Davis
