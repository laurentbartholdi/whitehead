module

public import RequestProject.ChamberZCoverCellularGeneration
public import RequestProject.OrderSubposetChains
public import RequestProject.OrderNerveH2Maps

@[expose] public section

namespace FiniteChains.Davis
open RACG Mirror Comb
universe u
variable {V : Type u} [DecidableEq V] [Fintype V] {A : CommRel V}
  {X : Type u} [PartialOrder X] [Nonempty X]
  {M : CayGroup A → Prop} {att : NeSpx A →o X}
  {P : Type u} [PartialOrder P] {f : P → Zpos A X M att}

/-- The actual lifted-base inclusion surjects onto second integral order-nerve
homology of the covering modified chamber complex. -/
theorem cover_base_homology_inclusion_surjective (hf : IsPosetCover f) :
    Function.Surjective (orderNerveH2Map
      (Subtype.val : {p : P // InZBase (f p)} → P) (fun _ _ h => h)) := by
  intro z
  induction z using Submodule.Quotient.induction_on with
  | H a =>
    obtain ⟨c, hc, hcc, y, he⟩ := exists_cover_base_cellular_cycle hf a.val a.property
    let S : Set P := {p | InZBase (f p)}
    have hs : ∀ t ∈ c.support, t.1.1 ∈ S ∧ t.1.2.1 ∈ S ∧ t.1.2.2 ∈ S := by
      intro t ht
      exact (Finsupp.mem_supported ℤ c).mp hc ht
    obtain ⟨d, hd, hdc⟩ := exists_ordSubposet_cycle S c hs hcc
    refine ⟨orderNerveH2Class S d hdc, ?_⟩
    change Submodule.Quotient.mk
      (orderNerveCycleMap (Subtype.val : S → P) (fun _ _ h => h) ⟨d, hdc⟩) =
        Submodule.Quotient.mk a
    apply (Submodule.Quotient.eq _).mpr
    refine ⟨-y, ?_⟩
    apply Subtype.ext
    change ordBoundary3 (-y) = chain2 (ordSubposetIncl S) d - a.val
    rw [map_neg, hd, he]
    abel

end FiniteChains.Davis
