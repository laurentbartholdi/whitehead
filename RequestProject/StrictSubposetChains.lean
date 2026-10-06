module

public import RequestProject.StrictOrderChains
public import RequestProject.UnivCoverIncl

@[expose] public section

/-! Finite chains and cycles on an actual induced subposet. -/
namespace FiniteChains.Comb
universe u
variable {P : Type u} [PartialOrder P] (S : Set P)

def strictSubposetIncl : Hom (strictOrderCx S) (strictOrderCx P) :=
  strictOrderCxMap Subtype.val (fun _ _ h => h)

theorem strictSubposetIncl_onE_injective :
    Function.Injective (strictSubposetIncl S).onE := by
  intro a b h
  apply Subtype.ext
  apply Prod.ext <;> apply Subtype.ext
  · exact congrArg (fun e : StrictOrdEdge P => e.1.1) h
  · exact congrArg (fun e : StrictOrdEdge P => e.1.2) h

theorem strictSubposetIncl_onF_injective :
    Function.Injective (strictSubposetIncl S).onF := by
  intro a b h
  apply Subtype.ext
  apply Prod.ext
  · apply Subtype.ext
    exact congrArg (fun t : StrictOrdTri P => t.1.1) h
  · apply Prod.ext <;> apply Subtype.ext
    · exact congrArg (fun t : StrictOrdTri P => t.1.2.1) h
    · exact congrArg (fun t : StrictOrdTri P => t.1.2.2) h

/-- A triangle is in the induced subcomplex exactly when its three vertices lie in it. -/
theorem strictSubposetIncl_onF_range (t : StrictOrdTri P) :
    t ∈ Set.range (strictSubposetIncl S).onF ↔
      t.1.1 ∈ S ∧ t.1.2.1 ∈ S ∧ t.1.2.2 ∈ S := by
  constructor
  · rintro ⟨a, rfl⟩
    exact ⟨a.1.1.2, a.1.2.1.2, a.1.2.2.2⟩
  · rintro ⟨ha, hb, hc⟩
    exact ⟨⟨(⟨t.1.1, ha⟩, ⟨t.1.2.1, hb⟩, ⟨t.1.2.2, hc⟩), t.2⟩,
      Subtype.ext rfl⟩

/-- Every finite chain supported on the actual subcomplex is the image of a finite
chain on that subcomplex. If it is a cycle, its unique lift is a cycle too. -/
theorem exists_strictSubposet_cycle (c : StrictOrdTri P →₀ ℤ)
    (hs : ∀ t ∈ c.support, t.1.1 ∈ S ∧ t.1.2.1 ∈ S ∧ t.1.2.2 ∈ S)
    (hc : bdry2 (strictOrderCx P) c = 0) :
    ∃ d : StrictOrdTri S →₀ ℤ,
      chain2 (strictSubposetIncl S) d = c ∧ bdry2 (strictOrderCx S) d = 0 := by
  let d := Finsupp.comapDomain (strictSubposetIncl S).onF c
    (strictSubposetIncl_onF_injective S).injOn
  have hd : chain2 (strictSubposetIncl S) d = c :=
    Finsupp.mapDomain_comapDomain _ (strictSubposetIncl_onF_injective S) c
      (fun t ht => (strictSubposetIncl_onF_range S t).mpr (hs t ht))
  refine ⟨d, hd, ?_⟩
  apply Finsupp.mapDomain_injective (strictSubposetIncl_onE_injective S)
  change chain1 (strictSubposetIncl S) (bdry2 (strictOrderCx S) d) =
    Finsupp.mapDomain _ 0
  rw [Finsupp.mapDomain_zero, ← bdry2_chain2, hd, hc]

end FiniteChains.Comb
