module

public import RequestProject.StrictOrderChains
public import RequestProject.UnivCoverIncl

@[expose] public section

/-! Finite chains and cycles on an actual induced subposet. -/
namespace FiniteChains.Comb
universe u
variable {P : Type u} [PartialOrder P] (S : Set P)

def ordSubposetIncl : Hom (orderCx S) (orderCx P) :=
  orderCxMap Subtype.val (fun _ _ h => h)

theorem ordSubposetIncl_onE_injective :
    Function.Injective (ordSubposetIncl S).onE := by
  intro a b h
  apply Subtype.ext
  apply Prod.ext <;> apply Subtype.ext
  · exact congrArg (fun e : OrdEdge P => e.1.1) h
  · exact congrArg (fun e : OrdEdge P => e.1.2) h

theorem ordSubposetIncl_onF_injective :
    Function.Injective (ordSubposetIncl S).onF := by
  intro a b h
  apply Subtype.ext
  apply Prod.ext
  · apply Subtype.ext
    exact congrArg (fun t : OrdTri P => t.1.1) h
  · apply Prod.ext <;> apply Subtype.ext
    · exact congrArg (fun t : OrdTri P => t.1.2.1) h
    · exact congrArg (fun t : OrdTri P => t.1.2.2) h

/-- A triangle is in the induced subcomplex exactly when its three vertices lie in it. -/
theorem ordSubposetIncl_onF_range (t : OrdTri P) :
    t ∈ Set.range (ordSubposetIncl S).onF ↔
      t.1.1 ∈ S ∧ t.1.2.1 ∈ S ∧ t.1.2.2 ∈ S := by
  constructor
  · rintro ⟨a, rfl⟩
    exact ⟨a.1.1.2, a.1.2.1.2, a.1.2.2.2⟩
  · rintro ⟨ha, hb, hc⟩
    exact ⟨⟨(⟨t.1.1, ha⟩, ⟨t.1.2.1, hb⟩, ⟨t.1.2.2, hc⟩), t.2⟩,
      Subtype.ext rfl⟩

/-- Every finite chain supported on the actual subcomplex is the image of a finite
chain on that subcomplex. If it is a cycle, its unique lift is a cycle too. -/
theorem exists_ordSubposet_cycle (c : OrdTri P →₀ ℤ)
    (hs : ∀ t ∈ c.support, t.1.1 ∈ S ∧ t.1.2.1 ∈ S ∧ t.1.2.2 ∈ S)
    (hc : bdry2 (orderCx P) c = 0) :
    ∃ d : OrdTri S →₀ ℤ,
      chain2 (ordSubposetIncl S) d = c ∧ bdry2 (orderCx S) d = 0 := by
  let d := Finsupp.comapDomain (ordSubposetIncl S).onF c
    (ordSubposetIncl_onF_injective S).injOn
  have hd : chain2 (ordSubposetIncl S) d = c :=
    Finsupp.mapDomain_comapDomain _ (ordSubposetIncl_onF_injective S) c
      (fun t ht => (ordSubposetIncl_onF_range S t).mpr (hs t ht))
  refine ⟨d, hd, ?_⟩
  apply Finsupp.mapDomain_injective (ordSubposetIncl_onE_injective S)
  change chain1 (ordSubposetIncl S) (bdry2 (orderCx S) d) =
    Finsupp.mapDomain _ 0
  rw [Finsupp.mapDomain_zero, ← bdry2_chain2, hd, hc]

end FiniteChains.Comb
