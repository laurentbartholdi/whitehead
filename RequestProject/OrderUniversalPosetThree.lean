import RequestProject.OrderUniversalPosetHom
import RequestProject.OrderUniversalThree

/-! The actual lifted three-boundary under the universal-cover order identification. -/
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains.Comb
universe u
variable {P : Type u} [PartialOrder P] {a : P}

def uOrderTet (t : OrdTet (UOrder P a)) : UOrdTet P a :=
  ⟨(t.1.1, ⟨(uOrderEnd t.1.1, uOrderEnd t.1.2.1,
    uOrderEnd t.1.2.2.1, uOrderEnd t.1.2.2.2),
    uOrderEnd_monotone t.2.1, uOrderEnd_monotone t.2.2.1,
    uOrderEnd_monotone t.2.2.2⟩), rfl⟩

/-- The four actual lifted faces have precisely the alternating nerve boundary. -/
theorem uOrderTet_boundary (t : OrdTet (UOrder P a)) :
    Finsupp.mapDomain uOrderFace (ordTetBoundary t) = uOrdTetBoundary (uOrderTet t) := by
  obtain ⟨⟨v, w, z, r⟩, hvw, hwz, hzr⟩ := t
  let t : OrdTet (UOrder P a) := ⟨(v, w, z, r), hvw, hwz, hzr⟩
  have h0 : uOrderFace ⟨(w, z, r), hwz, hzr⟩ = uOrdTetFace0 (uOrderTet t) := by
    apply Subtype.ext
    exact Prod.ext hvw.2.symm (Subtype.ext rfl)
  have h1 : uOrderFace ⟨(v, z, r), hvw.trans hwz, hzr⟩ =
      uOrdTetFace1 (uOrderTet t) := rfl
  have h2 : uOrderFace ⟨(v, w, r), hvw, hwz.trans hzr⟩ =
      uOrdTetFace2 (uOrderTet t) := rfl
  have h3 : uOrderFace ⟨(v, w, z), hvw, hwz⟩ = uOrdTetFace3 (uOrderTet t) := rfl
  have hsub (x y : OrdTri (UOrder P a) →₀ ℤ) :
      Finsupp.mapDomain uOrderFace (x - y) =
        Finsupp.mapDomain uOrderFace x - Finsupp.mapDomain uOrderFace y :=
    (Finsupp.lmapDomain ℤ ℤ uOrderFace).map_sub x y
  change Finsupp.mapDomain uOrderFace (ordTetBoundary t) = uOrdTetBoundary (uOrderTet t)
  simp only [ordTetBoundary, hsub, Finsupp.mapDomain_add, Finsupp.mapDomain_single,
    uOrdTetBoundary]
  rw [h0, h1, h2, h3]

/-- The cellular comparison commutes with the full actual universal-cover three-boundary. -/
theorem uOrderHom_ordBoundary3 (c : OrdTet (UOrder P a) →₀ ℤ) :
    chain2 uOrderHom (ordBoundary3 c) = uOrdBoundary3 (Finsupp.mapDomain uOrderTet c) := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd => rw [map_add, map_add, hc, hd, Finsupp.mapDomain_add, map_add]
  | single t n =>
    rw [ordBoundary3, Finsupp.linearCombination_single, map_smul]
    change n • Finsupp.mapDomain uOrderFace (ordTetBoundary t) = _
    rw [uOrderTet_boundary, Finsupp.mapDomain_single, uOrdBoundary3,
      Finsupp.linearCombination_single]

/-- Every genuine finite nerve filling in the lifted order is a filling of the
corresponding actual universal-cover two-chain. -/
theorem uOrder_cycle_filling (c : OrdTri (UOrder P a) →₀ ℤ)
    (y : OrdTet (UOrder P a) →₀ ℤ) (hy : ordBoundary3 y = c) :
    uOrdBoundary3 (Finsupp.mapDomain uOrderTet y) = chain2 uOrderHom c := by
  rw [← uOrderHom_ordBoundary3, hy]

end FiniteChains.Comb
