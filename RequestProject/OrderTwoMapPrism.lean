module

public import RequestProject.OrderNerveCellMaps

@[expose] public section

/-! Explicit finite cellular prisms for two monotone maps with different
source and target posets. Proof terms only; not compiled. -/

noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains.Comb
universe u
variable {P Q : Type u} [PartialOrder P] [PartialOrder Q]
  (f g : P → Q) (hf : Monotone f) (hg : Monotone g) (hfg : ∀ x, f x ≤ g x)

def ordMapPrismEdge (e : OrdEdge P) : OrdTri Q →₀ ℤ :=
  Finsupp.single ⟨(f e.1.1, g e.1.1, g e.1.2), hfg _, hg e.2⟩ 1 -
  Finsupp.single ⟨(f e.1.1, f e.1.2, g e.1.2), hf e.2, hfg _⟩ 1

def ordMapPrismTriangle (t : OrdTri P) : OrdTet Q →₀ ℤ :=
  Finsupp.single ⟨(f t.1.1, g t.1.1, g t.1.2.1, g t.1.2.2),
    hfg _, hg t.2.1, hg t.2.2⟩ 1 -
  Finsupp.single ⟨(f t.1.1, f t.1.2.1, g t.1.2.1, g t.1.2.2),
    hf t.2.1, hfg _, hg t.2.2⟩ 1 +
  Finsupp.single ⟨(f t.1.1, f t.1.2.1, f t.1.2.2, g t.1.2.2),
    hf t.2.1, hf t.2.2, hfg _⟩ 1

def ordMapPrism1 : (OrdEdge P →₀ ℤ) →ₗ[ℤ] (OrdTri Q →₀ ℤ) :=
  Finsupp.linearCombination ℤ (ordMapPrismEdge f g hf hg hfg)

def ordMapPrism2 : (OrdTri P →₀ ℤ) →ₗ[ℤ] (OrdTet Q →₀ ℤ) :=
  Finsupp.linearCombination ℤ (ordMapPrismTriangle f g hf hg hfg)

theorem ordMapPrism_triangle_identity (t : OrdTri P) :
    ordBoundary3 (ordMapPrismTriangle f g hf hg hfg t) +
      ordMapPrism1 f g hf hg hfg (Comb.bdry2 (orderCx P) (Finsupp.single t 1)) =
    chain2 (orderCxMap g hg) (Finsupp.single t 1) -
      chain2 (orderCxMap f hf) (Finsupp.single t 1) := by
  simp [ordMapPrismTriangle, ordMapPrism1, ordMapPrismEdge, ordBoundary3,
    ordTetBoundary, Comb.bdry2, orderCx, pathChain, chain2, orderCxMap]
  abel

theorem ordMapPrism_identity (c : OrdTri P →₀ ℤ) :
    ordBoundary3 (ordMapPrism2 f g hf hg hfg c) +
      ordMapPrism1 f g hf hg hfg (Comb.bdry2 (orderCx P) c) =
    chain2 (orderCxMap g hg) c - chain2 (orderCxMap f hf) c := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd =>
    simp only [map_add]
    rw [add_add_add_comm, hc, hd]
    abel
  | single t n =>
    have h := congrArg (fun z : OrdTri Q →₀ ℤ => n • z)
      (ordMapPrism_triangle_identity f g hf hg hfg t)
    simpa [ordMapPrism2, Comb.bdry2, smul_add, smul_sub, Finsupp.smul_single] using h

/-- Actual finite tetrahedra comparing the images of a cellular cycle. -/
theorem ordMapPrism_cycle (c : OrdTri P →₀ ℤ) (hc : Comb.bdry2 (orderCx P) c = 0) :
    ordBoundary3 (ordMapPrism2 f g hf hg hfg c) =
      chain2 (orderCxMap g hg) c - chain2 (orderCxMap f hf) c := by
  have h := ordMapPrism_identity f g hf hg hfg c
  simpa only [hc, map_zero, add_zero] using h

end FiniteChains.Comb
