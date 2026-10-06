module

public import RequestProject.UnivCoverIncl
public import RequestProject.OrderComplexGluing

@[expose] public section

/-! Explicit finite cellular cone fillings, rather than unspecified null-homotopy witnesses. -/
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains.Comb
universe u
variable {P Q : Type u} [Preorder P] [Preorder Q]
  (f : P → Q) (hf : Monotone f) (c : Q) (hc : ∀ x, c ≤ f x)

noncomputable def coneRadial (x : P) : (orderCx Q).E := ⟨(c, f x), hc x⟩
noncomputable def coneEdgeTriangle (e : (orderCx P).E) : (orderCx Q).F :=
  ⟨(c, f e.1.1, f e.1.2), hc _, hf e.2⟩
noncomputable def coneEdgeChain : ((orderCx P).E →₀ ℤ) →ₗ[ℤ] ((orderCx Q).F →₀ ℤ) :=
  Finsupp.linearCombination ℤ (fun e => Finsupp.single (coneEdgeTriangle f hf c hc e) (1 : ℤ))

theorem coneEdgeTriangle_boundary (e : (orderCx P).E) :
    bdry2 (orderCx Q) (Finsupp.single (coneEdgeTriangle f hf c hc e) (1 : ℤ)) =
      Finsupp.single ((orderCxMap f hf).onE e) (1 : ℤ) +
      Finsupp.single (coneRadial f c hc e.1.1) (1 : ℤ) -
      Finsupp.single (coneRadial f c hc e.1.2) (1 : ℤ) := by
  rw [bdry2_single, one_smul]
  simp [coneEdgeTriangle, coneRadial, orderCx, orderCxMap, pathChain]
  abel

/-- The fan boundary is the image path plus its initial radial edge minus its final one. -/
theorem coneEdgeChain_path_boundary {a b : P} {p : List ((orderCx P).E × Bool)}
    (hp : IsPath (orderCx P).src (orderCx P).tgt p a b) :
    bdry2 (orderCx Q) (coneEdgeChain f hf c hc (pathChain p)) =
      pathChain (mapPath (orderCxMap f hf) p) +
      Finsupp.single (coneRadial f c hc a) (1 : ℤ) -
      Finsupp.single (coneRadial f c hc b) (1 : ℤ) := by
  induction p generalizing a with
  | nil =>
      subst b
      simp [pathChain, mapPath, LinearMap.map_zero]
  | cons eb p ih =>
      obtain ⟨ha, hp⟩ := hp
      subst a
      rw [pathChain_cons, map_add, map_add, ih hp]
      obtain ⟨e, d⟩ := eb
      cases d
      · have he := coneEdgeTriangle_boundary f hf c hc e
        simp only [Bool.false_eq_true, ↓reduceIte]
        rw [map_neg, map_neg]
        change -bdry2 (orderCx Q)
          ((coneEdgeChain f hf c hc) (Finsupp.single e (1 : ℤ))) + _ = _
        rw [coneEdgeChain, Finsupp.linearCombination_single, one_smul, he]
        simp [mapPath, pathChain_cons, germSrc, germTgt, orderCx]
        abel
      · have he := coneEdgeTriangle_boundary f hf c hc e
        simp only [↓reduceIte]
        rw [coneEdgeChain, Finsupp.linearCombination_single, one_smul, he]
        simp [mapPath, pathChain_cons, germSrc, germTgt, orderCx]
        abel

/-- A loop has the explicit cone-edge fan as a finite two-chain filling. -/
theorem coneEdgeChain_loop_boundary {a : P} {p : List ((orderCx P).E × Bool)}
    (hp : IsPath (orderCx P).src (orderCx P).tgt p a a) :
    bdry2 (orderCx Q) (coneEdgeChain f hf c hc (pathChain p)) =
      pathChain (mapPath (orderCxMap f hf) p) := by
  rw [coneEdgeChain_path_boundary f hf c hc hp]
  abel

end FiniteChains.Comb
