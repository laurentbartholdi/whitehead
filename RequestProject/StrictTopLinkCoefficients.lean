import RequestProject.CellularChainMapZero
import RequestProject.StrictTopLinkChains

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains.Comb
universe u
variable {P : Type u} [PartialOrder P]

/-- The actual triangle over an actual edge in the strict lower interval. -/
def strictConeTriangle (v : P) (e : StrictOrdEdge (StrictBelow v)) : StrictOrdTri P :=
  ⟨(e.1.1.val, e.1.2.val, v), e.2, e.1.2.property⟩

/-- Extracting a link preserves each genuine cone-triangle coefficient. -/
theorem strictTopLinkChain_apply (v : P) (c : StrictOrdTri P →₀ ℤ)
    (e : StrictOrdEdge (StrictBelow v)) :
    strictTopLinkChain v c e = c (strictConeTriangle v e) := by
  classical
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd => simp only [map_add, Finsupp.add_apply, hc, hd]
  | single t n =>
    rcases t with ⟨⟨a, b, z⟩, hab, hbz⟩
    rcases e with ⟨⟨⟨x, hx⟩, ⟨y, hy⟩⟩, hxy⟩
    by_cases ht : z = v
    · subst z
      simp [strictTopLinkChain, strictTopLinkTriangle, strictConeTriangle,
        Finsupp.single_apply, StrictOrdTri, StrictOrdEdge, StrictBelow,
        Subtype.mk.injEq, Prod.mk.injEq]
    · simp [strictTopLinkChain, strictTopLinkTriangle, ht, strictConeTriangle,
        StrictOrdTri, StrictOrdEdge, StrictBelow]

theorem strictOrderCxMap_onE_injective {Q : Type u} [PartialOrder Q]
    (f : P → Q) (hf : StrictMono f) (hi : Function.Injective f) :
    Function.Injective (strictOrderCxMap f hf).onE := by
  intro e d h
  apply Subtype.ext
  apply Prod.ext
  · apply hi
    exact congrArg (fun t : StrictOrdEdge Q => t.1.1) h
  · apply hi
    exact congrArg (fun t : StrictOrdEdge Q => t.1.2) h

/-- An actual injective strict cellular map preserves its edge coefficients. -/
theorem strictOrderCxMap_chain1_apply {Q : Type u} [PartialOrder Q]
    (f : P → Q) (hf : StrictMono f) (hi : Function.Injective f)
    (c : StrictOrdEdge P →₀ ℤ) (e : StrictOrdEdge P) :
    chain1 (strictOrderCxMap f hf) c ((strictOrderCxMap f hf).onE e) = c e := by
  exact Finsupp.mapDomain_apply_of_injective (strictOrderCxMap_onE_injective f hf hi) c e

/-- An actual order isomorphism induces an equivalence of actual strict edges. -/
def strictOrderEdgeEquiv {Q : Type u} [PartialOrder Q] (e : P ≃o Q) :
    StrictOrdEdge P ≃ StrictOrdEdge Q where
  toFun := (strictOrderCxMap e e.strictMono).onE
  invFun := (strictOrderCxMap e.symm e.symm.strictMono).onE
  left_inv x := by
    apply Subtype.ext
    apply Prod.ext <;> simp [strictOrderCxMap]
  right_inv x := by
    apply Subtype.ext
    apply Prod.ext <;> simp [strictOrderCxMap]

end FiniteChains.Comb
