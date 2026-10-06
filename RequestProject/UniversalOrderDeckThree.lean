import RequestProject.UniversalOrderThreeNaturality
import RequestProject.UniversalCoverPi1Injection
import RequestProject.ComponentComplex

namespace FiniteChains.Comb
universe u

variable {X Y Z : Complex2.{u}}

theorem univLiftF_deckF (f : Hom X Y) (a : X.V) (g : Pi1 X a) (t : UF X a) :
    univLiftF a f (deckF g t) = deckF (pi1Map f a g) (univLiftF a f t) :=
  Subtype.ext (Prod.ext (univLiftV_deckV f a g t.1.1) rfl)

theorem univLift_chain2_deck (f : Hom X Y) (a : X.V) (g : Pi1 X a)
    (c : UF X a →₀ ℤ) :
    chain2 (univLift X f a) (Finsupp.mapDomain (deckF g) c) =
      Finsupp.mapDomain (deckF (pi1Map f a g)) (chain2 (univLift X f a) c) := by
  change Finsupp.mapDomain (univLiftF a f) (Finsupp.mapDomain (deckF g) c) =
    Finsupp.mapDomain (deckF (pi1Map f a g)) (Finsupp.mapDomain (univLiftF a f) c)
  rw [← Finsupp.mapDomain_comp, ← Finsupp.mapDomain_comp]
  exact congrArg (fun k => Finsupp.mapDomain k c) (funext (univLiftF_deckF f a g))

theorem univLift_chain2_comp (g : Hom Y Z) (f : Hom X Y) (a : X.V)
    (c : UF X a →₀ ℤ) :
    chain2 (univLift Y g (f.onV a)) (chain2 (univLift X f a) c) =
      chain2 (univLift X (g.comp f) a) c := by
  change Finsupp.mapDomain (univLiftF (f.onV a) g) (Finsupp.mapDomain (univLiftF a f) c) =
    Finsupp.mapDomain (univLiftF a (g.comp f)) c
  rw [← Finsupp.mapDomain_comp]
  exact congrArg (fun k => Finsupp.mapDomain k c) (funext (univLiftF_comp g f a))

variable {P : Type u} [PartialOrder P] {a : P}

/-- Deck transformations act on the actual lifted tetrahedra. -/
def deckUOrdTet (g : Pi1 (orderCx P) a) (t : UOrdTet P a) : UOrdTet P a :=
  ⟨(deckV g t.1.1, t.1.2), (endV_deckV g t.1.1).trans t.2⟩

theorem deckUOrdTet_face0 (g : Pi1 (orderCx P) a) (t : UOrdTet P a) :
    deckF g (uOrdTetFace0 t) = uOrdTetFace0 (deckUOrdTet g t) := by
  apply Subtype.ext
  apply Prod.ext
  · exact (extend_deckV g (ordPos t.1.2.2.1) t.1.1).symm
  · rfl

theorem deckUOrdTet_boundary (g : Pi1 (orderCx P) a) (t : UOrdTet P a) :
    Finsupp.mapDomain (deckF g) (uOrdTetBoundary t) =
      uOrdTetBoundary (deckUOrdTet g t) := by
  let L : (UF (orderCx P) a →₀ ℤ) →ₗ[ℤ] (UF (orderCx P) a →₀ ℤ) :=
    Finsupp.lmapDomain ℤ ℤ (deckF g)
  change L (uOrdTetBoundary t) = _
  simp only [uOrdTetBoundary, map_sub, map_add]
  simp only [L, Finsupp.lmapDomain_apply, Finsupp.mapDomain_single]
  rw [deckUOrdTet_face0]
  rfl

/-- Finite lifted three-fillings remain fillings under every deck transformation. -/
theorem deck_uOrdBoundary3 (g : Pi1 (orderCx P) a) (b : UOrdTet P a →₀ ℤ) :
    Finsupp.mapDomain (deckF g) (uOrdBoundary3 b) =
      uOrdBoundary3 (Finsupp.mapDomain (deckUOrdTet g) b) := by
  induction b using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd =>
    rw [map_add, Finsupp.mapDomain_add, hc, hd, Finsupp.mapDomain_add, map_add]
  | single t n =>
    simp only [uOrdBoundary3, Finsupp.mapDomain_single, Finsupp.linearCombination_single,
      Finsupp.mapDomain_smul, deckUOrdTet_boundary]

end FiniteChains.Comb
