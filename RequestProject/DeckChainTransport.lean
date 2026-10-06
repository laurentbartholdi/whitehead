import RequestProject.CombPi2

/-! Deck transformations act on genuine cellular chains and preserve their boundary. -/
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains.Comb
universe u v
variable {X : Complex2.{u}} {G : Type v} [Group G]

/-- The cellular self-map supplied by a deck transformation. -/
def DeckAction.cellHom (D : DeckAction X G) (g : G) : Hom X X where
  onV := D.smulV g
  onE := D.smulE g
  onF := D.smulF g
  src_onE := D.src_smul g
  tgt_onE := D.tgt_smul g
  base_onF := D.base_smul g
  att_onF := D.att_smul g

noncomputable def DeckAction.faceChains (D : DeckAction X G) (g : G) :
    (X.F →₀ ℤ) →ₗ[ℤ] (X.F →₀ ℤ) := chain2 (D.cellHom g)

theorem DeckAction.faceChains_boundary (D : DeckAction X G) (g : G) (c : X.F →₀ ℤ) :
    bdry2 X (D.faceChains g c) = chain1 (D.cellHom g) (bdry2 X c) :=
  bdry2_chain2 _ _

theorem DeckAction.faceChains_mul (D : DeckAction X G) (g h : G) (c : X.F →₀ ℤ) :
    D.faceChains (g * h) c = D.faceChains g (D.faceChains h c) := by
  change Finsupp.mapDomain (D.smulF (g * h)) c =
    Finsupp.mapDomain (D.smulF g) (Finsupp.mapDomain (D.smulF h) c)
  rw [← Finsupp.mapDomain_comp]
  exact congrArg (fun f => Finsupp.mapDomain f c) (funext (D.mul_smulF g h))

/-- Transport a concrete filling along a deck transformation. -/
theorem DeckAction.transport_filling (D : DeckAction X G) (g : G)
    (c : X.F →₀ ℤ) (p : List (X.E × Bool)) (hc : bdry2 X c = pathChain p) :
    bdry2 X (D.faceChains g c) = pathChain (mapPath (D.cellHom g) p) := by
  rw [D.faceChains_boundary, hc]
  exact (pathChain_map _ _).symm

/-- Forgetting the deck coordinate is invariant under the actual universal-cover action. -/
theorem hurewicz_deck_faceChains (a : X.V) (g : Pi1 X a)
    (c : (uCover X a).F →₀ ℤ) :
    hurewicz X a ((univDeck X a).faceChains g c) = hurewicz X a c := by
  change Finsupp.mapDomain (univProj X a).onF
    (Finsupp.mapDomain (deckF g) c) = Finsupp.mapDomain (univProj X a).onF c
  rw [← Finsupp.mapDomain_comp]
  rfl

end FiniteChains.Comb
