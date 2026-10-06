module

public import RequestProject.AcyclicRelativeTreeChains
public import RequestProject.TreeChainFinsupp

@[expose] public section

/-! The actual regular-cover sufficiency construction in the cellular
category: build relative chains upstairs and descend their particular
maps. No finite-cell or spherical-generation premise remains. The
topological realization of this result is a separate bridge. Pending
final Lean verification. -/

noncomputable section
open scoped Classical
namespace FiniteChains.Comb
universe v
variable {D K : Complex2} (T : SpanningTree D) (hD : IsAcyclic D)
  (p : Hom D K)

def regularCoverChainStages (n : ℕ) : ℕ → Complex2 :=
  (acyclicRelativeCellChain T hD n).desc p

def regularCoverChainInclusion (n i : ℕ) :
    Hom (regularCoverChainStages T hD p n i) (regularCoverChainStages T hD p n (i + 1)) :=
  (acyclicRelativeCellChain T hD n).descInc p i

@[simp] theorem regularCoverChainStages_zero (n : ℕ) :
    regularCoverChainStages T hD p n 0 = K := rfl

theorem regularCoverChainInclusion_V (n i : ℕ) :
    Function.Injective (regularCoverChainInclusion T hD p n i).onV :=
  (acyclicRelativeCellChain T hD n).descInc_injective_V p i

theorem regularCoverChainInclusion_E (n i : ℕ) :
    Function.Injective (regularCoverChainInclusion T hD p n i).onE :=
  (acyclicRelativeCellChain T hD n).descInc_injective_E p i

theorem regularCoverChainInclusion_F (n i : ℕ) :
    Function.Injective (regularCoverChainInclusion T hD p n i).onF :=
  (acyclicRelativeCellChain T hD n).descInc_injective_F p i

theorem regularCoverChain_connected (hp : IsCovering p) (n i : ℕ) :
    IsConnected (regularCoverChainStages T hD p n i) :=
  (acyclicRelativeCellChain T hD n).desc_connected p hp T.root i

theorem regularCoverChain_proper (n i : ℕ) (hi : i < n + 1) :
    (¬ Function.Surjective (regularCoverChainInclusion T hD p n i).onE) ∨
      (¬ Function.Surjective (regularCoverChainInclusion T hD p n i).onF) :=
  (acyclicRelativeCellChain T hD n).descInc_proper p i hi

variable (hp : IsCovering p) {Q : Type v} [Group Q]
  (a : DeckAction D Q) (hr : IsRegular p a)
  (he : ∀ q e, p.onE (a.smulE q e) = p.onE e)
  (hf : ∀ q f, p.onF (a.smulF q f) = p.onF f)

include hp hr he hf in
theorem regularCoverChain_zeroPi2 (n i : ℕ) (hi : i < n + 1) :
    ZeroPi2 (regularCoverChainInclusion T hD p n i) :=
  (acyclicRelativeCellChain T hD n).descInc_zeroPi2 p hp a hr he hf hD T.root i hi

/-- The actual descended inclusions form an arbitrary-length cellular
chain beginning literally at K. Strictness is regularCoverChain_proper. -/
def regularCoverTopChain (n : ℕ) : TopChainFS K (n + 1) where
  X := regularCoverChainStages T hD p n
  inc := regularCoverChainInclusion T hD p n
  incV := regularCoverChainInclusion_V T hD p n
  incE := regularCoverChainInclusion_E T hD p n
  incF := regularCoverChainInclusion_F T hD p n
  conn := regularCoverChain_connected T hD p hp n
  base := Hom.id K
  baseV := Function.injective_id
  baseE := Function.injective_id
  baseF := Function.injective_id
  zero_pi2 := regularCoverChain_zeroPi2 T hD p hp a hr he hf n

end FiniteChains.Comb
