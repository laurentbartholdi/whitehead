import Mathlib

/-!
# The group pushout of Proposition 3.11

Step 1 of the proof of Proposition 3.11 computes the fundamental group of the cellular
pushout `E_i = K ∪_{p : D → K} L_i`.  With `G = π₁(K)`, `N = p_*π₁(D)` and `J_i = π₁(L_i)`,
the map `π₁(D) → J_i` is trivial, so van Kampen gives

  `π₁(E_i) = G *_N J_i = H * J_i`,   `H = G/N`,

"a group pushout; no injection of `N` into `J_i` is assumed.  The resulting free factors do
embed."

This file proves exactly that group-theoretic statement, for an arbitrary normal subgroup
`N ◁ G` and an arbitrary group `J`: the free product `(G ⧸ N) * J` together with the two
obvious maps *is* the pushout of `G ← N → J` when the right-hand map is trivial, and both
free factors embed into it.  The topological input (van Kampen for the cellular pushout) is
not formalized; only its output is.
-/

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains

namespace Descent

open Monoid

variable (G J : Type*) [Group G] [Group J] (N : Subgroup G) [N.Normal]

/-- The group `H * J` of (3.4), with `H = G/N`. -/
abbrev PushoutGroup := Coprod (G ⧸ N) J

variable {G J N}

/-- The map `π₁(K) = G → π₁(E) = H * J` induced by `K ⊂ E`. -/
def fromBase : G →* PushoutGroup G J N :=
  (Coprod.inl : (G ⧸ N) →* PushoutGroup G J N).comp (QuotientGroup.mk' N)

/-- The map `π₁(L) = J → π₁(E) = H * J` induced by `L ⊂ E`. -/
def fromFibre : J →* PushoutGroup G J N := Coprod.inr

/-- The two maps agree on `N`: both kill it, the first because `N` is divided out, the second
because the map `π₁(D) → π₁(L)` is trivial. -/
theorem fromBase_eq_one_of_mem {n : G} (hn : n ∈ N) : fromBase (J := J) (N := N) n = 1 := by
  have h : (QuotientGroup.mk' N) n = 1 := (QuotientGroup.eq_one_iff n).mpr hn
  show (Coprod.inl : (G ⧸ N) →* PushoutGroup G J N) ((QuotientGroup.mk' N) n) = 1
  rw [h, map_one]

/-- **The pushout property.**  Given any group `K` and maps `f : G → K`, `g : J → K` whose
composites with `N → G` and the trivial map `N → J` agree — that is, `f` kills `N` — there is
a unique map `H * J → K` compatible with both. -/
theorem pushout_universal {K : Type*} [Group K] (f : G →* K) (g : J →* K)
    (hf : ∀ n ∈ N, f n = 1) :
    ∃! h : PushoutGroup G J N →* K,
      h.comp (fromBase (J := J) (N := N)) = f ∧ h.comp (fromFibre (G := G) (N := N)) = g := by
  refine ⟨Coprod.lift (QuotientGroup.lift N f hf) g, ⟨?_, rfl⟩, ?_⟩
  · ext x
    simp [fromBase, Coprod.lift_apply_inl]
  · rintro h ⟨h1, h2⟩
    refine Coprod.hom_ext ?_ h2
    ext a
    have := congrArg (fun k : G →* K => k a) h1
    simpa [fromBase, Coprod.lift_apply_inl] using this

/-- The quotient `H = G/N` embeds in the pushout: one of the "free factors that do embed". -/
theorem fromBase_quotient_injective :
    Function.Injective (Coprod.inl : (G ⧸ N) →* PushoutGroup G J N) :=
  Coprod.inl_injective

/-- The other free factor `J` embeds in the pushout. -/
theorem fromFibre_injective : Function.Injective (fromFibre (G := G) (N := N) (J := J)) :=
  Coprod.inr_injective

/-- The kernel of `π₁(K) → π₁(E)` is exactly `N`: downstairs the cover's fundamental group
dies, and nothing else does. -/
theorem ker_fromBase : (fromBase (J := J) (N := N)).ker = N := by
  ext a
  constructor
  · intro ha
    have h1 : (QuotientGroup.mk' N) a = 1 :=
      fromBase_quotient_injective (J := J) (by simpa [fromBase] using ha)
    exact (QuotientGroup.eq_one_iff a).mp (by simpa using h1)
  · intro ha
    exact fromBase_eq_one_of_mem ha

end Descent

end FiniteChains
