import RequestProject.RelatorCircleAttachingStrict
import RequestProject.PresCylinderCollapsedRoseLinear
import RequestProject.RoseCoverLetterChain

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains.PresModel
open Comb
universe u
variable {α J P : Type u} [PartialOrder P] (w : J → List (α × Bool)) (j : J)
  (f : P → CylBase w) (hf : IsPosetCover f) (m : RelatorCircle w j → P)
  (hm : StrictMono m) (hp : ∀ x, f (m x) = cylOuter (aHom w) x.val)

/-- The actual collapsed attaching-circle vertices in the actual rose preimage. -/
noncomputable def cylinderCoverCollapsedCircle (x : RelatorCircle w j) : cylinderCoverRoseSet w f :=
  ⟨cylinderCoverCollapse w hf (m x), cylinderCoverCollapse_mem_rose w f hf (m x)⟩

include hp in
/-- Actual collapse projects to the actual letter attaching map. -/
theorem cylinderCoverCollapsedCircle_projection (x : RelatorCircle w j) :
    cylinderCoverRoseEnd w f (cylinderCoverCollapsedCircle w j f hf m x) = aFun w x.val := by
  have h := cylinderCoverRoseEnd_projection w f (cylinderCoverCollapsedCircle w j f hf m x)
  change cylIn (aHom w) _ = f (cylinderCoverCollapse w hf (m x)) at h
  rw (config := { transparency := .default }) [cylinderCoverCollapse_projection w hf (m x), hp x] at h
  exact Sum.inl.inj h

include hm hp in
/-- The actual collapsed circle map is strict because its actual attaching projection is strict. -/
theorem cylinderCoverCollapsedCircle_strictMono :
    StrictMono (cylinderCoverCollapsedCircle w j f hf m) := by
  intro x y h
  apply lt_of_le_of_ne ((cylinderCoverCollapse_monotone w hf) (hm h).le)
  intro he
  have hs : cylinderCoverCollapsedCircle w j f hf m x = cylinderCoverCollapsedCircle w j f hf m y := Subtype.ext he
  have hp' := congrArg (cylinderCoverRoseEnd w f) hs
  rw (config := { transparency := .default }) [cylinderCoverCollapsedCircle_projection w j f hf m hp,
    cylinderCoverCollapsedCircle_projection w j f hf m hp] at hp'
  exact (relatorCircleAttaching_strictMono w j h).ne hp'

include hm hp in
/-- Actual collapsed circle chains include as the normalized collapse of the original lifted chains. -/
theorem cylinderCoverCollapsedCircle_chain_inclusion
    (c : StrictOrdEdge (RelatorCircle w j) →₀ ℤ) :
    chain1 (strictSubposetIncl (cylinderCoverRoseSet w f))
      (chain1 (strictOrderCxMap (cylinderCoverCollapsedCircle w j f hf m)
        (cylinderCoverCollapsedCircle_strictMono w j f hf m hm hp)) c) =
      normalizedStrictChain1 (cylinderCoverCollapse w hf) (cylinderCoverCollapse_monotone w hf)
        (chain1 (strictOrderCxMap m hm) c) := by
  classical
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd => simp only [map_add, hc, hd]
  | single e n =>
    change Finsupp.mapDomain (strictSubposetIncl (cylinderCoverRoseSet w f)).onE
      (Finsupp.mapDomain (strictOrderCxMap (cylinderCoverCollapsedCircle w j f hf m)
        (cylinderCoverCollapsedCircle_strictMono w j f hf m hm hp)).onE (Finsupp.single e n)) =
      normalizedStrictChain1 _ _ (Finsupp.mapDomain (strictOrderCxMap m hm).onE (Finsupp.single e n))
    rw (config := { transparency := .default }) [Finsupp.mapDomain_single, Finsupp.mapDomain_single, Finsupp.mapDomain_single,
      normalizedStrictChain1_single]
    have hn : cylinderCoverCollapse w hf (m e.val.1) ≠ cylinderCoverCollapse w hf (m e.val.2) :=
      fun he => (cylinderCoverCollapsedCircle_strictMono w j f hf m hm hp e.property).ne
        (Subtype.ext he)
    change Finsupp.single _ n = n • normalizeOrdEdge
      ⟨(cylinderCoverCollapse w hf (m e.val.1), cylinderCoverCollapse w hf (m e.val.2)), _⟩
    simp only [normalizeOrdEdge, dif_neg hn, Finsupp.smul_single, smul_eq_mul, mul_one]
    rfl

include hm hp in
/-- The actual linear rose pullback equals the actual collapsed circle chain map. -/
theorem cylinderCoverCollapsedCircle_chain
    (c : StrictOrdEdge (RelatorCircle w j) →₀ ℤ) :
    cylinderCoverCollapsedRoseChain w f hf (chain1 (strictOrderCxMap m hm) c) =
      chain1 (strictOrderCxMap (cylinderCoverCollapsedCircle w j f hf m)
        (cylinderCoverCollapsedCircle_strictMono w j f hf m hm hp)) c := by
  apply Finsupp.mapDomain_injective (strictSubposetIncl_onE_injective (cylinderCoverRoseSet w f))
  exact (cylinderCoverCollapsedRoseChain_inclusion w f hf _).trans
    (cylinderCoverCollapsedCircle_chain_inclusion w j f hf m hm hp c).symm

end FiniteChains.PresModel
