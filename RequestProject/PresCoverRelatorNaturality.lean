module

public import RequestProject.PresCoverConeCircleProjection
public import RequestProject.PosetCoverTopTriangle

@[expose] public section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains.Comb
universe u
variable {P Q : Type u} [PartialOrder P] [PartialOrder Q]
theorem strictOrderCxMap_onF_injective (k : P → Q) (hm : StrictMono k)
    (hi : Function.Injective k) : Function.Injective (strictOrderCxMap k hm).onF := by
  intro t s he
  apply Subtype.ext
  apply Prod.ext
  · exact hi (congrArg (fun r : StrictOrdTri Q => r.1.1) he)
  · apply Prod.ext
    · exact hi (congrArg (fun r : StrictOrdTri Q => r.1.2.1) he)
    · exact hi (congrArg (fun r : StrictOrdTri Q => r.1.2.2) he)
end FiniteChains.Comb

namespace FiniteChains.PresModel
open Comb
universe u
variable {α J P Q : Type u} [PartialOrder P] [PartialOrder Q]
  (w : J → List (α × Bool)) (f : P → PresPos w) (hf : IsPosetCover f)
  (hpos : ∀ j, 0 < (w j).length)

/-- The distinguished coordinate triangle is the unique triangle over its actual
first incidence with its actual apex. -/
theorem presCoverRelatorTriangle_unique (p : PresCoverRelator w f) (t : StrictOrdTri P)
    (ht : (strictOrderCxMap f hf.strictMono).onF t = presRelatorFirstTriangle w hpos p.1.2)
    (hv : t.1.2.2 = p.1.1) : t = presCoverRelatorTriangle w f hf hpos p := by
  let r := presCoverRelatorTriangle w f hf hpos p
  have he : (strictOrderCxMap f hf.strictMono).onF t =
      (strictOrderCxMap f hf.strictMono).onF r :=
    ht.trans (presCoverRelatorTriangle_projection w f hf hpos p).symm
  have hfa := congrArg (fun s : StrictOrdTri (PresPos w) => s.1.1) he
  have hfb := congrArg (fun s : StrictOrdTri (PresPos w) => s.1.2.1) he
  have ha : t.1.1 = r.1.1 := hf.down_inj (a := p.1.1)
    (hv ▸ (t.2.1.le.trans t.2.2.le)) (r.2.1.le.trans r.2.2.le) hfa
  have hb : t.1.2.1 = r.1.2.1 := hf.down_inj (a := p.1.1) (hv ▸ t.2.2.le) r.2.2.le hfb
  exact Subtype.ext (Prod.ext ha (Prod.ext hb hv))

/-- An actual map between presentation covers maps actual lifted relator apices. -/
def presCoverRelatorMap (f' : Q → PresPos w) (k : P → Q)
    (hk : ∀ x, f' (k x) = f x) (p : PresCoverRelator w f) : PresCoverRelator w f' :=
  ⟨(k p.1.1, p.1.2), (hk p.1.1).trans p.2⟩

/-- Actual maps of covers preserve the distinguished actual coordinate triangles. -/
theorem presCoverRelatorTriangle_natural (f' : Q → PresPos w) (hf' : IsPosetCover f')
    (k : P → Q) (hkm : StrictMono k) (hk : ∀ x, f' (k x) = f x)
    (p : PresCoverRelator w f) :
    (strictOrderCxMap k hkm).onF (presCoverRelatorTriangle w f hf hpos p) =
      presCoverRelatorTriangle w f' hf' hpos (presCoverRelatorMap w f f' k hk p) := by
  apply presCoverRelatorTriangle_unique w f' hf' hpos
  · have he : (strictOrderCxMap f' hf'.strictMono).onF
        ((strictOrderCxMap k hkm).onF (presCoverRelatorTriangle w f hf hpos p)) =
        (strictOrderCxMap f hf.strictMono).onF (presCoverRelatorTriangle w f hf hpos p) := by
      apply Subtype.ext
      apply Prod.ext
      · exact hk _
      · exact Prod.ext (hk _) (hk _)
    exact he.trans (presCoverRelatorTriangle_projection w f hf hpos p)
  · rfl

/-- The finite actual relator coordinates preserve coefficients under an actual
injective map between covers. -/
theorem presCoverRelatorChain_natural_apply (f' : Q → PresPos w)
    (hf' : IsPosetCover f') (k : P → Q) (hkm : StrictMono k)
    (hki : Function.Injective k) (hk : ∀ x, f' (k x) = f x)
    (c : StrictOrdTri P →₀ ℤ) (p : PresCoverRelator w f) :
    presCoverRelatorChain w f' hf' hpos (chain2 (strictOrderCxMap k hkm) c)
      (presCoverRelatorMap w f f' k hk p) = presCoverRelatorChain w f hf hpos c p := by
  rw (config := { transparency := .default }) [presCoverRelatorChain_apply, presCoverRelatorChain_apply,
    ← presCoverRelatorTriangle_natural w f hf hpos f' hf' k hkm hk p]
  exact Finsupp.mapDomain_apply_of_injective (strictOrderCxMap_onF_injective k hkm hki) c _

omit [PartialOrder P] [PartialOrder Q] in
theorem presCoverRelatorMap_injective (f' : Q → PresPos w) (k : P → Q)
    (hk : ∀ x, f' (k x) = f x) (hi : Function.Injective k) :
    Function.Injective (presCoverRelatorMap w f f' k hk) := by
  intro p q he
  apply Subtype.ext
  apply Prod.ext
  · exact hi (congrArg (fun r : PresCoverRelator w f' => r.1.1) he)
  · exact congrArg (fun r : PresCoverRelator w f' => r.1.2) he

omit [PartialOrder P] [PartialOrder Q] in
theorem presCoverRelatorMap_surjective (f' : Q → PresPos w) (k : P → Q)
    (hk : ∀ x, f' (k x) = f x) (hs : Function.Surjective k) :
    Function.Surjective (presCoverRelatorMap w f f' k hk) := by
  intro q
  obtain ⟨v, hv⟩ := hs q.1.1
  have hp : f v = apexOf w q.1.2 :=
    (hk v).symm.trans ((congrArg f' hv).trans q.2)
  refine ⟨⟨(v, q.1.2), hp⟩, ?_⟩
  exact Subtype.ext (Prod.ext hv rfl)

/-- Under a bijective actual map between covers, the complete finite coordinate
chain transforms by the actual map of lifted relators. -/
theorem presCoverRelatorChain_natural (f' : Q → PresPos w)
    (hf' : IsPosetCover f') (k : P → Q) (hkm : StrictMono k)
    (hki : Function.Injective k) (hks : Function.Surjective k)
    (hk : ∀ x, f' (k x) = f x) (c : StrictOrdTri P →₀ ℤ) :
    presCoverRelatorChain w f' hf' hpos (chain2 (strictOrderCxMap k hkm) c) =
      Finsupp.mapDomain (presCoverRelatorMap w f f' k hk)
        (presCoverRelatorChain w f hf hpos c) := by
  ext q
  obtain ⟨p, rfl⟩ := presCoverRelatorMap_surjective w f f' k hk hks q
  rw (config := { transparency := .default }) [Finsupp.mapDomain_apply_of_injective (presCoverRelatorMap_injective w f f' k hk hki)]
  exact presCoverRelatorChain_natural_apply w f hf hpos f' hf' k hkm hki hk c p

end FiniteChains.PresModel
