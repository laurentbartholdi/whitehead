module

public import RequestProject.PresCoverRelativeConeCylinder
public import RequestProject.PresCoverConeCircleProjection
public import RequestProject.StrictNormalizedOneMaps

@[expose] public section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

set_option maxHeartbeats 800000

namespace FiniteChains.PresModel.IdentityChains
open Comb Comb.StrictNormalized
universe u
variable {α J : Type u} (w : J → List (α × Bool))

def cover : IsPosetCover (id : PresPos w → PresPos w) :=
  ⟨monotone_id, Function.surjective_id,
    fun _ b h => ⟨b, ⟨h, rfl⟩, fun _ hz => hz.2⟩,
    fun _ b h => ⟨b, ⟨h, rfl⟩, fun _ hz => hz.2⟩⟩

/-- In the identity cover the actual lifted-apex labels are exactly the original labels. -/
def relatorEquiv : J ≃ PresCoverRelator w id where
  toFun j := ⟨(apexOf w j, j), rfl⟩
  invFun p := p.1.2
  left_inv _ := rfl
  right_inv p := Subtype.ext (Prod.ext p.2.symm rfl)

abbrev Base := {p : PresPos w // p ∈ coneAdjBaseSet (S := circSet w)}

noncomputable def baseIso : Base w ≃o CylBase w := coneAdjBaseOrderIso

noncomputable def baseProjection :
    (StrictOrdEdge (Base w) →₀ ℤ) →ₗ[ℤ] (StrictOrdEdge (CylBase w) →₀ ℤ) :=
  chain1 (strictOrderCxMap (baseIso w) (baseIso w).strictMono)

theorem baseProjection_injective : Function.Injective (baseProjection w) :=
  Finsupp.mapDomain_injective
    (strictOrderCxMap_onE_injective (baseIso w) (baseIso w).strictMono (baseIso w).injective)

theorem baseIso_collapse (p : Base w) :
    baseIso w (presCoverCylinderCollapse w id (cover w) p) =
      cylCollapse (aHom w) (baseIso w p) :=
  cylinderCoverCollapse_projection w (coneAdjCoverBaseEnd_isPosetCover id (cover w)) p

theorem baseProjection_collapse (c : StrictOrdEdge (Base w) →₀ ℤ) :
    baseProjection w (normalizedStrictChain1 (presCoverCylinderCollapse w id (cover w))
      (presCoverCylinderCollapse_monotone w id (cover w)) c) =
      normalizedStrictChain1 (cylCollapse (aHom w)) (cylCollapse_monotone (aHom w))
        (baseProjection w c) :=
  mapOne_semiconj (baseIso w) (baseIso w).strictMono _ _ _ _ (baseIso_collapse w) c

def circleIntoCylinder (j : J) : RelatorCircle w j → CylBase w :=
  fun x => cylOuter (aHom w) x.val

theorem circleIntoCylinder_strictMono (j : J) : StrictMono (circleIntoCylinder w j) := by
  intro a b h
  exact lt_of_le_of_ne h.le (fun he => h.ne (Subtype.ext (Sum.inr.inj he)))

noncomputable def cylinderBoundary (j : J) : StrictOrdEdge (CylBase w) →₀ ℤ :=
  mapOne (circleIntoCylinder w j) (circleIntoCylinder_strictMono w j).monotone
    (relatorCircleFundamentalChain w j)

theorem baseIso_circle (p : PresCoverRelator w id) (x : RelatorCircle w p.1.2) :
    baseIso w (presCoverCircleCylinderInclusion w id (cover w) p x) =
      circleIntoCylinder w p.1.2 x := by
  apply (Sum.inl_injective : Function.Injective (Sum.inl : CylBase w → PresPos w))
  exact (coneAdjCoverBaseEnd_spec id
    (presCoverCircleCylinderInclusion w id (cover w) p x)).trans
      (presCoverConeCircleOrderIso_symm_projection w id (cover w) p.1.1 p.1.2 p.2 x)

theorem baseProjection_relatorBoundary (p : PresCoverRelator w id) :
    baseProjection w (presCoverCylinderRelatorBoundary w id (cover w) p) =
      cylinderBoundary w p.1.2 := by
  change chain1 (strictOrderCxMap (baseIso w) (baseIso w).strictMono)
    (chain1 (strictOrderCxMap (presCoverCircleCylinderInclusion w id (cover w) p)
      (presCoverCircleCylinderInclusion_strictMono w id (cover w) p)) _) = _
  rw (config := { transparency := .default }) [← mapOne_strict (baseIso w) (baseIso w).strictMono,
    ← mapOne_strict _ (presCoverCircleCylinderInclusion_strictMono w id (cover w) p)]
  erw [mapOne_comp (presCoverCircleCylinderInclusion w id (cover w) p)
    (presCoverCircleCylinderInclusion_strictMono w id (cover w) p).monotone
    (baseIso w) (baseIso w).monotone (relatorCircleFundamentalChain w p.1.2)]
  have he : baseIso w ∘ presCoverCircleCylinderInclusion w id (cover w) p =
      circleIntoCylinder w p.1.2 := funext (baseIso_circle w p)
  simp only [he]
  rfl

/-- The actual cylinder retraction, in literal rose-edge coordinates. -/
noncomputable def roseProjection :
    (StrictOrdEdge (Base w) →₀ ℤ) →ₗ[ℤ] (StrictOrdEdge (Rose α) →₀ ℤ) :=
  (mapOne (cylRetr (aHom w)) (cylRetr_monotone (aHom w))).comp (baseProjection w)

theorem baseProjection_collapse_eq (c : StrictOrdEdge (Base w) →₀ ℤ) :
    baseProjection w (normalizedStrictChain1 (presCoverCylinderCollapse w id (cover w))
      (presCoverCylinderCollapse_monotone w id (cover w)) c) =
      mapOne (cylIn (aHom w)) (cylIn_monotone (aHom w)) (roseProjection w c) := by
  rw (config := { transparency := .default }) [baseProjection_collapse]
  change mapOne (cylCollapse (aHom w)) _ (baseProjection w c) =
    mapOne (cylIn (aHom w)) _ (mapOne (cylRetr (aHom w)) _ (baseProjection w c))
  rw [mapOne_comp]; rfl

theorem collapsed_eq_zero_of_roseProjection_eq_zero
    (c : StrictOrdEdge (Base w) →₀ ℤ) (hc : roseProjection w c = 0) :
    normalizedStrictChain1 (presCoverCylinderCollapse w id (cover w))
      (presCoverCylinderCollapse_monotone w id (cover w)) c = 0 := by
  apply baseProjection_injective w
  rw (config := { transparency := .default }) [baseProjection_collapse_eq, hc, map_zero]

theorem roseProjection_collapse (c : StrictOrdEdge (Base w) →₀ ℤ) :
    roseProjection w (normalizedStrictChain1 (presCoverCylinderCollapse w id (cover w))
      (presCoverCylinderCollapse_monotone w id (cover w)) c) = roseProjection w c := by
  change mapOne (cylRetr (aHom w)) _ (baseProjection w _) = _
  rw (config := { transparency := .default }) [baseProjection_collapse_eq, mapOne_comp]
  change mapOne id monotone_id (roseProjection w c) = _
  exact mapOne_id _

def roseIntoBase (x : Rose α) : Base w :=
  ⟨ConeAdj.inc (cylIn (aHom w) x), ⟨cylIn (aHom w) x, rfl⟩⟩

theorem roseIntoBase_strictMono : StrictMono (roseIntoBase w) := by
  intro a b h
  exact lt_of_le_of_ne h.le (fun he => h.ne (Sum.inl.inj (Sum.inl.inj (congrArg Subtype.val he))))

theorem baseIso_roseIntoBase (x : Rose α) : baseIso w (roseIntoBase w x) = cylIn (aHom w) x :=
  (baseIso w).apply_symm_apply (cylIn (aHom w) x)

noncomputable def roseInclusion :
    (StrictOrdEdge (Rose α) →₀ ℤ) →ₗ[ℤ] (StrictOrdEdge (Base w) →₀ ℤ) :=
  chain1 (strictOrderCxMap (roseIntoBase w) (roseIntoBase_strictMono w))

theorem roseProjection_inclusion (c : StrictOrdEdge (Rose α) →₀ ℤ) :
    roseProjection w (roseInclusion w c) = c := by
  change mapOne (cylRetr (aHom w)) _
    (chain1 (strictOrderCxMap (baseIso w) (baseIso w).strictMono)
      (chain1 (strictOrderCxMap (roseIntoBase w) (roseIntoBase_strictMono w)) c)) = c
  rw (config := { transparency := .default }) [← mapOne_strict (baseIso w) (baseIso w).strictMono,
    ← mapOne_strict (roseIntoBase w) (roseIntoBase_strictMono w), mapOne_comp, mapOne_comp]
  have he : (cylRetr (aHom w) ∘ baseIso w) ∘ roseIntoBase w = id := by
    funext x
    exact congrArg (cylRetr (aHom w)) (baseIso_roseIntoBase w x)
  simpa only [he] using (mapOne_id c)

end FiniteChains.PresModel.IdentityChains
