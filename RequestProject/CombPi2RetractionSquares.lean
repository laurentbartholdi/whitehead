import RequestProject.ComponentComplex
import RequestProject.ZeroPi2Descent

/-! Transfer vanishing through a commuting square whose target vertical
map admits a cellular left inverse. Pending final Lean verification. -/

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains.Comb
universe u
variable {X Y Z X' Y' : Complex2.{u}}

theorem zeroPi2_comp_left (g : Hom Y Z) (f : Hom X Y) (hz : ZeroPi2 f) :
    ZeroPi2 (g.comp f) := by
  intro x c hc
  have he : Finsupp.mapDomain (univLift X (g.comp f) x).onF c =
      Finsupp.mapDomain (univLift Y g (f.onV x)).onF
        (Finsupp.mapDomain (univLift X f x).onF c) := by
    rw [← Finsupp.mapDomain_comp]
    exact Finsupp.mapDomain_congr fun F _ => (univLiftF_comp g f x F).symm
  change Finsupp.mapDomain (univLift X (g.comp f) x).onF c = 0
  have hz' : Finsupp.mapDomain (univLift X f x).onF c = 0 := hz x c hc
  rw [he, hz', Finsupp.mapDomain_zero]

theorem hom_retraction_square (f : Hom X Y) (g : Hom X' Y')
    (a : Hom X X') (b : Hom Y Y') (r : Hom Y' Y)
    (hV : ∀ y, r.onV (b.onV y) = y)
    (hE : ∀ y, r.onE (b.onE y) = y)
    (hF : ∀ y, r.onF (b.onF y) = y)
    (hsq : b.comp f = g.comp a) : r.comp (g.comp a) = f := by
  rw [← hsq]
  apply Hom.ext'
  · exact funext fun x => hV (f.onV x)
  · exact funext fun x => hE (f.onE x)
  · exact funext fun x => hF (f.onF x)

theorem zeroPi2_of_retraction_square (f : Hom X Y) (g : Hom X' Y')
    (a : Hom X X') (b : Hom Y Y') (r : Hom Y' Y)
    (hV : ∀ y, r.onV (b.onV y) = y)
    (hE : ∀ y, r.onE (b.onE y) = y)
    (hF : ∀ y, r.onF (b.onF y) = y)
    (hsq : b.comp f = g.comp a) (hz : ZeroPi2 g) : ZeroPi2 f := by
  have H := zeroPi2_comp_left r (g.comp a) (zeroPi2_comp_right g a hz)
  rwa [hom_retraction_square f g a b r hV hE hF hsq] at H

theorem pi1Trivial_comp_right (g : Hom Y Z) (f : Hom X Y) (hz : Pi1Trivial g) :
    Pi1Trivial (g.comp f) := by
  intro x p hp
  simpa only [mapPath_comp, Hom.comp, Function.comp_def] using hz (f.onV x) (mapPath f p) (isPath_mapPath f hp)

theorem pi1Trivial_of_retraction_square (f : Hom X Y) (g : Hom X' Y')
    (a : Hom X X') (b : Hom Y Y') (r : Hom Y' Y)
    (hV : ∀ y, r.onV (b.onV y) = y)
    (hE : ∀ y, r.onE (b.onE y) = y)
    (hF : ∀ y, r.onF (b.onF y) = y)
    (hsq : b.comp f = g.comp a) (hz : Pi1Trivial g) : Pi1Trivial f := by
  have H := Pi1Trivial.comp_left r (pi1Trivial_comp_right g a hz)
  rwa [hom_retraction_square f g a b r hV hE hF hsq] at H

end FiniteChains.Comb
