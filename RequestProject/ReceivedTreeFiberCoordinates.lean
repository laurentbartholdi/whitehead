import RequestProject.ReceivedTreeComparison

/-! Exact sheet coordinates over each cell when the geometric receiver is
surjective. This applies before substitution to the spine/old-block group
equivalence; no surjectivity of a substituted group map is assumed.
Pending final Lean verification.
-/

namespace FiniteChains.Comb.ReceivedTree
open SpanningTree
universe u
variable {K Y : Complex2.{u}} (T : SpanningTree K) (f : Hom K Y)
  {G : Type u} [Group G] (ψ : G →* Pi1 Y (f.onV T.root))

/-- Every actual lift of the image of a vertex has a receiving-group sheet. -/
theorem receiverVertex_fiber_surjective (hψ : Function.Surjective ψ)
    (a : K.V) (v : UV Y (f.onV T.root)) (hv : endV v = f.onV a) :
    ∃ g : G, receiverVertex T f ψ g a = v := by
  have he : endV (mappedTreeReference T f a) = endV v :=
    (mappedTreeReference_end T f a).trans hv.symm
  obtain ⟨d, hd, _⟩ := (isRegular_univProj (X := Y) (x₀ := f.onV T.root)).simply_transitive
    (mappedTreeReference T f a) v he
  obtain ⟨g, rfl⟩ := hψ d
  exact ⟨g, hd⟩

theorem receiverVertex_fiber_injective (hψ : Function.Injective ψ) (a : K.V) :
    Function.Injective (fun g : G => receiverVertex T f ψ g a) := by
  intro g h hgh
  apply hψ
  obtain ⟨d, _, hd⟩ := (isRegular_univProj (X := Y) (x₀ := f.onV T.root)).simply_transitive
    (mappedTreeReference T f a) (receiverVertex T f ψ g a)
    ((mappedTreeReference_end T f a).trans (receiverVertex_end T f ψ g a).symm)
  exact (hd (ψ g) rfl).trans (hd (ψ h) hgh.symm).symm

/-- The based-face coordinate is also exact, not merely a homology class. -/
theorem receiverFace_fiber_surjective (hψ : Function.Surjective ψ)
    (t : K.F) (v : UF Y (f.onV T.root)) (hv : v.1.2 = f.onF t) :
    ∃ g : G, receiverFace T f ψ g t = v := by
  have he : endV v.1.1 = f.onV (K.base t) :=
    v.2.trans ((congrArg Y.base hv).trans (f.base_onF t))
  obtain ⟨g, hg⟩ := receiverVertex_fiber_surjective T f ψ hψ (K.base t) v.1.1 he
  refine ⟨g, Subtype.ext ?_⟩
  exact Prod.ext hg hv.symm

theorem receiverEdge_fiber_surjective (hψ : Function.Surjective ψ)
    (e : K.E) (v : UE Y (f.onV T.root)) (hv : v.1.2 = f.onE e) :
    ∃ g : G, receiverEdge T f ψ g e = v := by
  have he : endV v.1.1 = f.onV (K.src e) :=
    v.2.trans ((congrArg Y.src hv).trans (f.src_onE e))
  obtain ⟨g, hg⟩ := receiverVertex_fiber_surjective T f ψ hψ (K.src e) v.1.1 he
  refine ⟨g, Subtype.ext ?_⟩
  exact Prod.ext hg hv.symm

/-- All pairs consisting of a source face and an actual lift of its geometric
image have unique coordinates when the receiver is a group equivalence. -/
noncomputable def receiverFaceCoordinates (hψ : Function.Bijective ψ) :
    (G × K.F) ≃ {z : UF Y (f.onV T.root) × K.F // z.1.1.2 = f.onF z.2} :=
  Equiv.ofBijective (fun z => ⟨(receiverFace T f ψ z.1 z.2, z.2), rfl⟩) (by
    constructor
    · rintro ⟨g, t⟩ ⟨h, s⟩ he
      have ht : t = s := congrArg (fun z => z.1.2) he
      subst s
      have hv := congrArg (fun z => z.1.1.1.1) he
      exact Prod.ext (receiverVertex_fiber_injective T f ψ hψ.1 (K.base t) hv) rfl
    · rintro ⟨⟨v, t⟩, hv⟩
      obtain ⟨g, hg⟩ := receiverFace_fiber_surjective T f ψ hψ.2 t v hv
      exact ⟨(g, t), Subtype.ext (Prod.ext hg rfl)⟩)

end FiniteChains.Comb.ReceivedTree
