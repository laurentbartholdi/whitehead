import RequestProject.OrderNervePosetCoverVertexStars

namespace FiniteChains.Comb
open CategoryTheory Simplicial Topology
open scoped Classical

/-- The actual open vertex star, defined by positivity of its global coordinate. -/
def orderNerveRealizationOpenStar (P : Type) [PartialOrder P] (v : P) :
    Set (orderNerveRealization P) := {x | 0 < orderNerveRealizationCoordinates P x v}

/-- Coordinate positivity defines an open subset of the actual realization. -/
theorem orderNerveRealizationOpenStar_isOpen (P : Type) [PartialOrder P] (v : P) :
    IsOpen (orderNerveRealizationOpenStar P v) := by
  exact isOpen_Ioi.preimage ((continuous_apply v).comp
    (orderNerveRealizationCoordinates P).continuous)

/-- On simplex interiors, open-star membership is exactly vertex membership. -/
theorem orderNerveRealizationSimplex_mem_openStar_iff {P : Type} [PartialOrder P]
    {n : SimplexCategory} (s : (nerve P).obj (Opposite.op n))
    (z : SimplexCategory.toTop.obj n) (hz : ∀ i, 0 < z.down.weights i) (v : P) :
    orderNerveRealizationSimplex P s z ∈ orderNerveRealizationOpenStar P v ↔
      v ∈ Set.range s.obj := by
  have he := congrArg (fun k => k z)
    (orderNerveAffineRealization_simplex (fun p => if p = v then 1 else 0) s)
  change orderNerveRealizationCoordinates P (orderNerveRealizationSimplex P s z) v =
    orderNerveAffineSimplex (fun p => if p = v then 1 else 0) s z at he
  change 0 < orderNerveRealizationCoordinates P (orderNerveRealizationSimplex P s z) v ↔ _
  rw [he]
  exact orderNerveAffineSimplex_indicator_pos_iff s z hz v

/-- Actual open vertex stars cover the whole realization. -/
theorem orderNerveRealizationOpenStar_cover (P : Type) [PartialOrder P]
    (x : orderNerveRealization P) : ∃ v, x ∈ orderNerveRealizationOpenStar P v := by
  obtain ⟨n, s, z, hz, he⟩ := orderNerveRealization_interior_cover P x
  refine ⟨s.val.obj 0, ?_⟩
  rw [← he]
  exact (orderNerveRealizationSimplex_mem_openStar_iff s.val z hz _).mpr ⟨0, rfl⟩

/-- Every point of an open star lies in the genuine comparable-vertex CW carrier. -/
theorem orderNerveRealizationOpenStar_subset_subcomplex {P : Type} [PartialOrder P]
    (v : P) : orderNerveRealizationOpenStar P v ⊆
      (orderNerveRealizationSubcomplex P (orderNerveVertexStar P v) :
        Set (orderNerveRealization P)) := by
  intro x hx
  obtain ⟨n, s, z, hz, he⟩ := orderNerveRealization_interior_cover P x
  rw [← he] at hx ⊢
  obtain ⟨i, hi⟩ := (orderNerveRealizationSimplex_mem_openStar_iff s.val z hz v).mp hx
  apply orderNerveRealizationSimplex_supported (orderNerveVertexStar P v) s.val _ ⟨z, rfl⟩
  intro j
  rcases le_total j i with h | h
  · exact Or.inl (hi ▸ leOfHom (s.val.map (homOfLE h)))
  · exact Or.inr (hi ▸ leOfHom (s.val.map (homOfLE h)))

/-- Open stars over distinct lifts of one vertex are disjoint. -/
theorem IsPosetCover.realizationOpenStar_disjoint {P Q : Type}
    [PartialOrder P] [PartialOrder Q] {f : P → Q} (hf : IsPosetCover f)
    {a b : P} (hab : a ≠ b) (he : f a = f b) :
    Disjoint (orderNerveRealizationOpenStar P a) (orderNerveRealizationOpenStar P b) := by
  apply Set.disjoint_left.mpr
  intro x hxa hxb
  obtain ⟨n, s, z, hz, hx⟩ := orderNerveRealization_interior_cover P x
  rw [← hx] at hxa hxb
  obtain ⟨i, hi⟩ := (orderNerveRealizationSimplex_mem_openStar_iff s.val z hz a).mp hxa
  obtain ⟨j, hj⟩ := (orderNerveRealizationSimplex_mem_openStar_iff s.val z hz b).mp hxb
  have hij : f (s.val.obj i) = f (s.val.obj j) := by rw [hi, hj, he]
  rcases le_total i j with h | h
  · have hs := hf.up_inj (le_refl (s.val.obj i))
      (leOfHom (s.val.map (homOfLE h))) hij
    exact hab (hi.symm.trans (hs.trans hj))
  · have hs := hf.up_inj (le_refl (s.val.obj j))
      (leOfHom (s.val.map (homOfLE h))) hij.symm
    exact hab (hi.symm.trans (hs.symm.trans hj))

/-- The preimage of an open star is exactly the union of stars at its lifted vertices. -/
theorem orderNerveRealizationMap_mem_openStar_iff {P Q : Type}
    [PartialOrder P] [PartialOrder Q] (f : P → Q) (hf : Monotone f)
    (x : orderNerveRealization P) (q : Q) :
    orderNerveRealizationMap f hf x ∈ orderNerveRealizationOpenStar Q q ↔
      ∃ p : P, f p = q ∧ x ∈ orderNerveRealizationOpenStar P p := by
  obtain ⟨n, s, z, hz, hx⟩ := orderNerveRealization_interior_cover P x
  rw [← hx]
  have hn := congrArg (fun k => k z) (orderNerveRealizationSimplex_natural f hf s.val)
  change orderNerveRealizationMap f hf (orderNerveRealizationSimplex P s.val z) =
    orderNerveRealizationSimplex Q ((nerveMap hf.functor).app _ s.val) z at hn
  rw [hn, orderNerveRealizationSimplex_mem_openStar_iff _ z hz]
  constructor
  · rintro ⟨i, hi⟩
    refine ⟨s.val.obj i, hi, ?_⟩
    exact (orderNerveRealizationSimplex_mem_openStar_iff s.val z hz _).mpr ⟨i, rfl⟩
  · rintro ⟨p, hp, hxp⟩
    obtain ⟨i, hi⟩ := (orderNerveRealizationSimplex_mem_openStar_iff s.val z hz p).mp hxp
    exact ⟨i, (congrArg f hi).trans hp⟩

end FiniteChains.Comb
