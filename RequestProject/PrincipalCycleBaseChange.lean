import RequestProject.MonoidAlgebraMapDomain
import RequestProject.BaseChangeCycles

/-!
# Principal matrix kernels under an injective group-ring extension

Let `f : H →* G` be injective, and let a matrix have entries in `ℤ[H]`,
arbitrarily many rows, and finitely many columns.  If each cycle over `ℤ[H]`
is a left multiple of a fixed vector `c`, then each cycle of the mapped
matrix over `ℤ[G]` is a left multiple of the image of `c`.

The proof identifies `H` with the actual subgroup `f(H)`, applies the proved
coset decomposition of matrix cycles, and observes that the multiples of
the image of `c` are closed under sums and left scalar multiplication.
It makes no assertion about arbitrary coinvariant functors.  The smaller
ring's principal-generation hypothesis is explicit; the geometric polygon
calculation has to supply it separately.


-/

namespace FiniteChains

open MonoidAlgebra

universe u v w x

variable {H : Type u} {G : Type v} [Group H] [Group G]
  {J : Type w} [Fintype J] {I : Type x}

/-- Principal generation of matrix cycles survives an injective group-ring extension.
Only the column type is finite.  Multiplication is in the indicated order,
so this applies to noncommutative group rings. -/
theorem principal_cycles_baseChange (f : H →* G) (hf : Function.Injective f)
    (A : I → J → MonoidAlgebra ℤ H) (c : J → MonoidAlgebra ℤ H)
    (hgen : ∀ y : J → MonoidAlgebra ℤ H,
      (∀ i, ∑ j, y j * A i j = 0) →
        ∃ r : MonoidAlgebra ℤ H, ∀ j, y j = r * c j)
    (v : J → MonoidAlgebra ℤ G)
    (hv : ∀ i, ∑ j, v j * MonoidAlgebra.mapDomainRingHom ℤ f (A i j) = 0) :
    ∃ r : MonoidAlgebra ℤ G,
      ∀ j, v j = r * MonoidAlgebra.mapDomainRingHom ℤ f (c j) := by
  classical
  let e : H ≃* f.range := MonoidHom.ofInjective hf
  let er : MonoidAlgebra ℤ H →+* MonoidAlgebra ℤ f.range :=
    MonoidAlgebra.mapDomainRingHom ℤ e.toMonoidHom
  let eri : MonoidAlgebra ℤ f.range →+* MonoidAlgebra ℤ H :=
    MonoidAlgebra.mapDomainRingHom ℤ e.symm.toMonoidHom
  have hinc (z : MonoidAlgebra ℤ H) :
      subRingHom f.range (er z) = MonoidAlgebra.mapDomainRingHom ℤ f z := by
    show MonoidAlgebra.mapDomain f.range.subtype (MonoidAlgebra.mapDomain e.toMonoidHom z) =
      MonoidAlgebra.mapDomain f z
    rw [← MonoidAlgebra.mapDomain_comp]
    rfl
  have her_inj : Function.Injective er := MonoidAlgebra.mapDomain_injective e.injective
  have her_eri (z : MonoidAlgebra ℤ f.range) : er (eri z) = z := by
    show MonoidAlgebra.mapDomain e.toMonoidHom
      (MonoidAlgebra.mapDomain e.symm.toMonoidHom z) = z
    rw [← MonoidAlgebra.mapDomain_comp]
    have he : (e.toMonoidHom : H → f.range) ∘
        (e.symm.toMonoidHom : f.range → H) = id := by
      funext g
      exact e.apply_symm_apply g
    rw [he, MonoidAlgebra.mapDomain_id]
  let Ar : I → J → MonoidAlgebra ℤ f.range := fun i j => er (A i j)
  have hvr : ∀ i, ∑ j, v j * subRingHom f.range (Ar i j) = 0 := by
    intro i
    simpa only [Ar, hinc] using hv i
  have hspan := cycle_mem_span_subgroup_cycles f.range Ar v hvr
  refine Submodule.span_induction
    (p := fun z _ => ∃ r : MonoidAlgebra ℤ G,
      ∀ j, z j = r * MonoidAlgebra.mapDomainRingHom ℤ f (c j))
    ?_ ?_ ?_ ?_ hspan
  · rintro z ⟨y, hy, rfl⟩
    have hy' : ∀ i, ∑ j, eri (y j) * A i j = 0 := by
      intro i
      apply her_inj
      rw [map_sum, map_zero]
      rw [← hy i]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [map_mul, her_eri]
    obtain ⟨r, hr⟩ := hgen (fun j => eri (y j)) hy'
    refine ⟨MonoidAlgebra.mapDomainRingHom ℤ f r, fun j => ?_⟩
    calc
      subRingHom f.range (y j) = MonoidAlgebra.mapDomainRingHom ℤ f (eri (y j)) := by
        rw [← hinc, her_eri]
      _ = MonoidAlgebra.mapDomainRingHom ℤ f (r * c j) :=
        congrArg (MonoidAlgebra.mapDomainRingHom ℤ f) (hr j)
      _ = MonoidAlgebra.mapDomainRingHom ℤ f r *
          MonoidAlgebra.mapDomainRingHom ℤ f (c j) := map_mul _ _ _
  · refine ⟨0, fun j => ?_⟩
    simp
  · rintro a b _ _ ⟨r, hr⟩ ⟨s, hs⟩
    refine ⟨r + s, fun j => ?_⟩
    change a j + b j = (r + s) * MonoidAlgebra.mapDomainRingHom ℤ f (c j)
    rw [hr j, hs j, add_mul]
  · rintro a z _ ⟨r, hr⟩
    refine ⟨a * r, fun j => ?_⟩
    change a * z j = (a * r) * MonoidAlgebra.mapDomainRingHom ℤ f (c j)
    rw [hr j, mul_assoc]

end FiniteChains
