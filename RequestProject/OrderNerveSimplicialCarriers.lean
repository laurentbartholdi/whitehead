import RequestProject.OrderNerveSingularInverseMap

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains.Comb
open CategoryTheory AlgebraicTopology TopologicalSingular
open scoped Simplicial
variable {P : Type} [PartialOrder P]

noncomputable abbrev orderSimplicialBoundary (P : Type) [PartialOrder P] (n : ℕ) :=
  (AlternatingFaceMapComplex.objD (mathlibOrderNerveModule P) n).hom

theorem orderSimplicialBoundary_squared (n : ℕ) (c : ComposableArrows P (n + 2) →₀ ℤ) :
    orderSimplicialBoundary P n (orderSimplicialBoundary P (n + 1) c) = 0 := by
  apply orderNerveGradedEncode_injective n
  rw (config := { transparency := .default }) [orderNerveGradedEncode_boundary, orderNerveGradedEncode_boundary, Nerve.bdry_bdry, map_zero]

theorem orderNerveGradedEncode_length (n : ℕ) (c : ComposableArrows P n →₀ ℤ) :
    Nerve.lengthProjection (n + 1) (orderNerveGradedEncode n c) = orderNerveGradedEncode n c := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd => simp only [map_add, hc, hd]
  | single s r =>
    rw (config := { transparency := .default }) [orderNerveGradedEncode_single, map_zsmul, Nerve.lengthProjection_of,
      if_pos (orderNerveVertexList_length s)]

theorem orderNerveGradedEncode_single_supported (n : ℕ) (s : ComposableArrows P n) :
    orderNerveGradedEncode n (Finsupp.single s 1) ∈ Nerve.IncOn (Set.range s.obj) := by
  rw (config := { transparency := .default }) [orderNerveGradedEncode_single, one_smul]
  apply Nerve.of_mem_incOn (orderNerveVertexList_chain s)
  intro p hp
  exact List.mem_ofFn.mp hp

theorem orderNerveSimplexCarrier_acyclic {n : ℕ} (s : ComposableArrows P n) :
    Nerve.AcyclicIn (Set.range s.obj) := by
  apply Nerve.acyclicIn_of_subtype _ ⟨s.obj 0, ⟨0, rfl⟩⟩
  intro c hc hz
  apply orderNerve_cycle_bounds_of_comparable (⟨s.obj 0, ⟨0, rfl⟩⟩ : Set.range s.obj) ?_ hc hz
  rintro ⟨p, ⟨i, rfl⟩⟩
  exact Or.inr (s.monotone (Fin.zero_le i))

theorem orderNerveSimplexCarrier_face {n : ℕ} (s : ComposableArrows P (n + 1))
    (i : Fin (n + 2)) : Set.range ((nerve P).δ i s).obj ⊆ Set.range s.obj := by
  rintro p ⟨j, rfl⟩
  exact ⟨i.succAbove j, rfl⟩

theorem orderSimplicialBoundary_map_carrier {n : ℕ}
    (f : (ComposableArrows P n →₀ ℤ) →ₗ[ℤ] Nerve.Ch P)
    (hf : ∀ s : ComposableArrows P n, f (Finsupp.single s 1) ∈ Nerve.IncOn (Set.range s.obj))
    (s : ComposableArrows P (n + 1)) :
    f (orderSimplicialBoundary P n (Finsupp.single s 1)) ∈ Nerve.IncOn (Set.range s.obj) := by
  rw (config := { transparency := .default }) [mathlibOrderNerve_d_single, map_sum]
  apply AddSubgroup.sum_mem
  intro i _
  rw (config := { transparency := .default }) [map_smul]
  apply AddSubgroup.zsmul_mem
  exact Nerve.incOn_mono (fun _ hp => orderNerveSimplexCarrier_face s i hp) (hf _)

theorem orderSimplicialMap_mem_inc {n : ℕ}
    (f : (ComposableArrows P n →₀ ℤ) →ₗ[ℤ] Nerve.Ch P)
    (hf : ∀ s : ComposableArrows P n, f (Finsupp.single s 1) ∈ Nerve.IncOn (Set.range s.obj))
    (c : ComposableArrows P n →₀ ℤ) : f c ∈ Nerve.Inc P := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd => simpa only [map_add] using (Nerve.Inc P).add_mem hc hd
  | single s r =>
    rw (config := { transparency := .default }) [show Finsupp.single s r = r • Finsupp.single s 1 by simp, map_smul]
    exact (Nerve.Inc P).zsmul_mem (Nerve.incOn_le_inc _ (hf s)) r

end FiniteChains.Comb
