import RequestProject.CmpNerve
import RequestProject.OrderNormalizationNaturality

/-! Explicit finite barycentric subdivision in degrees one and two.
Proof terms only; not compiled under the current workflow. -/

noncomputable section
open scoped Classical

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains.Davis
open RACG Mirror Comb
universe u
variable {P Q : Type u} [PartialOrder P] [PartialOrder Q]

/-- Image of a finite nonempty chain under a monotone map. Repeated images
are removed from the simplex, without discarding their chain coefficients. -/
def barycentricMap (f : P → Q) (hf : Monotone f) (σ : NeSpx (cmpRel P)) :
    NeSpx (cmpRel Q) :=
  ⟨σ.1.image f, σ.2.1.image f, by
    apply isSimplex_cmpRel_iff.mpr
    intro a ha b hb
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hb
    exact ((isSimplex_cmpRel_iff.mp σ.2.2) x hx y hy).imp (fun h => hf h) (fun h => hf h)⟩

theorem barycentricMap_monotone (f : P → Q) (hf : Monotone f) :
    Monotone (barycentricMap f hf) := fun _ _ h => Finset.image_mono f h

@[simp] theorem barycentricMap_spx1 (f : P → Q) (hf : Monotone f) (a : P) :
    barycentricMap f hf (spx1 a) = spx1 (f a) := by
  apply Subtype.ext
  simp [barycentricMap, spx1]

@[simp] theorem barycentricMap_spx2 (f : P → Q) (hf : Monotone f)
    {a b : P} (hab : a ≤ b) :
    barycentricMap f hf (spx2 hab) = spx2 (hf hab) := by
  apply Subtype.ext
  simp [barycentricMap, spx2]

@[simp] theorem chainMax_barycentricMap (f : P → Q) (hf : Monotone f)
    (σ : NeSpx (cmpRel P)) :
    chainMax (barycentricMap f hf σ) = f (chainMax σ) := by
  apply le_antisymm
  · obtain ⟨x, hx, he⟩ := Finset.mem_image.mp (chainMax_mem (barycentricMap f hf σ))
    rw [← he]
    exact hf (le_chainMax σ hx)
  · exact le_chainMax (barycentricMap f hf σ)
      (Finset.mem_image.mpr ⟨chainMax σ, chainMax_mem σ, rfl⟩)

def spx3 {a b c : P} (hab : a ≤ b) (hbc : b ≤ c) : NeSpx (cmpRel P) :=
  ⟨{a, b, c}, by simp, by
    apply isSimplex_cmpRel_iff.mpr
    intro x hx y hy
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
    rcases hx with rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl
    exacts [Or.inl le_rfl, Or.inl hab, Or.inl (hab.trans hbc),
      Or.inr hab, Or.inl le_rfl, Or.inl hbc,
      Or.inr (hab.trans hbc), Or.inr hbc, Or.inl le_rfl]⟩

theorem spx2_le_spx3_left {a b c : P} (hab : a ≤ b) (hbc : b ≤ c) :
    spx2 hab ≤ spx3 hab hbc := by
  intro x hx
  simp only [spx2_val, Finset.mem_insert, Finset.mem_singleton] at hx
  rcases hx with rfl | rfl <;> simp [spx3]

theorem spx2_le_spx3_outer {a b c : P} (hab : a ≤ b) (hbc : b ≤ c) :
    spx2 (hab.trans hbc) ≤ spx3 hab hbc := by
  intro x hx
  simp only [spx2_val, Finset.mem_insert, Finset.mem_singleton] at hx
  rcases hx with rfl | rfl <;> simp [spx3]

theorem spx2_le_spx3_right {a b c : P} (hab : a ≤ b) (hbc : b ≤ c) :
    spx2 hbc ≤ spx3 hab hbc := by
  intro x hx
  simp only [spx2_val, Finset.mem_insert, Finset.mem_singleton] at hx
  rcases hx with rfl | rfl <;> simp [spx3]

@[simp] theorem chainMax_spx3 {a b c : P} (hab : a ≤ b) (hbc : b ≤ c) :
    chainMax (spx3 hab hbc) = c := by
  apply le_antisymm
  · have h := chainMax_mem (spx3 hab hbc)
    simp only [spx3, Finset.mem_insert, Finset.mem_singleton] at h
    rcases h with h | h | h
    · exact (le_of_eq h).trans (hab.trans hbc)
    · exact (le_of_eq h).trans hbc
    · exact le_of_eq h
  · exact le_chainMax (spx3 hab hbc) (by simp [spx3])

@[simp] theorem barycentricMap_spx3 (f : P → Q) (hf : Monotone f)
    {a b c : P} (hab : a ≤ b) (hbc : b ≤ c) :
    barycentricMap f hf (spx3 hab hbc) = spx3 (hf hab) (hf hbc) := by
  apply Subtype.ext
  simp [barycentricMap, spx3]

def barycentricFlag (x : P) (e t : NeSpx (cmpRel P))
    (hxe : spx1 x ≤ e) (het : e ≤ t) : OrdTri (NeSpx (cmpRel P)) :=
  ⟨(spx1 x, e, t), hxe, het⟩

def barycentricEdge (e : OrdEdge P) : OrdEdge (NeSpx (cmpRel P)) →₀ ℤ :=
  Finsupp.single ⟨(spx1 e.1.1, spx2 e.2), spx1_le_spx2_left e.2⟩ 1 -
    Finsupp.single ⟨(spx1 e.1.2, spx2 e.2), spx1_le_spx2_right e.2⟩ 1

def barycentricTriangle (t : OrdTri P) : OrdTri (NeSpx (cmpRel P)) →₀ ℤ :=
  Finsupp.single (barycentricFlag t.1.2.1 (spx2 t.2.2) (spx3 t.2.1 t.2.2)
    (spx1_le_spx2_left t.2.2) (spx2_le_spx3_right t.2.1 t.2.2)) 1 -
  Finsupp.single (barycentricFlag t.1.2.2 (spx2 t.2.2) (spx3 t.2.1 t.2.2)
    (spx1_le_spx2_right t.2.2) (spx2_le_spx3_right t.2.1 t.2.2)) 1 -
  Finsupp.single (barycentricFlag t.1.1 (spx2 (t.2.1.trans t.2.2)) (spx3 t.2.1 t.2.2)
    (spx1_le_spx2_left _) (spx2_le_spx3_outer t.2.1 t.2.2)) 1 +
  Finsupp.single (barycentricFlag t.1.2.2 (spx2 (t.2.1.trans t.2.2)) (spx3 t.2.1 t.2.2)
    (spx1_le_spx2_right _) (spx2_le_spx3_outer t.2.1 t.2.2)) 1 +
  Finsupp.single (barycentricFlag t.1.1 (spx2 t.2.1) (spx3 t.2.1 t.2.2)
    (spx1_le_spx2_left _) (spx2_le_spx3_left t.2.1 t.2.2)) 1 -
  Finsupp.single (barycentricFlag t.1.2.1 (spx2 t.2.1) (spx3 t.2.1 t.2.2)
    (spx1_le_spx2_right _) (spx2_le_spx3_left t.2.1 t.2.2)) 1

def barycentricChain1 : (OrdEdge P →₀ ℤ) →ₗ[ℤ] (OrdEdge (NeSpx (cmpRel P)) →₀ ℤ) :=
  Finsupp.linearCombination ℤ barycentricEdge

def barycentricChain2 : (OrdTri P →₀ ℤ) →ₗ[ℤ] (OrdTri (NeSpx (cmpRel P)) →₀ ℤ) :=
  Finsupp.linearCombination ℤ barycentricTriangle

theorem barycentricTriangle_boundary (t : OrdTri P) :
    Comb.bdry2 (orderCx (NeSpx (cmpRel P))) (barycentricTriangle t) =
      barycentricChain1 (Comb.bdry2 (orderCx P) (Finsupp.single t 1)) := by
  simp only [barycentricTriangle, map_add, map_sub, map_smul, Comb.bdry2_single, one_smul]
  simp only [pathChain, orderCx, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  simp only [map_add, map_neg, map_smul]
  simp [barycentricTriangle, barycentricFlag, barycentricChain1,
    barycentricEdge, Comb.bdry2, orderCx, pathChain]
  abel

theorem barycentricChain2_boundary (c : OrdTri P →₀ ℤ) :
    Comb.bdry2 (orderCx (NeSpx (cmpRel P))) (barycentricChain2 c) =
      barycentricChain1 (Comb.bdry2 (orderCx P) c) := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd => simp only [map_add, hc, hd]
  | single t n =>
    rw [← Finsupp.smul_single_one t n, map_smul, map_smul, map_smul, map_smul]
    congr 1
    simpa only [barycentricChain2, Finsupp.linearCombination_single, one_smul] using
      barycentricTriangle_boundary t

private theorem barycentric_mapDomain_sub {I J : Type u} (f : I → J) (x y : I →₀ ℤ) :
    Finsupp.mapDomain f (x - y) = Finsupp.mapDomain f x - Finsupp.mapDomain f y :=
  (Finsupp.mapDomain.addMonoidHom f).map_sub x y

theorem barycentricChain2_natural (f : P → Q) (hf : Monotone f) (c : OrdTri P →₀ ℤ) :
    chain2 (orderCxMap (barycentricMap f hf) (barycentricMap_monotone f hf))
      (barycentricChain2 c) = barycentricChain2 (chain2 (orderCxMap f hf) c) := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd => simp only [map_add, hc, hd]
  | single t n =>
    simp [barycentricChain2, barycentricTriangle, barycentricFlag, chain2,
      orderCxMap, barycentric_mapDomain_sub, Finsupp.mapDomain_add,
      barycentricMap_spx1, barycentricMap_spx2, barycentricMap_spx3]

/-- Degenerate weak triangles have zero subdivision, so no artificial
diagonal cell survives the reverse map. -/
theorem barycentricTriangle_degenerate (t : OrdTri P)
    (ht : t.1.1 = t.1.2.1 ∨ t.1.2.1 = t.1.2.2) : barycentricTriangle t = 0 := by
  rcases t with ⟨⟨a, b, c⟩, hab, hbc⟩
  rcases ht with h | h
  · change a = b at h
    subst b
    simp [barycentricTriangle, barycentricFlag, spx1, spx2, spx3]
  · change b = c at h
    subst c
    simp [barycentricTriangle, barycentricFlag, spx1, spx2, spx3]

theorem barycentricChain2_normalization (c : OrdTri P →₀ ℤ) :
    barycentricChain2 c = barycentricChain2 (ordStrictInclusion2 (normalizeOrdChain2 c)) := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd => simp only [map_add, hc, hd]
  | single t n =>
    by_cases hab : t.1.1 = t.1.2.1
    · simp [barycentricChain2, barycentricTriangle_degenerate t (Or.inl hab),
        normalizeOrdChain2_single, normalizeOrdTriangle, hab]
    · by_cases hbc : t.1.2.1 = t.1.2.2
      · simp [barycentricChain2, barycentricTriangle_degenerate t (Or.inr hbc),
          normalizeOrdChain2_single, normalizeOrdTriangle, hbc]
      · have h1 := lt_of_le_of_ne t.2.1 hab
        have h2 := lt_of_le_of_ne t.2.2 hbc
        simp [normalizeOrdChain2_single, normalizeOrdTriangle, h1, h2,
          ordStrictInclusion2, strictOrderIncl]

/-- The last-vertex map recovers the original strict triangle with coefficient
one; the other five flags collapse and have zero normalized coefficient. -/
theorem barycentricChain2_lastVertex (c : OrdTri P →₀ ℤ) :
    normalizeOrdChain2 (chain2 (orderCxMap (chainMax (P := P)) chainMax_monotone)
      (barycentricChain2 c)) = normalizeOrdChain2 c := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd => simp only [map_add, hc, hd]
  | single t n =>
    simp [barycentricChain2, barycentricTriangle, barycentricFlag, chain2,
      orderCxMap, barycentric_mapDomain_sub, Finsupp.mapDomain_add,
      normalizeOrdChain2, normalizeOrdTriangle]

end FiniteChains.Davis
