/- Adapted from the local 2026-09-11 Lean audit; see PROVENANCE.json. -/

import RequestProject.TopologyPaths.PathSubdivision

/-! # Induction over paths subordinate to an open cover

A property of paths which is invariant under endpoint-fixed homotopy and
closed under concatenation can be checked on paths in single cover members.
This proves the generation part of the open-cover argument; it makes no
claim about the relations between those generators.
-/


namespace FiniteChains.OpenCoverPaths

open Set Topology CategoryTheory
open scoped unitInterval

universe u v

variable {X : Type u} [TopologicalSpace X]

theorem property_cast_iff (P : ∀ {a b : X}, Path a b → Prop)
    {a b a' b' : X} (p : Path a b) (ha : a' = a) (hb : b' = b) :
    P (p.cast ha hb) ↔ P p := by
  subst a'; subst b'
  rfl

theorem path_induction {ι : Type v} (U : ι → Set X)
    (hU : ∀ i, IsOpen (U i)) (hcover : ∀ x, ∃ i, x ∈ U i)
    (P : ∀ {a b : X}, Path a b → Prop)
    (hrefl : ∀ a, P (Path.refl a))
    (htrans : ∀ {a b c} (p : Path a b) (q : Path b c), P p → P q → P (p.trans q))
    (hhomotopy : ∀ {a b} {p q : Path a b}, p.Homotopic q → P p → P q)
    (hlocal : ∀ {a b} (p : Path a b), (∃ i, Set.range p ⊆ U i) → P p)
    {a b : X} (p : Path a b) : P p := by
  obtain ⟨t,N,ht0,htN,_,ht⟩ := PathSubdivision.exists_subdivision p U hU
    (fun s => hcover (p s))
  have hall : ∀ k ≤ N, P (PathSubdivision.concatenateCuts p t k) := by
    intro k
    induction k with
    | zero => intro _; exact hrefl _
    | succ k ih =>
      intro hk
      exact htrans _ _ (ih (by omega)) (hlocal _ (ht k (by omega)))
  have hend := hhomotopy (PathSubdivision.concatenateCuts_homotopic p t N) (hall N le_rfl)
  rw [ht0,htN] at hend
  have hp := hhomotopy (PathSubdivision.cut_zero_one_homotopic p) hend
  exact (property_cast_iff P p p.source p.target).mp hp

def arrow {a b : X} (p : Path a b) : FundamentalGroupoid.mk a ⟶ FundamentalGroupoid.mk b :=
  .mk p

noncomputable def basedValue {x : X} (c : ∀ y, Path x y) {a b : X}
    (p : Path a b) : FundamentalGroup X x :=
  FundamentalGroup.fromArrow
    (arrow (c a) ≫ arrow p ≫ Groupoid.inv (arrow (c b)))

theorem basedValue_homotopic {x a b : X} (c : ∀ y, Path x y) {p q : Path a b}
    (h : p.Homotopic q) : basedValue c p = basedValue c q := by
  unfold basedValue arrow
  rw [show Path.Homotopic.Quotient.mk p = .mk q from Quotient.sound h]

theorem basedValue_refl {x : X} (c : ∀ y, Path x y) (a : X) :
    basedValue c (Path.refl a) = 1 := by
  change (arrow (c a) ≫ 𝟙 _ ≫ Groupoid.inv (arrow (c a))) = 𝟙 _
  simp only [Category.id_comp, Groupoid.comp_inv]

theorem basedValue_trans {x a b d : X} (c : ∀ y, Path x y)
    (p : Path a b) (q : Path b d) :
    basedValue c (p.trans q) = basedValue c q * basedValue c p := by
  change (arrow (c a) ≫ (arrow p ≫ arrow q) ≫ Groupoid.inv (arrow (c d))) =
    (arrow (c a) ≫ arrow p ≫ Groupoid.inv (arrow (c b))) ≫
      (arrow (c b) ≫ arrow q ≫ Groupoid.inv (arrow (c d)))
  simp only [Groupoid.inv_eq_inv, Category.assoc, IsIso.inv_hom_id_assoc]

theorem basedValue_loop {x : X} (c : ∀ y, Path x y) (hc : c x = Path.refl x)
    (p : Path x x) : basedValue c p = FundamentalGroup.fromPath (.mk p) := by
  unfold basedValue
  rw [hc]
  change (𝟙 _ ≫ arrow p ≫ Groupoid.inv (𝟙 (FundamentalGroupoid.mk x))) = arrow p
  simp

theorem fundamental_subgroup_eq_top {ι : Type v} (U : ι → Set X)
    (hU : ∀ i, IsOpen (U i)) (hcover : ∀ x, ∃ i, x ∈ U i)
    {x : X} (c : ∀ y, Path x y) (hc : c x = Path.refl x)
    (S : Subgroup (FundamentalGroup X x))
    (hlocal : ∀ {a b} (p : Path a b), (∃ i, Set.range p ⊆ U i) → basedValue c p ∈ S) :
    S = ⊤ := by
  apply top_unique
  intro g _
  obtain ⟨p,rfl⟩ := Path.Homotopic.Quotient.mk_surjective g
  change FundamentalGroup.fromPath (.mk p) ∈ S
  rw [← basedValue_loop c hc p]
  apply path_induction U hU hcover (fun p => basedValue c p ∈ S)
  · intro a
    rw [basedValue_refl]
    exact S.one_mem
  · intro a b d p q hp hq
    rw [basedValue_trans]
    exact S.mul_mem hq hp
  · intro a b p q h hp
    rwa [← basedValue_homotopic c h]
  · exact hlocal

end FiniteChains.OpenCoverPaths
