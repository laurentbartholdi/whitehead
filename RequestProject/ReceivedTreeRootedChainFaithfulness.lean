module

public import RequestProject.ReceivedTreeFoxCoordinates
public import RequestProject.TreeCoverAcyclic

@[expose] public section

/-! Edge chains are determined by their non-tree coordinates and off-root boundary. -/
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains.Comb.ReceivedTree
open SpanningTree
universe u
variable {K : Complex2.{u}} (T : SpanningTree K) {G : Type u} [Group G]
  (φ : PresGroup (treeRel T) →* G)

theorem cover_src (x : G × K.E) : (cover T φ).src x = (x.1, K.src x.2) := rfl

theorem cover_tgt_of_isTree {e : K.E} (h : T.isTree e) (g : G) :
    (cover T φ).tgt (g, e) = (g, K.tgt e) := by
  simp [cover, tgt, germValue, germWord, h]

/-- A finite chain supported on the tree cannot have boundary only at the
root in each sheet. The maximal-height argument is independent of the receiver. -/
theorem treeChain_eq_zero_off_root {z : (G × K.E) →₀ ℤ}
    (hsupp : ∀ x ∈ z.support, T.isTree x.2)
    (hz : ∀ g v, v ≠ T.root → bdry1 (cover T φ) z (g, v) = 0) : z = 0 := by
  classical
  by_contra hzne
  have hne : z.support.Nonempty := Finsupp.support_nonempty_iff.2 hzne
  obtain ⟨x₀, hx₀mem, hx₀max⟩ := z.support.exists_max_image
    (fun x => if h : T.isTree x.2 then T.ht (treeTop h) else 0) hne
  have he₀ : T.isTree x₀.2 := hsupp x₀ hx₀mem
  obtain ⟨a₀, ha₀ne, ha₀up⟩ := (T.isTree_iff x₀.2).1 he₀
  have hg : ∀ x ∈ z.support, ∀ (a : K.V) (ha : a ≠ T.root), (T.up a ha).1 = x.2 →
      (if h : T.isTree x.2 then T.ht (treeTop h) else 0) = T.ht a := by
    intro x hx a ha hup
    have hex : T.isTree x.2 := hsupp x hx
    rw [dif_pos hex, treeTop_eq hex ha hup]
  have hg₀ : (if h : T.isTree x₀.2 then T.ht (treeTop h) else 0) = T.ht a₀ :=
    hg x₀ hx₀mem a₀ ha₀ne ha₀up
  -- all terms but the one of `x₀` vanish at the vertex `(x₀.1, a₀)`
  have hterm : ∀ x ∈ z.support, x ≠ x₀ →
      z x * ((Finsupp.single ((cover T φ).tgt x) (1 : ℤ)) (x₀.1, a₀)
        - (Finsupp.single ((cover T φ).src x) (1 : ℤ)) (x₀.1, a₀)) = 0 := by
    intro x hx hxne
    have hex : T.isTree x.2 := hsupp x hx
    obtain ⟨a, hane, haup⟩ := (T.isTree_iff x.2).1 hex
    have hle : T.ht a ≤ T.ht a₀ := by
      have hmax := hx₀max x hx
      rw [hg x hx a hane haup, hg₀] at hmax
      exact hmax
    have key : ∀ v : K.V, (v = K.src x.2 ∨ v = K.tgt x.2) → (x.1, v) ≠ (x₀.1, a₀) := by
      intro v hv hc
      rw [Prod.mk.injEq] at hc
      obtain ⟨hq, hva⟩ := hc
      have hvertex : a = a₀ → False := by
        intro haa
        subst haa
        have hxe : x.2 = x₀.2 := haup.symm.trans ha₀up
        exact hxne (Prod.ext hq hxe)
      have hparent : T.parent a hane = a₀ → False := by
        intro hp
        have hht := T.ht_parent hane
        rw [hp] at hht
        omega
      rcases tree_edge_endpoints hane haup with ⟨hs, ht⟩ | ⟨hs, ht⟩
      · rcases hv with hv | hv
        · exact hvertex (by rw [← hs, ← hv, hva])
        · exact hparent (by rw [← ht, ← hv, hva])
      · rcases hv with hv | hv
        · exact hparent (by rw [← hs, ← hv, hva])
        · exact hvertex (by rw [← ht, ← hv, hva])
    have h1 : (cover T φ).tgt x ≠ (x₀.1, a₀) := by
      rw [cover_tgt_of_isTree T φ hex x.1]
      exact key (K.tgt x.2) (Or.inr rfl)
    have h2 : (cover T φ).src x ≠ (x₀.1, a₀) := by
      rw [cover_src]
      exact key (K.src x.2) (Or.inl rfl)
    rw [Finsupp.single_eq_of_ne (Ne.symm h1), Finsupp.single_eq_of_ne (Ne.symm h2)]
    ring
  -- evaluate the boundary at the vertex `(x₀.1, a₀)`
  have hzero : (0 : ℤ) = z x₀ *
      ((Finsupp.single ((cover T φ).tgt x₀) (1 : ℤ)) (x₀.1, a₀)
        - (Finsupp.single ((cover T φ).src x₀) (1 : ℤ)) (x₀.1, a₀)) := by
    have h := bdry1_apply (cover T φ) z (x₀.1, a₀)
    rw [hz x₀.1 a₀ ha₀ne] at h
    have h2 := h.trans (Finset.sum_eq_single_of_mem x₀ hx₀mem hterm)
    convert h2 using 1
  have hzx₀ : z x₀ ≠ 0 := Finsupp.mem_support_iff.1 hx₀mem
  have hsrc : (cover T φ).src x₀ = (x₀.1, K.src x₀.2) := rfl
  have htgt : (cover T φ).tgt x₀ = (x₀.1, K.tgt x₀.2) := by
    rw [cover_tgt_of_isTree T φ he₀ x₀.1]
  have hpne : T.parent a₀ ha₀ne ≠ a₀ := parent_ne_self (T := T) ha₀ne
  rcases tree_edge_endpoints ha₀ne ha₀up with ⟨hs, ht⟩ | ⟨hs, ht⟩
  · have h1 : (cover T φ).tgt x₀ ≠ (x₀.1, a₀) := by
      rw [htgt, ht]
      intro hc
      rw [Prod.mk.injEq] at hc
      exact hpne hc.2
    have h2 : (cover T φ).src x₀ = (x₀.1, a₀) := by rw [hsrc, hs]
    rw [Finsupp.single_eq_of_ne (Ne.symm h1), h2, Finsupp.single_eq_same] at hzero
    simp at hzero
    omega
  · have h1 : (cover T φ).tgt x₀ = (x₀.1, a₀) := by rw [htgt, ht]
    have h2 : (cover T φ).src x₀ ≠ (x₀.1, a₀) := by
      rw [hsrc, hs]
      intro hc
      rw [Prod.mk.injEq] at hc
      exact hpne hc.2
    rw [Finsupp.single_eq_of_ne (Ne.symm h2), h1, Finsupp.single_eq_same] at hzero
    simp at hzero
    omega

theorem edgeChain_eq_zero_of_nonTree_coordinates (c : (G × K.E) →₀ ℤ)
    (hc : ∀ i : NonTree T, cellCoefficient i.1 c = 0)
    (hb : ∀ g v, v ≠ T.root → bdry1 (cover T φ) c (g, v) = 0) : c = 0 := by
  apply treeChain_eq_zero_off_root T φ _ hb
  intro x hx
  by_contra ht
  have h := congrArg (fun a : MonoidAlgebra ℤ G => a.coeff x.1) (hc ⟨x.2, ht⟩)
  change (cellCoefficient (⟨x.2, ht⟩ : NonTree T).1 c).coeff x.1 = 0 at h
  rw [cellCoefficient_apply] at h
  exact (Finsupp.mem_support_iff.mp hx) h

/-- In particular, one-chains with boundary supported over the root are
determined by their non-tree Fox coordinates, even if they are not cycles. -/
theorem edgeChains_eq_of_nonTree_coordinates (c d : (G × K.E) →₀ ℤ)
    (hc : ∀ i : NonTree T, cellCoefficient i.1 c = cellCoefficient i.1 d)
    (hb : ∀ g v, v ≠ T.root →
      bdry1 (cover T φ) c (g, v) = bdry1 (cover T φ) d (g, v)) : c = d := by
  apply sub_eq_zero.mp
  apply edgeChain_eq_zero_of_nonTree_coordinates T φ
  · intro i
    rw [map_sub, hc, sub_self]
  · intro g v hv
    rw [map_sub, Finsupp.sub_apply, hb g v hv, sub_self]

end FiniteChains.Comb.ReceivedTree
