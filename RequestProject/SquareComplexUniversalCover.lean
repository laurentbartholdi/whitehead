module

public import RequestProject.SquareComplexCovering

@[expose] public section

/-!
# Uniqueness of the simply connected covering

Building on the combinatorial covering theory of `RequestProject/SquareComplexCovering.lean`, this
file proves the classification statement that the topological dictionary of the paper needs:

* `FiniteChains.SquareComplex.fiberProduct` — the fibre product of two coverings of a common base,
  and `FiniteChains.SquareComplex.isCovering_fiberProduct_fst` — its first projection is again a
  covering;
* `FiniteChains.SquareComplex.exists_covering_of_simplyConnectedW` — **the lifting criterion**: a
  connected, simply connected covering `q : U → B` factors through any covering `p : T → B`
  compatibly with base points, and the factorisation is itself a covering;
* `FiniteChains.SquareComplex.exists_iso_of_universal` — **uniqueness of the universal cover**: two
  connected simply connected coverings of the same base are isomorphic as square complexes, by an
  isomorphism over the base taking base point to base point.

Nothing here assumes finiteness, local finiteness or a dimension bound.
-/

namespace FiniteChains

namespace SquareComplex

universe u v w

variable {Vt : Type u} {Vb : Type v} {Vu : Type w}
variable {T : SquareComplex Vt} {B : SquareComplex Vb} {U : SquareComplex Vu}
variable {p : Vt → Vb} {q : Vu → Vb}

/-- The vertices of the fibre product of `q : U → B` and `p : T → B`. -/
abbrev FiberVertex (q : Vu → Vb) (p : Vt → Vb) : Type max u w := {z : Vu × Vt // q z.1 = p z.2}

/-- The **fibre product** of two square complexes over a common base: vertices are pairs with the
same image, edges and squares are pairs of edges and squares. -/
def fiberProduct (U : SquareComplex Vu) (T : SquareComplex Vt) (q : Vu → Vb) (p : Vt → Vb) :
    SquareComplex (FiberVertex q p) where
  adj z z' := U.adj z.1.1 z'.1.1 ∧ T.adj z.1.2 z'.1.2
  adj_symm h := ⟨U.adj_symm h.1, T.adj_symm h.2⟩
  adj_irrefl _ h := U.adj_irrefl _ h.1
  sq a b c d := U.sq a.1.1 b.1.1 c.1.1 d.1.1 ∧ T.sq a.1.2 b.1.2 c.1.2 d.1.2
  sq_adj h :=
    ⟨⟨(U.sq_adj h.1).1, (T.sq_adj h.2).1⟩, ⟨(U.sq_adj h.1).2.1, (T.sq_adj h.2).2.1⟩,
      ⟨(U.sq_adj h.1).2.2.1, (T.sq_adj h.2).2.2.1⟩, ⟨(U.sq_adj h.1).2.2.2, (T.sq_adj h.2).2.2.2⟩⟩
  sq_rotate h := ⟨U.sq_rotate h.1, T.sq_rotate h.2⟩
  sq_reverse h := ⟨U.sq_reverse h.1, T.sq_reverse h.2⟩

/-- **The first projection of the fibre product of two coverings is a covering.** -/
theorem isCovering_fiberProduct_fst (hp : IsCovering T B p) (hq : IsCovering U B q) :
    IsCovering (fiberProduct U T q p) U (fun z => z.1.1) where
  map_adj h := h.1
  map_sq h := h.1
  lift_adj := by
    intro z w hw
    have hb : B.adj (p z.1.2) (q w) := by
      rw [← z.2]; exact hq.map_adj hw
    obtain ⟨t', ⟨ht', hpt'⟩, huniq⟩ := hp.lift_adj z.1.2 hb
    refine ⟨⟨(w, t'), hpt'.symm⟩, ⟨⟨hw, ht'⟩, rfl⟩, ?_⟩
    rintro ⟨⟨w', t''⟩, hz''⟩ ⟨⟨hadj1, hadj2⟩, rfl⟩
    have : t'' = t' := huniq t'' ⟨hadj2, hz''.symm⟩
    subst this
    rfl
  lift_sq := by
    intro z b c d hsq
    have hb : B.sq (p z.1.2) (q b) (q c) (q d) := by
      rw [← z.2]; exact hq.map_sq hsq
    obtain ⟨b', c', d', hsq', hpb, hpc, hpd⟩ := hp.lift_sq z.1.2 hb
    exact ⟨⟨(b, b'), hpb.symm⟩, ⟨(c, c'), hpc.symm⟩, ⟨(d, d'), hpd.symm⟩,
      ⟨hsq, hsq'⟩, rfl, rfl, rfl⟩

/-- **The lifting criterion.**  A connected, simply connected covering `q : U → B` factors through
any covering `p : T → B` by a map `f` which is itself a covering and which matches prescribed base
points. -/
theorem exists_covering_of_simplyConnectedW (hp : IsCovering T B p) (hq : IsCovering U B q)
    (hUC : U.WalkConnected) (hUSC : U.SimplyConnectedW) {u₀ : Vu} {t₀ : Vt} (h0 : q u₀ = p t₀) :
    ∃ f : Vu → Vt, f u₀ = t₀ ∧ (∀ u, p (f u) = q u) ∧ IsCovering U T f := by
  classical
  have hπ : IsCovering (fiberProduct U T q p) U (fun z => z.1.1) :=
    isCovering_fiberProduct_fst hp hq
  have hex : ∀ u : Vu, ∃ z : FiberVertex q p,
      (fiberProduct U T q p).ReachableFrom ⟨(u₀, t₀), h0⟩ z ∧ z.1.1 = u := by
    intro u
    exact hπ.exists_reachable_over (x₀ := ⟨(u₀, t₀), h0⟩) (hUC u₀ u)
  choose g hgr hgπ using hex
  have key : ∀ (u : Vu) (z : FiberVertex q p),
      (fiberProduct U T q p).ReachableFrom ⟨(u₀, t₀), h0⟩ z → z.1.1 = u → z = g u := by
    intro u z hz hzu
    exact hπ.injOn_reachable hUSC hz (hgr u) (by rw [hzu, hgπ u])
  have hfib : ∀ u : Vu, p ((g u).1.2) = q u := by
    intro u
    rw [← (g u).2, hgπ u]
  have hmap_adj : ∀ {u w : Vu}, U.adj u w → T.adj (g u).1.2 (g w).1.2 := by
    intro u w huw
    have hadj : U.adj ((g u).1.1) w := by rw [hgπ u]; exact huw
    obtain ⟨z', hz'adj, hz'π⟩ := (hπ.lift_adj (g u) hadj).exists
    have hz'r : (fiberProduct U T q p).ReachableFrom ⟨(u₀, t₀), h0⟩ z' :=
      (hgr u).trans (ReachableFrom.of_adj hz'adj)
    have hz'g : z' = g w := key w z' hz'r hz'π
    rw [← hz'g]
    exact hz'adj.2
  have hmap_sq : ∀ {a b c d : Vu}, U.sq a b c d →
      T.sq (g a).1.2 (g b).1.2 (g c).1.2 (g d).1.2 := by
    intro a b c d hsq
    have hsq' : U.sq ((g a).1.1) b c d := by rw [hgπ a]; exact hsq
    obtain ⟨b', c', d', hsqF, hb, hc, hd⟩ := hπ.lift_sq (g a) hsq'
    obtain ⟨hab, hbc, hcd, hda⟩ := (fiberProduct U T q p).sq_adj hsqF
    have hbr : (fiberProduct U T q p).ReachableFrom ⟨(u₀, t₀), h0⟩ b' :=
      (hgr a).trans (ReachableFrom.of_adj hab)
    have hcr : (fiberProduct U T q p).ReachableFrom ⟨(u₀, t₀), h0⟩ c' :=
      hbr.trans (ReachableFrom.of_adj hbc)
    have hdr : (fiberProduct U T q p).ReachableFrom ⟨(u₀, t₀), h0⟩ d' :=
      hcr.trans (ReachableFrom.of_adj hcd)
    rw [← key b b' hbr hb, ← key c c' hcr hc, ← key d d' hdr hd]
    exact hsqF.2
  refine ⟨fun u => (g u).1.2, ?_, hfib, hmap_adj, hmap_sq, ?_, ?_⟩
  · have hg0 : g u₀ = ⟨(u₀, t₀), h0⟩ :=
      (key u₀ ⟨(u₀, t₀), h0⟩ (ReachableFrom.refl _) rfl).symm
    simp only [hg0]
  · intro u s hs
    have hb : B.adj (q u) (p s) := by rw [← hfib u]; exact hp.map_adj hs
    obtain ⟨w, ⟨hw, hqw⟩, hwuniq⟩ := hq.lift_adj u hb
    have hfw : (g w).1.2 = s := by
      refine hp.edge_unique (hmap_adj hw) hs ?_
      rw [hfib w, hqw]
    refine ⟨w, ⟨hw, hfw⟩, ?_⟩
    rintro w' ⟨hw', hfw'⟩
    exact hwuniq w' ⟨hw', by rw [← hfib w', hfw']⟩
  · intro a b c d hsq
    have hb : B.sq (q a) (p b) (p c) (p d) := by rw [← hfib a]; exact hp.map_sq hsq
    obtain ⟨b', c', d', hsqU, hqb, hqc, hqd⟩ := hq.lift_sq a hb
    obtain ⟨hab, hbc, hcd, hda⟩ := U.sq_adj hsqU
    obtain ⟨hTab, hTbc, hTcd, hTda⟩ := T.sq_adj hsq
    have hfb : (g b').1.2 = b := hp.edge_unique (hmap_adj hab) hTab (by rw [hfib b', hqb])
    have hfd : (g d').1.2 = d :=
      hp.edge_unique (T.adj_symm (hmap_adj hda)) (T.adj_symm hTda) (by rw [hfib d', hqd])
    have hfc : (g c').1.2 = c := by
      refine hp.edge_unique (hfb ▸ hmap_adj hbc) hTbc ?_
      rw [hfib c', hqc]
    exact ⟨b', c', d', hsqU, hfb, hfc, hfd⟩

/-- **Uniqueness of the universal cover.**  Two connected, simply connected coverings of the same
base are isomorphic square complexes, by an isomorphism over the base matching prescribed base
points. -/
theorem exists_iso_of_universal (hp : IsCovering T B p) (hq : IsCovering U B q)
    (hTC : T.WalkConnected) (hTSC : T.SimplyConnectedW)
    (hUC : U.WalkConnected) (hUSC : U.SimplyConnectedW)
    {u₀ : Vu} {t₀ : Vt} (h0 : q u₀ = p t₀) :
    ∃ f : Vu → Vt, Function.Bijective f ∧ f u₀ = t₀ ∧ (∀ u, p (f u) = q u) ∧
      (∀ u w, U.adj u w ↔ T.adj (f u) (f w)) ∧
      (∀ a b c d, U.sq a b c d ↔ T.sq (f a) (f b) (f c) (f d)) := by
  obtain ⟨f, hf0, hfp, hf⟩ := exists_covering_of_simplyConnectedW hp hq hUC hUSC h0
  have hinj : Function.Injective f := hf.injective_of_simplyConnectedW hTSC hUC
  have hsurj : Function.Surjective f := hf.surjective_of_walkConnected hTC u₀
  refine ⟨f, ⟨hinj, hsurj⟩, hf0, hfp, ?_, ?_⟩
  · exact fun u w => ⟨fun h => hf.map_adj h, fun h => hf.adj_of_map_adj hinj h⟩
  · exact fun a b c d => ⟨fun h => hf.map_sq h, fun h => hf.sq_of_map_sq hinj h⟩

end SquareComplex

end FiniteChains
