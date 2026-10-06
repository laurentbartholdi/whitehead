module

public import RequestProject.MedianGraphMetric

@[expose] public section

/-!
# Transporting a median structure along a graph isomorphism

A median graph structure (`FiniteChains.MedianSimpleGraph`) is stated in terms of the graph
metric, so it transports along any isomorphism of graphs.  This is what is needed to say that an
abstractly given complex, once its one-skeleton has been identified with the one-skeleton of a
median graph, is itself median.

* `FiniteChains.dist_le_of_hom` — a graph homomorphism does not increase distances;
* `FiniteChains.dist_eq_of_iso` — an isomorphism preserves them;
* `FiniteChains.MedianSimpleGraph.ofIso` — the transported median structure.
-/

namespace FiniteChains

universe u v

variable {Vx : Type u} {Vy : Type v}

/-- A graph homomorphism does not increase distances between reachable vertices. -/
theorem dist_le_of_hom {G' : SimpleGraph Vy} {G : SimpleGraph Vx} (f : G' →g G) {a b : Vy}
    (h : G'.Reachable a b) : G.dist (f a) (f b) ≤ G'.dist a b := by
  obtain ⟨w, hw⟩ := h.exists_walk_length_eq_dist
  calc G.dist (f a) (f b) ≤ (w.map f).length := SimpleGraph.dist_le _
    _ = w.length := by simp
    _ = G'.dist a b := hw

/-- An isomorphism of graphs preserves the graph metric. -/
theorem dist_eq_of_iso {G' : SimpleGraph Vy} {G : SimpleGraph Vx} (e : G' ≃g G)
    (hG : G.Connected) (a b : Vy) : G'.dist a b = G.dist (e a) (e b) := by
  have hreach : G.Reachable (e a) (e b) := hG _ _
  have hr' : G'.Reachable a b := by
    obtain ⟨w⟩ := hreach
    exact ⟨(w.map e.symm.toHom).copy (by simp) (by simp)⟩
  refine le_antisymm ?_ (dist_le_of_hom e.toHom hr')
  have h := dist_le_of_hom e.symm.toHom hreach
  simpa using h

/-- **Transport of a median structure** along an isomorphism of one-skeleta. -/
noncomputable def MedianSimpleGraph.ofIso (M : MedianSimpleGraph Vx) (G' : SimpleGraph Vy)
    (e : G' ≃g M.G) : MedianSimpleGraph Vy where
  G := G'
  conn := by
    rw [SimpleGraph.connected_iff]
    refine ⟨fun a b => ?_, ⟨e.symm M.conn.nonempty.some⟩⟩
    obtain ⟨w⟩ : M.G.Reachable (e a) (e b) := M.conn _ _
    exact ⟨(w.map e.symm.toHom).copy (by simp) (by simp)⟩
  base := e.symm M.base
  med a b c := e.symm (M.med (e a) (e b) (e c))
  med_ab a b c := by
    simp only [dist_eq_of_iso e M.conn, RelIso.apply_symm_apply]
    exact M.med_ab _ _ _
  med_bc a b c := by
    simp only [dist_eq_of_iso e M.conn, RelIso.apply_symm_apply]
    exact M.med_bc _ _ _
  med_ac a b c := by
    simp only [dist_eq_of_iso e M.conn, RelIso.apply_symm_apply]
    exact M.med_ac _ _ _
  med_unique a b c z h1 h2 h3 := by
    simp only [dist_eq_of_iso e M.conn] at h1 h2 h3
    have := M.med_unique (e a) (e b) (e c) (e z) h1 h2 h3
    rw [← this]
    simp
  dim_le w s hs := by
    classical
    have hcard : s.card = (s.image e).card :=
      (Finset.card_image_of_injective s e.toEquiv.injective).symm
    rw [hcard]
    refine M.dim_le (e w) (s.image e) ?_
    intro a ha
    obtain ⟨a', ha', rfl⟩ := Finset.mem_image.1 ha
    obtain ⟨hadj, hdist⟩ := hs a' ha'
    refine ⟨e.map_rel_iff.2 hadj, ?_⟩
    simp only [dist_eq_of_iso e M.conn] at hdist
    simpa using hdist

end FiniteChains
