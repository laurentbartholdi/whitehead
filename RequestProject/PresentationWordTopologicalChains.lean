module

public import RequestProject.OrderSequentialTopologicalChains
public import RequestProject.PresWordEmbeddingCombPi2

@[expose] public section

namespace FiniteChains.PresModel
open Comb
variable {α J : ℕ → Type} [∀ i, DecidableEq (α i)]
  (w : ∀ i, J i → List (α i × Bool))
  (e : ∀ i, PresWordEmbedding (w i) (w (i + 1)))
  (ρ : ∀ i, J i → FreeGroup (α i))
  (hw : ∀ i j, FreeGroup.mk (w i j) = ρ i j)
  (hpos : ∀ i j, 0 < (w i j).length)

/-- Successive labelled word embeddings with the existing algebraic cycle
condition give genuine chains of CW subcomplexes of any specified length.
All ambient embeddings and topological pi2 comparisons are constructed. -/
theorem valid_hasChain_of_word_embeddings (n : ℕ)
    (hp : ∀ i, i < n → (∃ a : α (i + 1), a ∉ Set.range (e i).gen) ∨
      ∃ j : J (i + 1), j ∉ Set.range (e i).cell)
    (hz : ∀ i, i < n → ∀ c : PresGroup (ρ i) × J i →₀ ℤ,
      Comb.bdry2 (univCover (ρ i)) c = 0 →
      Finsupp.mapDomain (Prod.map ((e i).groupHom (ρ i) (ρ (i + 1)) (hw i) (hw (i + 1)))
        (e i).cell) c = 0)
    (finite : Bool) (hfin : finite = true → Finite (α n) ∧ Finite (J n)) :
    Whitehead.HasChain (validPresTwoComplex (w 0)
      (fun j => List.length_pos_iff.mp (hpos 0 j))) n finite := by
  apply orderNerve_hasChain_of_successive_embeddings (fun i => (e i).validMap)
    (fun i => validPresPos_isConnected (w i) (fun j => List.length_pos_iff.mp (hpos i j)))
    n ?_ ?_ finite ?_
  · intro i hi
    rcases hp i hi with ⟨a, ha⟩ | ⟨j, hj⟩
    · exact ⟨⟨iRose _ (.mid a), trivial⟩, (e i).valid_mid_not_mem_range ha⟩
    · exact ⟨⟨apexOf _ j, trivial⟩, (e i).valid_apex_not_mem_range hj⟩
  · intro i hi
    apply (e i).valid_killsPi2_of_full
    exact ((e i).killsPi2_iff_univCover (hpos i) (hpos (i + 1))
      (ρ i) (ρ (i + 1)) (hw i) (hw (i + 1))).mpr (hz i hi)
  · intro hf
    letI := (hfin hf).1
    letI := (hfin hf).2
    infer_instance

end FiniteChains.PresModel
