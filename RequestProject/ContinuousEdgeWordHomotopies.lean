import RequestProject.ContinuousEdgeWords
import RequestProject.CombPi1
import Mathlib.AlgebraicTopology.FundamentalGroupoid.Basic
import Mathlib.Data.List.OfFn

/-! Endpoint-preserving reversal and naturality for actual finite edge-word
paths. These statements concern continuous paths, not only their fundamental
group classes. Pending Lean verification. -/

noncomputable section
open scoped Classical unitInterval Topology

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains.ContinuousEdgeWords

private theorem realize_congr_list {V E X : Type} [TopologicalSpace X]
    (src tgt : E → V) (v : V → X) (edge : ∀ e, Path (v (src e)) (v (tgt e)))
    {l m : List (E × Bool)} {a b : V}
    (hl : Comb.IsPath src tgt l a b) (hm : Comb.IsPath src tgt m a b) (he : l = m) :
    realize src tgt v edge l hl = realize src tgt v edge m hm := by
  subst m
  rfl

variable {K : Comb.Complex2} {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
  (v : K.V → X) (edge : ∀ e, Path (v (K.src e)) (v (K.tgt e)))

private theorem reversed_single (g : K.E × Bool) :
    (germPath K.src K.tgt v edge g).symm.Homotopic
      (realize K.src K.tgt v edge [Comb.revGerm (X := K) g]
        (by simp [Comb.IsPath])) := by
  rcases g with ⟨e, b⟩
  cases b
  · simpa [Comb.germSrc, Comb.germTgt, germPath, Comb.revGerm, Bool.not, Bool.not_false, realize, Path.cast_rfl_rfl,
      Path.symm_symm] using (Path.Homotopic.trans_refl (edge e)).symm
  · simpa [Comb.germSrc, Comb.germTgt, germPath, Comb.revGerm, Bool.not, Bool.not_true, realize, Path.cast_rfl_rfl]
      using (Path.Homotopic.trans_refl (edge e).symm).symm

theorem realize_revPath (l : List (K.E × Bool)) {a b : K.V}
    (hl : Comb.IsPath K.src K.tgt l a b) :
    (realize K.src K.tgt v edge l hl).symm.Homotopic
      (realize K.src K.tgt v edge (Comb.revPath (X := K) l) (Comb.isPath_revPath hl)) := by
  induction l generalizing a with
  | nil =>
    cases hl
    exact Path.Homotopic.refl _
  | cons g l ih =>
    obtain ⟨rfl, ht⟩ := hl
    rw [realize_congr_list K.src K.tgt v edge
      (Comb.isPath_revPath (p := g :: l) ⟨rfl, ht⟩)
      ((Comb.isPath_revPath ht).append (by simp [Comb.IsPath])) (Comb.revPath_cons g l)]
    change ((germPath K.src K.tgt v edge g).trans
      (realize K.src K.tgt v edge l ht)).symm.Homotopic _
    rw [Path.trans_symm]
    exact ((ih ht).hcomp (reversed_single v edge g)).trans
      (realize_append K.src K.tgt v edge (Comb.revPath l) [Comb.revGerm g]
        (Comb.isPath_revPath ht) (by simp [Comb.IsPath]))

theorem realize_map (f : C(X, Y)) (l : List (K.E × Bool)) {a b : K.V}
    (hl : Comb.IsPath K.src K.tgt l a b) :
    (realize K.src K.tgt v edge l hl).map f.continuous =
      realize K.src K.tgt (f ∘ v) (fun e => (edge e).map f.continuous) l hl := by
  induction l generalizing a with
  | nil => cases hl; rfl
  | cons g l ih =>
    obtain ⟨rfl, ht⟩ := hl
    rw [realize, Path.map_trans, ih ht]
    congr 1
    rcases g with ⟨e, b⟩
    cases b <;> simp only [germPath, Path.cast_rfl_rfl, Path.map_symm]

theorem realize_homotopic_of_edges
    (edge' : ∀ e, Path (v (K.src e)) (v (K.tgt e)))
    (h : ∀ e, (edge e).Homotopic (edge' e))
    (l : List (K.E × Bool)) {a b : K.V} (hl : Comb.IsPath K.src K.tgt l a b) :
    (realize K.src K.tgt v edge l hl).Homotopic
      (realize K.src K.tgt v edge' l hl) := by
  induction l generalizing a with
  | nil => cases hl; exact Path.Homotopic.refl _
  | cons g l ih =>
    obtain ⟨rfl, ht⟩ := hl
    apply Path.Homotopic.hcomp ?_ (ih ht)
    rcases g with ⟨e, b⟩
    cases b
    · exact (h e).symm₂
    · exact h e

end FiniteChains.ContinuousEdgeWords

namespace FiniteChains.Comb

theorem isPath_ofFn {V E : Type} (src tgt : E → V) (n : ℕ)
    (a : Fin (n + 1) → V) (g : Fin n → E × Bool)
    (hs : ∀ i, a i.castSucc = germSrc src tgt (g i))
    (ht : ∀ i, germTgt src tgt (g i) = a i.succ) :
    IsPath src tgt (List.ofFn g) (a 0) (a (Fin.last n)) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [List.ofFn_succ', List.concat_eq_append]
    exact (ih (a ∘ Fin.castSucc) (fun i => g i.castSucc)
      (fun i => hs i.castSucc) (fun i => ht i.castSucc)).append
      ⟨hs (Fin.last n), ht (Fin.last n)⟩

end FiniteChains.Comb

namespace FiniteChains.ContinuousEdgeWords

variable {V E X : Type} [TopologicalSpace X]
  (src tgt : E → V) (v : V → X) (edge : ∀ e, Path (v (src e)) (v (tgt e)))

theorem concat_homotopic_realize_ofFn (n : ℕ)
    (a : Fin (n + 1) → V) (g : Fin n → E × Bool)
    (hs : ∀ i, a i.castSucc = Comb.germSrc src tgt (g i))
    (ht : ∀ i, Comb.germTgt src tgt (g i) = a i.succ)
    (F : ∀ i : Fin n, Path (v (a i.castSucc)) (v (a i.succ)))
    (hF : ∀ i, (F i).Homotopic
      (realize src tgt v edge [g i] ⟨hs i, ht i⟩)) :
    (Path.concat (v ∘ a) F).Homotopic
      (realize src tgt v edge (List.ofFn g) (Comb.isPath_ofFn src tgt n a g hs ht)) := by
  induction n with
  | zero =>
    rw [Path.concat_zero]
    have he : List.ofFn g = ([] : List (E × Bool)) := by simp only [List.ofFn_zero]
    rw [realize_congr_list src tgt v edge (Comb.isPath_ofFn src tgt 0 a g hs ht)
      (show Comb.IsPath src tgt [] (a 0) (a (Fin.last 0)) from rfl) he]
    exact Path.Homotopic.refl _
  | succ n ih =>
    rw [Path.concat_succ]
    have he : List.ofFn g = List.ofFn (fun i : Fin n => g i.castSucc) ++ [g (Fin.last n)] := by
      rw [List.ofFn_succ', List.concat_eq_append]
    rw [realize_congr_list src tgt v edge (Comb.isPath_ofFn src tgt (n + 1) a g hs ht)
      ((Comb.isPath_ofFn src tgt n (a ∘ Fin.castSucc) (fun i => g i.castSucc)
        (fun i => hs i.castSucc) (fun i => ht i.castSucc)).append
          (show Comb.IsPath src tgt [g (Fin.last n)]
            ((a ∘ Fin.castSucc) (Fin.last n)) (a (Fin.last (n + 1))) from
              ⟨hs (Fin.last n), ht (Fin.last n)⟩)) he]
    exact ((ih (a ∘ Fin.castSucc) (fun i => g i.castSucc)
      (fun i => hs i.castSucc) (fun i => ht i.castSucc)
      (fun i => F i.castSucc) (fun i => hF i.castSucc)).hcomp (hF (Fin.last n))).trans
      (realize_append src tgt v edge
        (List.ofFn (fun i : Fin n => g i.castSucc)) [g (Fin.last n)]
        (Comb.isPath_ofFn src tgt n (a ∘ Fin.castSucc) (fun i => g i.castSucc)
          (fun i => hs i.castSucc) (fun i => ht i.castSucc))
        ⟨hs (Fin.last n), ht (Fin.last n)⟩)

end FiniteChains.ContinuousEdgeWords
