module

public import Mathlib.Topology.Subpath
public import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected

@[expose] public section

/-! A finite open-cover argument for replacing a path after moving its
vertices along specified connector paths. The result is an actual path and
an actual path homotopy; no fundamental-group surjectivity is assumed.
Pending Lean verification. -/

noncomputable section
open scoped Classical unitInterval
open Set

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains.PathReplacement

variable {X : Type} [TopologicalSpace X]

theorem quotient_cancel_middle {x y z w : X}
    (A : Path.Homotopic.Quotient x y) (C : Path.Homotopic.Quotient y z)
    (B : Path.Homotopic.Quotient y w) :
    (A.trans C).trans (C.symm.trans B) = A.trans B := by
  rw [Path.Homotopic.Quotient.trans_assoc,
    ← Path.Homotopic.Quotient.trans_assoc C C.symm B,
    Path.Homotopic.Quotient.trans_symm, Path.Homotopic.Quotient.refl_trans]

theorem concat_conjugate {n : ℕ} (p a : Fin (n + 1) → X)
    (C : ∀ i, Path (p i) (a i))
    (F : ∀ i : Fin n, Path (p i.castSucc) (p i.succ))
    (G : ∀ i : Fin n, Path (a i.castSucc) (a i.succ))
    (h : ∀ i, Path.Homotopic (((C i.castSucc).symm.trans (F i)).trans (C i.succ)) (G i)) :
    Path.Homotopic (((C 0).symm.trans (Path.concat p F)).trans (C (Fin.last n)))
      (Path.concat a G) := by
  induction n with
  | zero =>
    rw [Path.concat_zero, Path.concat_zero]
    change Path.Homotopic (((C 0).symm.trans (Path.refl (p 0))).trans (C 0))
      (Path.refl (a 0))
    apply Path.Homotopic.Quotient.eq.mp
    simp only [Path.Homotopic.Quotient.mk_trans,
      Path.Homotopic.Quotient.mk_symm, Path.Homotopic.Quotient.mk_refl,
      Path.Homotopic.Quotient.trans_refl,
      Path.Homotopic.Quotient.symm_trans]
  | succ n ih =>
    have hi := Path.Homotopic.Quotient.eq.mpr
      (ih (p ∘ Fin.castSucc) (a ∘ Fin.castSucc) (fun i => C i.castSucc)
        (fun i => F i.castSucc) (fun i => G i.castSucc) (fun i => h i.castSucc))
    have hj := Path.Homotopic.Quotient.eq.mpr (h (Fin.last n))
    apply Path.Homotopic.Quotient.eq.mp
    rw [Path.concat_succ, Path.concat_succ]
    calc
      _ = Path.Homotopic.Quotient.trans
          (Path.Homotopic.Quotient.mk (((C 0).symm.trans
            (Path.concat (p ∘ Fin.castSucc) (fun i => F i.castSucc))).trans
              (C (Fin.castSucc (Fin.last n)))))
          (Path.Homotopic.Quotient.mk (((C (Fin.castSucc (Fin.last n))).symm.trans
            (F (Fin.last n))).trans (C (Fin.last (n + 1))))) := by
        simp only [Path.Homotopic.Quotient.mk_trans, Path.Homotopic.Quotient.mk_symm,
          Path.Homotopic.Quotient.trans_assoc]
        rw [← Path.Homotopic.Quotient.trans_assoc
            (Path.Homotopic.Quotient.mk (C (Fin.castSucc (Fin.last n))))
            (Path.Homotopic.Quotient.mk (C (Fin.castSucc (Fin.last n)))).symm
            ((Path.Homotopic.Quotient.mk (F (Fin.last n))).trans
              (Path.Homotopic.Quotient.mk (C (Fin.last (n + 1))))),
          Path.Homotopic.Quotient.trans_symm, Path.Homotopic.Quotient.refl_trans]
      _ = Path.Homotopic.Quotient.trans
          (Path.Homotopic.Quotient.mk (Path.concat (a ∘ Fin.castSucc) (fun i => G i.castSucc)))
          (Path.Homotopic.Quotient.mk (G (Fin.last n))) := by
        congr 1
      _ = _ := rfl

theorem concat_range_subset {n : ℕ} (p : Fin (n + 1) → X)
    (F : ∀ i : Fin n, Path (p i.castSucc) (p i.succ)) (A : Set X)
    (hp : p 0 ∈ A) (hF : ∀ i, Set.range (F i) ⊆ A) : Set.range (Path.concat p F) ⊆ A := by
  induction n with
  | zero =>
    rw [Path.concat_zero]
    rintro _ ⟨t, rfl⟩
    exact hp
  | succ n ih =>
    simp only [Path.concat_succ, Path.trans_range]
    exact Set.union_subset (ih _ _ hp (fun i => hF i.castSucc)) (hF (Fin.last n))

/-- Local replacements on an open cover concatenate to a replacement of
the entire path. Connectors are allowed to move subdivision vertices. -/
theorem replace_of_open_cover {ι : Type} (U : ι → Set X)
    (hU : ∀ i, IsOpen (U i)) (hcover : Set.univ ⊆ ⋃ i, U i)
    (A : Set X) (a : X → X) (ha : ∀ x, a x ∈ A) (C : ∀ x, Path x (a x))
    (hlocal : ∀ i {x y : X} (p : Path x y), Set.range p ⊆ U i →
      ∃ q : Path (a x) (a y), Set.range q ⊆ A ∧
        Path.Homotopic (((C x).symm.trans p).trans (C y)) q)
    {x y : X} (p : Path x y) :
    ∃ q : Path (a x) (a y), Set.range q ⊆ A ∧
      Path.Homotopic (((C x).symm.trans p).trans (C y)) q := by
  obtain ⟨t, ht0, htm, ⟨n, htn⟩, htU⟩ :=
    exists_monotone_Icc_subset_open_cover_unitInterval
      (c := fun i => p ⁻¹' U i) (fun i => (hU i).preimage p.continuous)
      (by intro s _; obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (hcover (Set.mem_univ (p s)))
          exact Set.mem_iUnion.mpr ⟨i, hi⟩)
  let ts : Fin (n + 1) → I := fun i => t i.val
  let points : Fin (n + 1) → X := p ∘ ts
  let F : ∀ i : Fin n, Path (points i.castSucc) (points i.succ) :=
    fun i => p.subpath (ts i.castSucc) (ts i.succ)
  have hloc (i : Fin n) : ∃ q : Path (a (points i.castSucc)) (a (points i.succ)),
      Set.range q ⊆ A ∧
      Path.Homotopic (((C (points i.castSucc)).symm.trans (F i)).trans (C (points i.succ))) q := by
    obtain ⟨j, hj⟩ := htU i.val
    apply hlocal j (F i)
    rw [show Set.range (F i) = p '' Set.Icc (t i.val) (t (i.val + 1)) from
      p.range_subpath_of_le _ _ (htm (Nat.le_succ i.val))]
    rintro _ ⟨s, hs, rfl⟩
    exact hj hs
  choose G hGA hG using hloc
  have hcat := concat_conjugate points (a ∘ points) (fun i => C (points i)) F G hG
  have hsub : Path.Homotopic (Path.concat points F)
      (p.subpath (ts 0) (ts (Fin.last n))) := Path.Homotopic.concat_subpath p ts
  have hcat' : Path.Homotopic
      (((C (points 0)).symm.trans (p.subpath (ts 0) (ts (Fin.last n)))).trans
        (C (points (Fin.last n)))) (Path.concat (a ∘ points) G) :=
    ((Path.Homotopic.refl _).hcomp hsub.symm).hcomp (Path.Homotopic.refl _) |>.trans hcat
  have hp0 : points 0 = x := by change p (t 0) = x; rw [ht0, p.source]
  have hp1 : points (Fin.last n) = y := by
    change p (t n) = y
    rw [htn n le_rfl, p.target]
  let q := (Path.concat (a ∘ points) G).cast (congrArg a hp0.symm) (congrArg a hp1.symm)
  refine ⟨q, ?_, ?_⟩
  · exact concat_range_subset (a ∘ points) G A (ha _) hGA
  · have ht0' : ts 0 = 0 := ht0
    have ht1' : ts (Fin.last n) = 1 := htn n le_rfl
    have hc0 : (C (points 0)).cast hp0.symm (congrArg a hp0.symm) = C x := by
      apply Path.ext
      funext s
      change C (points 0) s = C x s
      rw [hp0]
    have hc1 : (C (points (Fin.last n))).cast hp1.symm (congrArg a hp1.symm) = C y := by
      apply Path.ext
      funext s
      change C (points (Fin.last n)) s = C y s
      rw [hp1]
    have hps : (p.subpath (ts 0) (ts (Fin.last n))).cast hp0.symm hp1.symm = p := by
      apply Path.ext
      funext s
      change p (Set.Icc.convexComb (ts 0) (ts (Fin.last n)) s) = p s
      rw [ht0', ht1']
      congr 1
      apply Subtype.ext
      simp [Set.Icc.convexComb]
    have hc := hcat'.pathCast (congrArg a hp0.symm) (congrArg a hp1.symm)
    rw [Path.cast_trans _ _ (congrArg a hp0.symm) hp1.symm (congrArg a hp1.symm),
      Path.cast_trans _ _ (congrArg a hp0.symm) hp0.symm hp1.symm,
      Path.cast_symm, hc0, hps, hc1] at hc
    exact hc

end FiniteChains.PathReplacement
