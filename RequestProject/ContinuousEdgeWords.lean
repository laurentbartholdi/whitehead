module

public import RequestProject.CellComplex
public import RequestProject.OpenCoverPathReplacement

@[expose] public section

/-! Actual continuous realizations of finite oriented edge words. The open
cover criterion retains a finite word, not merely a replacement continuous
path. Pending Lean verification. -/

noncomputable section
open scoped Classical unitInterval
open Set

namespace FiniteChains.ContinuousEdgeWords

variable {V E X : Type} [TopologicalSpace X]
  (src tgt : E → V) (v : V → X) (edge : ∀ e, Path (v (src e)) (v (tgt e)))

def germPath (g : E × Bool) : Path (v (Comb.germSrc src tgt g))
    (v (Comb.germTgt src tgt g)) :=
  match g with
  | (e, true) => edge e
  | (e, false) => (edge e).symm

/-- Read a genuinely composable finite list as a continuous path. -/
def realize : (l : List (E × Bool)) → {a b : V} →
    Comb.IsPath src tgt l a b → Path (v a) (v b)
  | [], a, _, h => (Path.refl (v a)).cast rfl (congrArg v h.symm)
  | g :: l, _, _, h =>
      ((germPath src tgt v edge g).cast (congrArg v h.1) rfl).trans
        (realize l h.2)

@[simp] theorem realize_nil (a : V) : realize src tgt v edge [] (a := a) rfl = Path.refl (v a) := rfl

theorem realize_append (l m : List (E × Bool)) {a b c : V}
    (hl : Comb.IsPath src tgt l a b) (hm : Comb.IsPath src tgt m b c) :
    Path.Homotopic
      ((realize src tgt v edge l hl).trans (realize src tgt v edge m hm))
      (realize src tgt v edge (l ++ m) (hl.append hm)) := by
  induction l generalizing a with
  | nil =>
    have hab : a = b := hl
    subst b
    exact Path.Homotopic.refl_trans _
  | cons g l ih =>
    change Path.Homotopic
      ((((germPath src tgt v edge g).cast (congrArg v hl.1) rfl).trans
        (realize src tgt v edge l hl.2)).trans (realize src tgt v edge m hm)) _
    exact (Path.Homotopic.trans_assoc _ _ _).trans
      ((Path.Homotopic.refl _).hcomp (ih hl.2))

def IsWord {a b : V} (p : Path (v a) (v b)) : Prop :=
  ∃ l : List (E × Bool), ∃ hl : Comb.IsPath src tgt l a b,
    Path.Homotopic p (realize src tgt v edge l hl)

theorem isWord_refl (a : V) : IsWord src tgt v edge (Path.refl (v a)) :=
  ⟨[], rfl, Path.Homotopic.refl _⟩

variable {src tgt v edge} in
theorem IsWord.trans {a b c : V} {p : Path (v a) (v b)} {q : Path (v b) (v c)}
    (hp : IsWord src tgt v edge p) (hq : IsWord src tgt v edge q) :
    IsWord src tgt v edge (p.trans q) := by
  obtain ⟨l, hl, hpl⟩ := hp
  obtain ⟨m, hm, hqm⟩ := hq
  exact ⟨l ++ m, hl.append hm,
    (hpl.hcomp hqm).trans (realize_append src tgt v edge l m hl hm)⟩

variable {src tgt v edge} in
theorem IsWord.of_homotopic {a b : V} {p q : Path (v a) (v b)}
    (hq : IsWord src tgt v edge q) (hpq : Path.Homotopic p q) :
    IsWord src tgt v edge p := by
  obtain ⟨l, hl, hq⟩ := hq
  exact ⟨l, hl, hpq.trans hq⟩

variable {src tgt v edge} in
theorem IsWord.pathCast {a b a' b' : V} {p : Path (v a) (v b)}
    (hp : IsWord src tgt v edge p) (ha : a' = a) (hb : b' = b) :
    IsWord src tgt v edge (p.cast (congrArg v ha) (congrArg v hb)) := by
  subst a'
  subst b'
  exact hp

theorem isWord_concat {n : ℕ} (a : Fin (n + 1) → V)
    (G : ∀ i : Fin n, Path (v (a i.castSucc)) (v (a i.succ)))
    (hG : ∀ i, IsWord src tgt v edge (G i)) :
    IsWord src tgt v edge (Path.concat (v ∘ a) G) := by
  induction n with
  | zero =>
    rw [Path.concat_zero]
    exact isWord_refl src tgt v edge (a 0)
  | succ n ih =>
    rw [Path.concat_succ]
    exact (ih (a ∘ Fin.castSucc) (fun i => G i.castSucc)
      (fun i => hG i.castSucc)).trans (hG (Fin.last n))

/-- An open-cover subdivision yields a finite edge word. Local connectors
may move subdivision points to vertices; no finiteness of the graph is used. -/
theorem isWord_of_open_cover {ι : Type} (U : ι → Set X)
    (hU : ∀ i, IsOpen (U i)) (hcover : Set.univ ⊆ ⋃ i, U i)
    (a : X → V) (C : ∀ x, Path x (v (a x)))
    (hlocal : ∀ i {x y : X} (p : Path x y), Set.range p ⊆ U i →
      IsWord src tgt v edge (((C x).symm.trans p).trans (C y)))
    {x y : X} (p : Path x y) :
    IsWord src tgt v edge (((C x).symm.trans p).trans (C y)) := by
  obtain ⟨t, ht0, htm, ⟨n, htn⟩, htU⟩ :=
    exists_monotone_Icc_subset_open_cover_unitInterval
      (c := fun i => p ⁻¹' U i) (fun i => (hU i).preimage p.continuous)
      (by intro s _; obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (hcover (Set.mem_univ (p s)))
          exact Set.mem_iUnion.mpr ⟨i, hi⟩)
  let ts : Fin (n + 1) → I := fun i => t i.val
  let points : Fin (n + 1) → X := p ∘ ts
  let F : ∀ i : Fin n, Path (points i.castSucc) (points i.succ) :=
    fun i => p.subpath (ts i.castSucc) (ts i.succ)
  let G : ∀ i : Fin n, Path (v (a (points i.castSucc))) (v (a (points i.succ))) :=
    fun i => ((C (points i.castSucc)).symm.trans (F i)).trans (C (points i.succ))
  have hG (i : Fin n) : IsWord src tgt v edge (G i) := by
    obtain ⟨j, hj⟩ := htU i.val
    apply hlocal j (F i)
    rw [show Set.range (F i) = p '' Set.Icc (t i.val) (t (i.val + 1)) from
      p.range_subpath_of_le _ _ (htm (Nat.le_succ i.val))]
    rintro _ ⟨s, hs, rfl⟩
    exact hj hs
  have hcat := PathReplacement.concat_conjugate points (v ∘ a ∘ points)
    (fun i => C (points i)) F G (fun _ => Path.Homotopic.refl _)
  have hsub : Path.Homotopic (Path.concat points F)
      (p.subpath (ts 0) (ts (Fin.last n))) := Path.Homotopic.concat_subpath p ts
  have hcat' : Path.Homotopic
      (((C (points 0)).symm.trans (p.subpath (ts 0) (ts (Fin.last n)))).trans
        (C (points (Fin.last n)))) (Path.concat (v ∘ a ∘ points) G) :=
    (((Path.Homotopic.refl _).hcomp hsub.symm).hcomp (Path.Homotopic.refl _)).trans hcat
  have hp0 : points 0 = x := by change p (t 0) = x; rw [ht0, p.source]
  have hp1 : points (Fin.last n) = y := by
    change p (t n) = y
    rw [htn n le_rfl, p.target]
  have hw := (isWord_concat src tgt v edge (a ∘ points) G hG).pathCast
    (congrArg a hp0.symm) (congrArg a hp1.symm)
  have hc := hcat'.pathCast (congrArg (v ∘ a) hp0.symm) (congrArg (v ∘ a) hp1.symm)
  have hc0 : (C (points 0)).cast hp0.symm (congrArg (v ∘ a) hp0.symm) = C x := by
    apply Path.ext
    funext s
    change C (points 0) s = C x s
    rw [hp0]
  have hc1 : (C (points (Fin.last n))).cast hp1.symm (congrArg (v ∘ a) hp1.symm) = C y := by
    apply Path.ext
    funext s
    change C (points (Fin.last n)) s = C y s
    rw [hp1]
  have hps : (p.subpath (ts 0) (ts (Fin.last n))).cast hp0.symm hp1.symm = p := by
    apply Path.ext
    funext s
    change p (Path.subpathAux (ts 0) (ts (Fin.last n)) s) = p s
    have ht0' : ts 0 = 0 := ht0
    have ht1' : ts (Fin.last n) = 1 := htn n le_rfl
    rw [ht0', ht1']
    congr 1
    apply Subtype.ext
    simp [Path.subpathAux]
  rw [Path.cast_trans _ _ (congrArg (v ∘ a) hp0.symm) hp1.symm (congrArg (v ∘ a) hp1.symm),
    Path.cast_trans _ _ (congrArg (v ∘ a) hp0.symm) hp0.symm hp1.symm,
    Path.cast_symm, hc0, hps, hc1] at hc
  exact hw.of_homotopic hc

end FiniteChains.ContinuousEdgeWords
