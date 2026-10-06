import RequestProject.AttCycle

/-!
# The concrete attaching map and the loop along which it spells the prescribed word

`RequestProject/AttCycle.lean` produced the labelled cycle.  This file turns it into the actual
attaching map

    `attCyc : NeSpx (cycA l hl) →o PresPos w`

of the chamber construction, and produces the **geometric loop of the cut surface**: the edge
path `sigLoop` which goes once around the cycle, based at the vertex `0`.  The computation
`mapPath_sigLoop_full` says that the image of that loop under the attaching map is *literally*
the loop `wordLoop w l` of the presentation complex which spells the word `l`.  This is the
reading hypothesis `hread` of `FiniteChains.Davis.injective_substHomF_of_spine`, on the nose.
-/

namespace FiniteChains
namespace Davis

open RACG Mirror Comb PresModel

universe u

/-- A pair of adjacent vertices is a simplex. -/
theorem isSimplex_pair {V : Type u} [DecidableEq V] {A : CommRel V} {x y : V} (h : A.rel x y) :
    IsSimplex A {x, y} := by
  intro s hs r hr hsr
  simp only [Finset.mem_insert, Finset.mem_singleton] at hs hr
  rcases hs with rfl | rfl <;> rcases hr with rfl | rfl
  · exact absurd rfl hsr
  · exact h
  · exact A.rel_symm h
  · exact absurd rfl hsr

section Loop

variable {α J : Type} (w : J → List (α × Bool)) (l : List (α × Bool)) (hl : 2 ≤ l.length)

/-- **The attaching map of the concrete block**: the simplicial map of the labelled cycle onto
the subdivided rose of the presentation complex. -/
def attCyc : NeSpx (cycA l hl) →o PresPos w :=
  ⟨fun σ => iRose w (roseLab l σ.1), (iRose_monotone w).comp (roseLab_monotone l hl)⟩

@[simp] theorem attCyc_apply (σ : NeSpx (cycA l hl)) :
    attCyc w l hl σ = iRose w (roseLab l σ.1) := rfl

/-! ### The vertices and the edges of the cycle -/

/-- The vertex of the cycle at the position `p`, read cyclically. -/
def vpt (p : ℕ) : Fin (2 * l.length) := ⟨p % (2 * l.length), Nat.mod_lt _ (by omega)⟩

@[simp] theorem vpt_val (p : ℕ) : (vpt l hl p).val = p % (2 * l.length) := rfl

theorem vpt_succ_val (p : ℕ) :
    (vpt l hl (p + 1)).val = (p % (2 * l.length) + 1) % (2 * l.length) := by
  simp [vpt, Nat.mod_add_mod]

theorem vpt_succ_lt {p : ℕ} (h : p % (2 * l.length) + 1 < 2 * l.length) :
    (vpt l hl (p + 1)).val = p % (2 * l.length) + 1 := by
  rw [vpt_succ_val, Nat.mod_eq_of_lt h]

theorem vpt_succ_wrap {p : ℕ} (h : p % (2 * l.length) + 1 = 2 * l.length) :
    (vpt l hl (p + 1)).val = 0 := by
  rw [vpt_succ_val, h, Nat.mod_self]

theorem vpt_adj (p : ℕ) : cycAdj (2 * l.length) (vpt l hl p) (vpt l hl (p + 1)) := by
  have hlt : p % (2 * l.length) < 2 * l.length := Nat.mod_lt _ (by omega)
  by_cases h : p % (2 * l.length) + 1 < 2 * l.length
  · exact Or.inl (by rw [vpt_val, vpt_succ_lt l hl h])
  · have hw : p % (2 * l.length) + 1 = 2 * l.length := by omega
    exact Or.inr (Or.inr (Or.inr ⟨vpt_succ_wrap l hl hw, by rw [vpt_val]; omega⟩))

/-- The vertex simplex at the position `p`. -/
def vtxSpx (p : ℕ) : NeSpx (cycA l hl) :=
  ⟨{vpt l hl p}, ⟨_, Finset.mem_singleton_self _⟩, isSimplex_singleton _⟩

/-- The edge simplex joining the positions `p` and `p+1`. -/
def edSpx (p : ℕ) : NeSpx (cycA l hl) :=
  ⟨{vpt l hl p, vpt l hl (p + 1)}, ⟨vpt l hl p, by simp⟩, isSimplex_pair (vpt_adj l hl p)⟩

@[simp] theorem vtxSpx_val (p : ℕ) : (vtxSpx l hl p).1 = {vpt l hl p} := rfl

@[simp] theorem edSpx_val (p : ℕ) :
    (edSpx l hl p).1 = {vpt l hl p, vpt l hl (p + 1)} := rfl

theorem vtx_le_ed (p : ℕ) : vtxSpx l hl p ≤ edSpx l hl p := by
  have h : ({vpt l hl p} : Finset (Fin (2 * l.length)))
      ⊆ {vpt l hl p, vpt l hl (p + 1)} := by
    intro x hx
    simp only [Finset.mem_singleton] at hx
    simp [hx]
  exact h

theorem vtx_succ_le_ed (p : ℕ) : vtxSpx l hl (p + 1) ≤ edSpx l hl p := by
  have h : ({vpt l hl (p + 1)} : Finset (Fin (2 * l.length)))
      ⊆ {vpt l hl p, vpt l hl (p + 1)} := by
    intro x hx
    simp only [Finset.mem_singleton] at hx
    simp [hx]
  exact h

/-! ### The values of the attaching map -/

theorem att_vtx (p : ℕ) :
    attCyc w l hl (vtxSpx l hl p) = iRose w (vertLab l (p % (2 * l.length))) := by
  rw [attCyc_apply, vtxSpx_val, roseLab_singleton, vpt_val]

theorem att_ed (p : ℕ) :
    attCyc w l hl (edSpx l hl p) = iRose w (edgeLab l (p % (2 * l.length))) := by
  have hlt : p % (2 * l.length) < 2 * l.length := Nat.mod_lt _ (by omega)
  rw [attCyc_apply, edSpx_val]
  by_cases h : p % (2 * l.length) + 1 < 2 * l.length
  · have hb := vpt_succ_lt l hl h
    have hxy : vpt l hl p < vpt l hl (p + 1) := by
      rw [Fin.lt_def, vpt_val, hb]; omega
    rw [roseLab_pair l hxy, vpt_val, hb]
    congr 1
    simp [edgePos]
  · have hw : p % (2 * l.length) + 1 = 2 * l.length := by omega
    have hb := vpt_succ_wrap l hl hw
    have hxy : vpt l hl (p + 1) < vpt l hl p := by
      rw [Fin.lt_def, hb, vpt_val]; omega
    rw [Finset.pair_comm, roseLab_pair l hxy, hb, vpt_val]
    congr 1
    have hne : ¬ p % (2 * l.length) = 0 + 1 := by omega
    simp [edgePos, hne]

/-! ### The loop around the cycle -/

/-- The two edges of the cycle at the position `p`: up to the edge and down to the next
vertex. -/
def segPath (p : ℕ) : List ((orderCx (NeSpx (cycA l hl))).E × Bool) :=
  [ordPos (vtx_le_ed l hl p), ordNeg (vtx_succ_le_ed l hl p)]

theorem isPath_segPath (p : ℕ) :
    IsPath (orderCx (NeSpx (cycA l hl))).src (orderCx (NeSpx (cycA l hl))).tgt
      (segPath l hl p) (vtxSpx l hl p) (vtxSpx l hl (p + 1)) :=
  ⟨rfl, rfl, rfl⟩

/-- The part of the loop that traverses the letter `k`: the two halves of its loop. -/
def letterPath (k : ℕ) : List ((orderCx (NeSpx (cycA l hl))).E × Bool) :=
  segPath l hl (2 * k) ++ segPath l hl (2 * k + 1)

theorem isPath_letterPath (k : ℕ) :
    IsPath (orderCx (NeSpx (cycA l hl))).src (orderCx (NeSpx (cycA l hl))).tgt
      (letterPath l hl k) (vtxSpx l hl (2 * k)) (vtxSpx l hl (2 * k + 2)) :=
  (isPath_segPath l hl (2 * k)).append (isPath_segPath l hl (2 * k + 1))

/-- **The geometric loop of the cut surface**: the path that goes around the cycle through its
first `m` letters. -/
def sigLoop : ℕ → List ((orderCx (NeSpx (cycA l hl))).E × Bool)
  | 0 => []
  | m + 1 => sigLoop m ++ letterPath l hl m

theorem isPath_sigLoop (m : ℕ) :
    IsPath (orderCx (NeSpx (cycA l hl))).src (orderCx (NeSpx (cycA l hl))).tgt
      (sigLoop l hl m) (vtxSpx l hl 0) (vtxSpx l hl (2 * m)) := by
  induction m with
  | zero => exact rfl
  | succ m ih =>
      have h := ih.append (isPath_letterPath l hl m)
      have he : 2 * m + 2 = 2 * (m + 1) := by omega
      rw [he] at h
      exact h

theorem vtxSpx_full : vtxSpx l hl (2 * l.length) = vtxSpx l hl 0 := by
  have hv : vpt l hl (2 * l.length) = vpt l hl 0 := by
    apply Fin.ext
    simp [Nat.mod_self]
  simp [vtxSpx, hv]

/-- The loop around the whole cycle, based at the vertex `0`. -/
theorem isPath_sigLoop_full :
    IsPath (orderCx (NeSpx (cycA l hl))).src (orderCx (NeSpx (cycA l hl))).tgt
      (sigLoop l hl l.length) (vtxSpx l hl 0) (vtxSpx l hl 0) := by
  have h := isPath_sigLoop l hl l.length
  rwa [vtxSpx_full] at h

/-! ### The attaching map spells the word along the loop -/

theorem letterLoop_eq (q : α × Bool) :
    letterLoop w q =
      [ordPos ((iRose_monotone w) (Rose.base_le_edg q.1 (!q.2))),
       ordNeg ((iRose_monotone w) (Rose.mid_le_edg q.1 (!q.2))),
       ordPos ((iRose_monotone w) (Rose.mid_le_edg q.1 q.2)),
       ordNeg ((iRose_monotone w) (Rose.base_le_edg q.1 q.2))] := by
  obtain ⟨i, b⟩ := q
  cases b <;> rfl

theorem mapPath_letterPath (k : ℕ) (hk : k < l.length) :
    mapPath (orderCxMap (attCyc w l hl) (attCyc w l hl).monotone) (letterPath l hl k)
      = letterLoop w (l[k]'hk) := by
  have hq : l[2 * k / 2]? = some (l[k]'hk) := by
    have h2 : 2 * k / 2 = k := by omega
    rw [h2]
    exact List.getElem?_eq_getElem hk
  have hq' : l[(2 * k + 1) / 2]? = some (l[k]'hk) := by
    have h2 : (2 * k + 1) / 2 = k := by omega
    rw [h2]
    exact List.getElem?_eq_getElem hk
  have hmod0 : (2 * k) % (2 * l.length) = 2 * k := Nat.mod_eq_of_lt (by omega)
  have hmod1 : (2 * k + 1) % (2 * l.length) = 2 * k + 1 := Nat.mod_eq_of_lt (by omega)
  have hmod2 : ((2 * k + 1 + 1) % (2 * l.length)) % 2 = 0 := by
    rcases Nat.lt_or_ge (2 * k + 2) (2 * l.length) with h | h
    · rw [Nat.mod_eq_of_lt (show 2 * k + 1 + 1 < 2 * l.length by omega)]; omega
    · have : 2 * k + 1 + 1 = 2 * l.length := by omega
      rw [this, Nat.mod_self]
  -- the five values of the attaching map along the letter
  have e1 : attCyc w l hl (vtxSpx l hl (2 * k)) = iRose w Rose.base := by
    rw [att_vtx, hmod0, vertLab_of_even (by omega)]
  have e2 : attCyc w l hl (edSpx l hl (2 * k))
      = iRose w (Rose.edg (l[k]'hk).1 (!(l[k]'hk).2)) := by
    rw [att_ed, hmod0, edgeLab_eq hq, if_pos (by omega)]
  have e3 : attCyc w l hl (vtxSpx l hl (2 * k + 1))
      = iRose w (Rose.mid (l[k]'hk).1) := by
    rw [att_vtx, hmod1, vertLab_of_odd (by omega) hq']
  have e4 : attCyc w l hl (edSpx l hl (2 * k + 1))
      = iRose w (Rose.edg (l[k]'hk).1 (l[k]'hk).2) := by
    rw [att_ed, hmod1, edgeLab_eq hq', if_neg (by omega)]
  have e5 : attCyc w l hl (vtxSpx l hl (2 * k + 1 + 1)) = iRose w Rose.base := by
    rw [att_vtx, vertLab_of_even hmod2]
  rw [letterLoop_eq]
  have c1 := ordPos_congr e1 e2 ((attCyc w l hl).monotone (vtx_le_ed l hl (2 * k)))
    ((iRose_monotone w) (Rose.base_le_edg (l[k]'hk).1 (!(l[k]'hk).2)))
  have c2 := ordNeg_congr e3 e2 ((attCyc w l hl).monotone (vtx_succ_le_ed l hl (2 * k)))
    ((iRose_monotone w) (Rose.mid_le_edg (l[k]'hk).1 (!(l[k]'hk).2)))
  have c3 := ordPos_congr e3 e4 ((attCyc w l hl).monotone (vtx_le_ed l hl (2 * k + 1)))
    ((iRose_monotone w) (Rose.mid_le_edg (l[k]'hk).1 (l[k]'hk).2))
  have c4 := ordNeg_congr e5 e4 ((attCyc w l hl).monotone (vtx_succ_le_ed l hl (2 * k + 1)))
    ((iRose_monotone w) (Rose.base_le_edg (l[k]'hk).1 (l[k]'hk).2))
  exact congrArg₂ List.cons c1 (congrArg₂ List.cons c2 (congrArg₂ List.cons c3
    (congrArg₂ List.cons c4 rfl)))

theorem mapPath_sigLoop (m : ℕ) (hm : m ≤ l.length) :
    mapPath (orderCxMap (attCyc w l hl) (attCyc w l hl).monotone) (sigLoop l hl m)
      = wordLoop w (l.take m) := by
  induction m with
  | zero => rfl
  | succ m ih =>
      have hmk : m < l.length := by omega
      have hrec : sigLoop l hl (m + 1) = sigLoop l hl m ++ letterPath l hl m := rfl
      rw [hrec]
      have hsplit : l.take (m + 1) = l.take m ++ [l[m]'hmk] := by
        rw [List.take_add_one, List.getElem?_eq_getElem hmk]
        rfl
      rw [hsplit, wordLoop_append]
      have hmap : mapPath (orderCxMap (attCyc w l hl) (attCyc w l hl).monotone)
          (sigLoop l hl m ++ letterPath l hl m)
          = mapPath (orderCxMap (attCyc w l hl) (attCyc w l hl).monotone) (sigLoop l hl m)
            ++ mapPath (orderCxMap (attCyc w l hl) (attCyc w l hl).monotone)
              (letterPath l hl m) := by
        simp [mapPath]
      rw [hmap, ih (by omega), mapPath_letterPath w l hl m hmk]
      have hone : wordLoop w [l[m]'hmk] = letterLoop w (l[m]'hmk) := by
        simp [wordLoop]
      rw [hone]

/-- **The attaching map spells the word `l` along the loop of the cut surface.** -/
theorem mapPath_sigLoop_full :
    mapPath (orderCxMap (attCyc w l hl) (attCyc w l hl).monotone) (sigLoop l hl l.length)
      = wordLoop w l := by
  rw [mapPath_sigLoop w l hl l.length le_rfl, List.take_length]

/-- The base vertex of the cycle is carried to the base point of the presentation complex. -/
theorem att_base : attCyc w l hl (vtxSpx l hl 0) = ptBase w := by
  rw [att_vtx, Nat.zero_mod, vertLab_of_even rfl]
  rfl

end Loop

end Davis
end FiniteChains
