import Mathlib

/-!
# The chain model of a mapping cylinder

For a chain map `f : S_* → A_*` of chain complexes of modules over one ring `R`, the standard
chain model of the mapping cylinder of `f` is

  `P_n = A_n ⊕ S_n ⊕ S_{n−1}`,
  `d (x, s, t) = (d_A x + f t, d_S s − t, − d_S t)`,

with the convention that negative degrees are zero.  This file constructs that complex and
verifies the structural identities:

* `FiniteChains.CylCx.cylD_cylD` — `d ∘ d = 0`;
* `FiniteChains.CylCx.incl` (`i x = (x,0,0)`), `FiniteChains.CylCx.inclOuter` (`j s = (0,s,0)`),
  `FiniteChains.CylCx.retr` (`r (x,s,t) = x + f s`) and `FiniteChains.CylCx.htpy`
  (`H (x,s,t) = (0,0,−s)`) are the inclusion of the base, the inclusion of the **outer end**,
  the retraction and the homotopy;
* `FiniteChains.CylCx.retr_incl` — `r ∘ i = id`;
* `FiniteChains.CylCx.cylD_htpy_add_htpy_cylD` and `FiniteChains.CylCx.cylD_htpy_zero` —
  `d H + H d = id − i r` (the second statement is the bottom degree, where the term `H d`
  is absent because `P_{-1} = 0`);
* `FiniteChains.CylCx.incl_chainMap`, `FiniteChains.CylCx.inclOuter_chainMap`,
  `FiniteChains.CylCx.retr_chainMap` — all three maps are chain maps;
* `FiniteChains.CylCx.retr_inclOuter` — `r ∘ j = f`, i.e. the outer end is glued to the base
  along `f`;
* `FiniteChains.CylCx.inclOuter_injective` — the outer end `j(S)` is retained as a direct
  summand in each degree.  This is the end on which the mirrors sit, so the model must keep it.

The ring `R` is arbitrary, so group coefficients `R = ℤ[G]` are the special case used for the
chains of a cover; the chain map `f` is data, given over that same ring.

Nothing here proves anything about coverings or about `π₁`-injectivity: these are the algebraic
identities of the cylinder, and nothing more.  In particular the identity `d H + H d = id − i r`
says exactly that the cylinder deformation-retracts, at chain level, onto the base; it does not
by itself compare the cylinder with any geometric block.
-/

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains
namespace CylCx

universe u v

variable (R : Type u) [Ring R]

/-! ### Graded data -/

/-- The degree shift `S ↦ S[-1]`, with `S_{-1} = 0`. -/
def Shift (S : ℕ → Type v) : ℕ → Type v
  | 0 => PUnit
  | (n + 1) => S n

instance instAddCommGroupShift (S : ℕ → Type v) [∀ n, AddCommGroup (S n)] :
    ∀ n, AddCommGroup (Shift S n)
  | 0 => inferInstanceAs (AddCommGroup PUnit)
  | (n + 1) => inferInstanceAs (AddCommGroup (S n))

instance instModuleShift (S : ℕ → Type v) [∀ n, AddCommGroup (S n)] [∀ n, Module R (S n)] :
    ∀ n, Module R (Shift S n)
  | 0 => by
      change Module R PUnit.{v+1}
      infer_instance
  | (n + 1) => by
      change Module R (S n)
      infer_instance

variable {R}
variable {A S : ℕ → Type v}
  [∀ n, AddCommGroup (A n)] [∀ n, Module R (A n)]
  [∀ n, AddCommGroup (S n)] [∀ n, Module R (S n)]

/-- The identification `S[-1]_{n+1} = S_n`, read as a linear map.  It is the identity; it is
introduced only to keep the two descriptions of the same module apart in the statements. -/
def shiftDown (R : Type u) [Ring R] {S : ℕ → Type v} [∀ n, AddCommGroup (S n)]
    [∀ n, Module R (S n)] (n : ℕ) : Shift S (n + 1) →ₗ[R] S n := LinearMap.id

/-- The identification `S_n = S[-1]_{n+1}`, read as a linear map. -/
def shiftUp (R : Type u) [Ring R] {S : ℕ → Type v} [∀ n, AddCommGroup (S n)]
    [∀ n, Module R (S n)] (n : ℕ) : S n →ₗ[R] Shift S (n + 1) := LinearMap.id

@[simp] theorem shiftDown_shiftUp (n : ℕ) (s : S n) :
    shiftDown R n (shiftUp R n s) = s := rfl

@[simp] theorem shiftUp_shiftDown (n : ℕ) (t : Shift S (n + 1)) :
    shiftUp R n (shiftDown R n t) = t := rfl

/-- The differential of `S`, read on the shifted family. -/
def dShift (dS : ∀ n, S (n + 1) →ₗ[R] S n) : ∀ n, Shift S (n + 1) →ₗ[R] Shift S n
  | 0 => 0
  | (n + 1) => (shiftUp R n).comp ((dS n).comp (shiftDown R (n + 1)))

@[simp] theorem dShift_succ_apply (dS : ∀ n, S (n + 1) →ₗ[R] S n) (n : ℕ)
    (t : Shift S (n + 2)) :
    dShift dS (n + 1) t = shiftUp R n (dS n (shiftDown R (n + 1) t)) := rfl

@[simp] theorem dShift_zero_apply (dS : ∀ n, S (n + 1) →ₗ[R] S n) (t : Shift S 1) :
    dShift dS 0 t = 0 := rfl

/-- Elements of the bottom shifted degree vanish: `S_{-1} = 0`. -/
theorem shift_zero_eq_zero (t : Shift S 0) : t = 0 := rfl

/-- `d ∘ d = 0` for the shifted differential. -/
theorem dShift_dShift (dS : ∀ n, S (n + 1) →ₗ[R] S n)
    (hSS : ∀ n (s : S (n + 2)), dS n (dS (n + 1) s) = 0) :
    ∀ (n : ℕ) (t : Shift S (n + 2)), dShift dS n (dShift dS (n + 1) t) = 0 := by
  intro n t
  cases n with
  | zero => rfl
  | succ k =>
      show shiftUp R k (dS k (shiftDown R (k + 1) (shiftUp R (k + 1) (dS (k + 1)
        (shiftDown R (k + 2) t))))) = 0
      rw [shiftDown_shiftUp, hSS]
      exact map_zero _

/-! ### The cylinder complex -/

/-- The chain groups of the mapping cylinder: `P_n = A_n ⊕ S_n ⊕ S_{n−1}`. -/
abbrev Cyl (A S : ℕ → Type v) (n : ℕ) : Type v := A n × S n × Shift S n

variable (dA : ∀ n, A (n + 1) →ₗ[R] A n) (dS : ∀ n, S (n + 1) →ₗ[R] S n)
  (f : ∀ n, S n →ₗ[R] A n)

/-- The differential of the mapping cylinder:
`d (x, s, t) = (d_A x + f t, d_S s − t, − d_S t)`. -/
def cylD (n : ℕ) : Cyl A S (n + 1) →ₗ[R] Cyl A S n where
  toFun p :=
    (dA n p.1 + f n (shiftDown R n p.2.2), dS n p.2.1 - shiftDown R n p.2.2,
      -(dShift dS n p.2.2))
  map_add' p q := by
    refine Prod.ext ?_ (Prod.ext ?_ ?_) <;>
      simp only [Prod.fst_add, Prod.snd_add, map_add, neg_add] <;> abel
  map_smul' c p := by
    refine Prod.ext ?_ (Prod.ext ?_ ?_) <;>
      simp only [Prod.smul_fst, Prod.smul_snd, map_smul, RingHom.id_apply, smul_add, smul_sub,
        smul_neg]

@[simp] theorem cylD_apply (n : ℕ) (p : Cyl A S (n + 1)) :
    cylD dA dS f n p =
      (dA n p.1 + f n (shiftDown R n p.2.2), dS n p.2.1 - shiftDown R n p.2.2,
        -(dShift dS n p.2.2)) := rfl

/-- **The cylinder is a complex**: `d ∘ d = 0`.  The hypotheses are that `A` and `S` are
complexes and that `f` is a chain map. -/
theorem cylD_cylD
    (hAA : ∀ n (x : A (n + 2)), dA n (dA (n + 1) x) = 0)
    (hSS : ∀ n (s : S (n + 2)), dS n (dS (n + 1) s) = 0)
    (hf : ∀ n (s : S (n + 1)), dA n (f (n + 1) s) = f n (dS n s))
    (n : ℕ) (p : Cyl A S (n + 2)) :
    cylD dA dS f n (cylD dA dS f (n + 1) p) = 0 := by
  obtain ⟨x, s, t⟩ := p
  refine Prod.ext ?_ (Prod.ext ?_ ?_)
  · show dA n (dA (n + 1) x + f (n + 1) (shiftDown R (n + 1) t)) +
      f n (shiftDown R n (-(dShift dS (n + 1) t))) = 0
    rw [map_add, hAA, hf, dShift_succ_apply, map_neg, shiftDown_shiftUp, map_neg]
    abel
  · show dS n (dS (n + 1) s - shiftDown R (n + 1) t) - shiftDown R n (-(dShift dS (n + 1) t)) = 0
    rw [map_sub, hSS, dShift_succ_apply, map_neg, shiftDown_shiftUp]
    abel
  · show -(dShift dS n (-(dShift dS (n + 1) t))) = 0
    rw [map_neg, dShift_dShift dS hSS]
    abel

/-! ### The three maps and the homotopy -/

/-- The inclusion of the base: `i x = (x, 0, 0)`. -/
def incl (R : Type u) [Ring R] {A S : ℕ → Type v} [∀ n, AddCommGroup (A n)] [∀ n, Module R (A n)]
    [∀ n, AddCommGroup (S n)] [∀ n, Module R (S n)] (n : ℕ) : A n →ₗ[R] Cyl A S n where
  toFun x := (x, 0, 0)
  map_add' x y := by refine Prod.ext rfl (Prod.ext ?_ ?_) <;> simp
  map_smul' c x := by refine Prod.ext rfl (Prod.ext ?_ ?_) <;> simp

/-- The inclusion of the **outer end** `Σ`: `j s = (0, s, 0)`.  This is the end carrying the
mirrors, and the model keeps it as a direct summand. -/
def inclOuter (R : Type u) [Ring R] {A S : ℕ → Type v} [∀ n, AddCommGroup (A n)]
    [∀ n, Module R (A n)] [∀ n, AddCommGroup (S n)] [∀ n, Module R (S n)] (n : ℕ) :
    S n →ₗ[R] Cyl A S n where
  toFun s := (0, s, 0)
  map_add' x y := by refine Prod.ext ?_ (Prod.ext rfl ?_) <;> simp
  map_smul' c x := by refine Prod.ext ?_ (Prod.ext rfl ?_) <;> simp

/-- The retraction onto the base: `r (x, s, t) = x + f s`. -/
def retr (n : ℕ) : Cyl A S n →ₗ[R] A n where
  toFun p := p.1 + f n p.2.1
  map_add' p q := by
    simp only [Prod.fst_add, Prod.snd_add, map_add]
    abel
  map_smul' c p := by
    simp only [Prod.smul_fst, Prod.smul_snd, map_smul, RingHom.id_apply, smul_add]

/-- The homotopy `H (x, s, t) = (0, 0, −s)`, raising the degree by one. -/
def htpy (R : Type u) [Ring R] {A S : ℕ → Type v} [∀ n, AddCommGroup (A n)] [∀ n, Module R (A n)]
    [∀ n, AddCommGroup (S n)] [∀ n, Module R (S n)] (n : ℕ) :
    Cyl A S n →ₗ[R] Cyl A S (n + 1) where
  toFun p := (0, 0, shiftUp R n (-p.2.1))
  map_add' p q := by
    refine Prod.ext ?_ (Prod.ext ?_ ?_) <;>
      simp only [Prod.fst_add, Prod.snd_add, neg_add, map_add, add_zero]
  map_smul' c p := by
    refine Prod.ext ?_ (Prod.ext ?_ ?_) <;>
      simp only [Prod.smul_fst, Prod.smul_snd, RingHom.id_apply, smul_zero, ← smul_neg, map_smul]

@[simp] theorem incl_apply (n : ℕ) (x : A n) :
    incl R (A := A) (S := S) n x = (x, 0, 0) := rfl

@[simp] theorem inclOuter_apply (n : ℕ) (s : S n) :
    inclOuter R (A := A) (S := S) n s = (0, s, 0) := rfl

@[simp] theorem retr_apply (n : ℕ) (p : Cyl A S n) : retr f n p = p.1 + f n p.2.1 := rfl

@[simp] theorem htpy_apply (n : ℕ) (p : Cyl A S n) :
    htpy R (A := A) (S := S) n p = (0, 0, shiftUp R n (-p.2.1)) := rfl

/-- `r ∘ i = id`. -/
theorem retr_incl (n : ℕ) (x : A n) : retr f n (incl R (A := A) (S := S) n x) = x := by
  simp

/-- `r ∘ j = f`: the outer end is glued to the base along `f`. -/
theorem retr_inclOuter (n : ℕ) (s : S n) : retr f n (inclOuter R (A := A) (S := S) n s) = f n s := by
  simp

/-- The inclusion of the outer end is injective in every degree. -/
theorem inclOuter_injective (n : ℕ) :
    Function.Injective (inclOuter R (A := A) (S := S) n) := by
  intro s s' h
  simpa using congrArg (fun p : Cyl A S n => p.2.1) h

/-- The inclusion of the base is a chain map. -/
theorem incl_chainMap (n : ℕ) (x : A (n + 1)) :
    cylD dA dS f n (incl R (A := A) (S := S) (n + 1) x) = incl R (A := A) (S := S) n (dA n x) := by
  refine Prod.ext ?_ (Prod.ext ?_ ?_)
  · show dA n x + f n (shiftDown R n 0) = dA n x
    simp
  · show dS n 0 - shiftDown R n (0 : Shift S (n + 1)) = 0
    simp
  · show -(dShift dS n (0 : Shift S (n + 1))) = 0
    simp

/-- The inclusion of the outer end is a chain map. -/
theorem inclOuter_chainMap (n : ℕ) (s : S (n + 1)) :
    cylD dA dS f n (inclOuter R (A := A) (S := S) (n + 1) s) =
      inclOuter R (A := A) (S := S) n (dS n s) := by
  refine Prod.ext ?_ (Prod.ext ?_ ?_)
  · show dA n 0 + f n (shiftDown R n 0) = 0
    simp
  · show dS n s - shiftDown R n (0 : Shift S (n + 1)) = dS n s
    simp
  · show -(dShift dS n (0 : Shift S (n + 1))) = 0
    simp

/-- The retraction is a chain map; this is where the chain-map property of `f` is used. -/
theorem retr_chainMap (hf : ∀ n (s : S (n + 1)), dA n (f (n + 1) s) = f n (dS n s))
    (n : ℕ) (p : Cyl A S (n + 1)) :
    retr f n (cylD dA dS f n p) = dA n (retr f (n + 1) p) := by
  obtain ⟨x, s, t⟩ := p
  show (dA n x + f n (shiftDown R n t)) + f n (dS n s - shiftDown R n t) = dA n (x + f (n + 1) s)
  rw [map_add, map_sub, hf]
  abel

/-- **The homotopy identity `d H + H d = id − i r` in positive degrees.** -/
theorem cylD_htpy_add_htpy_cylD (n : ℕ) (p : Cyl A S (n + 1)) :
    cylD dA dS f (n + 1) (htpy R (A := A) (S := S) (n + 1) p) + htpy R (A := A) (S := S) n (cylD dA dS f n p) =
      p - incl R (A := A) (S := S) (n + 1) (retr f (n + 1) p) := by
  obtain ⟨x, s, t⟩ := p
  refine Prod.ext ?_ (Prod.ext ?_ ?_)
  · show (dA (n + 1) 0 + f (n + 1) (shiftDown R (n + 1) (shiftUp R (n + 1) (-s)))) + 0 =
      x - (x + f (n + 1) s)
    rw [shiftDown_shiftUp, map_zero, map_neg]
    abel
  · show (dS (n + 1) 0 - shiftDown R (n + 1) (shiftUp R (n + 1) (-s))) + 0 = s - 0
    rw [shiftDown_shiftUp, map_zero]
    abel
  · show -(dShift dS (n + 1) (shiftUp R (n + 1) (-s))) + shiftUp R n (-(dS n s - shiftDown R n t)) =
      t - 0
    rw [dShift_succ_apply, shiftDown_shiftUp]
    rw [map_neg (shiftUp R n) (dS n s - shiftDown R n t), map_sub (shiftUp R n),
      shiftUp_shiftDown, map_neg (dS n) s, map_neg (shiftUp R n) (dS n s)]
    abel

/-- **The homotopy identity in the bottom degree**, where `P_{-1} = 0` and the term `H d` is
absent. -/
theorem cylD_htpy_zero (p : Cyl A S 0) :
    cylD dA dS f 0 (htpy R (A := A) (S := S) 0 p) = p - incl R (A := A) (S := S) 0 (retr f 0 p) := by
  obtain ⟨x, s, t⟩ := p
  refine Prod.ext ?_ (Prod.ext ?_ ?_)
  · show dA 0 0 + f 0 (shiftDown R 0 (shiftUp R 0 (-s))) = x - (x + f 0 s)
    rw [shiftDown_shiftUp, map_zero, map_neg]
    abel
  · show dS 0 0 - shiftDown R 0 (shiftUp R 0 (-s)) = s - 0
    rw [shiftDown_shiftUp, map_zero]
    abel
  · exact (shift_zero_eq_zero _).trans (shift_zero_eq_zero _).symm

/-! ### Consequence: the cycles of the cylinder come from the base -/

/-- **Every cycle of the cylinder is a cycle of the base plus a boundary.**  This is the form in
which the homotopy identity is used in the gluing argument: a cylinder piece contributes only
the images of the cycles of its copy of the base. -/
theorem cycle_eq_incl_add_bdry (n : ℕ) (z : Cyl A S (n + 1)) (hz : cylD dA dS f n z = 0) :
    z = incl R (A := A) (S := S) (n + 1) (retr f (n + 1) z) +
      cylD dA dS f (n + 1) (htpy R (A := A) (S := S) (n + 1) z) := by
  have h := cylD_htpy_add_htpy_cylD dA dS f n z
  rw [hz, map_zero, add_zero] at h
  rw [h]
  abel

/-- The retraction of a cycle of the cylinder is a cycle of the base. -/
theorem retr_cycle (hf : ∀ n (s : S (n + 1)), dA n (f (n + 1) s) = f n (dS n s))
    (n : ℕ) (z : Cyl A S (n + 1)) (hz : cylD dA dS f n z = 0) :
    dA n (retr f (n + 1) z) = 0 := by
  rw [← retr_chainMap dA dS f hf n z, hz, map_zero]

end CylCx
end FiniteChains
