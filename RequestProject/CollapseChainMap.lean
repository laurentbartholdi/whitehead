import Mathlib

/-!
# The chain map induced by a collapse

`RequestProject/Collapse.lean` proves the combinatorial half of Lemma 3.3 (ii) of the paper:
the three-cells of the truncated complex `M_q` disappear under elementary collapses, leaving
a two-dimensional spine.  Two further steps of the block argument are chain level statements
about that collapse:

* Lemma 3.3 (iii) — *the inclusion sends `[Σ_q]` to zero in `H₂(M_q)`* — is used by the
  capping argument in the form: the cellular chain of the cut surface **is the zero chain of
  the spine**;
* Lemma 3.3 (i) — *the cone model `C_q` is aspherical* — is used in the form: in the
  collapsed complex every two-cycle is a multiple of the boundary of the single remaining
  three-cell.

Both follow from the chain map of the collapse, which is what this file builds, over an
arbitrary ring of coefficients `R` (for the second application `R` is the group ring of the
fundamental group and the chains are those of the universal cover).

An elementary collapse removes a top cell `t` together with a free face `f` of it, and
induces on chains the Whitehead retraction

  `retr t f x = x - (x f)·(d t f)⁻¹·(d t)`,

where `d t` is the cellular boundary of `t` and `d t f` is a unit.  It kills the
`f`-coordinate, it kills `d t`, and it fixes the boundary of every top cell which does not
contain `f` — and a top cell removed later than `t` does not contain `f`, precisely because
`f` was free for `t` at the moment of the collapse.  Composing the retractions of a whole
collapse therefore gives a map `cmap` which

* kills the boundary of every collapsed top cell (`CollapseChain.cmap_bdry_eq_zero`), hence
  kills every combination of such boundaries (`CollapseChain.cmap_sum_eq_zero`),
* vanishes on every collapsed face (`CollapseChain.cmap_apply_eq_zero`), so its values are
  genuinely chains of the spine, and
* fixes every chain of the spine (`CollapseChain.cmap_of_forall_eq_zero`).

Consequently a two-chain which bounds becomes the zero chain of the spine
(`CollapseChain.cmap_eq_zero_of_isBoundary`) — the step "in a two-complex a homologically
zero two-cycle is the zero cellular chain" of the paper's proof of (B3) — and, if all
three-cells but one are collapsed away, every two-cycle of the spine is a multiple of the
boundary of the surviving three-cell
(`CollapseChain.exists_mul_bdry_of_cycles_bound`), which is the asphericity hypothesis of the
cone model in the form in which (B3) uses it.
-/

namespace FiniteChains
namespace CollapseChain

variable {T F R : Type*} [Ring R]

/-- The Whitehead retraction of an elementary collapse removing the top cell `t` across its
free face `f`: subtract the multiple of the boundary `d t` which kills the `f`-coordinate. -/
noncomputable def retr (d : T → F → R) (t : T) (f : F) (x : F → R) : F → R :=
  fun g => x g - x f * Ring.inverse (d t f) * d t g

/-- The chain map of a sequence of elementary collapses: the composite of the retractions of
its steps, each step being recorded as the removed top cell together with the face it is
collapsed across. -/
noncomputable def cmap (d : T → F → R) : List (T × F) → (F → R) → (F → R)
  | [], x => x
  | (t, f) :: l, x => cmap d l (retr d t f x)

/-- The hypotheses under which a list of (top cell, face) pairs is a sequence of elementary
collapses on the chain level: the face is a *unit* face of the cell it is collapsed across,
and it is *free*, i.e. no cell removed later meets it. -/
def IsChainCollapse (d : T → F → R) : List (T × F) → Prop
  | [] => True
  | (t, f) :: l => IsUnit (d t f) ∧ (∀ p ∈ l, d p.1 f = 0) ∧ IsChainCollapse d l

variable {d : T → F → R}

@[simp] theorem retr_zero (t : T) (f : F) : retr d t f 0 = 0 := by
  funext g; simp [retr]

theorem retr_add (t : T) (f : F) (x y : F → R) :
    retr d t f (x + y) = retr d t f x + retr d t f y := by
  funext g
  simp only [retr, Pi.add_apply, add_mul]
  abel

theorem retr_leftMul (a : R) (t : T) (f : F) (x : F → R) :
    retr d t f (fun g => a * x g) = fun g => a * retr d t f x g := by
  funext g
  simp only [retr, mul_sub, mul_assoc]

@[simp] theorem cmap_zero (l : List (T × F)) : cmap d l 0 = 0 := by
  induction l with
  | nil => rfl
  | cons p l ih => obtain ⟨t, f⟩ := p; simp [cmap, ih]

theorem cmap_add (l : List (T × F)) (x y : F → R) :
    cmap d l (x + y) = cmap d l x + cmap d l y := by
  induction l generalizing x y with
  | nil => rfl
  | cons p l ih => obtain ⟨t, f⟩ := p; simp [cmap, retr_add, ih]

theorem cmap_leftMul (l : List (T × F)) (a : R) (x : F → R) :
    cmap d l (fun g => a * x g) = fun g => a * cmap d l x g := by
  induction l generalizing x with
  | nil => rfl
  | cons p l ih =>
      obtain ⟨t, f⟩ := p
      show cmap d l (retr d t f fun g => a * x g) = fun g => a * cmap d l (retr d t f x) g
      rw [retr_leftMul, ih]

/-- The retraction of an elementary collapse kills the boundary of the cell it removes. -/
theorem retr_self {t : T} {f : F} (h : IsUnit (d t f)) : retr d t f (d t) = 0 := by
  funext g
  simp [retr, Ring.mul_inverse_cancel _ h]

/-- The retraction of an elementary collapse fixes the boundary of a cell which does not
meet the face it is collapsed across. -/
theorem retr_of_notMem {t t' : T} {f : F} (h : d t' f = 0) : retr d t f (d t') = d t' := by
  funext g; simp [retr, h]

/-- **The chain map of a collapse kills the boundary of every collapsed cell.** -/
theorem cmap_bdry_eq_zero {l : List (T × F)} (hl : IsChainCollapse d l) :
    ∀ p ∈ l, cmap d l (d p.1) = 0 := by
  induction l with
  | nil => intro p hp; exact absurd hp List.not_mem_nil
  | cons p l ih =>
      obtain ⟨t, f⟩ := p
      obtain ⟨hunit, hfree, hrest⟩ := hl
      intro r hr
      rcases List.mem_cons.1 hr with rfl | hrl
      · show cmap d l (retr d t f (d t)) = 0
        rw [retr_self hunit, cmap_zero]
      · show cmap d l (retr d t f (d r.1)) = 0
        rw [retr_of_notMem (hfree r hrl)]
        exact ih hrest r hrl

/-- The chain map of a collapse, applied to a combination of boundaries of top cells. -/
theorem cmap_sum (l : List (T × F)) [DecidableEq T] (s : Finset T) (c : T → R) :
    cmap d l (fun g => ∑ t ∈ s, c t * d t g) = fun g => ∑ t ∈ s, c t * cmap d l (d t) g := by
  classical
  induction s using Finset.induction with
  | empty =>
      have hz : (fun g => ∑ t ∈ (∅ : Finset T), c t * d t g) = (0 : F → R) := by
        funext g; simp
      rw [hz, cmap_zero]
      funext g; simp
  | insert t s ht ih =>
      have hsplit : (fun g => ∑ u ∈ insert t s, c u * d u g)
          = (fun g => c t * d t g) + (fun g => ∑ u ∈ s, c u * d u g) := by
        funext g
        simp only [Pi.add_apply]
        rw [Finset.sum_insert ht]
      rw [hsplit, cmap_add, cmap_leftMul, ih]
      funext g
      simp only [Pi.add_apply]
      rw [Finset.sum_insert ht]

/-- **The chain map of a collapse kills every combination of boundaries of collapsed
cells.** -/
theorem cmap_sum_eq_zero {l : List (T × F)} (hl : IsChainCollapse d l) [DecidableEq T]
    (s : Finset T) (c : T → R) (hs : ∀ t ∈ s, ∃ f, (t, f) ∈ l) :
    cmap d l (fun g => ∑ t ∈ s, c t * d t g) = 0 := by
  classical
  rw [cmap_sum]
  funext g
  refine Finset.sum_eq_zero fun t htt => ?_
  obtain ⟨f, hf⟩ := hs t htt
  rw [cmap_bdry_eq_zero hl (t, f) hf]
  simp

/-- The retraction of an elementary collapse kills the coordinate of the face it removes. -/
theorem retr_apply_self {t : T} {f : F} (h : IsUnit (d t f)) (x : F → R) :
    retr d t f x f = 0 := by
  simp [retr, mul_assoc, Ring.inverse_mul_cancel _ h]

/-- A later retraction does not revive the coordinate of an already collapsed face. -/
theorem retr_apply_of_notMem {t : T} {f f' : F} (h : d t f = 0) (x : F → R) :
    retr d t f' x f = x f := by
  simp [retr, h]

/-- **The values of the chain map of a collapse are chains of the spine**: every collapsed
face has coefficient zero. -/
theorem cmap_apply_eq_zero {l : List (T × F)} (hl : IsChainCollapse d l) (x : F → R) :
    ∀ p ∈ l, cmap d l x p.2 = 0 := by
  induction l generalizing x with
  | nil => intro p hp; exact absurd hp List.not_mem_nil
  | cons p l ih =>
      obtain ⟨t, f⟩ := p
      obtain ⟨hunit, hfree, hrest⟩ := hl
      intro r hr
      rcases List.mem_cons.1 hr with rfl | hrl
      · -- the collapsed face `f`: killed by its own retraction and never revived
        show cmap d l (retr d t f x) f = 0
        have key : ∀ (l' : List (T × F)), IsChainCollapse d l' →
            (∀ p ∈ l', d p.1 f = 0) → ∀ y : F → R, y f = 0 → cmap d l' y f = 0 := by
          intro l'
          induction l' with
          | nil => intro _ _ y hy; exact hy
          | cons p' l'' ih' =>
              obtain ⟨t', f'⟩ := p'
              intro hl'' hzero y hy
              refine ih' hl''.2.2 (fun q hq => hzero q (List.mem_cons_of_mem _ hq)) _ ?_
              rw [retr_apply_of_notMem (hzero (t', f') List.mem_cons_self) y]
              exact hy
        exact key l hrest hfree _ (retr_apply_self hunit x)
      · show cmap d l (retr d t f x) r.2 = 0
        exact ih hrest _ r hrl

/-- **The chain map of a collapse fixes the chains of the spine**: a chain which already
vanishes on every collapsed face is left unchanged. -/
theorem cmap_of_forall_eq_zero {l : List (T × F)} (x : F → R) (hx : ∀ p ∈ l, x p.2 = 0) :
    cmap d l x = x := by
  induction l generalizing x with
  | nil => rfl
  | cons p l ih =>
      obtain ⟨t, f⟩ := p
      have hf : x f = 0 := hx (t, f) List.mem_cons_self
      have hretr : retr d t f x = x := by
        funext g; simp [retr, hf]
      show cmap d l (retr d t f x) = x
      rw [hretr]
      exact ih x fun q hq => hx q (List.mem_cons_of_mem _ hq)

/-- **A boundary collapses to the zero chain of the spine.**  If every top cell is collapsed
away, then the cellular chain obtained from a boundary is zero: this is the step "in a
two-complex a homologically zero two-cycle is the zero cellular chain". -/
theorem cmap_eq_zero_of_isBoundary {l : List (T × F)} (hl : IsChainCollapse d l)
    [DecidableEq T] {s : Finset T} {c : T → R} (hs : ∀ t ∈ s, ∃ f, (t, f) ∈ l)
    {x : F → R} (hx : ∀ g, x g = ∑ t ∈ s, c t * d t g) :
    cmap d l x = 0 := by
  have hxe : x = fun g => ∑ t ∈ s, c t * d t g := funext hx
  rw [hxe]
  exact cmap_sum_eq_zero hl s c hs

/-! ### The surviving three-cell -/

/-- **A boundary is, after the collapse, a multiple of the boundary of the surviving cell.**
If all top cells but `e` are collapsed away, then a chain of the spine which bounds in the
big complex is a left multiple of the collapsed boundary of `e`. -/
theorem exists_mul_bdry_of_isBoundary {l : List (T × F)} (hl : IsChainCollapse d l)
    [DecidableEq T] (e : T) {s : Finset T} {c : T → R}
    (hs : ∀ t ∈ s, t ≠ e → ∃ f, (t, f) ∈ l) {x : F → R} (hspine : ∀ p ∈ l, x p.2 = 0)
    (hx : ∀ g, x g = ∑ t ∈ s, c t * d t g) :
    ∃ lam : R, ∀ g, x g = lam * cmap d l (d e) g := by
  classical
  refine ⟨if e ∈ s then c e else 0, fun g => ?_⟩
  have hxe : x = fun g => ∑ t ∈ s, c t * d t g := funext hx
  have hfix : cmap d l x = x := cmap_of_forall_eq_zero x hspine
  have hsum : cmap d l x = fun g => ∑ t ∈ s, c t * cmap d l (d t) g := by
    rw [hxe, cmap_sum]
  have hval : x g = ∑ t ∈ s, c t * cmap d l (d t) g := by
    rw [← hfix, hsum]
  rw [hval]
  by_cases he : e ∈ s
  · rw [if_pos he, ← Finset.sum_erase_add s _ he]
    have hzero : ∑ t ∈ s.erase e, c t * cmap d l (d t) g = 0 := by
      refine Finset.sum_eq_zero fun t ht => ?_
      obtain ⟨f, hf⟩ :=
        hs t (Finset.mem_of_mem_erase ht) (Finset.ne_of_mem_erase ht)
      rw [cmap_bdry_eq_zero hl (t, f) hf]
      simp
    rw [hzero, zero_add]
  · rw [if_neg he, zero_mul]
    refine Finset.sum_eq_zero fun t ht => ?_
    obtain ⟨f, hf⟩ := hs t ht (by rintro rfl; exact he ht)
    rw [cmap_bdry_eq_zero hl (t, f) hf]
    simp

/-- **A boundary is, after the collapse, a combination of the boundaries of the surviving
cells.**  This is the form of the previous statement for a whole set `E` of surviving cells —
in the application to the universal cover of the cone model, `E` is the set of lifts of the
single three-cell, one for each element of the fundamental group. -/
theorem exists_sum_bdry_of_isBoundary {l : List (T × F)} (hl : IsChainCollapse d l)
    [DecidableEq T] (E : Set T) {s : Finset T} {c : T → R}
    (hs : ∀ t ∈ s, t ∉ E → ∃ f, (t, f) ∈ l) {x : F → R} (hspine : ∀ p ∈ l, x p.2 = 0)
    (hx : ∀ g, x g = ∑ t ∈ s, c t * d t g) :
    ∃ s' : Finset T, (∀ t ∈ s', t ∈ E) ∧ ∀ g, x g = ∑ t ∈ s', c t * cmap d l (d t) g := by
  classical
  refine ⟨s.filter (fun t => t ∈ E), fun t ht => (Finset.mem_filter.1 ht).2, fun g => ?_⟩
  have hxe : x = fun g => ∑ t ∈ s, c t * d t g := funext hx
  have hfix : cmap d l x = x := cmap_of_forall_eq_zero x hspine
  have hval : x g = ∑ t ∈ s, c t * cmap d l (d t) g := by
    rw [← hfix, hxe, cmap_sum]
  rw [hval, ← Finset.sum_filter_add_sum_filter_not s (fun t => t ∈ E)]
  have hzero : ∑ t ∈ s.filter (fun t => t ∉ E), c t * cmap d l (d t) g = 0 := by
    refine Finset.sum_eq_zero fun t ht => ?_
    obtain ⟨htS, htE⟩ := Finset.mem_filter.1 ht
    obtain ⟨f, hf⟩ := hs t htS htE
    rw [cmap_bdry_eq_zero hl (t, f) hf]
    simp
  rw [hzero, add_zero]

/-- **Asphericity passes to the collapsed model.**  Suppose that in the three-dimensional
complex every two-cycle bounds (`hH2`, the vanishing of the second homology of the universal
cover, which for a CAT(0) cube complex is the Cartan–Hadamard input of the paper), and that a
collapse removes every three-cell except `e`.  Then every two-cycle of the collapsed complex
is a left multiple of the boundary of `e`.

This is exactly the hypothesis `hasph` of the capping argument of (B3): the cone model `C_q`
has a single three-cell, obtained by coning the surface polygon, and every Fox cycle of the
two-skeleton is a group-ring multiple of its boundary. -/
theorem exists_mul_bdry_of_cycles_bound {l : List (T × F)} (hl : IsChainCollapse d l)
    [DecidableEq T] (e : T) (IsCycle : (F → R) → Prop)
    (hH2 : ∀ x, IsCycle x → ∃ (s : Finset T) (c : T → R), ∀ g, x g = ∑ t ∈ s, c t * d t g)
    (hcoll : ∀ t : T, t ≠ e → ∃ f, (t, f) ∈ l)
    {x : F → R} (hcyc : IsCycle x) (hspine : ∀ p ∈ l, x p.2 = 0) :
    ∃ lam : R, ∀ g, x g = lam * cmap d l (d e) g := by
  obtain ⟨s, c, hx⟩ := hH2 x hcyc
  exact exists_mul_bdry_of_isBoundary hl e (fun t _ hte => hcoll t hte) hspine hx

/-- **A cycle bounds in the whole complex, hence in the collapsed one.**  The version of
`CollapseChain.exists_mul_bdry_of_cycles_bound` for a set `E` of surviving cells. -/
theorem exists_sum_bdry_of_cycles_bound {l : List (T × F)} (hl : IsChainCollapse d l)
    [DecidableEq T] (E : Set T) (IsCycle : (F → R) → Prop)
    (hH2 : ∀ x, IsCycle x → ∃ (s : Finset T) (c : T → R), ∀ g, x g = ∑ t ∈ s, c t * d t g)
    (hcoll : ∀ t : T, t ∉ E → ∃ f, (t, f) ∈ l)
    {x : F → R} (hcyc : IsCycle x) (hspine : ∀ p ∈ l, x p.2 = 0) :
    ∃ (s' : Finset T) (c' : T → R), (∀ t ∈ s', t ∈ E) ∧
      ∀ g, x g = ∑ t ∈ s', c' t * cmap d l (d t) g := by
  obtain ⟨s, c, hx⟩ := hH2 x hcyc
  obtain ⟨s', hs', hsum⟩ :=
    exists_sum_bdry_of_isBoundary hl E (fun t _ htE => hcoll t htE) hspine hx
  exact ⟨s', c, hs', hsum⟩

/-! ### Chain complexes presented by linear maps -/

/-- The boundary matrix of a chain complex given by a linear map of finitely supported
functions: the coefficient of the face `g` in the boundary of the cell `t`. -/
noncomputable def ofLinearMap {T F : Type*} (d₃ : (T →₀ ℤ) →ₗ[ℤ] (F →₀ ℤ)) (t : T) (g : F) : ℤ :=
  d₃ (Finsupp.single t 1) g

/-- Evaluating a boundary cell by cell: a boundary is the combination, over the support of
the three-chain, of the boundaries of its cells. -/
theorem apply_eq_sum_ofLinearMap {T F : Type*} [DecidableEq T]
    (d₃ : (T →₀ ℤ) →ₗ[ℤ] (F →₀ ℤ)) (c : T →₀ ℤ) (g : F) :
    d₃ c g = ∑ t ∈ c.support, c t * ofLinearMap d₃ t g := by
  have hc : c = ∑ t ∈ c.support, c t • Finsupp.single t (1 : ℤ) := by
    ext u
    simp [Finsupp.single_apply, Finset.sum_apply', Finsupp.mem_support_iff]
  conv_lhs => rw [hc]
  rw [map_sum]
  simp only [ofLinearMap, Finsupp.coe_finset_sum, Finset.sum_apply, map_smul, Finsupp.coe_smul,
    Pi.smul_apply, smul_eq_mul]

/-- **The hypothesis `hH2` from a chain complex of finitely supported functions.**  If every
two-cycle of the complex is the boundary of a three-chain — the form in which the project
proves `H₂ = 0` for cube complexes with median one-skeleton — then the hypothesis of
`CollapseChain.exists_sum_bdry_of_cycles_bound` holds for the boundary matrix. -/
theorem exists_sum_of_exists_preimage {T F : Type*} [DecidableEq T]
    (d₃ : (T →₀ ℤ) →ₗ[ℤ] (F →₀ ℤ)) (IsCycle : (F →₀ ℤ) → Prop)
    (hH2 : ∀ z, IsCycle z → ∃ c : T →₀ ℤ, d₃ c = z) (z : F →₀ ℤ) (hz : IsCycle z) :
    ∃ (s : Finset T) (c : T → ℤ), ∀ g, z g = ∑ t ∈ s, c t * ofLinearMap d₃ t g := by
  obtain ⟨c, hc⟩ := hH2 z hz
  refine ⟨c.support, c, fun g => ?_⟩
  rw [← hc]
  exact apply_eq_sum_ofLinearMap d₃ c g

end CollapseChain
end FiniteChains
