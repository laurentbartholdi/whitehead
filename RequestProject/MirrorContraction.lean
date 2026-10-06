import RequestProject.NervePrism
import RequestProject.ChamberDescent

/-!
# The union of the descending mirrors is contractible

The chamber proof needs the following fact about the chamber `F = |𝒫|`, the order complex of
the poset `𝒫` of simplices of `L`: for a nonempty simplex `D` of `L`, the union of mirrors

  `⋃_{s ∈ D} F_s`,  `F_s = |{σ ∈ L : s ∈ σ}|`,

is nonempty and contractible.  Two statements are proved here.

* `FiniteChains.Mirror.exists_mem_forall_mem_iff` — the union of mirrors **is** the order complex
  of the poset `𝒫_D = {σ ∈ L : σ ∩ D ≠ ∅}`: a nonempty chain of simplices lies in a single
  mirror `F_s` with `s ∈ D` if and only if each of its members meets `D`.
* `FiniteChains.Mirror.exists_bdry_eq_of_cycle` — the augmented simplicial chain complex of the
  order complex of `𝒫_D` is contractible: every cycle is a boundary, by the explicit prism
  homotopy of `RequestProject/NervePrism.lean` applied to `ρ σ = σ ∩ D`, which satisfies
  `ρ ≤ id` and `ρ ≤ c_D`.

The final section instantiates this for the right-angled Coxeter group of
`RequestProject/ChamberDescent.lean`, with `D` the descent set `D(w)`: by
`FiniteChains.RACG.rdesc_rel` the descent set is a simplex of `L`, and by
`FiniteChains.RACG.exists_rdesc` it is nonempty for `w ≠ 1`, so the attaching subcomplex of the
chamber `F_w` is contractible.
-/

namespace FiniteChains
namespace Mirror

universe u

variable {V : Type u} [DecidableEq V]

/-- The simplices of `L` that meet `D`: the poset `𝒫_D` whose order complex is the union of the
mirrors `F_s`, `s ∈ D`. -/
def MeetPoset (L : Finset V → Prop) (D : Finset V) : Type u :=
  {σ : Finset V // L σ ∧ (σ ∩ D).Nonempty}

instance (L : Finset V → Prop) (D : Finset V) : PartialOrder (MeetPoset L D) :=
  Subtype.partialOrder _

@[simp] theorem MeetPoset.le_def {L : Finset V → Prop} {D : Finset V} (σ τ : MeetPoset L D) :
    σ ≤ τ ↔ σ.1 ⊆ τ.1 := Iff.rfl

/-! ### The union of mirrors is the order complex of `𝒫_D` -/

omit [DecidableEq V] in
/-- In an increasing chain of simplices, the first one is contained in all of them. -/
theorem head_subset_of_isChain : ∀ {a : Finset V} {t : List (Finset V)},
    List.IsChain (· ⊆ ·) (a :: t) → ∀ σ ∈ a :: t, a ⊆ σ := by
  intro a t
  induction t generalizing a with
  | nil =>
      intro _ σ hσ
      rcases List.mem_cons.1 hσ with rfl | h
      · exact Finset.Subset.refl _
      · exact absurd h (by simp)
  | cons b r ih =>
      intro h σ hσ
      have hab : a ⊆ b := (List.isChain_cons.1 h).1 b (by simp)
      have hbr : List.IsChain (· ⊆ ·) (b :: r) := (List.isChain_cons.1 h).2
      rcases List.mem_cons.1 hσ with rfl | hσ'
      · exact Finset.Subset.refl _
      · exact hab.trans (ih hbr σ hσ')

/-- **The union of the mirrors `F_s`, `s ∈ D`, is the order complex of `𝒫_D`.**  A nonempty
chain of simplices is contained in a single mirror `F_s` with `s ∈ D` exactly when each of its
members meets `D`. -/
theorem exists_mem_forall_mem_iff {D : Finset V} {a : Finset V} {t : List (Finset V)}
    (h : List.IsChain (· ⊆ ·) (a :: t)) :
    (∃ s ∈ D, ∀ σ ∈ a :: t, s ∈ σ) ↔ ∀ σ ∈ a :: t, (σ ∩ D).Nonempty := by
  constructor
  · rintro ⟨s, hsD, hs⟩ σ hσ
    exact ⟨s, Finset.mem_inter.2 ⟨hs σ hσ, hsD⟩⟩
  · intro hmeet
    obtain ⟨s, hs⟩ := hmeet a (by simp)
    rw [Finset.mem_inter] at hs
    exact ⟨s, hs.2, fun σ hσ => head_subset_of_isChain h σ hσ hs.1⟩

/-! ### Contractibility -/

variable {L : Finset V → Prop} {D : Finset V}

/-- The order map `ρ σ = σ ∩ D`. -/
def rho (hL : ∀ σ τ : Finset V, σ ⊆ τ → L τ → L σ) (σ : MeetPoset L D) : MeetPoset L D :=
  ⟨σ.1 ∩ D, hL _ _ Finset.inter_subset_left σ.2.1, by
    refine σ.2.2.imp fun s hs => ?_
    rw [Finset.mem_inter] at hs ⊢
    exact ⟨Finset.mem_inter.2 ⟨hs.1, hs.2⟩, hs.2⟩⟩

/-- The vertex `D` of the poset `𝒫_D`. -/
def top (hLD : L D) (hD : D.Nonempty) : MeetPoset L D :=
  ⟨D, hLD, by simpa using hD⟩

theorem rho_monotone (hL : ∀ σ τ : Finset V, σ ⊆ τ → L τ → L σ) :
    Monotone (rho (L := L) (D := D) hL) := by
  intro σ τ hστ
  exact Finset.inter_subset_inter_right hστ

theorem rho_le (hL : ∀ σ τ : Finset V, σ ⊆ τ → L τ → L σ) (σ : MeetPoset L D) :
    rho hL σ ≤ σ := Finset.inter_subset_left

theorem rho_le_top (hL : ∀ σ τ : Finset V, σ ⊆ τ → L τ → L σ) (hLD : L D) (hD : D.Nonempty)
    (σ : MeetPoset L D) : rho hL σ ≤ top (L := L) hLD hD := Finset.inter_subset_right

/-- **Contractibility of the union of the descending mirrors.**  If `L` is closed under passing
to subsets and `D` is a nonempty simplex of `L`, then in the augmented simplicial chain complex
of the order complex of `𝒫_D` every cycle is a boundary; the contracting homotopy is the
explicit prism combination `P_{ρ,id} - P_{ρ,c_D}` corrected by the cone on the vertex `D`. -/
theorem exists_bdry_eq_of_cycle (hL : ∀ σ τ : Finset V, σ ⊆ τ → L τ → L σ) (hLD : L D)
    (hD : D.Nonempty) {x : Nerve.Ch (MeetPoset L D)} (hx : x ∈ Nerve.Inc (MeetPoset L D))
    (hcyc : Nerve.bdry x = 0) :
    ∃ y ∈ Nerve.Inc (MeetPoset L D), Nerve.bdry y = x :=
  Nerve.exists_bdry_eq_of_cycle (rho hL) (top (L := L) hLD hD) (rho_monotone hL) (rho_le hL)
    (rho_le_top hL hLD hD) hx hcyc

/-! ### The descent set of an element of a right-angled Coxeter group -/

section RACG

open RACG

variable [Fintype V] (A : CommRel V)

/-- The descent set `D(x) = {s : ℓ(xs) < ℓ(x)}` as a finite set of generators. -/
noncomputable def rdescFinset (x : CayGroup A) : Finset V := by
  classical
  exact Finset.univ.filter fun s => IsRDesc A x s

theorem mem_rdescFinset {x : CayGroup A} {s : V} :
    s ∈ rdescFinset A x ↔ IsRDesc A x s := by
  classical
  simp [rdescFinset]

/-- The simplices of `L`: the cliques of the commutation graph. -/
def IsSimplex (σ : Finset V) : Prop := ∀ s ∈ σ, ∀ r ∈ σ, s ≠ r → A.rel s r

omit [DecidableEq V] [Fintype V] in
theorem isSimplex_subset {σ τ : Finset V} (hστ : σ ⊆ τ) (hτ : IsSimplex A τ) :
    IsSimplex A σ := fun s hs r hr hsr => hτ s (hστ hs) r (hστ hr) hsr

/-- **The descent set is a simplex of `L`**, in the form needed by the chamber argument. -/
theorem isSimplex_rdescFinset (x : CayGroup A) : IsSimplex A (rdescFinset A x) := by
  intro s hs r hr hsr
  exact rdesc_rel A hsr ((mem_rdescFinset A).1 hs) ((mem_rdescFinset A).1 hr)

/-- **The descent set is nonempty** for `x ≠ 1`. -/
theorem rdescFinset_nonempty {x : CayGroup A} (hx : x ≠ 1) : (rdescFinset A x).Nonempty := by
  obtain ⟨s, hs⟩ := exists_rdesc A hx
  exact ⟨s, (mem_rdescFinset A).2 hs⟩

/-- **The attaching subcomplex of a chamber is contractible.**  For `x ≠ 1` the union of the
descending mirrors of the chamber `F_x` — the order complex of the poset of simplices of `L`
meeting the descent set `D(x)` — has contractible augmented chain complex. -/
theorem exists_bdry_eq_of_cycle_rdesc {x : CayGroup A} (hx : x ≠ 1)
    {c : Nerve.Ch (MeetPoset (IsSimplex A) (rdescFinset A x))}
    (hc : c ∈ Nerve.Inc (MeetPoset (IsSimplex A) (rdescFinset A x)))
    (hcyc : Nerve.bdry c = 0) :
    ∃ y ∈ Nerve.Inc (MeetPoset (IsSimplex A) (rdescFinset A x)), Nerve.bdry y = c :=
  exists_bdry_eq_of_cycle (fun _ _ hστ hτ => isSimplex_subset A hστ hτ)
    (isSimplex_rdescFinset A x) (rdescFinset_nonempty A hx) hc hcyc

end RACG

end Mirror
end FiniteChains
