import RequestProject.MirrorContraction
import RequestProject.CombPi1

/-!
# Simple connectivity of the attaching subcomplex, by paths and triangular relations

`RequestProject/MirrorContraction.lean` contracts the *augmented chain complex* of the order
complex of the poset `𝒫_D = {σ ∈ L : σ ∩ D ≠ ∅}`.  Chain contractibility does not by itself
give simple connectivity, and the chamber argument needs the fundamental group.  This file
supplies the missing statement directly, in the language of edge paths and triangular
relations, exactly as in the remark "The corresponding contraction of edge paths" of
`block-substitution-chamber-proof.tex`.

* `FiniteChains.Comb.orderCx P` — the two-skeleton of the order complex of a preorder `P`:
  vertices are the elements, oriented edges are the comparable pairs `a ≤ b`, two-cells are
  the chains `a ≤ b ≤ c`, attached along `[a,b][b,c][a,c]⁻¹`.
* `FiniteChains.Comb.htpy_orderCx_tri` — the triangular relation `[a,b][b,c] ≃ [a,c]`.
* `FiniteChains.Comb.ordPth` — the path `p_σ = [σ,ρσ]⁻¹[ρσ,d]` of the text.
* `FiniteChains.Comb.htpy_ordPos_ordPth` — the key identity `[σ,τ] p_τ ≃ p_σ` for `σ ≤ τ`,
  proved from the three triangular relations for
  `ρσ ≤ σ ≤ τ`, `ρσ ≤ ρτ ≤ τ` and `ρσ ≤ ρτ ≤ d`.
* `FiniteChains.Comb.htpy_path_ordPth` — every edge path `p` from `σ` to `τ` satisfies
  `p · p_τ ≃ p_σ`, hence every path `σ → τ` is homotopic to `p_σ p_τ⁻¹`, and
* `FiniteChains.Comb.simplyConnected_orderCx` — the order complex of a preorder carrying an
  order map `ρ ≤ id` with `ρ ≤ c_d` is simply connected.

The last section applies this to `𝒫_D` with `ρ σ = σ ∩ D` and `d = D`, and to the descent set
`D(w)` of a right-angled Coxeter group, giving the simple connectivity half of the lemma on the
attaching subcomplex.

Note on flagness: the poset `𝒫_D` and the vertex `D` only make sense because `D` *is* a simplex
of `L`.  In the right-angled Coxeter model of this project `L` is the clique complex
`FiniteChains.RACG.IsSimplex` of the commutation graph, so the normal-form computation
`FiniteChains.RACG.rdesc_rel` (the descent set is a clique) is exactly what makes `D(w)` a
simplex; for a general `L` this is the flagness hypothesis and it may not be dropped.
-/

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains
namespace Comb

universe u

/-! ### The order complex of a preorder -/

section OrderComplex

variable (P : Type u) [Preorder P]

/-- Oriented edges of the order complex: comparable ordered pairs. -/
def OrdEdge : Type u := {p : P × P // p.1 ≤ p.2}

/-- Two-cells of the order complex: chains `a ≤ b ≤ c`. -/
def OrdTri : Type u := {t : P × P × P // t.1 ≤ t.2.1 ∧ t.2.1 ≤ t.2.2}

/-- The two-skeleton of the order complex of a preorder: vertices are elements, edges are
comparable pairs, and every chain `a ≤ b ≤ c` carries a triangle attached along
`[a,b][b,c][a,c]⁻¹`. -/
def orderCx : Complex2.{u} where
  V := P
  E := OrdEdge P
  F := OrdTri P
  src e := e.1.1
  tgt e := e.1.2
  base t := t.1.1
  att t :=
    [((⟨(t.1.1, t.1.2.1), t.2.1⟩ : OrdEdge P), true),
     ((⟨(t.1.2.1, t.1.2.2), t.2.2⟩ : OrdEdge P), true),
     ((⟨(t.1.1, t.1.2.2), le_trans t.2.1 t.2.2⟩ : OrdEdge P), false)]
  att_isLoop := fun _ => ⟨rfl, rfl, rfl, rfl⟩

variable {P}

/-- The edge `a → b` attached to `a ≤ b`. -/
def ordPos {a b : P} (h : a ≤ b) : (orderCx P).E × Bool := ((⟨(a, b), h⟩ : OrdEdge P), true)

/-- The edge `a ≤ b` traversed backwards, from `b` to `a`. -/
def ordNeg {a b : P} (h : a ≤ b) : (orderCx P).E × Bool := ((⟨(a, b), h⟩ : OrdEdge P), false)

@[simp] theorem revGerm_ordPos {a b : P} (h : a ≤ b) : revGerm (ordPos h) = ordNeg h := rfl

@[simp] theorem revGerm_ordNeg {a b : P} (h : a ≤ b) : revGerm (ordNeg h) = ordPos h := rfl

theorem isPath_ordPos {a b : P} (h : a ≤ b) :
    IsPath (orderCx P).src (orderCx P).tgt [ordPos h] a b := ⟨rfl, rfl⟩

theorem isPath_ordNeg {a b : P} (h : a ≤ b) :
    IsPath (orderCx P).src (orderCx P).tgt [ordNeg h] b a := ⟨rfl, rfl⟩

theorem isPath_nil' (a : P) :
    IsPath (orderCx P).src (orderCx P).tgt ([] : List ((orderCx P).E × Bool)) a a := rfl

/-- Backtrack cancellation for an edge traversed forwards and then backwards. -/
theorem htpy_ordPos_ordNeg {a b : P} (h : a ≤ b) :
    Htpy (orderCx P) a a [ordPos h, ordNeg h] [] := by
  have := htpy_append_revPath (X := orderCx P) (isPath_single (X := orderCx P) (ordPos h))
  simpa [revPath, revGerm, Bool.not, Bool.not_true, Bool.not_false, ordPos, ordNeg, germSrc, germTgt, orderCx] using this

/-- Backtrack cancellation for an edge traversed backwards and then forwards. -/
theorem htpy_ordNeg_ordPos {a b : P} (h : a ≤ b) :
    Htpy (orderCx P) b b [ordNeg h, ordPos h] [] := by
  have := htpy_append_revPath (X := orderCx P) (isPath_single (X := orderCx P) (ordNeg h))
  simpa [revPath, revGerm, Bool.not, Bool.not_true, Bool.not_false, ordPos, ordNeg, germSrc, germTgt, orderCx] using this

/-- **The triangular relation**: `[a,b][b,c] ≃ [a,c]` for a chain `a ≤ b ≤ c`. -/
theorem htpy_orderCx_tri {a b c : P} (hab : a ≤ b) (hbc : b ≤ c) :
    Htpy (orderCx P) a c [ordPos hab, ordPos hbc] [ordPos (hab.trans hbc)] := by
  have hac : a ≤ c := hab.trans hbc
  have hp : IsPath (orderCx P).src (orderCx P).tgt [ordPos hab, ordPos hbc] a c :=
    ⟨rfl, rfl, rfl⟩
  have hq : IsPath (orderCx P).src (orderCx P).tgt ([] : List ((orderCx P).E × Bool)) c c := rfl
  have h1 : Htpy (orderCx P) a c ([ordPos hab, ordPos hbc] ++ [])
      ([ordPos hab, ordPos hbc] ++ [ordNeg hac, ordPos hac]) :=
    Htpy.append_congr hp hq (Htpy.refl _) (htpy_ordNeg_ordPos hac).symm
  have hfull : IsPath (orderCx P).src (orderCx P).tgt
      [ordPos hab, ordPos hbc, ordNeg hac, ordPos hac] a c := ⟨rfl, rfl, rfl, rfl, rfl⟩
  have h2 : Htpy (orderCx P) a c [ordPos hab, ordPos hbc, ordNeg hac, ordPos hac]
      [ordPos hac] := by
    refine Htpy.of_step ⟨hfull, isPath_ordPos hac, Or.inr ?_⟩
    exact ⟨[], [ordPos hac], (⟨(a, b, c), hab, hbc⟩ : OrdTri P), rfl, rfl⟩
  simpa using h1.trans h2

end OrderComplex

/-! ### The explicit contraction of edge paths -/

section Contraction

variable {P : Type u} [Preorder P]

/-- The path `p_σ = [σ,ρσ]⁻¹[ρσ,d]` of the text: from `σ` down to `ρσ` and up to `d`. -/
def ordPth (d : P) (rho : P → P) (hle : ∀ x, rho x ≤ x) (htop : ∀ x, rho x ≤ d) (x : P) :
    List ((orderCx P).E × Bool) := [ordNeg (hle x), ordPos (htop x)]

theorem isPath_ordPth (d : P) (rho : P → P) (hle : ∀ x, rho x ≤ x) (htop : ∀ x, rho x ≤ d)
    (x : P) :
    IsPath (orderCx P).src (orderCx P).tgt (ordPth d rho hle htop x) x d := ⟨rfl, rfl, rfl⟩

/-- **The key identity** `[σ,τ] p_τ ≃ p_σ` for `σ ≤ τ`, obtained from the three triangular
relations for the chains `ρσ ≤ σ ≤ τ`, `ρσ ≤ ρτ ≤ τ` and `ρσ ≤ ρτ ≤ d`. -/
theorem htpy_ordPos_ordPth (d : P) (rho : P → P) (hle : ∀ x, rho x ≤ x)
    (htop : ∀ x, rho x ≤ d) (hmono : ∀ {x y : P}, x ≤ y → rho x ≤ rho y) {a b : P}
    (hab : a ≤ b) :
    Htpy (orderCx P) a d (ordPos hab :: ordPth d rho hle htop b) (ordPth d rho hle htop a) := by
  have hrs : rho a ≤ rho b := hmono hab
  have hrb : rho a ≤ b := hrs.trans (hle b)
  have pa2 : IsPath (orderCx P).src (orderCx P).tgt [ordNeg (hle a), ordPos hrs] a (rho b) :=
    ⟨rfl, rfl, rfl⟩
  have pb2 : IsPath (orderCx P).src (orderCx P).tgt
      [ordNeg (hle b), ordPos (htop b)] b d := ⟨rfl, rfl, rfl⟩
  have p3 : IsPath (orderCx P).src (orderCx P).tgt
      [ordPos hab, ordNeg (hle b), ordPos (htop b)] a d := ⟨rfl, rfl, rfl, rfl⟩
  -- Step 1: expand `[ρa,d]` as `[ρa,ρb][ρb,d]`.
  have s1 : Htpy (orderCx P) a d ([ordNeg (hle a)] ++ [ordPos (htop a)])
      ([ordNeg (hle a)] ++ [ordPos hrs, ordPos (htop b)]) :=
    Htpy.append_congr (isPath_ordNeg (hle a)) (isPath_ordPos (htop a)) (Htpy.refl _)
      (htpy_orderCx_tri hrs (htop b)).symm
  -- Step 2: insert the backtrack `[ρb,b][ρb,b]⁻¹`.
  have s2 : Htpy (orderCx P) a d
      ([ordNeg (hle a), ordPos hrs] ++ [] ++ [ordPos (htop b)])
      ([ordNeg (hle a), ordPos hrs] ++ [ordPos (hle b), ordNeg (hle b)] ++
        [ordPos (htop b)]) :=
    (htpy_ordPos_ordNeg (hle b)).symm.congr_append (c := a) (d := d) pa2
      (isPath_ordPos (htop b))
  -- Step 3: contract `[ρa,ρb][ρb,b]` to `[ρa,b]`.
  have s3 : Htpy (orderCx P) a d
      ([ordNeg (hle a)] ++ [ordPos hrs, ordPos (hle b)] ++ [ordNeg (hle b), ordPos (htop b)])
      ([ordNeg (hle a)] ++ [ordPos hrb] ++ [ordNeg (hle b), ordPos (htop b)]) :=
    (htpy_orderCx_tri hrs (hle b)).congr_append (c := a) (d := d) (isPath_ordNeg (hle a)) pb2
  -- Step 4: expand `[ρa,b]` as `[ρa,a][a,b]`.
  have s4 : Htpy (orderCx P) a d
      ([ordNeg (hle a)] ++ [ordPos hrb] ++ [ordNeg (hle b), ordPos (htop b)])
      ([ordNeg (hle a)] ++ [ordPos (hle a), ordPos hab] ++
        [ordNeg (hle b), ordPos (htop b)]) :=
    (htpy_orderCx_tri (hle a) hab).symm.congr_append (c := a) (d := d)
      (isPath_ordNeg (hle a)) pb2
  -- Step 5: cancel the backtrack `[ρa,a]⁻¹[ρa,a]`.
  have s5 : Htpy (orderCx P) a d
      ([] ++ [ordNeg (hle a), ordPos (hle a)] ++ [ordPos hab, ordNeg (hle b), ordPos (htop b)])
      ([] ++ [] ++ [ordPos hab, ordNeg (hle b), ordPos (htop b)]) :=
    (htpy_ordNeg_ordPos (hle a)).congr_append (c := a) (d := d) (isPath_nil' a) p3
  have chain : Htpy (orderCx P) a d (ordPth d rho hle htop a)
      (ordPos hab :: ordPth d rho hle htop b) := by
    simp only [ordPth]
    simp only [List.nil_append, List.cons_append] at s1 s2 s3 s4 s5 ⊢
    exact ((((s1.trans s2).trans s3).trans s4).trans s5)
  exact chain.symm

/-- The reversed form of the key identity: `[σ,τ]⁻¹ p_σ ≃ p_τ`. -/
theorem htpy_ordNeg_ordPth (d : P) (rho : P → P) (hle : ∀ x, rho x ≤ x)
    (htop : ∀ x, rho x ≤ d) (hmono : ∀ {x y : P}, x ≤ y → rho x ≤ rho y) {a b : P}
    (hab : a ≤ b) :
    Htpy (orderCx P) b d (ordNeg hab :: ordPth d rho hle htop a) (ordPth d rho hle htop b) := by
  have h1 : Htpy (orderCx P) b d ([ordNeg hab] ++ ordPth d rho hle htop a)
      ([ordNeg hab] ++ (ordPos hab :: ordPth d rho hle htop b)) :=
    Htpy.append_congr (isPath_ordNeg hab) (isPath_ordPth d rho hle htop a) (Htpy.refl _)
      (htpy_ordPos_ordPth d rho hle htop hmono hab).symm
  have h2 : Htpy (orderCx P) b d
      ([] ++ [ordNeg hab, ordPos hab] ++ ordPth d rho hle htop b)
      ([] ++ [] ++ ordPth d rho hle htop b) :=
    (htpy_ordNeg_ordPos hab).congr_append (c := b) (d := d) (isPath_nil' b)
      (isPath_ordPth d rho hle htop b)
  simp only [List.nil_append, List.cons_append] at h1 h2 ⊢
  exact h1.trans h2

/-- **Every edge path is the standard one**: for a path `p` from `σ` to `τ` one has
`p · p_τ ≃ p_σ`; in particular every path `σ → τ` is homotopic to `p_σ p_τ⁻¹`. -/
theorem htpy_path_ordPth (d : P) (rho : P → P) (hle : ∀ x, rho x ≤ x)
    (htop : ∀ x, rho x ≤ d) (hmono : ∀ {x y : P}, x ≤ y → rho x ≤ rho y) :
    ∀ (p : List ((orderCx P).E × Bool)) {x y : P},
      IsPath (orderCx P).src (orderCx P).tgt p x y →
      Htpy (orderCx P) x d (p ++ ordPth d rho hle htop y) (ordPth d rho hle htop x) := by
  intro p
  induction p with
  | nil =>
      intro x y hp
      cases hp
      exact Htpy.refl _
  | cons eb p ih =>
      rintro x y ⟨hx, hrest⟩
      obtain ⟨⟨⟨a, b⟩, hab⟩, tag⟩ := eb
      cases tag with
      | false =>
          have hxb : x = b := hx
          have hrest' : IsPath (orderCx P).src (orderCx P).tgt p a y := hrest
          have hih := ih hrest'
          have h1 : Htpy (orderCx P) b d
              ([ordNeg hab] ++ (p ++ ordPth d rho hle htop y))
              ([ordNeg hab] ++ ordPth d rho hle htop a) :=
            Htpy.append_congr (isPath_ordNeg hab)
              (isPath_append_iff.mpr ⟨y, hrest', isPath_ordPth d rho hle htop y⟩)
              (Htpy.refl _) hih
          have h2 := htpy_ordNeg_ordPth d rho hle htop hmono hab
          have hgoal : Htpy (orderCx P) b d ((ordNeg hab :: p) ++ ordPth d rho hle htop y)
              (ordPth d rho hle htop b) := by
            simp only [List.cons_append] at h1 ⊢
            exact h1.trans h2
          rw [hxb]
          exact hgoal
      | true =>
          have hxa : x = a := hx
          have hrest' : IsPath (orderCx P).src (orderCx P).tgt p b y := hrest
          have hih := ih hrest'
          have h1 : Htpy (orderCx P) a d
              ([ordPos hab] ++ (p ++ ordPth d rho hle htop y))
              ([ordPos hab] ++ ordPth d rho hle htop b) :=
            Htpy.append_congr (isPath_ordPos hab)
              (isPath_append_iff.mpr ⟨y, hrest', isPath_ordPth d rho hle htop y⟩)
              (Htpy.refl _) hih
          have h2 := htpy_ordPos_ordPth d rho hle htop hmono hab
          have hgoal : Htpy (orderCx P) a d ((ordPos hab :: p) ++ ordPth d rho hle htop y)
              (ordPth d rho hle htop a) := by
            simp only [List.cons_append] at h1 ⊢
            exact h1.trans h2
          rw [hxa]
          exact hgoal

/-- **Simple connectivity of the order complex** of a preorder carrying an order map
`ρ ≤ id` with `ρ ≤ c_d`.  This is proved with edges and triangular relations alone; it is not
inferred from acyclicity of the chain complex. -/
theorem simplyConnected_orderCx (d : P) (rho : P → P) (hle : ∀ x, rho x ≤ x)
    (htop : ∀ x, rho x ≤ d) (hmono : ∀ {x y : P}, x ≤ y → rho x ≤ rho y) :
    SimplyConnected (orderCx P) := by
  intro a p hp
  have hq : IsPath (orderCx P).src (orderCx P).tgt (ordPth d rho hle htop (a : P)) (a : P) d :=
    isPath_ordPth d rho hle htop a
  set q := ordPth d rho hle htop (a : P) with hqdef
  have h := htpy_path_ordPth d rho hle htop hmono p hp
  have h3 : Htpy (orderCx P) a a (q ++ revPath q) [] := htpy_append_revPath hq
  have h1 : Htpy (orderCx P) a a (p ++ (q ++ revPath q)) (p ++ []) :=
    Htpy.append_congr hp (isPath_append_iff.mpr ⟨d, hq, isPath_revPath hq⟩) (Htpy.refl _) h3
  have h2 : Htpy (orderCx P) a a ((p ++ q) ++ revPath q) (q ++ revPath q) :=
    Htpy.append_congr (isPath_append_iff.mpr ⟨a, hp, hq⟩) (isPath_revPath hq) h (Htpy.refl _)
  have h1' : Htpy (orderCx P) a a p ((p ++ q) ++ revPath q) := by
    simpa [List.append_assoc] using h1.symm
  exact (h1'.trans h2).trans h3

/-- The order complex of a preorder with such a contraction is connected. -/
theorem isConnected_orderCx (d : P) (rho : P → P) (hle : ∀ x, rho x ≤ x)
    (htop : ∀ x, rho x ≤ d) : IsConnected (orderCx P) := by
  intro a b
  exact ⟨ordPth d rho hle htop (a : P) ++ revPath (ordPth d rho hle htop (b : P)),
    isPath_append_iff.mpr ⟨d, isPath_ordPth d rho hle htop (a : P),
      isPath_revPath (isPath_ordPth d rho hle htop (b : P))⟩⟩

end Contraction

end Comb

/-! ### The attaching subcomplex of a chamber is simply connected -/

namespace Mirror

universe u

variable {V : Type u} [DecidableEq V]

/-- The vertex `D` of the order complex of `𝒫_D`. -/
def meetTop {L : Finset V → Prop} {D : Finset V} (hLD : L D) (hD : D.Nonempty) :
    MeetPoset L D := ⟨D, hLD, by simpa using hD⟩

/-- The order map `ρ(σ) = σ ∩ D` of the text. -/
def meetRho {L : Finset V → Prop} {D : Finset V}
    (hL : ∀ σ τ : Finset V, σ ⊆ τ → L τ → L σ) (σ : MeetPoset L D) : MeetPoset L D :=
  ⟨σ.1 ∩ D, hL _ _ Finset.inter_subset_left σ.2.1, by
    rw [Finset.inter_assoc, Finset.inter_self]; exact σ.2.2⟩

theorem meetRho_le {L : Finset V → Prop} {D : Finset V}
    (hL : ∀ σ τ : Finset V, σ ⊆ τ → L τ → L σ) (σ : MeetPoset L D) : meetRho hL σ ≤ σ :=
  Finset.inter_subset_left

theorem meetRho_le_top {L : Finset V → Prop} {D : Finset V}
    (hL : ∀ σ τ : Finset V, σ ⊆ τ → L τ → L σ) (hLD : L D) (hD : D.Nonempty)
    (σ : MeetPoset L D) : meetRho hL σ ≤ meetTop hLD hD :=
  Finset.inter_subset_right

theorem meetRho_mono {L : Finset V → Prop} {D : Finset V}
    (hL : ∀ σ τ : Finset V, σ ⊆ τ → L τ → L σ) {σ τ : MeetPoset L D} (h : σ ≤ τ) :
    meetRho hL σ ≤ meetRho hL τ := fun _ ha =>
  Finset.mem_inter.2 ⟨h (Finset.mem_inter.1 ha).1, (Finset.mem_inter.1 ha).2⟩

/-- **The attaching subcomplex of a chamber is simply connected.**  For a nonempty simplex `D`
of a downward closed family `L`, the order complex of `𝒫_D = {σ ∈ L : σ ∩ D ≠ ∅}` — the union
of the mirrors `F_s`, `s ∈ D`, by `FiniteChains.Mirror.exists_mem_forall_mem_iff` — has trivial
fundamental group: every edge loop contracts using edges and triangular relations alone. -/
theorem simplyConnected_meetOrderCx {L : Finset V → Prop} {D : Finset V}
    (hL : ∀ σ τ : Finset V, σ ⊆ τ → L τ → L σ) (hLD : L D) (hD : D.Nonempty) :
    Comb.SimplyConnected (Comb.orderCx (MeetPoset L D)) :=
  Comb.simplyConnected_orderCx (meetTop hLD hD) (meetRho hL) (meetRho_le hL)
    (meetRho_le_top hL hLD hD) (fun h => meetRho_mono hL h)

/-- The order complex of `𝒫_D` is connected: every vertex is joined to `D`. -/
theorem isConnected_meetOrderCx {L : Finset V → Prop} {D : Finset V}
    (hL : ∀ σ τ : Finset V, σ ⊆ τ → L τ → L σ) (hLD : L D) (hD : D.Nonempty) :
    Comb.IsConnected (Comb.orderCx (MeetPoset L D)) :=
  Comb.isConnected_orderCx (meetTop hLD hD) (meetRho hL) (meetRho_le hL)
    (meetRho_le_top hL hLD hD)

section RACG

open RACG

variable [Fintype V] (A : CommRel V)

/-- **The attaching subcomplex of the chamber `F_w` is simply connected.**  Here `L` is the
clique complex `FiniteChains.RACG.IsSimplex` of the commutation graph, and the descent set
`D(w)` is a simplex of it by `FiniteChains.RACG.rdesc_rel` — this is where flagness of `L`
enters. -/
theorem simplyConnected_meetOrderCx_rdesc {x : CayGroup A} (hx : x ≠ 1) :
    Comb.SimplyConnected
      (Comb.orderCx (MeetPoset (IsSimplex A) (rdescFinset A x))) :=
  simplyConnected_meetOrderCx (fun _ _ hστ hτ => isSimplex_subset A hστ hτ)
    (isSimplex_rdescFinset A x) (rdescFinset_nonempty A hx)

/-- The attaching subcomplex of the chamber `F_w` is connected. -/
theorem isConnected_meetOrderCx_rdesc {x : CayGroup A} (hx : x ≠ 1) :
    Comb.IsConnected (Comb.orderCx (MeetPoset (IsSimplex A) (rdescFinset A x))) :=
  isConnected_meetOrderCx (fun _ _ hστ hτ => isSimplex_subset A hστ hτ)
    (isSimplex_rdescFinset A x) (rdescFinset_nonempty A hx)

end RACG

end Mirror
end FiniteChains
