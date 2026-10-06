import RequestProject.CoreSignedCollapse
import RequestProject.GenusCappedCockcroft
import RequestProject.GenusMarkedSpineFamily
import RequestProject.CockcroftRelatorReindex
import RequestProject.LemmaTerminal

/-! B3 for the actual terminal presentation.  The stable generators are capped,
the original core is retained, and every extra relation is replaced by its actual
named-spine block.  The quotient by the capped core is the wedge of the genuine
capped spines, with the marking cells carrying the opposite orientation.
No collapse map, Hurewicz injection or block Cockcroftness is assumed.
Written proof terms; not compiled in the current proof-first workflow. -/

noncomputable section
open scoped Classical

namespace FiniteChains.Davis.Genus

open BlockFamily

variable {A K M S : Type} [Fintype A] [Fintype K] [Fintype M] [Fintype S]
  [DecidableEq A] [DecidableEq K] [DecidableEq S]
  (core : M → FreeGroup A) (q : S → ℕ) [∀ s, NeZero (q s)]
  (u : ∀ s, Fin (q s) × Bool → FreeGroup (A ⊕ K))

/-- The original core together with one disk on each stable generator. -/
def terminalSpineCore : M ⊕ K → FreeGroup (A ⊕ K) :=
  corePres core (fun k => FreeGroup.of (Sum.inr k))

omit [Fintype A] in
theorem terminalSpineCore_expInjective (hcore : ExpInjective core) :
    ExpInjective (terminalSpineCore (K := K) core) := by
  intro c hc
  have hleft (a : A) :
      ∑ m : M, c (Sum.inl m) * expEntry core a m = 0 := by
    have h := hc (Sum.inl a)
    rw [Fintype.sum_sum_type] at h
    have hcap (k : K) :
        expEntry (terminalSpineCore (K := K) core) (Sum.inl a) (Sum.inr k) = 0 := by
      simp [expEntry, terminalSpineCore, corePres, expSum_of]
    have hentry (m : M) :
        expEntry (terminalSpineCore (K := K) core) (Sum.inl a) (Sum.inl m) =
          expEntry core a m := expEntry_corePres_inl core
            (fun k : K => FreeGroup.of (Sum.inr k)) a m
    simpa only [hentry, hcap, mul_zero,
      Finset.sum_const_zero, add_zero] using h
  have hright (k : K) : c (Sum.inr k) = 0 := by
    have h := hc (Sum.inr k)
    rw [Fintype.sum_sum_type] at h
    have hold (m : M) :
        expEntry (terminalSpineCore (K := K) core) (Sum.inr k) (Sum.inl m) = 0 := by
      rw [← augPres_foxMatrixPres]
      change augPres (corePres core (fun k : K => FreeGroup.of (Sum.inr k)))
        (foxMatrixPres (corePres core (fun k : K => FreeGroup.of (Sum.inr k)))
          (Sum.inr k) (Sum.inl m)) = 0
      rw [CoreSignedCollapse.matrix_core, map_zero]
    have hcap (l : K) :
        expEntry (terminalSpineCore (K := K) core) (Sum.inr k) (Sum.inr l) =
          if k = l then 1 else 0 := by
      simp [expEntry, terminalSpineCore, corePres, expSum_of]
    simpa only [hold, mul_zero, Finset.sum_const_zero, zero_add, hcap,
      mul_ite, mul_one, mul_zero, Fintype.sum_ite_eq] using h
  rintro (m | k)
  · exact hcore (fun m => c (Sum.inl m)) hleft m
  · exact hright k

/-- Each new internal generator belongs to exactly one spine. -/
def terminalSpineGen (s : S) (z : SpinePresentationGen (q s)) :
    (A ⊕ K) ⊕ (Σ s, SpinePresentationGen (q s)) := Sum.inr ⟨s, z⟩

/-- Actual substituted relators, written out to retain their orientation. -/
def terminalSpineExtra : (Σ s, NamedSpineRel (q s)) →
    FreeGroup ((A ⊕ K) ⊕ (Σ s, SpinePresentationGen (q s)))
  | ⟨s, .inl f⟩ => FreeGroup.map (terminalSpineGen (A := A) (K := K) q s)
      (spinePresentation (q s) f)
  | ⟨s, .inr x⟩ => FreeGroup.map Sum.inl (u s x) *
      (FreeGroup.map (terminalSpineGen (A := A) (K := K) q s)
        (spinePresentationMarkedWord (q s) x))⁻¹

/-- Q after capping the stable generators, with caps placed next to the core. -/
def terminalSpinePres : (M ⊕ K) ⊕ (Σ s, NamedSpineRel (q s)) →
    FreeGroup ((A ⊕ K) ⊕ (Σ s, SpinePresentationGen (q s))) :=
  corePres (terminalSpineCore (K := K) core) (terminalSpineExtra q u)

private def terminalNamedWordMap (s : S) : FreeGroup (NamedSpineGen (q s)) →*
    FreeGroup ((A ⊕ K) ⊕ (Σ s, SpinePresentationGen (q s))) :=
  (FreeGroup.map (genEmb (Zt := fun s => SpinePresentationGen (q s)) s)).comp
    ((blockSubst (Zt := fun _ : PUnit.{1} => SpinePresentationGen (q s))
      (fun _ => u s) PUnit.unit).comp (FreeGroup.map Sum.swap))

omit [Fintype A] [Fintype K] [Fintype S] [DecidableEq A] [DecidableEq K] [DecidableEq S] in
private theorem terminalNamedWordMap_old (s : S)
    (w : FreeGroup (SpinePresentationGen (q s))) :
    terminalNamedWordMap q u s (FreeGroup.map Sum.inl w) =
      FreeGroup.map (terminalSpineGen (A := A) (K := K) q s) w := by
  have h : (terminalNamedWordMap q u s).comp (FreeGroup.map Sum.inl) =
      FreeGroup.map (terminalSpineGen (A := A) (K := K) q s) := by
    apply FreeGroup.ext_hom
    intro z
    simp [terminalNamedWordMap, terminalSpineGen]
  exact DFunLike.congr_fun h w

omit [Fintype A] [Fintype K] [Fintype S] [DecidableEq A] [DecidableEq K] [DecidableEq S] in
private theorem terminalNamedWordMap_mark (s : S) (x : Fin (q s) × Bool) :
    terminalNamedWordMap q u s (FreeGroup.of (Sum.inr x)) =
      FreeGroup.map Sum.inl (u s x) := by
  change FreeGroup.map (genEmb (Zt := fun s => SpinePresentationGen (q s)) s)
    (blockSubst (Zt := fun _ : PUnit.{1} => SpinePresentationGen (q s))
      (fun _ => u s) PUnit.unit (FreeGroup.map Sum.swap (FreeGroup.of (Sum.inr x)))) = _
  simp only [FreeGroup.map.of, Sum.swap_inr, blockSubst_of_inl]
  have h : (FreeGroup.map (genEmb (Zt := fun s => SpinePresentationGen (q s)) s)).comp
      (FreeGroup.map (Sum.inl : A ⊕ K → (A ⊕ K) ⊕ SpinePresentationGen (q s))) =
      FreeGroup.map (Sum.inl : A ⊕ K → (A ⊕ K) ⊕ (Σ s, SpinePresentationGen (q s))) := by
    apply FreeGroup.ext_hom
    intro a
    simp
  exact DFunLike.congr_fun h (u s x)

omit [Fintype A] [Fintype K] [Fintype M] [Fintype S]
  [DecidableEq A] [DecidableEq K] [DecidableEq S] in
/-- The explicit terminal words are exactly the words used in actual B1/B2,
not a different block presentation. -/
theorem terminalSpineExtra_eq_family (s : S) (m : NamedSpineRel (q s)) :
    terminalSpineExtra q u ⟨s, m⟩ =
      FreeGroup.map (genEmb (Zt := fun s => SpinePresentationGen (q s)) s)
        (familyFiniteSpineWordBlock q u s m) := by
  change terminalSpineExtra q u ⟨s, m⟩ =
    terminalNamedWordMap q u s (namedSpinePresentation (q s) m)
  cases m with
  | inl f =>
      exact (terminalNamedWordMap_old q u s (spinePresentation (q s) f)).symm
  | inr x =>
      change FreeGroup.map Sum.inl (u s x) *
        (FreeGroup.map (terminalSpineGen (A := A) (K := K) q s)
          (spinePresentationMarkedWord (q s) x))⁻¹ =
        terminalNamedWordMap q u s (FreeGroup.of (Sum.inr x) *
          (FreeGroup.map Sum.inl (spinePresentationMarkedWord (q s) x))⁻¹)
      rw [map_mul, map_inv, terminalNamedWordMap_mark, terminalNamedWordMap_old]

/-- The target is the actual wedge of genuine capped-spine presentations. -/
def terminalSpineWedge : (Σ s, NamedSpineRel (q s)) →
    FreeGroup (Σ s, SpinePresentationGen (q s)) :=
  sigmaWedgeRel (fun s => cappedSpinePresentation (q s))

def terminalSpineReverse : (Σ s, NamedSpineRel (q s)) → Bool
  | ⟨_, .inl _⟩ => false
  | ⟨_, .inr _⟩ => true

omit [Fintype A] [Fintype K] [Fintype S] [DecidableEq A] [DecidableEq K] [DecidableEq S] in
private theorem terminalSpineGen_drop (s : S)
    (w : FreeGroup (SpinePresentationGen (q s))) :
    CoreSignedCollapse.dropCore
      (FreeGroup.map (terminalSpineGen (A := A) (K := K) q s) w) =
      FreeGroup.map (Sigma.mk s) w := by
  have h : (CoreSignedCollapse.dropCore (A := A ⊕ K)).comp
      (FreeGroup.map (terminalSpineGen (A := A) (K := K) q s)) =
      FreeGroup.map (Sigma.mk (β := fun s => SpinePresentationGen (q s)) s) := by
    apply FreeGroup.ext_hom
    intro z
    simp [terminalSpineGen]
  exact DFunLike.congr_fun h w

omit [Fintype A] [Fintype K] [Fintype M] [Fintype S]
  [DecidableEq A] [DecidableEq K] [DecidableEq S] in
theorem terminalSpine_collapse_word (p : Σ s, NamedSpineRel (q s)) :
    CoreSignedCollapse.dropCore (terminalSpineExtra q u p) =
      if terminalSpineReverse q p then (terminalSpineWedge q p)⁻¹
        else terminalSpineWedge q p := by
  obtain ⟨s, f | x⟩ := p
  · exact terminalSpineGen_drop q s (spinePresentation (q s) f)
  · change CoreSignedCollapse.dropCore
      (FreeGroup.map Sum.inl (u s x) *
        (FreeGroup.map (terminalSpineGen (A := A) (K := K) q s)
          (spinePresentationMarkedWord (q s) x))⁻¹) =
      (FreeGroup.map (Sigma.mk s) (spinePresentationMarkedWord (q s) x))⁻¹
    rw [map_mul, map_inv, CoreSignedCollapse.dropCore_map_inl,
      terminalSpineGen_drop, one_mul]

/-- The actual collapse on the presented group and its universal-cover cells. -/
def terminalSpineCollapse : PresMor (terminalSpinePres core q u) (terminalSpineWedge q) :=
  CoreSignedCollapse.mor (terminalSpineCore (K := K) core) (terminalSpineExtra q u)
    (terminalSpineWedge q) (terminalSpineReverse q) (terminalSpine_collapse_word q u)

omit [Fintype S] in
/-- Each capped factor has the actual free-group retraction `killOther`. -/
theorem terminalSpineWedge_factor (s : S) :
    IsBlock (cappedSpinePresentation (q s)) (terminalSpineWedge q)
      (Sigma.mk (β := fun s => SpinePresentationGen (q s)) s)
      (Sigma.mk (β := fun s => NamedSpineRel (q s)) s) (killOther s) :=
  isBlock_sigmaWedge (fun s => cappedSpinePresentation (q s)) s

theorem terminalSpineWedge_isCockcroft : IsCockcroft (terminalSpineWedge q) :=
  isCockcroft_sigmaWedgeRel (fun s => cappedSpinePresentation (q s))
    (fun s => cappedSpinePresentation_isCockcroft (q s))

omit [Fintype A] in
/-- The constructed collapse reflects the Hurewicz image, using only the
original core's exponent-sum injection. -/
theorem terminalSpineCollapse_hurewicz_reflect (hcore : ExpInjective core)
    (v : (M ⊕ K) ⊕ (Σ s, NamedSpineRel (q s)) →
      MonoidAlgebra ℤ (PresGroup (terminalSpinePres core q u)))
    (hv : IsFoxCycle (terminalSpinePres core q u) v)
    (hz : ∀ p, augPres (terminalSpineWedge q)
      ((terminalSpineCollapse core q u).cells v p) = 0) :
    ∀ j, augPres (terminalSpinePres core q u) (v j) = 0 :=
  CoreSignedCollapse.hurewicz_reflect (terminalSpineCore (K := K) core)
    (terminalSpineExtra q u) (terminalSpineWedge q) (terminalSpineReverse q)
    (terminalSpine_collapse_word q u) (terminalSpineCore_expInjective core hcore)
    v hv hz

omit [Fintype A] in
/-- Concrete terminal B3.  There is no terminal Cockcroft, collapse-map or
Hurewicz-injectivity premise.  The source need not have trivial fundamental group. -/
theorem terminalSpine_isCockcroft (hcore : ExpInjective core) :
    IsCockcroft (terminalSpinePres core q u) :=
  CoreSignedCollapse.isCockcroft (terminalSpineCore (K := K) core)
    (terminalSpineExtra q u) (terminalSpineWedge q) (terminalSpineReverse q)
    (terminalSpine_collapse_word q u) (terminalSpineCore_expInjective core hcore)
    (terminalSpineWedge_isCockcroft q)

/-- The presentation just before rule 3: retain the core and replace the
specified products of commutators. -/
def terminalSpineSource : M ⊕ S → FreeGroup (A ⊕ K) :=
  Sum.elim (fun m => FreeGroup.map Sum.inl (core m))
    (fun s => commWord (u s) (finitePairs (q s)))

/-- The actual simultaneous rule-3 target, before the stable generators are capped. -/
def terminalSpineStructural : M ⊕ (Σ s, NamedSpineRel (q s)) →
    FreeGroup ((A ⊕ K) ⊕ (Σ s, SpinePresentationGen (q s))) :=
  substPresF (terminalSpineSource core q u) (familyFiniteSpineWordBlock q u)

/-- The stable loops capped at the terminal step. -/
def terminalSpineCaps (k : K) :
    FreeGroup ((A ⊕ K) ⊕ (Σ s, SpinePresentationGen (q s))) :=
  FreeGroup.of (Sum.inl (Sum.inr k))

/-- The terminal step in the literal `addRels` indexing. -/
def terminalSpineQ : (M ⊕ (Σ s, NamedSpineRel (q s))) ⊕ K →
    FreeGroup ((A ⊕ K) ⊕ (Σ s, SpinePresentationGen (q s))) :=
  addRels (terminalSpineStructural core q u) (terminalSpineCaps (A := A) (K := K) q)

/-- Move the stable cap labels next to the core labels, retaining every label. -/
def terminalCapReindex {J : Type} : (M ⊕ J) ⊕ K ≃ (M ⊕ K) ⊕ J where
  toFun
    | .inl (.inl m) => .inl (.inl m)
    | .inl (.inr j) => .inr j
    | .inr k => .inl (.inr k)
  invFun
    | .inl (.inl m) => .inl (.inl m)
    | .inl (.inr k) => .inr k
    | .inr j => .inl (.inr j)
  left_inv := by rintro ((m | j) | k) <;> rfl
  right_inv := by rintro ((m | k) | j) <;> rfl

omit [Fintype A] [Fintype K] [Fintype M] [Fintype S]
  [DecidableEq A] [DecidableEq K] [DecidableEq S] in
theorem terminalSpineQ_reindex
    (j : (M ⊕ (Σ s, NamedSpineRel (q s))) ⊕ K) :
    terminalSpinePres core q u (terminalCapReindex j) = terminalSpineQ core q u j := by
  rcases j with (m | ⟨s, f⟩) | k
  · rfl
  · exact terminalSpineExtra_eq_family q u s f
  · change FreeGroup.map Sum.inl (FreeGroup.of (Sum.inr k)) =
      FreeGroup.of (Sum.inl (Sum.inr k))
    simp

omit [Fintype A] in
/-- Terminal B3 in the actual operation's indexing: only the original core
H2-injectivity is required. -/
theorem terminalSpineQ_isCockcroft (hcore : ExpInjective core) :
    IsCockcroft (terminalSpineQ core q u) :=
  RelatorReindex.isCockcroft_of (terminalSpineQ core q u) (terminalSpinePres core q u)
    terminalCapReindex (terminalSpineQ_reindex core q u)
    (terminalSpine_isCockcroft core q u hcore)

omit [Fintype A] [Fintype K] [Fintype M] [Fintype S]
  [DecidableEq A] [DecidableEq K] [DecidableEq S] in
/-- The terminal presentation depends only on retained core relators: the
replaced source entries no longer occur in the result of rule 3. -/
theorem terminalSpineQ_eq_actual
    (ρ : M ⊕ S → FreeGroup (A ⊕ K))
    (hcore : ∀ m, ρ (Sum.inl m) = FreeGroup.map Sum.inl (core m)) :
    terminalSpineQ core q u =
      addRels (substPresF ρ (familyFiniteSpineWordBlock q u))
        (terminalSpineCaps (A := A) (K := K) q) := by
  funext j
  rcases j with (m | p) | k
  · change FreeGroup.map Sum.inl (FreeGroup.map Sum.inl (core m)) =
      FreeGroup.map Sum.inl (ρ (Sum.inl m))
    rw [hcore]
  · rfl
  · rfl

omit [Fintype A] in
/-- Applicable to the actual normalized source of rules 1 and 2, without a
separate terminal Cockcroft assumption. -/
theorem actualTerminalSpine_isCockcroft
    (ρ : M ⊕ S → FreeGroup (A ⊕ K))
    (hretained : ∀ m, ρ (Sum.inl m) = FreeGroup.map Sum.inl (core m))
    (hcore : ExpInjective core) :
    IsCockcroft (addRels (substPresF ρ (familyFiniteSpineWordBlock q u))
      (terminalSpineCaps (A := A) (K := K) q)) := by
  rw [← terminalSpineQ_eq_actual core q u ρ hretained]
  exact terminalSpineQ_isCockcroft core q u hcore

end FiniteChains.Davis.Genus
