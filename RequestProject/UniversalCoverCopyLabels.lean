import RequestProject.UnivCoverCopies
import RequestProject.DeckChainTransport

/-! Actual components of the pullback of a universal cover to L, described
without choosing coset representatives.  The label keeps the L-vertex as
well as its universal-cover image, which matters when a pushout identifies
distinct old vertices. Unverified source. -/

noncomputable section
open scoped Classical
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains.Comb.UniversalCopy
universe u
variable {L E : Complex2.{u}} (f : Hom L E) (a : L.V)

def map (g : Pi1 E (f.onV a)) : Hom (uCover L a) (uCover E (f.onV a)) :=
  ((univDeck E (f.onV a)).cellHom g).comp (univLift L f a)

theorem projection_V (g : Pi1 E (f.onV a)) (v : UV L a) :
    endV ((map f a g).onV v) = f.onV (endV v) := by
  change endV (deckV g (univLiftV a f v)) = _
  rw [endV_deckV, endV_univLiftV]

theorem projection_E (g : Pi1 E (f.onV a)) (e : UE L a) :
    ((map f a g).onE e).val.2 = f.onE e.val.2 := rfl

theorem projection_F (g : Pi1 E (f.onV a)) (e : UF L a) :
    ((map f a g).onF e).val.2 = f.onF e.val.2 := rfl

def vertexPair (g : Pi1 E (f.onV a)) (v : UV L a) : UV E (f.onV a) × L.V :=
  ((map f a g).onV v, endV v)

def vertices (g : Pi1 E (f.onV a)) : Set (UV E (f.onV a) × L.V) :=
  Set.range (vertexPair f a g)

def label (v : UV E (f.onV a) × L.V) : Set (UV E (f.onV a) × L.V) :=
  {w | ∃ g, v ∈ vertices f a g ∧ w ∈ vertices f a g}

theorem identified_of_meet (hE : IsConnected E)
    (g h : Pi1 E (f.onV a)) (v w : UV L a)
    (hm : vertexPair f a g v = vertexPair f a h w) :
    ∃ k : Pi1 L a,
      (∀ x, (map f a g).onV x = (map f a h).onV (deckV k x)) ∧
      (∀ e, (map f a g).onE e = (map f a h).onE (deckE k e)) ∧
      (∀ t, (map f a g).onF t = (map f a h).onF (deckF k t)) := by
  have hend : endV v = endV w := congrArg Prod.snd hm
  obtain ⟨k, hk, _⟩ := (isRegular_univProj (X := L) (x₀ := a)).simply_transitive v w hend
  let F := map f a g
  let H := (map f a h).comp ((univDeck L a).cellHom k)
  have hprojE : ∀ e, (univProj E (f.onV a)).onE (F.onE e) =
      (univProj E (f.onV a)).onE (H.onE e) := fun _ => rfl
  have hprojF : ∀ t, (univProj E (f.onV a)).onF (F.onF t) =
      (univProj E (f.onV a)).onF (H.onF t) := fun _ => rfl
  have hb : F.onV v = H.onV v := by
    change (map f a g).onV v = (map f a h).onV (deckV k v)
    change deckV k v = w at hk
    rw [hk]
    exact congrArg Prod.fst hm
  have hV := lift_onV_eq (isCovering_univProj hE) isConnected_univCover hprojE hb
  exact ⟨k, hV, lift_onE_eq (isCovering_univProj hE) hprojE hV,
    lift_onF_eq (isCovering_univProj hE) hprojF hV⟩

theorem vertices_eq_of_meet (hE : IsConnected E)
    (g h : Pi1 E (f.onV a)) (v w : UV L a)
    (hm : vertexPair f a g v = vertexPair f a h w) : vertices f a g = vertices f a h := by
  obtain ⟨k, hV, _, _⟩ := identified_of_meet f a hE g h v w hm
  ext z
  constructor
  · rintro ⟨x, rfl⟩
    refine ⟨deckV k x, Prod.ext (hV x).symm (endV_deckV k x)⟩
  · rintro ⟨x, rfl⟩
    refine ⟨deckV k⁻¹ x, Prod.ext ?_ (endV_deckV k⁻¹ x)⟩
    simpa only [← deckV_mul, mul_inv_cancel, deckV_one, vertexPair, map] using hV (deckV k⁻¹ x)

theorem label_on_pair (hE : IsConnected E) (g : Pi1 E (f.onV a)) (v : UV L a) :
    label f a (vertexPair f a g v) = vertices f a g := by
  ext z
  constructor
  · rintro ⟨h, ⟨w, hw⟩, hz⟩
    rw [vertices_eq_of_meet f a hE g h v w hw.symm]
    exact hz
  · intro hz
    exact ⟨g, ⟨v, rfl⟩, hz⟩

theorem vertices_nonempty (g : Pi1 E (f.onV a)) : (vertices f a g).Nonempty :=
  ⟨vertexPair f a g (UV.base L a), ⟨UV.base L a, rfl⟩⟩

theorem vertices_covered (hL : IsConnected L) (v : UV E (f.onV a)) (l : L.V)
    (hv : endV v = f.onV l) : ∃ g x, vertexPair f a g x = (v, l) := by
  obtain ⟨x, hx⟩ := endV_surjective (x₀ := a) hL l
  have hproj : endV (univLiftV a f x) = endV v := by
    rw [endV_univLiftV, hx, hv]
  obtain ⟨g, hg, _⟩ := (isRegular_univProj (X := E) (x₀ := f.onV a)).simply_transitive _ _ hproj
  exact ⟨g, x, Prod.ext hg hx⟩

theorem edges_covered (hL : IsConnected L) (e : UE E (f.onV a)) (l : L.E)
    (he : e.val.2 = f.onE l) :
    ∃ (g : Pi1 E (f.onV a)) (x : UE L a), (map f a g).onE x = e ∧ x.val.2 = l := by
  have hv : endV e.val.1 = f.onV (L.src l) := by
    rw [e.property, he, f.src_onE]
  obtain ⟨g, x, hx⟩ := vertices_covered f a hL e.val.1 (L.src l) hv
  let e' : UE L a := ⟨(x, l), congrArg Prod.snd hx⟩
  refine ⟨g, e', ?_, rfl⟩
  apply Subtype.ext
  change ((map f a g).onV x, f.onE l) = e.val
  have hv' : (map f a g).onV x = e.val.1 :=
    congrArg (fun z : UV E (f.onV a) × L.V => z.1) hx
  exact Prod.ext hv' he.symm

theorem faces_covered (hL : IsConnected L) (t : UF E (f.onV a)) (l : L.F)
    (ht : t.val.2 = f.onF l) :
    ∃ (g : Pi1 E (f.onV a)) (x : UF L a), (map f a g).onF x = t ∧ x.val.2 = l := by
  have hv : endV t.val.1 = f.onV (L.base l) := by
    rw [t.property, ht, f.base_onF]
  obtain ⟨g, x, hx⟩ := vertices_covered f a hL t.val.1 (L.base l) hv
  let t' : UF L a := ⟨(x, l), congrArg Prod.snd hx⟩
  refine ⟨g, t', ?_, rfl⟩
  apply Subtype.ext
  change ((map f a g).onV x, f.onF l) = t.val
  have hv' : (map f a g).onV x = t.val.1 :=
    congrArg (fun z : UV E (f.onV a) × L.V => z.1) hx
  exact Prod.ext hv' ht.symm

theorem edge_range_of_label (hE : IsConnected E) (hL : IsConnected L)
    (g : Pi1 E (f.onV a)) (e : UE E (f.onV a)) (l : L.E)
    (he : e.val.2 = f.onE l)
    (hl : label f a (e.val.1, L.src l) = vertices f a g) :
    e ∈ Set.range (map f a g).onE := by
  obtain ⟨h, x, hx, hxl⟩ := edges_covered f a hL e l he
  have hp : vertexPair f a h x.val.1 = (e.val.1, L.src l) := by
    apply Prod.ext
    · exact congrArg (fun e : UE E (f.onV a) => e.val.1) hx
    · exact x.property.trans (congrArg L.src hxl)
  have hvg : vertices f a h = vertices f a g := by
    rw [← label_on_pair f a hE h x.val.1, hp]
    exact hl
  have hmem : vertexPair f a h x.val.1 ∈ vertices f a g := by
    rw [← hvg]
    exact ⟨x.val.1, rfl⟩
  obtain ⟨y, hy⟩ := hmem
  obtain ⟨k, _, hkE, _⟩ := identified_of_meet f a hE h g x.val.1 y hy.symm
  exact ⟨deckE k x, (hkE x).symm.trans hx⟩

theorem face_range_of_label (hE : IsConnected E) (hL : IsConnected L)
    (g : Pi1 E (f.onV a)) (t : UF E (f.onV a)) (l : L.F)
    (ht : t.val.2 = f.onF l)
    (hl : label f a (t.val.1, L.base l) = vertices f a g) :
    t ∈ Set.range (map f a g).onF := by
  obtain ⟨h, x, hx, hxl⟩ := faces_covered f a hL t l ht
  have hp : vertexPair f a h x.val.1 = (t.val.1, L.base l) := by
    apply Prod.ext
    · exact congrArg (fun t : UF E (f.onV a) => t.val.1) hx
    · exact x.property.trans (congrArg L.base hxl)
  have hvg : vertices f a h = vertices f a g := by
    rw [← label_on_pair f a hE h x.val.1, hp]
    exact hl
  have hmem : vertexPair f a h x.val.1 ∈ vertices f a g := by
    rw [← hvg]
    exact ⟨x.val.1, rfl⟩
  obtain ⟨y, hy⟩ := hmem
  obtain ⟨k, _, _, hkF⟩ := identified_of_meet f a hE h g x.val.1 y hy.symm
  exact ⟨deckF k x, (hkF x).symm.trans hx⟩

theorem map_injective_V (hV : Function.Injective (univLift L f a).onV)
    (g : Pi1 E (f.onV a)) : Function.Injective (map f a g).onV := by
  intro v w h
  apply hV
  have hh := congrArg (deckV g⁻¹) h
  change deckV g⁻¹ (deckV g ((univLift L f a).onV v)) =
    deckV g⁻¹ (deckV g ((univLift L f a).onV w)) at hh
  simpa only [← deckV_mul, inv_mul_cancel, deckV_one] using hh

theorem map_injective_E (hE : Function.Injective (univLift L f a).onE)
    (g : Pi1 E (f.onV a)) : Function.Injective (map f a g).onE := by
  intro e t h
  apply hE
  have hh := congrArg ((univDeck E (f.onV a)).smulE g⁻¹) h
  change (univDeck E (f.onV a)).smulE g⁻¹
      ((univDeck E (f.onV a)).smulE g ((univLift L f a).onE e)) =
    (univDeck E (f.onV a)).smulE g⁻¹
      ((univDeck E (f.onV a)).smulE g ((univLift L f a).onE t)) at hh
  simpa only [← DeckAction.mul_smulE, inv_mul_cancel, DeckAction.one_smulE] using hh

theorem map_injective_F (hF : Function.Injective (univLift L f a).onF)
    (g : Pi1 E (f.onV a)) : Function.Injective (map f a g).onF := by
  intro e t h
  apply hF
  have hh := congrArg ((univDeck E (f.onV a)).smulF g⁻¹) h
  change (univDeck E (f.onV a)).smulF g⁻¹
      ((univDeck E (f.onV a)).smulF g ((univLift L f a).onF e)) =
    (univDeck E (f.onV a)).smulF g⁻¹
      ((univDeck E (f.onV a)).smulF g ((univLift L f a).onF t)) at hh
  simpa only [← DeckAction.mul_smulF, inv_mul_cancel, DeckAction.one_smulF] using hh

theorem cycle_image_mem (g : Pi1 E (f.onV a)) (c : UF L a →₀ ℤ)
    (hc : bdry2 (uCover L a) c = 0) : chain2 (map f a g) c ∈ Pi2FromSub f (f.onV a) :=
  ⟨a, map f a g, projection_V f a g, projection_E f a g,
    projection_F f a g, c, hc, rfl⟩

end FiniteChains.Comb.UniversalCopy
