module

public import RequestProject.SurfaceCoverPolygonLift
public import RequestProject.StrictOrderNormalizationMaps

@[expose] public section

/-! Naturality and deck reconstruction of the actual lifted polygon filling. -/
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains.Davis
open Comb Cell
variable {κ ι P Q : Type} {M : ℕ} [NeZero M] [PartialOrder P] [PartialOrder Q]
  {vc : Fin M → κ} {ec : Fin M → ι} (hc : Compat vc ec)
  (f : P → SCell vc ec hc) (hf : IsPosetCover f)

namespace CoveredPolygon
variable {v : PolygonCoverPole hc f} (D E : CoveredPolygon hc f v)

include hf in
/-- All positions in a lifted polygon are forced by its centre, including the
identified boundary positions. This removes all dependence on interval choices. -/
theorem fundamental_unique : D.fundamental = E.fundamental := by
  have hR : D.R = E.R := funext fun p => hf.up_inj (D.cr p) (E.cr p)
    ((D.projR p).trans (E.projR p).symm)
  have hI : D.I = E.I := funext fun p => hf.up_inj
    ((D.cr p).trans (D.ri p)) ((E.cr p).trans (E.ri p))
    ((D.projI p).trans (E.projI p).symm)
  have hW : D.W = E.W := funext fun p => hf.down_inj (D.wr p)
    (by rw (config := { transparency := .default }) [hR]; exact E.wr p) ((D.projW p).trans (E.projW p).symm)
  have hF : D.F = E.F := funext fun p => hf.down_inj (D.fi p)
    (by rw (config := { transparency := .default }) [hI]; exact E.fi p) ((D.projF p).trans (E.projF p).symm)
  have hT2 : D.T2 = E.T2 := funext fun p => hf.up_inj (D.ft2 p)
    (by rw (config := { transparency := .default }) [hF]; exact E.ft2 p) ((D.projT2 p).trans (E.projT2 p).symm)
  have hV : D.V = E.V := funext fun p => hf.down_inj
    ((D.vd p).trans (D.dt2 p))
    (by rw (config := { transparency := .default }) [hT2]; exact (E.vd p).trans (E.dt2 p))
    ((D.projV p).trans (E.projV p).symm)
  have hD : D.D = E.D := funext fun p => hf.down_inj (D.dt2 p)
    (by rw (config := { transparency := .default }) [hT2]; exact E.dt2 p) ((D.projD p).trans (E.projD p).symm)
  have hG : D.G = E.G := funext fun p => hf.down_inj (D.gt2 p)
    (by rw (config := { transparency := .default }) [hT2]; exact E.gt2 p) ((D.projG p).trans (E.projG p).symm)
  have hT1 : D.T1 = E.T1 := funext fun p => hf.up_inj (D.gt1 p)
    (by rw (config := { transparency := .default }) [hG]; exact E.gt1 p) ((D.projT1 p).trans (E.projT1 p).symm)
  have hE : D.E = E.E := funext fun p => hf.down_inj (D.et1 p)
    (by rw (config := { transparency := .default }) [hT1]; exact E.et1 p) ((D.projE p).trans (E.projE p).symm)
  simp only [fundamental, sector, hR, hI, hW, hF, hT2, hV, hD, hG, hT1, hE]

include hf in
theorem cellularFundamental_unique : D.cellularFundamental = E.cellularFundamental := by
  rw (config := { transparency := .default }) [cellularFundamental, cellularFundamental, fundamental_unique hc f hf D E]

variable (g : Q → SCell vc ec hc) (h : P → Q) (hm : Monotone h)
  (hp : ∀ p, g (h p) = f p)

def mapPole : PolygonCoverPole hc g := ⟨h v.1, (hp v.1).trans v.2⟩

/-- Mapping every actual polygon position through a map of covers preserves
the complete disk diagram. -/
def map : CoveredPolygon hc g (mapPole hc f g h hp (v := v)) where
  V := h ∘ D.V
  W := h ∘ D.W
  E := h ∘ D.E
  D := h ∘ D.D
  G := h ∘ D.G
  F := h ∘ D.F
  R := h ∘ D.R
  T1 := h ∘ D.T1
  T2 := h ∘ D.T2
  I := h ∘ D.I
  projV p := (hp _).trans (D.projV p)
  projW p := (hp _).trans (D.projW p)
  projE p := (hp _).trans (D.projE p)
  projD p := (hp _).trans (D.projD p)
  projG p := (hp _).trans (D.projG p)
  projF p := (hp _).trans (D.projF p)
  projR p := (hp _).trans (D.projR p)
  projT1 p := (hp _).trans (D.projT1 p)
  projT2 p := (hp _).trans (D.projT2 p)
  projI p := (hp _).trans (D.projI p)
  ve p := hm (D.ve p)
  v1e p := hm (D.v1e p)
  vd p := hm (D.vd p)
  wd p := hm (D.wd p)
  vg p := hm (D.vg p)
  w1g p := hm (D.w1g p)
  wf p := hm (D.wf p)
  w1f p := hm (D.w1f p)
  cr p := hm (D.cr p)
  wr p := hm (D.wr p)
  et1 p := hm (D.et1 p)
  d1t1 p := hm (D.d1t1 p)
  gt1 p := hm (D.gt1 p)
  gt2 p := hm (D.gt2 p)
  ft2 p := hm (D.ft2 p)
  dt2 p := hm (D.dt2 p)
  ri p := hm (D.ri p)
  fi p := hm (D.fi p)
  r1i p := hm (D.r1i p)

theorem map_fundamental :
    (D.map hc f g h hm hp).fundamental = Nerve.cmap h D.fundamental := by
  simp only [fundamental, sector, map, triangleFlagChain, map_add, map_sub, map_sum,
    Nerve.cmap_of, List.map_cons, List.map_nil, Function.comp_apply, mapPole]

theorem map_cellularFundamental (hs : StrictMono h) :
    (D.map hc f g h hm hp).cellularFundamental =
      chain2 (strictOrderCxMap h hs) D.cellularFundamental := by
  have he : decodeOrdNerve2 ((D.map hc f g h hm hp).fundamental) =
      chain2 (orderCxMap h hs.monotone) (decodeOrdNerve2 D.fundamental) := by
    apply ordNerveChain2_injective
    rw (config := { transparency := .default }) [ordNerveChain2_decode (D.map hc f g h hm hp).fundamental_mem_inc,
      (D.map hc f g h hm hp).fundamental_degree, ordNerveChain2_chain2,
      ordNerveChain2_decode D.fundamental_mem_inc, D.fundamental_degree,
      map_fundamental]
  rw (config := { transparency := .default }) [cellularFundamental, he, normalizeOrdChain2_strict_map]
  rfl

end CoveredPolygon

/-- Canonical lifted polygon fillings are natural under genuine strict maps of
surface covers. No equivariant choice is imposed on interval lifts. -/
theorem polygonCoverFilling_map
    (g : Q → SCell vc ec hc) (hg : IsPosetCover g)
    (h : P → Q) (hs : StrictMono h) (hp : ∀ p, g (h p) = f p)
    (v : PolygonCoverPole hc f) :
    chain2 (strictOrderCxMap h hs) (polygonCoverFilling hc f hf v) =
      polygonCoverFilling hc g hg ⟨h v.1, (hp v.1).trans v.2⟩ := by
  let D := coveredPolygon hc f hf v
  rw (config := { transparency := .default }) [show polygonCoverFilling hc f hf v = D.cellularFundamental from rfl,
    ← CoveredPolygon.map_cellularFundamental hc f D g h hs.monotone hp hs]
  exact CoveredPolygon.cellularFundamental_unique hc g hg _ _

/-- With an actual transitive deck parametrization of the pole fibre, the
finite sheet coefficient is precisely a group-ring multiple of one canonical
polygon filling. -/
theorem polygonRelative_eq_deck_sum (hd : PolygonData vc ec)
    {G : Type} [Group G] (deck : G → P ≃o P)
    (hdeck : ∀ g p, f (deck g p) = f p)
    (v : PolygonCoverPole hc f) (e : G ≃ PolygonCoverPole hc f)
    (he : ∀ g, (e g).1 = deck g v.1)
    (c : StrictOrdTri P →₀ ℤ) (hrel : PolygonRelativeChain hc f c) :
    c = Finsupp.linearCombination ℤ
      (fun g : G => chain2 (strictOrderCxMap (deck g) (deck g).strictMono)
        (polygonCoverFilling hc f hf v))
      (polygonCoverGroupCoefficient hc f hf e.symm c).coeff := by
  have hsum (a : PolygonCoverPole hc f →₀ ℤ) :
      polygonCoverReconstruct hc f hf a = Finsupp.linearCombination ℤ
        (fun g : G => chain2 (strictOrderCxMap (deck g) (deck g).strictMono)
          (polygonCoverFilling hc f hf v)) (Finsupp.mapDomain e.symm a) := by
    induction a using Finsupp.induction_linear with
    | zero => simp
    | add a b ha hb => rw (config := { transparency := .default }) [map_add, Finsupp.mapDomain_add, map_add, ha, hb]
    | single w n =>
      rw (config := { transparency := .default }) [polygonCoverReconstruct, Finsupp.linearCombination_single,
        Finsupp.mapDomain_single, Finsupp.linearCombination_single,
        polygonCoverFilling_map hc f hf f hf (deck (e.symm w))
          (deck (e.symm w)).strictMono (hdeck (e.symm w)) v]
      apply congrArg (fun x => n • polygonCoverFilling hc f hf x)
      apply Subtype.ext
      have hh := he (e.symm w)
      simpa only [e.apply_symm_apply] using hh
  exact (polygonRelative_reconstruct hc f hf hd c hrel).trans
    (hsum (polygonCoverPoleCoefficients hc f hf c))

end FiniteChains.Davis
