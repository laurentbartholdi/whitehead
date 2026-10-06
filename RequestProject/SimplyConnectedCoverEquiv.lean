import RequestProject.UniversalToCover
import RequestProject.ZeroPi2Descent

/-! A connected simply connected cellular covering is the actual path-class universal cover. -/

namespace FiniteChains.Comb
universe u
variable {D K : Complex2.{u}} {p : Hom D K} {d₀ : D.V}

theorem coverV_surjective (hcov : IsCovering p) (hconn : IsConnected D) :
    Function.Surjective (coverV hcov (d₀ := d₀) rfl) := by
  intro v
  obtain ⟨m, hm⟩ := hconn d₀ v
  refine ⟨UV.mk (pathFromMap p d₀ hm), ?_⟩
  exact coverV_eq hcov rfl ⟨m, hm, rfl⟩

/-- Simple connectivity removes precisely the ambiguity between lifts of path classes. -/
theorem coverV_injective (hcov : IsCovering p) (hsc : SimplyConnected D) :
    Function.Injective (coverV hcov (d₀ := d₀) rfl) := by
  intro c d
  induction c using UV.ind with
  | h q =>
    induction d using UV.ind with
    | h r =>
      intro he
      obtain ⟨m, hm, hmq⟩ := coverV_spec hcov rfl q
      obtain ⟨n, hn, hnr⟩ := coverV_spec hcov rfl r
      rw [← he] at hn
      have htriv : Pi1Trivial p := fun a l hl => mapPath_htpy p (hsc a l hl)
      have hh := htpy_mapPath_of_pi1Trivial htriv hm hn
      rw [hmq, hnr] at hh
      apply UV.sound
      have hend := onV_coverV hcov rfl (UV.mk q)
      rw [hend] at hh
      exact hh

noncomputable def simplyConnectedCoverVertexEquiv (hcov : IsCovering p)
    (hconn : IsConnected D) (hsc : SimplyConnected D) :
    UV K (p.onV d₀) ≃ D.V :=
  Equiv.ofBijective _ ⟨coverV_injective hcov hsc, coverV_surjective hcov hconn⟩

theorem coverE_injective (hcov : IsCovering p) (hsc : SimplyConnected D) :
    Function.Injective (coverE hcov (d₀ := d₀) rfl) := by
  intro c d he
  apply Subtype.ext
  apply Prod.ext
  · apply coverV_injective hcov hsc
    rw [← src_coverE, ← src_coverE, he]
  · rw [← onE_coverE hcov rfl c, ← onE_coverE hcov rfl d, he]

theorem coverF_injective (hcov : IsCovering p) (hsc : SimplyConnected D) :
    Function.Injective (coverF hcov (d₀ := d₀) rfl) := by
  intro c d he
  apply Subtype.ext
  apply Prod.ext
  · apply coverV_injective hcov hsc
    rw [← base_coverF, ← base_coverF, he]
  · rw [← onF_coverF hcov rfl c, ← onF_coverF hcov rfl d, he]

theorem coverE_surjective (hcov : IsCovering p) (hconn : IsConnected D) :
    Function.Surjective (coverE hcov (d₀ := d₀) rfl) := by
  intro e
  obtain ⟨v, hv⟩ := coverV_surjective (d₀ := d₀) hcov hconn (D.src e)
  have hc : endV v = K.src (p.onE e) := by
    rw [← onV_coverV hcov rfl v, hv, p.src_onE]
  let c : UE K (p.onV d₀) := ⟨(v, p.onE e), hc⟩
  refine ⟨c, ?_⟩
  have h := liftGerm_unique hcov
    (x := (coverE hcov rfl c, true)) (y := (e, true))
    (by simpa only [germSrc_true] using src_coverE hcov rfl c)
    (by change D.src e = coverV hcov rfl v; exact hv.symm)
    (Prod.ext (onE_coverE hcov rfl c) rfl)
  exact congrArg Prod.fst h

theorem coverF_surjective (hcov : IsCovering p) (hconn : IsConnected D) :
    Function.Surjective (coverF hcov (d₀ := d₀) rfl) := by
  intro f
  obtain ⟨v, hv⟩ := coverV_surjective (d₀ := d₀) hcov hconn (D.base f)
  have hc : endV v = K.base (p.onF f) := by
    rw [← onV_coverV hcov rfl v, hv, p.base_onF]
  let c : UF K (p.onV d₀) := ⟨(v, p.onF f), hc⟩
  refine ⟨c, ?_⟩
  obtain ⟨g, -, hu⟩ := exists_unique_liftCell hcov (p.onF f)
    (v := coverV hcov rfl v) (by rw [hv]; exact p.base_onF f)
  exact (hu _ ⟨onF_coverF hcov rfl c, base_coverF hcov rfl c⟩).trans
    (hu f ⟨rfl, hv.symm⟩).symm

noncomputable def simplyConnectedCoverEdgeEquiv (hcov : IsCovering p)
    (hconn : IsConnected D) (hsc : SimplyConnected D) :
    UE K (p.onV d₀) ≃ D.E :=
  Equiv.ofBijective _ ⟨coverE_injective hcov hsc, coverE_surjective hcov hconn⟩

noncomputable def simplyConnectedCoverFaceEquiv (hcov : IsCovering p)
    (hconn : IsConnected D) (hsc : SimplyConnected D) :
    UF K (p.onV d₀) ≃ D.F :=
  Equiv.ofBijective _ ⟨coverF_injective hcov hsc, coverF_surjective hcov hconn⟩

/-- Identify a lifted face by its projected cell and its lifted base vertex. -/
theorem coverF_eq_of_base_and_image (hcov : IsCovering p) (c : UF K (p.onV d₀))
    (g : D.F) (himage : p.onF g = c.1.2)
    (hbase : D.base g = coverV hcov (d₀ := d₀) rfl c.1.1) :
    coverF hcov (d₀ := d₀) rfl c = g := by
  obtain ⟨w, -, hw⟩ := exists_unique_liftCell hcov c.1.2
    (v := coverV hcov (d₀ := d₀) rfl c.1.1) (coverF_cond hcov rfl c)
  exact (hw _ ⟨onF_coverF hcov rfl c, base_coverF hcov rfl c⟩).trans
    (hw g ⟨himage, hbase⟩).symm

end FiniteChains.Comb
