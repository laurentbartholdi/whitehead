import RequestProject.PresPosetReading

namespace FiniteChains.PresModel
universe u v
variable {α J : Type u} {G : Type v} [Group G]
  (w : J → List (α × Bool)) (gen : α → G)

/-- The actual cone trivialization at a letter midpoint has the signed prefix value. -/
theorem trivVal_cmid_of_get (j : J) (k : ℕ) (a : α × Bool)
    (ha : (w j)[k]? = some a) :
    trivVal w gen j k CPos.cmid =
      (if a.2 then (1 : G) else gen a.1) * (prefixVal w gen j k)⁻¹ := by
  unfold trivVal
  rw [aFun_cedgL_of_get w ha]
  cases a.2 <;> simp [roseVal]

/-- Inverting the actual midpoint trivialization yields the positive prefix or negative-letter Fox prefix. -/
theorem trivVal_cmid_inv_of_get (j : J) (k : ℕ) (a : α × Bool)
    (ha : (w j)[k]? = some a) :
    (trivVal w gen j k CPos.cmid)⁻¹ =
      prefixVal w gen j k * (if a.2 then (1 : G) else (gen a.1)⁻¹) := by
  rw [trivVal_cmid_of_get w gen j k a ha, mul_inv_rev, inv_inv]
  cases a.2 <;> simp

end FiniteChains.PresModel
