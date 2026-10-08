import NetworkCoding33.Defs

/-!
# Upper bounds on routing from potentials (weak LP duality)

If each session `i` has a potential `φ i : V → ℝ` that increases by at most one along every
edge, then any routing at rate `r` satisfies

  `r * ∑ i, (φ i (dst i) - φ i (src i)) ≤ (∑ u, ∑ v, cap u v) / 2 = total capacity`.

Each unit of session-`i` flow gains `φ i (dst i) - φ i (src i)` in potential but at most one per
unit of capacity it uses.  This is weak duality for the multicommodity-flow LP, with unit edge
lengths, and the potentials certify the distances.
-/

open Finset

namespace NetCoding

variable {V M : Type} [Fintype V] [DecidableEq V] [Fintype M]
  {cap : V → V → ℕ} {src dst : M → V} {r : ℝ}

namespace Routing

/-- No session sends flow along an edge of capacity zero. -/
lemma flow_eq_zero (R : Routing cap src dst r) {u v : V} (h : cap u v = 0) (i : M) :
    R.f i u v = 0 := by
  have h1 : R.f i u v ≤ ∑ j, (R.f j u v + R.f j v u) :=
    (le_add_of_nonneg_right (R.nonneg i v u)).trans
      (Finset.single_le_sum (f := fun j => R.f j u v + R.f j v u)
        (fun j _ => add_nonneg (R.nonneg j u v) (R.nonneg j v u)) (mem_univ i))
  have h2 := R.capacity u v
  rw [h, Nat.cast_zero] at h2
  exact le_antisymm (h1.trans h2) (R.nonneg i u v)

/-- Flow conservation weighted by a potential: session `i`'s flow gains exactly
`r * (φ (dst i) - φ (src i))` in potential. -/
lemma potential_gain (R : Routing cap src dst r) (φ : V → ℝ) (i : M) :
    ∑ u, ∑ v, R.f i u v * (φ v - φ u) = r * (φ (dst i) - φ (src i)) := by
  have split : ∑ u, ∑ v, R.f i u v * (φ v - φ u) =
      ∑ v, φ v * ∑ w, R.f i w v - ∑ v, φ v * ∑ w, R.f i v w := by
    simp only [mul_sub, Finset.sum_sub_distrib, Finset.mul_sum]
    rw [Finset.sum_comm (f := fun u v => R.f i u v * φ v)]
    congr 1 <;>
      exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => mul_comm _ _
  have cons : ∀ v, φ v * ∑ w, R.f i w v - φ v * ∑ w, R.f i v w =
      -(φ v * ((if v = src i then r else 0) - (if v = dst i then r else 0))) := by
    intro v
    rw [← R.conservation i v]
    ring
  rw [split, ← Finset.sum_sub_distrib, Finset.sum_congr rfl fun v _ => cons v,
    Finset.sum_neg_distrib]
  simp only [mul_sub, mul_ite, mul_zero, Finset.sum_sub_distrib, Finset.sum_ite_eq',
    mem_univ, if_true]
  ring

/-- **Weak duality.** Potentials that increase by at most one along each edge bound the rate. -/
theorem rate_mul_le (R : Routing cap src dst r) (φ : M → V → ℝ)
    (hφ : ∀ i u v, 0 < cap u v → φ i v - φ i u ≤ 1) :
    r * ∑ i, (φ i (dst i) - φ i (src i)) ≤ (∑ u, ∑ v, (cap u v : ℝ)) / 2 := by
  have step1 : ∀ i u v, R.f i u v * (φ i v - φ i u) ≤ R.f i u v := by
    intro i u v
    rcases Nat.eq_zero_or_pos (cap u v) with h | h
    · simp [R.flow_eq_zero h i]
    · exact mul_le_of_le_one_right (R.nonneg i u v) (hφ i u v h)
  have step2 : 2 * ∑ i, ∑ u, ∑ v, R.f i u v ≤ ∑ u, ∑ v, (cap u v : ℝ) := by
    have hsym : ∑ i, ∑ u, ∑ v, R.f i u v = ∑ i, ∑ u, ∑ v, R.f i v u :=
      Finset.sum_congr rfl fun i _ => Finset.sum_comm
    calc 2 * ∑ i, ∑ u, ∑ v, R.f i u v
        = ∑ i, ∑ u, ∑ v, (R.f i u v + R.f i v u) := by
          rw [two_mul]
          nth_rewrite 2 [hsym]
          simp only [Finset.sum_add_distrib]
      _ = ∑ u, ∑ v, ∑ i, (R.f i u v + R.f i v u) := by
          rw [Finset.sum_comm]
          exact Finset.sum_congr rfl fun u _ => Finset.sum_comm
      _ ≤ ∑ u, ∑ v, (cap u v : ℝ) := by
          gcongr with u _ v _
          exact R.capacity u v
  have step3 : r * ∑ i, (φ i (dst i) - φ i (src i)) =
      ∑ i, ∑ u, ∑ v, R.f i u v * (φ i v - φ i u) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => (R.potential_gain (φ i) i).symm
  have step4 : ∑ i, ∑ u, ∑ v, R.f i u v * (φ i v - φ i u) ≤ ∑ i, ∑ u, ∑ v, R.f i u v := by
    gcongr with i _ u _ v _
    exact step1 i u v
  linarith

end Routing

end NetCoding
