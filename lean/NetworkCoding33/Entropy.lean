import Mathlib

/-!
# Shannon entropy of a function of a uniformly random input

For a finite type `Ω` carrying the uniform distribution and a function `f : Ω → γ` into a finite
type, `entropy f` is the Shannon entropy, in bits, of the random variable `f ω`:

  `H(f) = (∑ y, negMulLog (P[f = y])) / log 2`,  where `P[f = y] = #{ω | f ω = y} / #Ω`

and `negMulLog x = -x * log x`.  Mathlib has no Shannon entropy yet, so we define it here and
prove the two facts we need:

* `entropy_le_logb_card`: `H(f) ≤ log₂ #γ`;
* `entropy_eval`: if `Ω = ∀ i, β i`, the coordinate `ω ↦ ω i` has entropy `log₂ #(β i)`.
-/

open Finset Real

namespace NetCoding

section Basic

variable {Ω γ : Type*} [Fintype Ω] [Fintype γ] [DecidableEq γ]

/-- The probability that `f ω = y` when `ω` is uniform on `Ω`. -/
noncomputable def prob (f : Ω → γ) (y : γ) : ℝ :=
  (#{ω | f ω = y} : ℝ) / Fintype.card Ω

/-- The Shannon entropy, in bits, of `f ω` when `ω` is uniform on `Ω`. -/
noncomputable def entropy (f : Ω → γ) : ℝ :=
  (∑ y, negMulLog (prob f y)) / log 2

omit [Fintype γ] in
lemma prob_nonneg (f : Ω → γ) (y : γ) : 0 ≤ prob f y := by
  unfold prob
  positivity

lemma sum_prob [Nonempty Ω] (f : Ω → γ) : ∑ y, prob f y = 1 := by
  have hΩ : (Fintype.card Ω : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hcard : (Fintype.card Ω : ℝ) = ∑ y, (#{ω | f ω = y} : ℝ) := by
    rw [← Finset.card_univ]
    exact_mod_cast Finset.card_eq_sum_card_fiberwise (f := f) (t := univ) (by intro x _; simp)
  simp only [prob, ← Finset.sum_div, ← hcard, div_self hΩ]

/-- Gibbs' inequality for the uniform distribution, via Jensen. -/
lemma sum_negMulLog_prob_le [Nonempty Ω] (f : Ω → γ) :
    ∑ y, negMulLog (prob f y) ≤ log (Fintype.card γ) := by
  have : Nonempty γ := ⟨f (Classical.arbitrary Ω)⟩
  have hn : (0 : ℝ) < Fintype.card γ := by exact_mod_cast Fintype.card_pos
  have hJ := concaveOn_negMulLog.le_map_sum (t := univ) (w := fun _ => (Fintype.card γ : ℝ)⁻¹)
    (p := prob f) (fun _ _ => inv_nonneg.mpr hn.le)
    (by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_inv_cancel₀ hn.ne'])
    (fun y _ => Set.mem_Ici.mpr (prob_nonneg f y))
  simp only [smul_eq_mul, ← Finset.mul_sum, sum_prob, mul_one, negMulLog, log_inv] at hJ
  have h : (Fintype.card γ : ℝ)⁻¹ * ∑ y, negMulLog (prob f y) ≤
      (Fintype.card γ : ℝ)⁻¹ * log (Fintype.card γ) := by
    simp only [negMulLog] at hJ ⊢
    linarith
  exact le_of_mul_le_mul_left h (inv_pos.mpr hn)

/-- **Maximum entropy.** A random variable with values in `γ` has at most `log₂ #γ` bits. -/
theorem entropy_le_logb_card [Nonempty Ω] (f : Ω → γ) :
    entropy f ≤ logb 2 (Fintype.card γ) := by
  unfold entropy logb
  exact div_le_div_of_nonneg_right (sum_negMulLog_prob_le f) (log_pos one_lt_two).le

end Basic

section Pi

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {β : ι → Type*} [∀ i, Fintype (β i)]
  [∀ i, DecidableEq (β i)]

lemma card_fiber_eval (i : ι) (y y' : β i) :
    #{ω : (∀ j, β j) | ω i = y} = #{ω : (∀ j, β j) | ω i = y'} := by
  refine Finset.card_nbij' (fun ω => Function.update ω i y') (fun ω => Function.update ω i y)
    ?_ ?_ ?_ ?_
  · intro ω _
    simp
  · intro ω _
    simp
  · intro ω hω
    simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at hω
    simp [Function.update_idem, ← hω]
  · intro ω hω
    simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at hω
    simp [Function.update_idem, ← hω]

lemma prob_eval [∀ i, Nonempty (β i)] (i : ι) (y : β i) :
    prob (fun ω : (∀ j, β j) => ω i) y = (Fintype.card (β i) : ℝ)⁻¹ := by
  have hsum : Fintype.card (∀ j, β j) = Fintype.card (β i) * #{ω : (∀ j, β j) | ω i = y} := by
    rw [← Finset.card_univ,
      Finset.card_eq_sum_card_fiberwise (f := fun ω : (∀ j, β j) => ω i) (t := univ)
        (by intro x _; simp),
      Finset.sum_congr rfl fun y' _ => card_fiber_eval i y' y]
    simp
  have hpos : 0 < #{ω : (∀ j, β j) | ω i = y} := by
    rcases Nat.eq_zero_or_pos #{ω : (∀ j, β j) | ω i = y} with h | h
    · rw [h, mul_zero] at hsum
      exact absurd hsum Fintype.card_ne_zero
    · exact h
  unfold prob
  rw [hsum]
  push_cast
  have : (#{ω : (∀ j, β j) | ω i = y} : ℝ) ≠ 0 := by exact_mod_cast hpos.ne'
  field_simp

/-- **Uniform messages.** A coordinate of a uniform tuple has entropy `log₂ #(β i)`. -/
theorem entropy_eval [∀ i, Nonempty (β i)] (i : ι) :
    entropy (fun ω : (∀ j, β j) => ω i) = logb 2 (Fintype.card (β i)) := by
  have hn : (0 : ℝ) < Fintype.card (β i) := by exact_mod_cast Fintype.card_pos
  unfold entropy logb
  simp only [prob_eval, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, negMulLog, log_inv]
  congr 1
  field_simp

end Pi

/-! ### Information inequalities

The proofs use entropy as average surprisal, `H(f) = avg_ω (-log₂ P[f = f ω])` (`entropy_eq_surprisal`),
and Gibbs' inequality in the form `log x ≤ x - 1`.
-/

section Inequalities

variable {Ω γ δ : Type*} [Fintype Ω] [Fintype γ] [DecidableEq γ] [Fintype δ] [DecidableEq δ]

omit [Fintype γ] in
lemma prob_le_one (f : Ω → γ) (y : γ) : prob f y ≤ 1 := by
  unfold prob
  rcases (Fintype.card Ω).eq_zero_or_pos with h | h
  · simp [h]
  · rw [div_le_one (by exact_mod_cast h)]
    exact_mod_cast Finset.card_le_univ _

omit [Fintype γ] in
lemma prob_self_pos (f : Ω → γ) (ω : Ω) : 0 < prob f (f ω) := by
  unfold prob
  have h1 : 0 < #{ω' | f ω' = f ω} := Finset.card_pos.mpr ⟨ω, by simp⟩
  have h2 : 0 < Fintype.card Ω := Fintype.card_pos_iff.mpr ⟨ω⟩
  exact div_pos (by exact_mod_cast h1) (by exact_mod_cast h2)

lemma entropy_nonneg (f : Ω → γ) : 0 ≤ entropy f :=
  div_nonneg (Finset.sum_nonneg fun y _ => negMulLog_nonneg (prob_nonneg f y) (prob_le_one f y))
    (log_nonneg one_le_two)

lemma entropy_of_isEmpty [IsEmpty Ω] (f : Ω → γ) : entropy f = 0 := by
  simp [entropy, prob]

lemma sum_surprisal [Nonempty Ω] (f : Ω → γ) :
    ∑ ω, -log (prob f (f ω)) = Fintype.card Ω * ∑ y, negMulLog (prob f y) := by
  rw [← Finset.sum_fiberwise' univ f (fun y => -log (prob f y)), Finset.mul_sum]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [Finset.sum_const, nsmul_eq_mul]
  have hΩ : (Fintype.card Ω : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hcount : (#{ω | f ω = y} : ℝ) = Fintype.card Ω * prob f y := by
    unfold prob
    field_simp
  rw [hcount, negMulLog]
  ring

/-- Entropy as average surprisal. -/
lemma entropy_eq_surprisal [Nonempty Ω] (f : Ω → γ) :
    entropy f = (∑ ω, -log (prob f (f ω))) / (Fintype.card Ω * log 2) := by
  have hΩ : (Fintype.card Ω : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  rw [sum_surprisal, entropy, mul_div_mul_left _ _ hΩ]

lemma surprisal_denom_pos [Nonempty Ω] : 0 < (Fintype.card Ω : ℝ) * log 2 :=
  mul_pos (by exact_mod_cast Fintype.card_pos) (log_pos one_lt_two)

/-- **Data processing.** If `g ω` is determined by `f ω`, then `H(g) ≤ H(f)`. -/
theorem entropy_le_of_determined [Nonempty Ω] (f : Ω → γ) (g : Ω → δ)
    (h : ∀ ω ω', f ω = f ω' → g ω = g ω') : entropy g ≤ entropy f := by
  rw [entropy_eq_surprisal g, entropy_eq_surprisal f]
  refine div_le_div_of_nonneg_right (Finset.sum_le_sum fun ω _ => ?_) surprisal_denom_pos.le
  have hle : prob f (f ω) ≤ prob g (g ω) := by
    unfold prob
    refine div_le_div_of_nonneg_right ?_ (Nat.cast_nonneg _)
    refine Nat.cast_le.mpr (Finset.card_le_card fun ω' hω' => ?_)
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hω' ⊢
    exact h ω' ω hω'
  have := log_le_log (prob_self_pos f ω) hle
  linarith

/-- **Subadditivity.** `H(f, g) ≤ H(f) + H(g)`. -/
theorem entropy_pair_le [Nonempty Ω] (f : Ω → γ) (g : Ω → δ) :
    entropy (fun ω => (f ω, g ω)) ≤ entropy f + entropy g := by
  set k : Ω → γ × δ := fun ω => (f ω, g ω) with hk
  set N : ℝ := (Fintype.card Ω : ℝ) with hN
  have hN0 : N ≠ 0 := by rw [hN]; exact_mod_cast Fintype.card_ne_zero
  have hNpos : 0 < N := by rw [hN]; exact_mod_cast Fintype.card_pos
  -- `Q ω = P[f = f ω] P[g = g ω] / P[(f, g) = (f ω, g ω)]` sums to at most `N`.
  have hQ : ∑ ω, prob f (f ω) * prob g (g ω) / prob k (k ω) ≤ N := by
    have hgroup : ∑ ω, prob f (f ω) * prob g (g ω) / prob k (k ω) =
        ∑ yz : γ × δ, #{ω | k ω = yz} * (prob f yz.1 * prob g yz.2 / prob k yz) := by
      rw [← Finset.sum_fiberwise univ k (fun ω => prob f (f ω) * prob g (g ω) / prob k (k ω))]
      refine Finset.sum_congr rfl fun yz _ => ?_
      have hfib : ∀ ω ∈ ({ω | k ω = yz} : Finset Ω),
          prob f (f ω) * prob g (g ω) / prob k (k ω) = prob f yz.1 * prob g yz.2 / prob k yz := by
        intro ω hω
        have hkω : k ω = yz := (Finset.mem_filter.mp hω).2
        have h1 : f ω = yz.1 := congrArg Prod.fst hkω
        have h2 : g ω = yz.2 := congrArg Prod.snd hkω
        rw [h1, h2, hkω]
      rw [Finset.sum_congr rfl hfib, Finset.sum_const, nsmul_eq_mul]
    have hterm : ∀ yz : γ × δ, (#{ω | k ω = yz} : ℝ) * (prob f yz.1 * prob g yz.2 / prob k yz) ≤
        N * (prob f yz.1 * prob g yz.2) := by
      intro yz
      rcases Nat.eq_zero_or_pos #{ω | k ω = yz} with h0 | hpos
      · rw [h0, Nat.cast_zero, zero_mul]
        exact mul_nonneg hNpos.le (mul_nonneg (prob_nonneg f _) (prob_nonneg g _))
      · have hc : (#{ω | k ω = yz} : ℝ) ≠ 0 := by exact_mod_cast hpos.ne'
        apply le_of_eq
        unfold prob
        rw [← hN]
        field_simp
    calc ∑ ω, prob f (f ω) * prob g (g ω) / prob k (k ω)
        = ∑ yz : γ × δ, #{ω | k ω = yz} * (prob f yz.1 * prob g yz.2 / prob k yz) := hgroup
      _ ≤ ∑ yz : γ × δ, N * (prob f yz.1 * prob g yz.2) := Finset.sum_le_sum fun yz _ => hterm yz
      _ = N * ((∑ y, prob f y) * ∑ z, prob g z) := by
        rw [← Finset.mul_sum, Fintype.sum_prod_type, Finset.sum_mul_sum]
      _ = N := by rw [sum_prob, sum_prob, mul_one, mul_one]
  -- Gibbs: `∑ log Q ≤ ∑ (Q - 1) ≤ 0`.
  have hpos : ∀ ω, 0 < prob f (f ω) * prob g (g ω) / prob k (k ω) := fun ω =>
    div_pos (mul_pos (prob_self_pos f ω) (prob_self_pos g ω)) (prob_self_pos k ω)
  have hgibbs : ∑ ω, log (prob f (f ω) * prob g (g ω) / prob k (k ω)) ≤ 0 := by
    calc ∑ ω, log (prob f (f ω) * prob g (g ω) / prob k (k ω))
        ≤ ∑ ω, (prob f (f ω) * prob g (g ω) / prob k (k ω) - 1) :=
          Finset.sum_le_sum fun ω _ => log_le_sub_one_of_pos (hpos ω)
      _ = ∑ ω, prob f (f ω) * prob g (g ω) / prob k (k ω) - N := by
          rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
      _ ≤ 0 := by linarith
  have hlog : ∀ ω, log (prob f (f ω) * prob g (g ω) / prob k (k ω)) =
      log (prob f (f ω)) + log (prob g (g ω)) - log (prob k (k ω)) := fun ω => by
    rw [log_div (mul_pos (prob_self_pos f ω) (prob_self_pos g ω)).ne' (prob_self_pos k ω).ne',
      log_mul (prob_self_pos f ω).ne' (prob_self_pos g ω).ne']
  simp only [hlog, Finset.sum_sub_distrib, Finset.sum_add_distrib] at hgibbs
  rw [entropy_eq_surprisal k, entropy_eq_surprisal f, entropy_eq_surprisal g, ← add_div]
  refine div_le_div_of_nonneg_right ?_ surprisal_denom_pos.le
  simp only [Finset.sum_neg_distrib]
  linarith

/-- A function whose fibres all have the same size has entropy `log₂ #γ`. -/
theorem entropy_of_balanced [Nonempty Ω] (f : Ω → γ)
    (hbal : ∀ y y', #{ω | f ω = y} = #{ω | f ω = y'}) :
    entropy f = logb 2 (Fintype.card γ) := by
  obtain ⟨ω₀⟩ := ‹Nonempty Ω›
  have hγ : (0 : ℝ) < Fintype.card γ := by exact_mod_cast Fintype.card_pos_iff.mpr ⟨f ω₀⟩
  have hsum : Fintype.card Ω = Fintype.card γ * #{ω | f ω = f ω₀} := by
    rw [← Finset.card_univ,
      Finset.card_eq_sum_card_fiberwise (f := f) (t := univ) (by intro x _; simp),
      Finset.sum_congr rfl fun y _ => hbal y (f ω₀)]
    simp
  have hpos : 0 < #{ω | f ω = f ω₀} := Finset.card_pos.mpr ⟨ω₀, by simp⟩
  have hp : ∀ y, prob f y = (Fintype.card γ : ℝ)⁻¹ := by
    intro y
    unfold prob
    rw [hbal y (f ω₀), hsum]
    push_cast
    have : (#{ω | f ω = f ω₀} : ℝ) ≠ 0 := by exact_mod_cast hpos.ne'
    field_simp
  unfold entropy logb
  simp only [hp, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, negMulLog, log_inv]
  congr 1
  field_simp

end Inequalities

section Restrict

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {β : ι → Type*} [∀ i, Fintype (β i)]
  [∀ i, DecidableEq (β i)]

/-- The coordinates of a tuple that satisfy `p`. -/
def restrictTo (p : ι → Prop) (ω : ∀ i, β i) : (i : {i // p i}) → β i := fun i => ω i

lemma card_fiber_restrictTo (p : ι → Prop) [DecidablePred p] (y y' : (i : {i // p i}) → β i) :
    #{ω | restrictTo p ω = y} = #{ω | restrictTo p ω = y'} := by
  refine Finset.card_nbij' (fun ω i => if h : p i then y' ⟨i, h⟩ else ω i)
    (fun ω i => if h : p i then y ⟨i, h⟩ else ω i) ?_ ?_ ?_ ?_
  · intro ω _
    simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq]
    funext i
    simp [restrictTo, i.2]
  · intro ω _
    simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq]
    funext i
    simp [restrictTo, i.2]
  · intro ω hω
    simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at hω
    funext i
    by_cases h : p i
    · simp only [h, dite_true]
      exact (congrFun hω ⟨i, h⟩).symm
    · simp [h]
  · intro ω hω
    simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at hω
    funext i
    by_cases h : p i
    · simp only [h, dite_true]
      exact (congrFun hω ⟨i, h⟩).symm
    · simp [h]

/-- **Independence.** The coordinates of a uniform tuple that satisfy `p` have entropy
`∑_{p i} log₂ #(β i)`. -/
theorem entropy_restrictTo [∀ i, Nonempty (β i)] (p : ι → Prop) [DecidablePred p] :
    entropy (restrictTo (β := β) p) = ∑ i ∈ univ.filter p, logb 2 (Fintype.card (β i)) := by
  rw [entropy_of_balanced _ (card_fiber_restrictTo p), Fintype.card_pi]
  push_cast
  unfold logb
  rw [log_prod (fun i _ => by exact_mod_cast Fintype.card_ne_zero), Finset.sum_div]
  exact (Finset.sum_subtype (univ.filter p) (by simp) (fun i => log (Fintype.card (β i)) / log 2)).symm

end Restrict

end NetCoding
