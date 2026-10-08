import NetworkCoding33.Instance
import NetworkCoding33.Potential
import NetworkCoding33.Transfer
import NetworkCoding33.CutBound

/-!
# Main results: on the 33-vertex network, coding beats routing

* `coding_achieves`: network coding achieves rate 1 (a causal zero-error XOR code, block length 1).
* `routing_le`: every fractional multicommodity flow has rate at most `149 / 150`.
* `routingRate_lt_codingRate`: `routingRate < codingRate` (binary codes) for this instance.
* `routingRate_lt_entropyCodingRate`: `routingRate < entropyCodingRate`, the coding rate of
  Braverman–Garg–Schvartzman Definition A.3 (entropy-based, arbitrary finite alphabets).
* `entropyCodingRate_eq_one`: that coding rate is exactly 1.  The upper bound is the cut bound
  (`CutBound.lean`) applied to the cut between layers 2 and 3.
* `not_undirectedMultipleUnicastConjecture`: the conjecture, with that coding rate, is false.

All finite facts about the instance are checked by the kernel with `decide +kernel`; no
`native_decide`, floating point, or LP solver is used.
-/

open Finset

namespace NetCoding.Ex33

/-! ### Sanity checks on the instance -/

theorem card_vertices : Fintype.card V = 33 := rfl
theorem card_sessions : Fintype.card Msg = 30 := rfl
theorem edges_length : edges.length = 91 := by decide +kernel
theorem total_capacity : (edges.map fun e => e.2.2).sum = 149 := by decide +kernel
theorem cap_symm : ∀ u v : V, cap u v = cap v u := by decide +kernel
theorem cap_self : ∀ v : V, cap v v = 0 := by decide +kernel
theorem src_ne_dst : ∀ i : Msg, src i ≠ dst i := by decide +kernel
theorem program_length : program.length = 149 := by decide +kernel

/-! ### Network coding achieves rate 1 -/

/-- Every operand of every transmission is available to its sender (kernel-checked). -/
theorem program_wellFormed : wellFormed idx (src ∘ Prod.fst) bits program = true := by
  decide +kernel

/-- Every sink can recover its bit (kernel-checked). -/
theorem program_decodable :
    decodable idx (src ∘ Prod.fst) (dst ∘ Prod.fst) bits program (fun j => dec j.1) = true := by
  decide +kernel

/-- Every undirected edge carries exactly its capacity (kernel-checked). -/
theorem program_load : ∀ u v : V, loadList program u v = cap u v := by
  decide +kernel

/-- **Network coding achieves rate 1** on this network. -/
theorem coding_achieves : CodingAchieves cap src dst 1 1 := by
  refine ⟨program.length, toCode idx program, ?_, ?_, ?_⟩
  · exact causal_of_wellFormed idx_injective program_wellFormed
  · exact decodes_of_decodable idx_injective mem_bits program_decodable
  · intro u v
    rw [load_toCode, program_load, one_mul]

/-! ### Routing achieves at most 149/150 -/

/-- The layer of a vertex: `O ↦ 0`; `H, s ↦ 1`; `C, p ↦ 2`; `D, q ↦ 3`; `G, t ↦ 4`; `Z ↦ 5`. -/
def layer (v : V) : ℕ :=
  let n := v.val
  if n = 0 then 0 else if n = 1 then 1 else if n = 2 then 4 else if n = 3 then 5
  else if n < 6 then 2 else if n < 9 then 3 else if n < 15 then 1 else if n < 21 then 2
  else if n < 27 then 3 else 4

/-- The hop distance from `s a b`.  It depends only on the type of a vertex and on whether it
shares row `a` or column `b`. -/
def distX (a : Fin 3) (b : Fin 2) (v : V) : ℕ :=
  let n := v.val
  if n = 0 then 1 else if n = 1 then 2 else if n = 2 then 3 else if n = 3 then 4
  else if n < 6 then (if n - 4 = b.val then 1 else 3)
  else if n < 9 then (if n - 6 = a.val then 4 else 2)
  else
    let r := (n - 9) % 6 / 2
    let c := (n - 9) % 6 % 2
    let kind := (n - 9) / 6
    if kind = 0 then (if r = a.val ∧ c = b.val then 0 else 2)
    else if kind = 1 then (if r ≠ a.val ∧ c = b.val then 1 else 3)
    else if kind = 2 then (if r = a.val ∧ c ≠ b.val then 4 else 2)
    else (if r = a.val ∧ c = b.val then 5 else 3)

/-- The potential certifying that session `m` needs at least 5 hops. -/
def pot (m : Msg) (v : V) : ℕ :=
  if h : m.val < 6 then distX ⟨m.val / 2, by omega⟩ ⟨m.val % 2, by omega⟩ v else layer v

/-- Every potential changes by at most one along every edge (kernel-checked). -/
theorem pot_edge : ∀ m : Msg, ∀ e ∈ edges, pot m e.2.1 ≤ pot m e.1 + 1 ∧ pot m e.1 ≤ pot m e.2.1 + 1 := by
  decide +kernel

/-- Every session's sink lies 5 above its source (kernel-checked). -/
theorem pot_endpoints : ∀ m : Msg, pot m (dst m) = pot m (src m) + 5 := by
  decide +kernel

/-- The capacities summed over ordered pairs: twice the total capacity 149. -/
theorem sum_cap : (∑ u : V, ∑ v : V, cap u v) = 298 := by
  decide +kernel

lemma exists_edge_of_cap_pos {u v : V} (h : 0 < cap u v) :
    ∃ e ∈ edges, (e.1 = u ∧ e.2.1 = v) ∨ (e.1 = v ∧ e.2.1 = u) := by
  by_contra hne
  have hnil : (edges.filter fun e => decide ((e.1 = u ∧ e.2.1 = v) ∨ (e.1 = v ∧ e.2.1 = u))) = [] :=
    List.filter_eq_nil_iff.mpr fun e he hp => hne ⟨e, he, of_decide_eq_true hp⟩
  unfold cap at h
  rw [hnil] at h
  simp at h

lemma pot_lipschitz (m : Msg) {u v : V} (h : 0 < cap u v) :
    (pot m v : ℝ) - pot m u ≤ 1 := by
  obtain ⟨e, he, hor⟩ := exists_edge_of_cap_pos h
  have hb := pot_edge m e he
  have key : pot m v ≤ pot m u + 1 := by
    rcases hor with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact hb.1
    · exact hb.2
  have : (pot m v : ℝ) ≤ pot m u + 1 := by exact_mod_cast key
  linarith

/-- **Routing achieves at most rate 149/150.** -/
theorem routing_le {r : ℝ} (R : Routing cap src dst r) : r ≤ 149 / 150 := by
  have h := R.rate_mul_le (fun m v => (pot m v : ℝ)) fun m u v huv => pot_lipschitz m huv
  have h5 : ∀ m : Msg, ((pot m (dst m) : ℝ) - pot m (src m)) = 5 := fun m => by
    rw [pot_endpoints m]
    push_cast
    ring
  have hsum : ∑ m : Msg, ((pot m (dst m) : ℝ) - pot m (src m)) = 150 := by
    simp only [h5, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    norm_num
  have hcap : (∑ u : V, ∑ v : V, (cap u v : ℝ)) = 298 := by
    exact_mod_cast sum_cap
  rw [hsum, hcap] at h
  linarith

/-! ### The rates -/

theorem routingRate_le : routingRate cap src dst ≤ ENNReal.ofReal (149 / 150) :=
  iSup₂_le fun _ ⟨R⟩ => ENNReal.ofReal_le_ofReal (routing_le R)

theorem one_le_codingRate : 1 ≤ codingRate cap src dst :=
  le_iSup₂_of_le 1 1 (le_iSup₂_of_le one_pos coding_achieves (by simp))

/-- **Coding beats routing** on the 33-vertex network: routing rate `≤ 149/150 < 1 ≤` coding rate. -/
theorem routingRate_lt_codingRate : routingRate cap src dst < codingRate cap src dst :=
  calc routingRate cap src dst ≤ ENNReal.ofReal (149 / 150) := routingRate_le
    _ < 1 := by rw [ENNReal.ofReal_lt_one]; norm_num
    _ ≤ codingRate cap src dst := one_le_codingRate

/-- **Coding beats routing in the entropy-based model** (BGS Definition A.3). -/
theorem routingRate_lt_entropyCodingRate :
    routingRate cap src dst < entropyCodingRate cap src dst :=
  routingRate_lt_codingRate.trans_le (codingRate_le_entropyCodingRate cap src dst)

theorem one_le_entropyCodingRate : 1 ≤ entropyCodingRate cap src dst :=
  one_le_codingRate.trans (codingRate_le_entropyCodingRate cap src dst)

/-! ### The coding rate is exactly 1 -/

/-- The cut between layers 2 and 3 separates all 30 sessions (kernel-checked). -/
theorem layerCut_sessions :
    #{i : Msg | layer (src i) ≤ 2 ∧ ¬ layer (dst i) ≤ 2 ∨ ¬ layer (src i) ≤ 2 ∧ layer (dst i) ≤ 2} =
      30 := by
  decide +kernel

/-- The cut between layers 2 and 3 has capacity 30 (kernel-checked). -/
theorem layerCut_capacity :
    ∑ e ∈ univ.filter (fun e : V × V => layer e.1 ≤ 2 ∧ ¬ layer e.2 ≤ 2), cap e.1 e.2 = 30 := by
  decide +kernel

/-- The cut bound caps the coding rate at `30 / 30 = 1`. -/
theorem entropyCodingRate_le_one : entropyCodingRate cap src dst ≤ 1 := by
  have h := entropyCodingRate_le_cut cap src dst (fun v => layer v ≤ 2) (by norm_num)
    layerCut_sessions
  have hcap : (∑ e ∈ univ.filter (fun e : V × V => layer e.1 ≤ 2 ∧ ¬ layer e.2 ≤ 2),
      (cap e.1 e.2 : ℝ)) = 30 := by
    exact_mod_cast layerCut_capacity
  rw [hcap] at h
  simpa using h

/-- **The network coding rate of the 33-vertex network is exactly 1** (BGS Definition A.3). -/
theorem entropyCodingRate_eq_one : entropyCodingRate cap src dst = 1 :=
  le_antisymm entropyCodingRate_le_one one_le_entropyCodingRate

/-- The binary coding rate is exactly 1 too. -/
theorem codingRate_eq_one : codingRate cap src dst = 1 :=
  le_antisymm ((codingRate_le_entropyCodingRate cap src dst).trans entropyCodingRate_le_one)
    one_le_codingRate

end NetCoding.Ex33

namespace NetCoding

/-- The undirected multiple-unicast conjecture (Li–Li 2004; Harvey–Kleinberg–Lehman 2006; Adler,
Harvey, Jain, Kleinberg and Lehman 2006): on every undirected network, the network coding rate
(Braverman–Garg–Schvartzman, Definition A.3: `entropyCodingRate`) is at most the routing rate
(maximum concurrent multicommodity flow).  Here capacities are natural numbers and all demands
are `1`.  Those are special cases, so refuting this statement refutes the general one. -/
def UndirectedMultipleUnicastConjecture : Prop :=
  ∀ (V M : Type) [Fintype V] [DecidableEq V] [Fintype M] [DecidableEq M] (cap : V → V → ℕ)
    (src dst : M → V),
    (∀ u v, cap u v = cap v u) → (∀ v, cap v v = 0) → (∀ i, src i ≠ dst i) →
      entropyCodingRate cap src dst ≤ routingRate cap src dst

/-- **The 33-vertex network is a counterexample.** -/
theorem not_undirectedMultipleUnicastConjecture : ¬ UndirectedMultipleUnicastConjecture :=
  fun h => (h Ex33.V Ex33.Msg Ex33.cap Ex33.src Ex33.dst Ex33.cap_symm Ex33.cap_self
    Ex33.src_ne_dst).not_gt Ex33.routingRate_lt_entropyCodingRate

end NetCoding
