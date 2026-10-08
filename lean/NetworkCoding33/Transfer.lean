import NetworkCoding33.EntropyModel

/-!
# Binary codes are entropy-model codes

A binary code that carries `k` bits of every session in `b` uses of the network is a code of
the entropy model with rate `k / b`.  Pack each session's `k` bits into one message from
`Fin (2 ^ k)`; each one-bit transmission has entropy at most one bit; and a session's uniform
`k`-bit message has entropy exactly `k`.  Hence `codingRate ≤ entropyCodingRate`.
-/

open Finset Real
open scoped ENNReal

namespace NetCoding

variable {V M : Type} [Fintype V] [DecidableEq V] [Fintype M] [DecidableEq M]

/-- Unpack `k`-bit messages, stored as elements of `Fin (2 ^ k)`, into bits. -/
def toBits {k : ℕ} (m : Messages (fun _ : M => 2 ^ k)) : M × Fin k → Bit :=
  fun j => finFunctionFinEquiv.symm (m j.1) j.2

omit [Fintype M] [DecidableEq M] in
lemma eq_of_toBits_eq {k : ℕ} {m m' : Messages (fun _ : M => 2 ^ k)} {i : M}
    (h : ∀ l : Fin k, toBits m (i, l) = toBits m' (i, l)) : m i = m' i :=
  finFunctionFinEquiv.symm.injective (funext h)

/-- Run a binary code with `k` bits per session as a code of the entropy model. -/
def BinaryCode.toEntropyCode {k T : ℕ} (C : BinaryCode V (M × Fin k) T) :
    Code V M (fun _ => 2 ^ k) where
  T := T
  sender := C.sender
  receiver := C.receiver
  alph _ := 2
  send t m := C.bit t (toBits m)

namespace BinaryCode

variable {k T : ℕ} {C : BinaryCode V (M × Fin k) T} {src dst : M → V}

omit [Fintype V] [DecidableEq V] [Fintype M] [DecidableEq M] in
lemma toEntropyCode_causal (h : C.Causal (src ∘ Prod.fst)) : C.toEntropyCode.Causal src := by
  rintro t m m' ⟨h1, h2⟩
  exact h t (toBits m) (toBits m')
    ⟨fun j hj => by simp only [toBits]; rw [h1 j.1 hj], fun s hs hr => h2 s hs hr⟩

omit [Fintype V] [DecidableEq V] [Fintype M] [DecidableEq M] in
lemma toEntropyCode_decodes (h : C.Decodes (src ∘ Prod.fst) (dst ∘ Prod.fst)) :
    C.toEntropyCode.Decodes src dst := by
  rintro i m m' ⟨h1, h2⟩
  refine eq_of_toBits_eq fun l => h (i, l) (toBits m) (toBits m') ⟨fun j hj => ?_, h2⟩
  simp only [toBits]
  rw [h1 j.1 hj]

omit [Fintype V] [Fintype M] [DecidableEq M] in
/-- Over one edge the two directions together carry exactly the load of the edge. -/
lemma card_arc_add_card_arc (C : BinaryCode V (M × Fin k) T) {u v : V} (huv : u ≠ v) :
    #{t | C.sender t = u ∧ C.receiver t = v} + #{t | C.sender t = v ∧ C.receiver t = u} =
      C.load u v := by
  rw [BinaryCode.load, Finset.filter_or, Finset.card_union_of_disjoint]
  rw [Finset.disjoint_filter]
  rintro t - ⟨h1, -⟩ ⟨h2, -⟩
  exact huv (h1.symm.trans h2)

omit [Fintype V] in
/-- Each one-bit transmission contributes at most one bit of entropy to its transcript. -/
lemma entropy_transcript_le (C : BinaryCode V (M × Fin k) T) (u v : V) :
    entropy (C.toEntropyCode.transcript u v) ≤ (#{t | C.sender t = u ∧ C.receiver t = v} : ℝ) := by
  have : ∀ i : M, Nonempty (Fin (2 ^ k)) := fun _ => ⟨⟨0, by positivity⟩⟩
  have hc : Fintype.card ((t : {t : Fin C.toEntropyCode.T //
      C.toEntropyCode.sender t = u ∧ C.toEntropyCode.receiver t = v}) →
        Fin (C.toEntropyCode.alph t)) = 2 ^ #{t | C.sender t = u ∧ C.receiver t = v} := by
    have h2 : ∀ i : {t : Fin C.toEntropyCode.T //
        C.toEntropyCode.sender t = u ∧ C.toEntropyCode.receiver t = v},
        Fintype.card (Fin (C.toEntropyCode.alph i)) = 2 := fun i => Fintype.card_fin _
    rw [Fintype.card_pi, Finset.prod_congr rfl fun i _ => h2 i, Finset.prod_const,
      Finset.card_univ, Fintype.card_subtype]
    rfl
  refine (entropy_le_logb_card _).trans (le_of_eq ?_)
  rw [hc]
  push_cast
  rw [Real.logb_pow, Real.logb_self_eq_one one_lt_two, mul_one]

end BinaryCode

omit [Fintype V] [DecidableEq V] in
/-- A uniform `k`-bit message has `k` bits of entropy. -/
lemma entropy_message (k : ℕ) (i : M) :
    entropy (fun m : Messages (fun _ : M => 2 ^ k) => m i) = k := by
  have : ∀ i : M, Nonempty (Fin (2 ^ k)) := fun _ => ⟨⟨0, by positivity⟩⟩
  rw [entropy_eval, Fintype.card_fin]
  push_cast
  rw [Real.logb_pow, Real.logb_self_eq_one one_lt_two, mul_one]

omit [Fintype V] in
/-- **Binary codes are entropy-model codes**: a binary code achieving rate `k / b` achieves rate
`k / b` in the sense of BGS Definition A.3. -/
theorem CodingAchieves.entropyAchieves {cap : V → V → ℕ} {src dst : M → V} {k b : ℕ}
    (hb : 0 < b) (h : CodingAchieves cap src dst k b) :
    EntropyAchieves cap src dst ((k : ℝ) / b) := by
  obtain ⟨T, C, hC, hD, hL⟩ := h
  have hbR : (0 : ℝ) < b := by exact_mod_cast hb
  refine ⟨fun _ => 2 ^ k, C.toEntropyCode, b, hbR, BinaryCode.toEntropyCode_causal hC,
    BinaryCode.toEntropyCode_decodes hD, fun i => ?_, fun u v huv => ?_⟩
  · rw [entropy_message, div_mul_cancel₀ _ hbR.ne']
  · have h1 := BinaryCode.entropy_transcript_le C u v
    have h2 := BinaryCode.entropy_transcript_le C v u
    have h3 : (C.load u v : ℝ) ≤ cap u v * b := by
      have := hL u v
      rw [mul_comm] at this
      exact_mod_cast this
    rw [← BinaryCode.card_arc_add_card_arc C huv] at h3
    push_cast at h3
    linarith

omit [Fintype V] in
/-- The binary coding rate is at most the coding rate of BGS. -/
theorem codingRate_le_entropyCodingRate (cap : V → V → ℕ) (src dst : M → V) :
    codingRate cap src dst ≤ entropyCodingRate cap src dst := by
  refine iSup_le fun k => iSup_le fun b => iSup_le fun hb => iSup_le fun h => ?_
  have hbR : (0 : ℝ) < b := by exact_mod_cast hb
  calc (k : ℝ≥0∞) / b = ENNReal.ofReal ((k : ℝ) / b) := by
        rw [ENNReal.ofReal_div_of_pos hbR, ENNReal.ofReal_natCast, ENNReal.ofReal_natCast]
    _ ≤ entropyCodingRate cap src dst := le_iSup₂_of_le ((k : ℝ) / b) (h.entropyAchieves hb) le_rfl

end NetCoding
