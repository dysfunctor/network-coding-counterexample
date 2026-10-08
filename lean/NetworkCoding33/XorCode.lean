import NetworkCoding33.Defs

/-!
# XOR programs

A linear network code is written as a list of instructions.  Instruction `t` says that `sender`
sends to `receiver` the XOR of some linear forms `ops`.  A linear form over `𝔽₂` in the message
bits is encoded as a bitmask `f : ℕ`: bit `idx j` of `f` is the coefficient of message bit `j`.

`wellFormed` and `decodable` are executable checks.  The soundness theorems
`causal_of_wellFormed` and `decodes_of_decodable` turn successful checks into the semantic
properties `BinaryCode.Causal` and `BinaryCode.Decodes`, and `load_toCode` computes edge loads.
-/

open Finset

namespace NetCoding

variable {V B : Type}

/-- Evaluate a linear form (a bitmask) on the message bits `x`. -/
def evalForm [Fintype B] (idx : B → ℕ) (f : ℕ) (x : B → Bit) : Bit :=
  ∑ j, if f.testBit (idx j) then x j else 0

/-- The XOR of a list of bitmasks. -/
def xorAll (l : List ℕ) : ℕ := l.foldr (· ^^^ ·) 0

/-- One instruction: `sender` sends to `receiver` the XOR of the linear forms `ops`. -/
structure Instr (V : Type) where
  sender : V
  receiver : V
  ops : List ℕ

/-- The linear form that an instruction transmits. -/
def Instr.form (I : Instr V) : ℕ := xorAll I.ops

/-- The binary code run by an XOR program. -/
def toCode [Fintype B] (idx : B → ℕ) (P : List (Instr V)) : BinaryCode V B P.length where
  sender t := (P.get t).sender
  receiver t := (P.get t).receiver
  bit t x := evalForm idx (P.get t).form x

variable [DecidableEq V]

/-- Is the form `f` a single message bit that originates at `u`? -/
def isOwn (idx : B → ℕ) (src : B → V) (bits : List B) (u : V) (f : ℕ) : Bool :=
  bits.any fun j => f == 2 ^ idx j && decide (src j = u)

/-- Did `u` receive the form `f` from one of the first `t` instructions? -/
def wasReceived (P : List (Instr V)) (t : ℕ) (u : V) (f : ℕ) : Bool :=
  (P.take t).any fun I => decide (I.receiver = u) && I.form == f

/-- Is the form `f` available to `u` before instruction `t`? -/
def avail (idx : B → ℕ) (src : B → V) (bits : List B) (P : List (Instr V)) (t : ℕ) (u : V)
    (f : ℕ) : Bool :=
  isOwn idx src bits u f || wasReceived P t u f

/-- Every operand of every instruction is available to the instruction's sender. -/
def wellFormed (idx : B → ℕ) (src : B → V) (bits : List B) (P : List (Instr V)) : Bool :=
  (List.finRange P.length).all fun t =>
    (P.get t).ops.all (avail idx src bits P t (P.get t).sender)

/-- Every message bit `j` is the XOR of the forms `dec j`, all available to its sink at the end. -/
def decodable (idx : B → ℕ) (src dst : B → V) (bits : List B) (P : List (Instr V))
    (dec : B → List ℕ) : Bool :=
  bits.all fun j =>
    (dec j).all (avail idx src bits P P.length (dst j)) && xorAll (dec j) == 2 ^ idx j

/-- The number of instructions that use the undirected edge `{u, v}`. -/
def loadList (P : List (Instr V)) (u v : V) : ℕ :=
  P.countP fun I => decide ((I.sender = u ∧ I.receiver = v) ∨ (I.sender = v ∧ I.receiver = u))

/-! ### Soundness -/

section Soundness

variable [Fintype B] (idx : B → ℕ)

lemma evalForm_zero (x : B → Bit) : evalForm idx 0 x = 0 := by
  simp [evalForm]

lemma evalForm_xor (f g : ℕ) (x : B → Bit) :
    evalForm idx (f ^^^ g) x = evalForm idx f x + evalForm idx g x := by
  simp only [evalForm, ← Finset.sum_add_distrib, Nat.testBit_xor]
  refine Finset.sum_congr rfl fun j _ => ?_
  generalize x j = z
  cases f.testBit (idx j) <;> cases g.testBit (idx j) <;> revert z <;> decide

lemma evalForm_xorAll (l : List ℕ) (x : B → Bit) :
    evalForm idx (xorAll l) x = (l.map fun f => evalForm idx f x).sum := by
  induction l with
  | nil => simp [xorAll, evalForm_zero]
  | cons f l ih =>
    simp only [xorAll, List.foldr_cons, List.map_cons, List.sum_cons] at ih ⊢
    rw [evalForm_xor, ih]

lemma evalForm_two_pow (hidx : Function.Injective idx) (j : B) (x : B → Bit) :
    evalForm idx (2 ^ idx j) x = x j := by
  unfold evalForm
  rw [Finset.sum_eq_single j]
  · simp [Nat.testBit_two_pow_self]
  · intro j' _ hj'
    have : idx j ≠ idx j' := fun h => hj' (hidx h).symm
    simp [this]
  · simp

variable {idx}

lemma wasReceived_sound {P : List (Instr V)} {t : ℕ} {u : V} {f : ℕ}
    (h : wasReceived P t u f = true) :
    ∃ s : Fin P.length, (s : ℕ) < t ∧ (P.get s).receiver = u ∧ (P.get s).form = f := by
  simp only [wasReceived, List.any_eq_true, Bool.and_eq_true, decide_eq_true_eq,
    beq_iff_eq] at h
  obtain ⟨I, hI, hr, hf⟩ := h
  obtain ⟨n, hn, rfl⟩ := List.getElem_of_mem hI
  rw [List.length_take] at hn
  refine ⟨⟨n, by omega⟩, by simp only; omega, ?_, ?_⟩
  · simpa [List.getElem_take] using hr
  · simpa [List.getElem_take] using hf

/-- An available operand has the same value on inputs that its holder cannot tell apart. -/
lemma avail_eval (hidx : Function.Injective idx) {src : B → V} {bits : List B}
    {P : List (Instr V)} {t : ℕ} {u : V} {f : ℕ} {x y : B → Bit}
    (hav : avail idx src bits P t u f = true) (hxy : (toCode idx P).Indist src u t x y) :
    evalForm idx f x = evalForm idx f y := by
  rcases Bool.or_eq_true_iff.mp hav with h | h
  · simp only [isOwn, List.any_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
    obtain ⟨j, -, rfl, hj⟩ := h
    rw [evalForm_two_pow idx hidx, evalForm_two_pow idx hidx]
    exact hxy.1 j hj
  · obtain ⟨s, hs, hr, rfl⟩ := wasReceived_sound h
    exact hxy.2 s hs hr

/-- A well-formed XOR program is a causal code. -/
theorem causal_of_wellFormed (hidx : Function.Injective idx) {src : B → V} {bits : List B}
    {P : List (Instr V)} (h : wellFormed idx src bits P = true) :
    (toCode idx P).Causal src := by
  intro t x y hxy
  have ht := List.all_eq_true.mp h t (List.mem_finRange t)
  show evalForm idx (P.get t).form x = evalForm idx (P.get t).form y
  simp only [Instr.form, evalForm_xorAll]
  congr 1
  exact List.map_congr_left fun f hf => avail_eval hidx (List.all_eq_true.mp ht f hf) hxy

/-- If every message bit is the XOR of forms available to its sink, the code decodes. -/
theorem decodes_of_decodable (hidx : Function.Injective idx) {src dst : B → V}
    {bits : List B} (hbits : ∀ j, j ∈ bits) {P : List (Instr V)} {dec : B → List ℕ}
    (h : decodable idx src dst bits P dec = true) : (toCode idx P).Decodes src dst := by
  intro j x y hxy
  have hj := List.all_eq_true.mp h j (hbits j)
  simp only [Bool.and_eq_true, beq_iff_eq] at hj
  obtain ⟨hav, hx⟩ := hj
  rw [← evalForm_two_pow idx hidx j x, ← evalForm_two_pow idx hidx j y, ← hx,
    evalForm_xorAll, evalForm_xorAll]
  congr 1
  exact List.map_congr_left fun f hf => avail_eval hidx (List.all_eq_true.mp hav f hf) hxy

lemma card_filter_get {α : Type} (P : List α) (p : α → Bool) :
    (univ.filter fun t : Fin P.length => p (P.get t) = true).card = P.countP p := by
  induction P with
  | nil => simp
  | cons a P ih =>
    rw [List.countP_cons, ← ih, Finset.card_filter, Finset.card_filter]
    simp only [List.length_cons]
    rw [Fin.sum_univ_succ]
    simp only [List.get_eq_getElem, Fin.val_zero, Fin.val_succ, List.getElem_cons_zero,
      List.getElem_cons_succ]
    rw [add_comm]
    by_cases h : p a = true <;> simp [h]

/-- The load of the code run by a program is the program's edge count. -/
theorem load_toCode (P : List (Instr V)) (u v : V) :
    (toCode (B := B) idx P).load u v = loadList P u v := by
  rw [loadList, ← card_filter_get]
  simp only [BinaryCode.load, toCode, decide_eq_true_eq]
  congr 1

end Soundness

end NetCoding
