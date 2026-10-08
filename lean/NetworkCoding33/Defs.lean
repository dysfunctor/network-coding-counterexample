import Mathlib

/-!
# The model: network coding versus routing in undirected networks

An instance consists of a finite vertex type `V`, natural-number capacities `cap u v` on the
undirected edges `{u, v}` (`cap u v = 0` when there is no edge), and a finite type `M` of unit
sessions: session `i` must carry data from `src i` to `dst i`.

* **Routing** (`Routing`, `routingRate`) is fractional multicommodity flow.  The two directions of
  an undirected edge share its capacity, and `routingRate` is the maximum concurrent flow rate.
* **Network coding** (`BinaryCode`, `CodingAchieves`, `codingRate`): a vertex may send any function
  of the message bits it owns and the bits it has received so far (causality); every sink must
  recover its session's bits with zero error; and in `b` uses of the network an edge of capacity
  `c` carries at most `b * c` bits, counting both directions together.

This follows Section 2 and Appendix A of Braverman–Garg–Schvartzman (arXiv:1608.06545) and
Section III.A of Liu–Que–Li–Li (arXiv:2608.06070), restricted to binary codes.  The restriction
can only lower the coding rate.  `EntropyModel.lean` formalizes the unrestricted, entropy-based
definition (BGS Definition A.3), and `Transfer.lean` proves `codingRate ≤ entropyCodingRate`.
-/

open Finset
open scoped ENNReal

namespace NetCoding

/-- A bit: an element of `𝔽₂`. -/
abbrev Bit := ZMod 2

/-- A binary network code with `T` transmissions over message bits indexed by `B`.  At time
`t : Fin T`, vertex `sender t` sends one bit to vertex `receiver t`; as a function of all message
bits `x : B → Bit`, that bit is `bit t x`. -/
structure BinaryCode (V B : Type) (T : ℕ) where
  sender : Fin T → V
  receiver : Fin T → V
  bit : Fin T → (B → Bit) → Bit

namespace BinaryCode

variable {V B : Type} {T : ℕ} (C : BinaryCode V B T)

/-- Message inputs `x` and `y` look the same to vertex `v` before time `t`: they agree on every
message bit that originates at `v` and on every bit that `v` received before time `t`. -/
def Indist (src : B → V) (v : V) (t : ℕ) (x y : B → Bit) : Prop :=
  (∀ j, src j = v → x j = y j) ∧
    ∀ s : Fin T, (s : ℕ) < t → C.receiver s = v → C.bit s x = C.bit s y

/-- Causality: every transmitted bit is a function of what its sender knows when sending it. -/
def Causal (src : B → V) : Prop :=
  ∀ (t : Fin T) (x y : B → Bit), C.Indist src (C.sender t) t x y → C.bit t x = C.bit t y

/-- Zero-error decoding: every message bit is a function of what its sink knows at the end. -/
def Decodes (src dst : B → V) : Prop :=
  ∀ (j : B) (x y : B → Bit), C.Indist src (dst j) T x y → x j = y j

/-- The number of bits sent across the undirected edge `{u, v}`, in either direction. -/
def load [DecidableEq V] (u v : V) : ℕ :=
  (univ.filter fun t =>
    (C.sender t = u ∧ C.receiver t = v) ∨ (C.sender t = v ∧ C.receiver t = u)).card

end BinaryCode

variable {V M : Type} [Fintype V] [DecidableEq V] [Fintype M]

/-- Network coding achieves rate `k / b`: a causal, zero-error binary code delivers `k` bits of
every session (message bits `M × Fin k`) while sending at most `b * cap u v` bits across each
undirected edge `{u, v}`, both directions together. -/
def CodingAchieves (cap : V → V → ℕ) (src dst : M → V) (k b : ℕ) : Prop :=
  ∃ (T : ℕ) (C : BinaryCode V (M × Fin k) T),
    C.Causal (src ∘ Prod.fst) ∧ C.Decodes (src ∘ Prod.fst) (dst ∘ Prod.fst) ∧
      ∀ u v, C.load u v ≤ b * cap u v

/-- The network coding rate: the supremum of the achievable rates `k / b`. -/
noncomputable def codingRate (cap : V → V → ℕ) (src dst : M → V) : ℝ≥0∞ :=
  ⨆ (k : ℕ) (b : ℕ) (_ : 0 < b) (_ : CodingAchieves cap src dst k b), (k : ℝ≥0∞) / b

/-- A fractional multicommodity flow that routes `r` units of every session `i` from `src i` to
`dst i`.  `f i u v ≥ 0` is the flow of session `i` along the arc `u → v`; the two directions of an
undirected edge share its capacity. -/
structure Routing (cap : V → V → ℕ) (src dst : M → V) (r : ℝ) where
  f : M → V → V → ℝ
  nonneg : ∀ i u v, 0 ≤ f i u v
  conservation : ∀ i v, (∑ w, f i v w) - (∑ w, f i w v) =
    (if v = src i then r else 0) - (if v = dst i then r else 0)
  capacity : ∀ u v, (∑ i, (f i u v + f i v u)) ≤ cap u v

/-- The routing rate: the maximum concurrent multicommodity flow rate. -/
noncomputable def routingRate (cap : V → V → ℕ) (src dst : M → V) : ℝ≥0∞ :=
  ⨆ (r : ℝ) (_ : Nonempty (Routing cap src dst r)), ENNReal.ofReal r

end NetCoding
