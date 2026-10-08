import NetworkCoding33.Entropy
import NetworkCoding33.Defs

/-!
# The entropy-based model of network coding (Braverman–Garg–Schvartzman, Appendix A)

This is the definition of the network coding rate used in the literature on the undirected
multiple-unicast conjecture (BGS arXiv:1608.06545, Definitions A.1–A.3; following Adler, Harvey,
Jain, Kleinberg and Lehman, SODA 2006).

* Session `i` sends a message from the finite set `Fin (msgSize i)`.  Messages are independent
  and uniform: the message tuple `m : Messages msgSize` is uniform (Section 2: `M = ∏ M(i)`).
* A code (Definitions A.1 and A.2) is a sequence of `T` transmissions.  Transmission `t` sends
  one symbol from the finite alphabet `Fin (alph t)` from `sender t` to `receiver t`.  Any finite
  alphabet can be relabelled as some `Fin n`, and entropy does not change under relabelling.
* **Causality:** every symbol is a function of what its sender knows when sending it: its own
  sessions' messages and the symbols it received earlier.
* **Correctness:** every sink can recover its session's message from what it knows at the end.
* The transcript of the arc `u → v` is the tuple of all symbols sent from `u` to `v`.
* **Rate** (Definition A.3): rate `r` is achieved if for some `b > 0` every message has entropy
  at least `r * b` (all demands are `1` here) and every edge `{u, v}` satisfies
  `H(u → v) + H(v → u) ≤ cap u v * b`.  BGS write `b ≥ 0`.  With `b = 0` every rate would be
  achievable by one-element message sets, so `b > 0` is the intended reading.

`CutBound.lean` proves the cut bound for this rate.  As a check that the definition is not too
permissive, `Main.lean` uses it to show that the 33-vertex network has coding rate exactly 1.
-/

open Finset
open scoped ENNReal

namespace NetCoding

/-- Message tuples: session `i` sends an element of `Fin (msgSize i)`. -/
abbrev Messages {M : Type} (msgSize : M → ℕ) := (i : M) → Fin (msgSize i)

/-- A network code (BGS Definitions A.1 and A.2).  Transmission `t : Fin T` sends the symbol
`send t m : Fin (alph t)` from `sender t` to `receiver t` when the messages are `m`. -/
structure Code (V M : Type) (msgSize : M → ℕ) where
  T : ℕ
  sender : Fin T → V
  receiver : Fin T → V
  alph : Fin T → ℕ
  send : (t : Fin T) → Messages msgSize → Fin (alph t)

namespace Code

variable {V M : Type} {msgSize : M → ℕ} (c : Code V M msgSize)

/-- Message tuples `m` and `m'` look the same to vertex `v` before time `t`: they agree on the
messages of sessions that start at `v` and on every symbol that `v` received before time `t`. -/
def Indist (src : M → V) (v : V) (t : ℕ) (m m' : Messages msgSize) : Prop :=
  (∀ i, src i = v → m i = m' i) ∧
    ∀ s : Fin c.T, (s : ℕ) < t → c.receiver s = v → c.send s m = c.send s m'

/-- Causality: every symbol is a function of what its sender knows when sending it. -/
def Causal (src : M → V) : Prop :=
  ∀ (t : Fin c.T) (m m' : Messages msgSize),
    c.Indist src (c.sender t) t m m' → c.send t m = c.send t m'

/-- Correctness: every sink recovers its session's message from what it knows at the end. -/
def Decodes (src dst : M → V) : Prop :=
  ∀ (i : M) (m m' : Messages msgSize), c.Indist src (dst i) c.T m m' → m i = m' i

/-- The transcript of the arc `u → v`: the tuple of all symbols sent from `u` to `v`. -/
def transcript [DecidableEq V] (u v : V) (m : Messages msgSize) :
    (t : {t : Fin c.T // c.sender t = u ∧ c.receiver t = v}) → Fin (c.alph t) :=
  fun t => c.send t m

end Code

variable {V M : Type} [Fintype V] [DecidableEq V] [Fintype M] [DecidableEq M]

/-- **BGS Definition A.3.** Network coding achieves rate `r`: for some `b > 0`, some causal and
correct code gives every session's message at least `r * b` bits of entropy, while the two
transcripts of every edge `{u, v}` have total entropy at most `cap u v * b`. -/
def EntropyAchieves (cap : V → V → ℕ) (src dst : M → V) (r : ℝ) : Prop :=
  ∃ (msgSize : M → ℕ) (c : Code V M msgSize) (b : ℝ), 0 < b ∧
    c.Causal src ∧ c.Decodes src dst ∧
    (∀ i, r * b ≤ entropy fun m : Messages msgSize => m i) ∧
    ∀ u v, u ≠ v → entropy (c.transcript u v) + entropy (c.transcript v u) ≤ cap u v * b

/-- The network coding rate of BGS: the supremum of the achievable rates. -/
noncomputable def entropyCodingRate (cap : V → V → ℕ) (src dst : M → V) : ℝ≥0∞ :=
  ⨆ (r : ℝ) (_ : EntropyAchieves cap src dst r), ENNReal.ofReal r

end NetCoding
