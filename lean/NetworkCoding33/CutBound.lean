import NetworkCoding33.EntropyModel

/-!
# The cut bound for the entropy-based coding rate

**Theorem** (`EntropyAchieves.cut_bound`).  If network coding achieves rate `r`, then for every
set `S` of vertices,

  `r * #(sessions separated by S) ≤ total capacity of the edges leaving S`.

Proof outline, with `X` the symbols sent from `S` to its complement:
1. (Causality) Every symbol sent from outside `S` is determined by the messages that start
   outside `S` together with `X`.  So every session from `S` to the complement is decoded from
   `X` and those messages (`eq_of_dst_outside`).
2. (Information) Messages are independent, so the entropy of the sessions crossing from `S` is
   at most `H(X)` (`sum_logb_le_entropy_cut`).  The same holds in the other direction.
3. (Capacity) `H(X)` is at most the sum of the entropies of the arc transcripts across the cut
   (subadditivity), and BGS Definition A.3 bounds each edge's pair of transcripts by `cap * b`.
-/

open Finset Real

namespace NetCoding

namespace Code

variable {V M : Type} [DecidableEq V] {msgSize : M → ℕ} (c : Code V M msgSize) {src dst : M → V}

/-- The symbols sent at the times in `F`. -/
def symbols (F : Finset (Fin c.T)) (m : Messages msgSize) : (t : {t // t ∈ F}) → Fin (c.alph t) :=
  fun t => c.send t m

omit [DecidableEq V] in
/-- **Causal simulation.** If two message tuples agree on the messages that start outside `S` and
on every symbol sent from `S` to its complement, they agree on every symbol sent from outside
`S`. -/
lemma send_eq_of_outside (hc : c.Causal src) (S : V → Prop) {m m' : Messages msgSize}
    (hm : ∀ i, ¬ S (src i) → m i = m' i)
    (hcut : ∀ t : Fin c.T, S (c.sender t) → ¬ S (c.receiver t) → c.send t m = c.send t m') :
    ∀ t : Fin c.T, ¬ S (c.sender t) → c.send t m = c.send t m' := by
  suffices H : ∀ n (t : Fin c.T), (t : ℕ) = n → ¬ S (c.sender t) → c.send t m = c.send t m' from
    fun t => H t t rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro t ht hS
    refine hc t m m' ⟨fun i hi => hm i (by rw [hi]; exact hS), fun s hs hr => ?_⟩
    by_cases hsS : S (c.sender s)
    · exact hcut s hsS (by rw [hr]; exact hS)
    · exact ih s (ht ▸ hs) s rfl hsS

omit [DecidableEq V] in
/-- Sinks outside `S` then decode the same messages. -/
lemma eq_of_dst_outside (hc : c.Causal src) (hd : c.Decodes src dst) (S : V → Prop)
    {m m' : Messages msgSize} (hm : ∀ i, ¬ S (src i) → m i = m' i)
    (hcut : ∀ t : Fin c.T, S (c.sender t) → ¬ S (c.receiver t) → c.send t m = c.send t m')
    {i : M} (hi : ¬ S (dst i)) : m i = m' i := by
  refine hd i m m' ⟨fun j hj => hm j (by rw [hj]; exact hi), fun s _ hr => ?_⟩
  by_cases hsS : S (c.sender s)
  · exact hcut s hsS (by rw [hr]; exact hi)
  · exact c.send_eq_of_outside hc S hm hcut s hsS

variable [Fintype M] [DecidableEq M]

/-- The messages of the sessions that satisfy `p`. -/
abbrev msgsOf (msgSize : M → ℕ) (p : M → Prop) :
    Messages msgSize → (i : {i // p i}) → Fin (msgSize i) :=
  restrictTo p

omit [DecidableEq V] in
/-- **One side of the cut.** The sessions from `S` to its complement carry at most `H(X)` bits,
where `X` is everything sent from `S` to its complement. -/
theorem sum_logb_le_entropy_cut [Nonempty (Messages msgSize)] (hc : c.Causal src)
    (hd : c.Decodes src dst) (S : V → Prop) [DecidablePred S] :
    ∑ i ∈ univ.filter (fun i => S (src i) ∧ ¬ S (dst i)), logb 2 (msgSize i) ≤
      entropy (c.symbols (univ.filter fun t => S (c.sender t) ∧ ¬ S (c.receiver t))) := by
  obtain ⟨m₀⟩ := ‹Nonempty (Messages msgSize)›
  have : ∀ i, Nonempty (Fin (msgSize i)) := fun i => ⟨m₀ i⟩
  set X := c.symbols (univ.filter fun t => S (c.sender t) ∧ ¬ S (c.receiver t)) with hX
  set pA : M → Prop := fun i => S (src i) ∧ ¬ S (dst i) with hpA
  set pZ : M → Prop := fun i => ¬ S (src i) with hpZ
  have hent : ∀ (p : M → Prop) [DecidablePred p],
      entropy (msgsOf msgSize p) = ∑ i ∈ univ.filter p, logb 2 (msgSize i) := by
    intro p _
    have h := entropy_restrictTo (β := fun i => Fin (msgSize i)) p
    simp only [Fintype.card_fin] at h
    convert h using 2
  -- `H(m_A) + H(m_Z) = H(m_{A ∪ Z})`, since `A` and `Z` are disjoint.
  have hunion : entropy (msgsOf msgSize fun i => pA i ∨ pZ i) =
      entropy (msgsOf msgSize pA) + entropy (msgsOf msgSize pZ) := by
    rw [hent, hent, hent, Finset.filter_or, Finset.sum_union]
    exact Finset.disjoint_filter.mpr fun i _ hA hZ => hZ hA.1
  -- `H(m_{A ∪ Z}) ≤ H(m_A, m_Z)`.
  have h1 : entropy (msgsOf msgSize fun i => pA i ∨ pZ i) ≤
      entropy (fun m => (msgsOf msgSize pA m, msgsOf msgSize pZ m)) := by
    refine entropy_le_of_determined _ _ fun m m' h => ?_
    funext ⟨i, hi⟩
    rcases hi with hi | hi
    · exact congrFun (congrArg Prod.fst h) ⟨i, hi⟩
    · exact congrFun (congrArg Prod.snd h) ⟨i, hi⟩
  -- `(m_A, m_Z)` is determined by `(X, m_Z)` (causal simulation).
  have h2 : entropy (fun m => (msgsOf msgSize pA m, msgsOf msgSize pZ m)) ≤
      entropy (fun m => (X m, msgsOf msgSize pZ m)) := by
    refine entropy_le_of_determined _ _ fun m m' h => ?_
    have hXm := congrArg Prod.fst h
    have hZm := congrArg Prod.snd h
    refine Prod.ext ?_ hZm
    funext ⟨i, hi⟩
    exact c.eq_of_dst_outside hc hd S (fun j hj => congrFun hZm ⟨j, hj⟩)
      (fun t h1 h2 => congrFun hXm ⟨t, by simp [h1, h2]⟩) hi.2
  have h3 := entropy_pair_le X (msgsOf msgSize pZ)
  rw [← hent pA]
  linarith

/-- The transcript of `u → v` has the same entropy as the symbols sent at its times. -/
lemma entropy_transcript_eq [Nonempty (Messages msgSize)] (u v : V) :
    entropy (c.transcript u v) =
      entropy (c.symbols (univ.filter fun t => c.sender t = u ∧ c.receiver t = v)) := by
  apply le_antisymm
  · refine entropy_le_of_determined _ _ fun m m' h => ?_
    funext ⟨t, ht⟩
    exact congrFun h ⟨t, by simpa using ht⟩
  · refine entropy_le_of_determined _ _ fun m m' h => ?_
    funext ⟨t, ht⟩
    exact congrFun h ⟨t, by simpa using ht⟩

omit [DecidableEq V] in
lemma entropy_symbols_union_le [Nonempty (Messages msgSize)] (F G : Finset (Fin c.T)) :
    entropy (c.symbols (F ∪ G)) ≤ entropy (c.symbols F) + entropy (c.symbols G) := by
  refine (entropy_le_of_determined (fun m => (c.symbols F m, c.symbols G m)) _ ?_).trans
    (entropy_pair_le _ _)
  intro m m' h
  funext ⟨t, ht⟩
  rcases Finset.mem_union.mp ht with ht | ht
  · exact congrFun (congrArg Prod.fst h) ⟨t, ht⟩
  · exact congrFun (congrArg Prod.snd h) ⟨t, ht⟩

omit [DecidableEq V] in
lemma entropy_symbols_empty [Nonempty (Messages msgSize)] {F : Finset (Fin c.T)} (hF : F = ∅) :
    entropy (c.symbols F) ≤ 0 := by
  subst hF
  refine (entropy_le_logb_card _).trans (le_of_eq ?_)
  have : Fintype.card ((t : {t // t ∈ (∅ : Finset (Fin c.T))}) → Fin (c.alph t)) = 1 :=
    Fintype.card_eq_one_iff.mpr ⟨fun t => absurd t.2 (Finset.notMem_empty _),
      fun g => funext fun t => absurd t.2 (Finset.notMem_empty _)⟩
  rw [this]
  simp

omit [DecidableEq V] in
lemma entropy_symbols_biUnion_le [Nonempty (Messages msgSize)] {α : Type*} [DecidableEq α]
    (A : Finset α) (F : α → Finset (Fin c.T)) :
    entropy (c.symbols (A.biUnion F)) ≤ ∑ a ∈ A, entropy (c.symbols (F a)) := by
  induction A using Finset.induction_on with
  | empty =>
    rw [Finset.sum_empty]
    exact c.entropy_symbols_empty Finset.biUnion_empty
  | insert a A ha ih =>
    rw [Finset.biUnion_insert, Finset.sum_insert ha]
    exact (c.entropy_symbols_union_le _ _).trans (by linarith)

/-- `H(X)` is at most the total entropy of the arc transcripts leaving `S`. -/
lemma entropy_cut_le [Fintype V] [Nonempty (Messages msgSize)] (S : V → Prop) [DecidablePred S] :
    entropy (c.symbols (univ.filter fun t => S (c.sender t) ∧ ¬ S (c.receiver t))) ≤
      ∑ e ∈ univ.filter (fun e : V × V => S e.1 ∧ ¬ S e.2), entropy (c.transcript e.1 e.2) := by
  have hbu : (univ.filter fun t => S (c.sender t) ∧ ¬ S (c.receiver t)) =
      (univ.filter fun e : V × V => S e.1 ∧ ¬ S e.2).biUnion
        (fun e => univ.filter fun t => c.sender t = e.1 ∧ c.receiver t = e.2) := by
    ext t
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_biUnion, Prod.exists]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨c.sender t, c.receiver t, ⟨h1, h2⟩, rfl, rfl⟩
    · rintro ⟨u, v, ⟨h1, h2⟩, rfl, rfl⟩
      exact ⟨h1, h2⟩
  rw [hbu]
  refine (c.entropy_symbols_biUnion_le _ _).trans (le_of_eq ?_)
  exact Finset.sum_congr rfl fun e _ => (c.entropy_transcript_eq e.1 e.2).symm

end Code

variable {V M : Type} [Fintype V] [DecidableEq V] [Fintype M] [DecidableEq M]

/-- **Cut bound.** If network coding achieves rate `r` (BGS Definition A.3), then for every set `S`
of vertices, `r` times the number of sessions separated by `S` is at most the capacity of the
edges leaving `S`. -/
theorem EntropyAchieves.cut_bound {cap : V → V → ℕ} {src dst : M → V} {r : ℝ}
    (h : EntropyAchieves cap src dst r) (S : V → Prop) [DecidablePred S] :
    r * #{i | S (src i) ∧ ¬ S (dst i) ∨ ¬ S (src i) ∧ S (dst i)} ≤
      ∑ e ∈ univ.filter (fun e : V × V => S e.1 ∧ ¬ S e.2), (cap e.1 e.2 : ℝ) := by
  obtain ⟨msgSize, c, b, hb, hc, hd, hrate, hcap⟩ := h
  have hRHS : 0 ≤ ∑ e ∈ univ.filter (fun e : V × V => S e.1 ∧ ¬ S e.2), (cap e.1 e.2 : ℝ) :=
    Finset.sum_nonneg fun _ _ => Nat.cast_nonneg _
  rcases le_or_gt r 0 with hr | hr
  · exact (mul_nonpos_of_nonpos_of_nonneg hr (Nat.cast_nonneg _)).trans hRHS
  -- With `r > 0`, every message set is nonempty.
  have hpos : ∀ i, 0 < msgSize i := by
    intro i
    by_contra h0
    have : IsEmpty (Messages msgSize) := ⟨fun m => by have := (m i).2; omega⟩
    have hi := hrate i
    rw [entropy_of_isEmpty] at hi
    nlinarith [mul_pos hr hb]
  have : Nonempty (Messages msgSize) := ⟨fun i => ⟨0, hpos i⟩⟩
  have : ∀ i, Nonempty (Fin (msgSize i)) := fun i => ⟨⟨0, hpos i⟩⟩
  have hri : ∀ i, r * b ≤ logb 2 (msgSize i) := fun i => by
    have := hrate i
    rwa [entropy_eval, Fintype.card_fin] at this
  -- Sessions separated by `S`, in the two directions.
  set A := univ.filter fun i => S (src i) ∧ ¬ S (dst i) with hA
  set B := univ.filter fun i => ¬ S (src i) ∧ ¬ ¬ S (dst i) with hB
  have hsplit : (univ.filter fun i => S (src i) ∧ ¬ S (dst i) ∨ ¬ S (src i) ∧ S (dst i)) =
      A ∪ B := by
    ext i
    simp [hA, hB]
  have hdisj : Disjoint A B := Finset.disjoint_filter.mpr fun i _ h1 h2 => h2.1 h1.1
  -- The edges leaving `S`.
  set E := univ.filter fun e : V × V => S e.1 ∧ ¬ S e.2 with hE
  have hswap : ∑ e ∈ univ.filter (fun e : V × V => ¬ S e.1 ∧ ¬ ¬ S e.2),
      entropy (c.transcript e.1 e.2) = ∑ e ∈ E, entropy (c.transcript e.2 e.1) := by
    refine Finset.sum_nbij' Prod.swap Prod.swap ?_ ?_ ?_ ?_ ?_ <;>
      simp +contextual [hE]
  have hedge : ∑ e ∈ E, (entropy (c.transcript e.1 e.2) + entropy (c.transcript e.2 e.1)) ≤
      ∑ e ∈ E, (cap e.1 e.2 : ℝ) * b := by
    refine Finset.sum_le_sum fun e he => hcap e.1 e.2 ?_
    simp only [hE, Finset.mem_filter, Finset.mem_univ, true_and] at he
    exact fun heq => he.2 (heq ▸ he.1)
  have hlhs : r * b * #(A ∪ B) ≤ ∑ i ∈ A, logb 2 (msgSize i) + ∑ i ∈ B, logb 2 (msgSize i) := by
    rw [Finset.card_union_of_disjoint hdisj]
    push_cast
    calc r * b * ((#A : ℝ) + #B) = ∑ i ∈ A, r * b + ∑ i ∈ B, r * b := by
          simp only [Finset.sum_const, nsmul_eq_mul]
          ring
      _ ≤ _ := add_le_add (Finset.sum_le_sum fun i _ => hri i) (Finset.sum_le_sum fun i _ => hri i)
  have hsideA := c.sum_logb_le_entropy_cut hc hd S
  have hsideB := c.sum_logb_le_entropy_cut hc hd (fun v => ¬ S v)
  have hcutA := c.entropy_cut_le S
  have hcutB := c.entropy_cut_le (fun v => ¬ S v)
  rw [hswap] at hcutB
  have hchain : r * b * #(A ∪ B) ≤ (∑ e ∈ E, (cap e.1 e.2 : ℝ)) * b := by
    rw [Finset.sum_mul]
    calc r * b * #(A ∪ B)
        ≤ ∑ i ∈ A, logb 2 (msgSize i) + ∑ i ∈ B, logb 2 (msgSize i) := hlhs
      _ ≤ ∑ e ∈ E, entropy (c.transcript e.1 e.2) + ∑ e ∈ E, entropy (c.transcript e.2 e.1) :=
          add_le_add (hsideA.trans hcutA) (hsideB.trans hcutB)
      _ = ∑ e ∈ E, (entropy (c.transcript e.1 e.2) + entropy (c.transcript e.2 e.1)) :=
          (Finset.sum_add_distrib).symm
      _ ≤ ∑ e ∈ E, (cap e.1 e.2 : ℝ) * b := hedge
  rw [hsplit]
  have := hchain
  nlinarith

/-- **Sparsity bound** for the coding rate: a cut that separates `k > 0` sessions bounds the rate by
its capacity divided by `k`. -/
theorem entropyCodingRate_le_cut (cap : V → V → ℕ) (src dst : M → V) (S : V → Prop)
    [DecidablePred S] {k : ℕ} (hk : 0 < k)
    (hcount : #{i | S (src i) ∧ ¬ S (dst i) ∨ ¬ S (src i) ∧ S (dst i)} = k) :
    entropyCodingRate cap src dst ≤
      ENNReal.ofReal ((∑ e ∈ univ.filter (fun e : V × V => S e.1 ∧ ¬ S e.2), (cap e.1 e.2 : ℝ)) / k) := by
  refine iSup₂_le fun r hr => ENNReal.ofReal_le_ofReal ?_
  have h := hr.cut_bound S
  rw [hcount] at h
  rw [le_div_iff₀ (by exact_mod_cast hk)]
  linarith

end NetCoding
