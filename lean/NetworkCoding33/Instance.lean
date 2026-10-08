import NetworkCoding33.XorCode

/-!
# The 33-vertex instance and its transmission table

This transcribes the 3 × 2 table of `writeup/swap-dont-route.tex` (Appendix A).  Rows `a : Fin 3`
and columns `b : Fin 2` are numbered from 0 here; the writeup numbers them from 1.
-/

namespace NetCoding.Ex33

/-! ### Vertices -/

/-- The 33 vertices, numbered `0, …, 32`. -/
abbrev V := Fin 33

def O : V := 0
def H : V := 1
def G : V := 2
def Z : V := 3
/-- The collector of column `b`. -/
def C (b : Fin 2) : V := ⟨4 + b.val, by have := b.isLt; omega⟩
/-- The collector of row `a`. -/
def D (a : Fin 3) : V := ⟨6 + a.val, by have := a.isLt; omega⟩
def s (a : Fin 3) (b : Fin 2) : V := ⟨9 + 2 * a.val + b.val, by have := a.isLt; have := b.isLt; omega⟩
def p (a : Fin 3) (b : Fin 2) : V := ⟨15 + 2 * a.val + b.val, by have := a.isLt; have := b.isLt; omega⟩
def q (a : Fin 3) (b : Fin 2) : V := ⟨21 + 2 * a.val + b.val, by have := a.isLt; have := b.isLt; omega⟩
def t (a : Fin 3) (b : Fin 2) : V := ⟨27 + 2 * a.val + b.val, by have := a.isLt; have := b.isLt; omega⟩

def rows : List (Fin 3) := [0, 1, 2]
def cols : List (Fin 2) := [0, 1]
def cells : List (Fin 3 × Fin 2) := rows.flatMap fun a => cols.map fun b => (a, b)
/-- Ordered pairs of distinct rows, and of distinct columns. -/
def rowPairs : List (Fin 3 × Fin 3) :=
  rows.flatMap fun i => (rows.filter (· ≠ i)).map fun j => (i, j)
def colPairs : List (Fin 2 × Fin 2) :=
  cols.flatMap fun i => (cols.filter (· ≠ i)).map fun j => (i, j)
/-- Indices `(i, j, b)` of the carriers `α i j b`, and `(a, i, j)` of the carriers `β a i j`. -/
def alphas : List (Fin 3 × Fin 3 × Fin 2) :=
  cols.flatMap fun b => rowPairs.map fun (i, j) => (i, j, b)
def betas : List (Fin 3 × Fin 2 × Fin 2) :=
  rows.flatMap fun a => colPairs.map fun (i, j) => (a, i, j)

/-! ### Edges and capacities (the note's edge table, Section 3) -/

/-- The 91 undirected edges with their capacities. -/
def edges : List (V × V × ℕ) :=
  [(O, H, 12), (G, Z, 18)] ++
  (cells.flatMap fun (a, b) =>
    [(O, s a b, 2), (H, p a b, 2), (s a b, C b, 1), (C b, q a b, 1),
     (p a b, D a, 1), (D a, t a b, 1), (q a b, G, 3), (t a b, Z, 2)]) ++
  (cols.map fun b => (H, C b, 1)) ++
  (rows.map fun a => (D a, G, 1)) ++
  (cols.flatMap fun b => rowPairs.flatMap fun (i, j) =>
    [(s j b, p i b, 1), (p i b, q j b, 1)]) ++
  (rows.flatMap fun a => colPairs.flatMap fun (i, j) =>
    [(p a j, q a i, 1), (q a i, t a j, 1)])

/-- The capacity of the undirected edge `{u, v}` (zero if there is no such edge). -/
def cap (u v : V) : ℕ :=
  ((edges.filter fun e => (e.1 = u ∧ e.2.1 = v) ∨ (e.1 = v ∧ e.2.1 = u)).map
    fun e => e.2.2).sum

/-! ### Sessions -/

/-- The 30 unit sessions.  Sessions `0, …, 5` are `x a b` (number `2a + b`), from `s a b` to
`t a b`.  Sessions `6, …, 29` all go from `O` to `Z`: `y a b` (number `6 + 2a + b`), the twelve
carriers `α i j b` (`12, …, 23`) and the six carriers `β a i j` (`24, …, 29`). -/
abbrev Msg := Fin 30

def src (m : Msg) : V :=
  if h : m.val < 6 then s ⟨m.val / 2, by omega⟩ ⟨m.val % 2, by omega⟩ else O

def dst (m : Msg) : V :=
  if h : m.val < 6 then t ⟨m.val / 2, by omega⟩ ⟨m.val % 2, by omega⟩ else Z

/-! ### Linear forms -/

def xIdx (a : Fin 3) (b : Fin 2) : ℕ := 2 * a.val + b.val
def yIdx (a : Fin 3) (b : Fin 2) : ℕ := 6 + 2 * a.val + b.val
def αIdx (i j : Fin 3) (b : Fin 2) : ℕ :=
  12 + 6 * b.val + 2 * i.val + (if j.val < i.val then j.val else j.val - 1)
def βIdx (a : Fin 3) (i _j : Fin 2) : ℕ := 24 + 2 * a.val + i.val

def fx (a : Fin 3) (b : Fin 2) : ℕ := 2 ^ xIdx a b
def fy (a : Fin 3) (b : Fin 2) : ℕ := 2 ^ yIdx a b
def fα (i j : Fin 3) (b : Fin 2) : ℕ := 2 ^ αIdx i j b
def fβ (a : Fin 3) (i j : Fin 2) : ℕ := 2 ^ βIdx a i j
/-- `P b`, the parity of column `b`. -/
def fP (b : Fin 2) : ℕ := xorAll (rows.map fun j => fx j b)
/-- What `O` sends to `H` for cell `(i, b)`: `y i b + Σ_{j ≠ i} α i j b`. -/
def fym (i : Fin 3) (b : Fin 2) : ℕ :=
  xorAll (fy i b :: (rows.filter (· ≠ i)).map fun j => fα i j b)
def fu (i : Fin 3) (b : Fin 2) : ℕ := fym i b ^^^ fP b
def fax (i j : Fin 3) (b : Fin 2) : ℕ := fα i j b ^^^ fx j b
def fw (a : Fin 3) (b : Fin 2) : ℕ := fx a b ^^^ fy a b
def fv (a : Fin 3) (i j : Fin 2) : ℕ := fβ a i j ^^^ fw a j
/-- `Q a`, the parity of row `a`. -/
def fQ (a : Fin 3) : ℕ := xorAll (cols.map fun j => fw a j)
def fF (a : Fin 3) (i : Fin 2) : ℕ :=
  xorAll (fx a i :: (cols.filter (· ≠ i)).map fun j => fv a i j)
def fFQ (a : Fin 3) (i : Fin 2) : ℕ := fF a i ^^^ fQ a

/-! ### The transmission table (Section 3 of the note) -/

/-- The forms that `p a b` holds and combines into `w a b`: `u a b` and `α a j b + x j b`. -/
def wOps (a : Fin 3) (b : Fin 2) : List ℕ :=
  fu a b :: (rows.filter (· ≠ a)).map fun j => fax a j b

def send (u v : V) (ops : List ℕ) : Instr V := ⟨u, v, ops⟩

/-- The note's transmission table, row by row: 149 one-bit transmissions.  Each instruction lists
the forms its sender combines; `wellFormed` checks that the sender holds them. -/
def program : List (Instr V) :=
  -- 1. α i j b : O → s j b
  (alphas.map fun (i, j, b) => send O (s j b) [fα i j b]) ++
  -- 2. x a b : s a b → C b → q a b
  (cells.flatMap fun (a, b) => [send (s a b) (C b) [fx a b], send (C b) (q a b) [fx a b]]) ++
  -- 3. P b : C b → H
  (cols.map fun b => send (C b) H (rows.map fun j => fx j b)) ++
  -- 4. y i b + Σ_{j ≠ i} α i j b : O → H
  (cells.map fun (i, b) => send O H (fy i b :: (rows.filter (· ≠ i)).map fun j => fα i j b)) ++
  -- 5. u i b : H → p i b
  (cells.map fun (i, b) => send H (p i b) [fym i b, fP b]) ++
  -- 6. α i j b + x j b : s j b → p i b → q j b
  (alphas.flatMap fun (i, j, b) =>
    [send (s j b) (p i b) [fα i j b, fx j b], send (p i b) (q j b) [fax i j b]]) ++
  -- 7. α i j b : q j b → G → Z  (q j b strips x j b)
  (alphas.flatMap fun (i, j, b) =>
    [send (q j b) G [fax i j b, fx j b], send G Z [fα i j b]]) ++
  -- 8. β a i j : O → H → p a j
  (betas.flatMap fun (a, i, j) => [send O H [fβ a i j], send H (p a j) [fβ a i j]]) ++
  -- 9. w a b : p a b → D a → t a b
  (cells.flatMap fun (a, b) => [send (p a b) (D a) (wOps a b), send (D a) (t a b) [fw a b]]) ++
  -- 10. v a i j = β a i j + w a j : p a j → q a i → t a j
  (betas.flatMap fun (a, i, j) =>
    [send (p a j) (q a i) (fβ a i j :: wOps a j), send (q a i) (t a j) [fv a i j]]) ++
  -- 11. β a i j : t a j → Z
  (betas.map fun (a, i, j) => send (t a j) Z [fv a i j, fw a j]) ++
  -- 12. Q a : D a → G
  (rows.map fun a => send (D a) G (cols.map fun j => fw a j)) ++
  -- 13. F a i : q a i → G
  (cells.map fun (a, i) =>
    send (q a i) G (fx a i :: (cols.filter (· ≠ i)).map fun j => fv a i j)) ++
  -- 14. F a i + Q a : G → Z
  (cells.map fun (a, i) => send G Z [fF a i, fQ a]) ++
  -- 15. y a i : Z → t a i
  (cells.map fun (a, i) =>
    send Z (t a i) (fFQ a i :: (cols.filter (· ≠ i)).map fun j => fβ a i j))

/-- How each sink recovers its bit: `x a b = w a b + y a b` at `t a b`;
`y a i = (F a i + Q a) + Σ_{j ≠ i} β a i j` at `Z`; the carriers arrive at `Z` in the clear. -/
def dec (m : Msg) : List ℕ :=
  if h : m.val < 6 then
    [fw ⟨m.val / 2, by omega⟩ ⟨m.val % 2, by omega⟩, fy ⟨m.val / 2, by omega⟩ ⟨m.val % 2, by omega⟩]
  else if h' : m.val < 12 then
    fFQ ⟨(m.val - 6) / 2, by omega⟩ ⟨(m.val - 6) % 2, by omega⟩ ::
      (cols.filter (· ≠ ⟨(m.val - 6) % 2, by omega⟩)).map
        fun j => fβ ⟨(m.val - 6) / 2, by omega⟩ ⟨(m.val - 6) % 2, by omega⟩ j
  else [2 ^ m.val]

/-! ### Message bits of the code (one bit per session) -/

def idx (j : Msg × Fin 1) : ℕ := j.1.val

lemma idx_injective : Function.Injective idx := by
  rintro ⟨m, f⟩ ⟨m', f'⟩ h
  exact Prod.ext (Fin.ext h) (Subsingleton.elim _ _)

def bits : List (Msg × Fin 1) := (List.finRange 30).map fun m => (m, 0)

lemma mem_bits (j : Msg × Fin 1) : j ∈ bits := by
  obtain ⟨m, f⟩ := j
  simp [bits, Subsingleton.elim f 0]

end NetCoding.Ex33
