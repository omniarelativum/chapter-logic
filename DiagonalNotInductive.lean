import Mathlib.Data.Nat.Basic
import Mathlib.Tactic.Use

-- Let Enumeration be a function ℕ → ℕ → Bool
def Enumeration := ℕ → ℕ → Bool

-- The diagonal constructed at step n
def diagonal (E : Enumeration) (n : ℕ) : ℕ → Option Bool :=
  fun i => if i ≤ n then some (!(E i i)) else none

-- Proposition P(n): The diagonal at step n exists as a mathematical object,
-- but is not proven to be outside the enumeration E.
def P (E : Enumeration) (n : ℕ) : Prop :=
  ∃ (d : ℕ → Option Bool),
    d = diagonal E n ∧
    (∃ m > n, ∀ i ≤ n, d i = some (!(E i i))) ∧
    (¬∃ (j : ℕ), d = some ∘ E j)

theorem diagonal_not_proven_outside (E : Enumeration) : ∀ n : ℕ, P E n := by
  intro n
  use diagonal E n
  constructor
  · -- d = diagonal E n
    rfl
  constructor
  · -- ∃ m > n, ∀ i ≤ n, d i = some (!(E i i))
    use n + 1
    constructor
    · exact Nat.lt_succ_self n
    · intro i hi
      simp only [diagonal]
      -- The condition is i ≤ n, so this is always true for hi
      rw [if_pos hi]
  · -- ¬ ∃ (j : ℕ), d = some ∘ E j
    -- Suppose for contradiction d = some ∘ E j for some j.
    rintro ⟨j, h_eq⟩
    -- For i = n+1, d (n+1) = none, but (some ∘ E j) (n+1) = some (E j (n+1)), so they can't be equal.
    have h_none : diagonal E n (n+1) = none := by
      simp only [diagonal]
      have hle : ¬ (n + 1) ≤ n := Nat.not_le_of_gt (Nat.lt_succ_self n)
      rw [if_neg hle]
    have h_some : (some ∘ E j) (n+1) = some (E j (n+1)) := rfl
    rw [h_eq] at h_none
    -- This gives none = some (E j (n+1)), a contradiction.
    contradiction
