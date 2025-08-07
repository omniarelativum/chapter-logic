import Mathlib.Data.Rat.Defs
import Mathlib.Tactic.Linarith
import Mathlib.Data.Set.Finite

/--
If `f : ℕ → ℚ` has the property that every natural number (as a rational) is in its range,
and every value in its range is a natural number cast to rational,
then there does not exist `n` such that `f n = -1`.
-/
theorem no_neg_one_of_nat_range (f : ℕ → ℚ)
  (h_range : ∀ n : ℕ, ∃ k : ℕ, f n = (k : ℚ)) :
  ¬ ∃ n : ℕ, f n = -1 := by
  intro hex
  obtain ⟨n, hn⟩ := hex
  obtain ⟨k, hk⟩ := h_range n
  rw [hn] at hk
  -- Now we have -1 = (k : ℚ), which is impossible
  have : (k : ℚ) ≥ 0 := by positivity
  rw [←hk] at this
  linarith

/--
Alternative formulation:
If `f : ℕ → ℚ` is surjective onto the naturals
AND its range is exactly the naturals (as rationals),
then there does not exist `n` such that `f n = -1` and therefore f: ℕ → ℚ
is not bijective in this instance, since -1 (as an element of ℚ) must be in
the range of f for some n ∈ ℕ for f to be bijective onto ℚ.
-/
theorem no_neg_one_of_nat_surj_and_range (f : ℕ → ℚ)
  (h_range : ∀ n : ℕ, ∃ k : ℕ, f n = (k : ℚ)) :
  ¬ ∃ n : ℕ, f n = -1 := by
  -- We only need h_range for this proof
  exact no_neg_one_of_nat_range f h_range

/--
Corollary: No function f : ℕ → ℚ can be bijective if its range is exactly
the natural numbers (as rationals), since -1 ∈ ℚ but -1 ∉ range(f).
-/
theorem nat_to_rat_not_bijective (f : ℕ → ℚ)
  (h_range : ∀ n : ℕ, ∃ k : ℕ, f n = (k : ℚ)) :
  ¬ Function.Bijective f := by
  intro h_bij
  -- If f is bijective, it's surjective, so ∃ n, f n = -1
  have h_surj : Function.Surjective f := h_bij.2
  have : ∃ n : ℕ, f n = -1 := h_surj (-1)
  -- But this contradicts no_neg_one_of_nat_range
  exact no_neg_one_of_nat_range f h_range this

/--
For a function f: ℕ → ℚ, define the set D = {n ∈ ℕ : ∀ m ∈ ℕ, f(m) ≠ (n : ℚ)}.
If D = ∅, then f: ℕ → ℚ has the property that f is surjective onto the naturals
AND its range is exactly the naturals (as rationals),
then there does not exist `n` such that `f n = -1` and therefore f: ℕ → ℚ
is not bijective in this instance, since -1 (as an element of ℚ) must be in
the range of f for some n ∈ ℕ for f to be bijective onto ℚ.
-/
theorem no_neg_one_with_empty_D (f : ℕ → ℚ)
  (h_D_empty : ∀ n : ℕ, ∃ m : ℕ, f m = (n : ℚ))
  (h_range : ∀ m : ℕ, ∃ k : ℕ, f m = (k : ℚ)) :
  ¬ ∃ n : ℕ, f n = -1 := by
  exact no_neg_one_of_nat_range f h_range

/--
Alternative characterization: If D = ∅ (i.e., every natural number as a rational
is hit by f), then f is surjective onto the naturals.
-/
theorem empty_D_implies_surjective (f : ℕ → ℚ)
  (h_D_empty : ∀ n : ℕ, ∃ m : ℕ, f m = (n : ℚ)) :
  ∀ k : ℕ, ∃ n : ℕ, f n = (k : ℚ) := h_D_empty

/--
Main theorem with D characterization: For f: ℕ → ℚ, if
D = {n ∈ ℕ : ∀ m ∈ ℕ, f(m) ≠ (n : ℚ)} = ∅ and the range of f
consists exactly of natural numbers as rationals, then f cannot be bijective.
-/
theorem f_not_bijective_with_empty_D (f : ℕ → ℚ)
  (h_D_empty : ∀ n : ℕ, ∃ m : ℕ, f m = (n : ℚ))
  (h_range : ∀ m : ℕ, ∃ k : ℕ, f m = (k : ℚ)) :
  ¬ Function.Bijective f := by
  intro h_bij
  -- If f is bijective, it's surjective, so ∃ n, f n = -1
  have h_surj : Function.Surjective f := h_bij.2
  have : ∃ n : ℕ, f n = -1 := h_surj (-1)
  -- But this contradicts our theorem (we use both hypotheses via no_neg_one_of_nat_range)
  exact no_neg_one_of_nat_range f h_range this

/--
Case when D ≠ ∅: If D = {n ∈ ℕ : ∀ m ∈ ℕ, f(m) ≠ (n : ℚ)} ≠ ∅,
then we can take the least element of D to equal n*, and we can show
there exists no element m ∈ ℕ such that f(m) = (n* : ℚ), and therefore
f: ℕ → ℚ is also not a bijection for the case when D ≠ ∅.
-/
theorem f_not_bijective_with_nonempty_D (f : ℕ → ℚ)
  (h_range : ∀ m : ℕ, ∃ k : ℕ, f m = (k : ℚ))
  (h_D_nonempty : ∃ n : ℕ, ∀ m : ℕ, f m ≠ (n : ℚ)) :
  ¬ Function.Bijective f := by
  intro h_bij
  obtain ⟨n_star, hn_star⟩ := h_D_nonempty
  -- If f is bijective, it's surjective, so ∃ m, f m = (n_star : ℚ)
  have h_surj : Function.Surjective f := h_bij.2
  have : ∃ m : ℕ, f m = (n_star : ℚ) := h_surj (n_star : ℚ)
  obtain ⟨m, hm⟩ := this
  -- But this contradicts hn_star which says ∀ m, f m ≠ (n_star : ℚ)
  exact hn_star m hm

/--
Example construction: For any f: ℕ → ℚ with range exactly the naturals as rationals,
we can always find a natural number n* that is not in the range of f.
This shows that either D = ∅ (impossible for bijection due to -1) or
D ≠ ∅ (impossible for bijection due to missing n*).
-/
theorem f_nat_to_rat_never_bijective (f : ℕ → ℚ)
  (h_range : ∀ m : ℕ, ∃ k : ℕ, f m = (k : ℚ)) :
  ¬ Function.Bijective f := by
  -- Case analysis on whether D is empty or not
  by_cases h : ∀ n : ℕ, ∃ m : ℕ, f m = (n : ℚ)
  case pos =>
    -- D = ∅ case: use the -1 argument
    exact f_not_bijective_with_empty_D f h h_range
  case neg =>
    -- D ≠ ∅ case: use the missing n* argument
    push_neg at h
    exact f_not_bijective_with_nonempty_D f h_range h

/--
Complete characterization: Thus f: ℕ → ℚ can never be a bijection
in both cases of D = ∅ or D ≠ ∅, when the range of f consists
exactly of natural numbers as rationals.
-/
theorem complete_non_bijection_theorem (f : ℕ → ℚ)
  (h_range : ∀ m : ℕ, ∃ k : ℕ, f m = (k : ℚ)) :
  ¬ Function.Bijective f :=
f_nat_to_rat_never_bijective f h_range

/--
Explicit example when D ≠ ∅: Consider f(n) = (n+1 : ℚ) for all n ∈ ℕ.
Then 0 ∉ range(f), so n* = 0 demonstrates the non-bijection.
-/
example : ¬ Function.Bijective (fun n : ℕ => (n + 1 : ℚ)) := by
  have h_range : ∀ m : ℕ, ∃ k : ℕ, (m + 1 : ℚ) = (k : ℚ) := by
    intro m
    use m + 1
    simp
  have h_missing_zero : ∀ m : ℕ, (m + 1 : ℚ) ≠ (0 : ℚ) := by
    intro m
    simp
    linarith
  exact f_not_bijective_with_nonempty_D (fun n => (n + 1 : ℚ)) h_range ⟨0, h_missing_zero⟩
