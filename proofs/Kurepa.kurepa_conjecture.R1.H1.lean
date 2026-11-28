import OMAReductions.R_Kurepa_kurepa_conjecture_R1

-- Step Kurepa.kurepa_conjecture.R1.H1: hypothesis H1 of reduction Kurepa.kurepa_conjecture.R1

/-! A single pass `i = 3, 4, …, 50000` carrying the exact values `f = i!` and `s = !i`
(binary naturals, so the kernel uses its accelerated arithmetic) and testing `s % i` at each
step. The loop is proved correct against `Kurepa.left_factorial` and then evaluated by the
kernel. -/

namespace OMA.KurepaFiniteCheckH1

open Kurepa

/-- `loop k i f s`: with `f = i!` and `s = !i`, checks `!j % j ≠ 0` for `i ≤ j < i + k`. -/
def loop : ℕ → ℕ → ℕ → ℕ → Bool
  | 0, _, _, _ => true
  | k + 1, i, f, s =>
    cond (Nat.beq (s % i) 0) false (loop k (i + 1) (f * (i + 1)) (s + f))

lemma loop_spec : ∀ k i : ℕ, loop k i i.factorial (left_factorial i) = true →
    ∀ n, i ≤ n → n < i + k → left_factorial n % n ≠ 0 := by
  intro k
  induction k with
  | zero => intro i _ n h1 h2; omega
  | succ k ih =>
    intro i h n h1 h2
    rw [loop] at h
    cases hb : Nat.beq (left_factorial i % i) 0 with
    | true => rw [hb] at h; simp at h
    | false =>
      rw [hb] at h
      simp only [cond_false] at h
      rcases Nat.eq_or_lt_of_le h1 with rfl | h3
      · intro h0
        rw [h0] at hb
        simp at hb
      · have e1 : i.factorial * (i + 1) = (i + 1).factorial := by
          rw [Nat.factorial_succ, Nat.mul_comm]
        have e2 : left_factorial i + i.factorial = left_factorial (i + 1) := by
          unfold left_factorial
          rw [Finset.sum_range_succ]
        rw [e1, e2] at h
        exact ih (i + 1) h n h3 (by omega)

lemma run : loop 49998 3 6 4 = true := by decide +kernel

end OMA.KurepaFiniteCheckH1

theorem OMA.solution : OMA.R_Kurepa_kurepa_conjecture_R1.H1 := by
  intro n h1 h2
  have h : OMA.KurepaFiniteCheckH1.loop 49998 3 (Nat.factorial 3) (Kurepa.left_factorial 3) = true := by
    have e1 : Nat.factorial 3 = 6 := by decide
    have e2 : Kurepa.left_factorial 3 = 4 := by decide
    rw [e1, e2]
    exact OMA.KurepaFiniteCheckH1.run
  exact OMA.KurepaFiniteCheckH1.loop_spec 49998 3 h n h1 (by omega)
