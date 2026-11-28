import OMAReductions.R_oeis_a182519_R1
import Mathlib

/-!
Step oeis-a182519.R1.H1: if 2 ≤ p ≤ q and n (q - p) < p log p then q^n < p^(n+1).
Credit: @xor2k
With x = (q - p)/p we have q/p = 1 + x ≤ exp x, so (q/p)^n ≤ exp (n x) < exp (log p) = p,
hence q^n < p^n * p.
-/

namespace OMA.StepFiroozbakhtGap
end OMA.StepFiroozbakhtGap

theorem OMA.solution : OMA.R_oeis_a182519_R1.H1 := by
  intro n p q hp hpq h
  have hp0 : (0:ℝ) < p := by exact_mod_cast (by omega : 0 < p)
  have hqp : (p:ℝ) ≤ q := by exact_mod_cast hpq
  have hx0 : (0:ℝ) ≤ ((q:ℝ) - p) / p := div_nonneg (by linarith) hp0.le
  have hx : (q:ℝ) / p ≤ Real.exp (((q:ℝ) - p) / p) := by
    have := Real.add_one_le_exp (((q:ℝ) - p) / p)
    have e : ((q:ℝ) - p) / p + 1 = q / p := by field_simp; ring
    rw [e] at this
    exact this
  have hlt : (n:ℝ) * (((q:ℝ) - p) / p) < Real.log p := by
    rw [← mul_div_assoc, div_lt_iff₀ hp0]
    linarith [h]
  have hexp : Real.exp ((n:ℝ) * (((q:ℝ) - p) / p)) < p := by
    calc Real.exp ((n:ℝ) * (((q:ℝ) - p) / p)) < Real.exp (Real.log p) := Real.exp_lt_exp.mpr hlt
      _ = p := Real.exp_log hp0
  have hpow : ((q:ℝ) / p) ^ n ≤ Real.exp ((n:ℝ) * (((q:ℝ) - p) / p)) := by
    rw [Real.exp_nat_mul]
    exact pow_le_pow_left₀ (div_nonneg (by linarith) hp0.le) hx n
  have hq : (q:ℝ) ^ n = ((q:ℝ) / p) ^ n * (p:ℝ) ^ n := by
    rw [div_pow, div_mul_cancel₀]
    exact pow_ne_zero _ hp0.ne'
  have hreal : (q:ℝ) ^ n < (p:ℝ) ^ (n + 1) := by
    rw [hq, pow_succ]
    have hpn : (0:ℝ) < (p:ℝ) ^ n := pow_pos hp0 n
    calc ((q:ℝ) / p) ^ n * (p:ℝ) ^ n < p * (p:ℝ) ^ n :=
          mul_lt_mul_of_pos_right (lt_of_le_of_lt hpow hexp) hpn
      _ = (p:ℝ) ^ n * p := mul_comm _ _
  exact_mod_cast hreal
