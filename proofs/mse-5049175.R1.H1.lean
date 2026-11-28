import OMAReductions.R_mse_5049175_R1

-- Step mse-5049175.R1.H1: hypothesis H1 of reduction mse-5049175.R1

/-! Classical divisibilities of Faulhaber polynomials: roots at `0`, `-1` (always), at `-1/2`
(even index), and double roots at `0`, `-1` (odd index at least 3), combined with the explicit
factorisations of `f 1`, `f 2`, `f 3`. -/

namespace OMA.FaulhaberDvdH1

open Polynomial

/-- The unnormalised Faulhaber polynomial. -/
noncomputable def g (n : ℕ) : ℚ[X] :=
  (Polynomial.bernoulli (n + 1)).comp (X + 1) - C ((Polynomial.bernoulli (n + 1)).eval 0)

lemma f_eq (n : ℕ) : OMA.S_mse_5049175.f n = C (1 / ((n : ℚ) + 1)) * g n := by
  unfold OMA.S_mse_5049175.f g
  rw [smul_eq_C_mul]

lemma dvd_f {P : ℚ[X]} {n : ℕ} (h : P ∣ g n) : P ∣ OMA.S_mse_5049175.f n := by
  rw [f_eq]; exact dvd_mul_of_dvd_right h _

lemma g_eval_neg_one (n : ℕ) : (g n).eval (-1) = 0 := by
  simp [g]

lemma g_eval_zero (n : ℕ) (hn : 1 ≤ n) : (g n).eval 0 = 0 := by
  have h : n + 1 ≠ 1 := by omega
  simp [g, bernoulli_eq_bernoulli'_of_ne_one h]

lemma g_eval_half (n : ℕ) (hn : 2 ≤ n) (he : Even n) : (g n).eval (-(1 / 2)) = 0 := by
  have hodd : Odd (n + 1) := he.add_one
  have h0 : _root_.bernoulli (n + 1) = 0 := bernoulli_eq_zero_of_odd hodd (by omega)
  have h1 := Polynomial.bernoulli_eval_one_sub (n + 1) (1 / 2)
  rw [hodd.neg_one_pow] at h1
  have h2 : (1 : ℚ) - 1 / 2 = 1 / 2 := by norm_num
  rw [h2] at h1
  have h3 : (Polynomial.bernoulli (n + 1)).eval (1 / 2 : ℚ) = 0 := by linarith
  have h4 : (-(1 / 2) : ℚ) + 1 = 1 / 2 := by norm_num
  unfold g
  rw [eval_sub, eval_comp, eval_add, eval_X, eval_one, eval_C, h4, h3,
    Polynomial.bernoulli_eval_zero, h0, sub_zero]

lemma g_derivative (n : ℕ) :
    derivative (g n) = C ((n : ℚ) + 1) * (Polynomial.bernoulli n).comp (X + 1) := by
  unfold g
  rw [derivative_sub, derivative_C, sub_zero, derivative_comp,
    Polynomial.derivative_bernoulli_add_one]
  simp [mul_comp]

lemma g_derivative_eval_neg_one (n : ℕ) (hn : 3 ≤ n) (ho : Odd n) :
    (derivative (g n)).eval (-1) = 0 := by
  rw [g_derivative]
  simp [bernoulli_eq_zero_of_odd ho (by omega)]

lemma g_derivative_eval_zero (n : ℕ) (hn : 3 ≤ n) (ho : Odd n) :
    (derivative (g n)).eval 0 = 0 := by
  rw [g_derivative]
  simp [bernoulli'_eq_zero_of_odd ho (by omega)]

lemma sq_dvd_of_double_root {p : ℚ[X]} {a : ℚ} (h0 : p.eval a = 0)
    (h1 : (derivative p).eval a = 0) : (X - C a) ^ 2 ∣ p := by
  obtain ⟨q, rfl⟩ := dvd_iff_isRoot.2 (show IsRoot p a from h0)
  have hq : q.eval a = 0 := by simpa using h1
  obtain ⟨r, rfl⟩ := dvd_iff_isRoot.2 (show IsRoot q a from hq)
  exact ⟨r, by ring⟩

lemma cop (a b : ℚ) (h : a ≠ b) : IsCoprime (X - C a : ℚ[X]) (X - C b) :=
  isCoprime_X_sub_C_of_isUnit_sub (sub_ne_zero.2 h).isUnit

lemma bern3 : _root_.bernoulli 3 = 0 := bernoulli_eq_zero_of_odd (by decide) (by norm_num)

lemma bern4 : _root_.bernoulli 4 = -1 / 30 := by
  rw [bernoulli_eq_bernoulli'_of_ne_one (by norm_num), bernoulli'_four]

lemma f1_eq : OMA.S_mse_5049175.f 1 = C (1 / 2 : ℚ) * ((X - C 0) * (X - C (-1))) := by
  apply Polynomial.funext
  intro r
  simp [OMA.S_mse_5049175.f, Polynomial.bernoulli, Finset.sum_range_succ, Nat.choose]
  ring

lemma f2_eq : OMA.S_mse_5049175.f 2 =
    C (1 / 3 : ℚ) * ((X - C 0) * (X - C (-1)) * (X - C (-(1 / 2)))) := by
  apply Polynomial.funext
  intro r
  simp [OMA.S_mse_5049175.f, Polynomial.bernoulli, Finset.sum_range_succ, Nat.choose, bern3]
  ring

lemma f3_eq : OMA.S_mse_5049175.f 3 =
    C (1 / 4 : ℚ) * ((X - C 0) ^ 2 * (X - C (-1)) ^ 2) := by
  apply Polynomial.funext
  intro r
  simp [OMA.S_mse_5049175.f, Polynomial.bernoulli, Finset.sum_range_succ, Nat.choose, bern3,
    bern4]
  ring

lemma unit_mul_dvd {u : ℚ} (hu : u ≠ 0) {P Q : ℚ[X]} (h : P ∣ Q) : C u * P ∣ Q :=
  (isUnit_C.2 hu.isUnit).mul_left_dvd.2 h

end OMA.FaulhaberDvdH1

open Polynomial OMA.FaulhaberDvdH1 in
theorem OMA.solution : OMA.R_mse_5049175_R1.H1 := by
  refine ⟨fun n hn => ?_, fun n hn he => ?_, fun n hn ho => ?_⟩
  · rw [f1_eq]
    refine unit_mul_dvd (by norm_num) (dvd_f ?_)
    exact (cop 0 (-1) (by norm_num)).mul_dvd
      (dvd_iff_isRoot.2 (g_eval_zero n hn)) (dvd_iff_isRoot.2 (g_eval_neg_one n))
  · rw [f2_eq]
    refine unit_mul_dvd (by norm_num) (dvd_f ?_)
    refine IsCoprime.mul_dvd ?_ ?_ (dvd_iff_isRoot.2 (g_eval_half n hn he))
    · exact IsCoprime.mul_left (cop 0 (-(1 / 2)) (by norm_num))
        (cop (-1) (-(1 / 2)) (by norm_num))
    · exact (cop 0 (-1) (by norm_num)).mul_dvd
        (dvd_iff_isRoot.2 (g_eval_zero n (by omega))) (dvd_iff_isRoot.2 (g_eval_neg_one n))
  · rw [f3_eq]
    refine unit_mul_dvd (by norm_num) (dvd_f ?_)
    exact ((cop 0 (-1) (by norm_num)).pow).mul_dvd
      (sq_dvd_of_double_root (g_eval_zero n (by omega)) (g_derivative_eval_zero n hn ho))
      (sq_dvd_of_double_root (g_eval_neg_one n) (g_derivative_eval_neg_one n hn ho))
