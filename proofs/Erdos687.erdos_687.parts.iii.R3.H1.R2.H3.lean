import OMAReductions.R_Erdos687_erdos_687_parts_iii_R3_H1_R2
import Mathlib

/-! Prime extraction. The second difference of `ψ₁` at `n+1` with step `h` is a tent-weighted
sum of `Λ k` with weights in `[0, h]`, vanishing for `k ≤ n+1`. If no prime lies in `(n, n+2h]`
the sum is at most `h (ψ(M) - θ(M)) ≤ 2 h √M log M` with `M = n+1+2h`, which is below `h^2/4`
for large `n`. Hence there is a prime `p ∈ (n, n+2h]`, and `(p-n)^3 ≤ ⌊n^(33/50)⌋^3 ≤ n^2`. -/

namespace OMA.Erdos687PrimeExtract

open Finset Real

noncomputable def f (m : ℕ) : ℝ := ∑ k ∈ Finset.range m,
  (ArithmeticFunction.vonMangoldt k : ℝ) * ((m : ℝ) - k)

lemma f_eq {m M : ℕ} (hm : m ≤ M) :
    f m = ∑ k ∈ Finset.range M, (ArithmeticFunction.vonMangoldt k : ℝ) * max ((m : ℝ) - k) 0 := by
  unfold f
  rw [← Finset.sum_subset (Finset.range_mono hm)]
  · apply Finset.sum_congr rfl
    intro k hk
    have h1 := Finset.mem_range.1 hk
    have h2 : (k : ℝ) ≤ m := by exact_mod_cast h1.le
    rw [max_eq_left (by linarith)]
  · intro k _ hk'
    have h1 : m ≤ k := by simpa using hk'
    have h2 : (m : ℝ) ≤ k := by exact_mod_cast h1
    rw [max_eq_right (by linarith)]
    simp

lemma tent_le (x a hh : ℝ) (hh0 : 0 ≤ hh) :
    (a + 2 * hh - x) - 2 * max (a + hh - x) 0 + max (a - x) 0 ≤ hh := by
  rcases max_cases (a + hh - x) 0 with ⟨h1, h1'⟩ | ⟨h1, h1'⟩ <;>
  rcases max_cases (a - x) 0 with ⟨h2, h2'⟩ | ⟨h2, h2'⟩ <;>
  rw [h1, h2] <;> linarith

lemma tent_zero (x a hh : ℝ) (hh0 : 0 ≤ hh) (hx : x ≤ a) :
    (a + 2 * hh - x) - 2 * max (a + hh - x) 0 + max (a - x) 0 = 0 := by
  rw [max_eq_left (by linarith), max_eq_left (by linarith)]
  ring

lemma key (n h : ℕ) (hno : ∀ p : ℕ, p.Prime → n < p → n + 2 * h < p) :
    f (n + 1 + 2 * h) - 2 * f (n + 1 + h) + f (n + 1) ≤
      (h : ℝ) * (Chebyshev.psi ((n + 1 + 2 * h : ℕ) : ℝ) - Chebyshev.theta ((n + 1 + 2 * h : ℕ) : ℝ)) := by
  set M := n + 1 + 2 * h with hM
  have hh0 : (0 : ℝ) ≤ h := Nat.cast_nonneg h
  rw [f_eq (le_refl M), f_eq (m := n + 1 + h) (M := M) (by omega),
    f_eq (m := n + 1) (M := M) (by omega), Chebyshev.psi_sub_theta_eq_sum_not_prime,
    Nat.floor_natCast]
  have e1 : (∑ k ∈ Finset.range M, (ArithmeticFunction.vonMangoldt k : ℝ) * max ((M : ℝ) - k) 0)
      - 2 * (∑ k ∈ Finset.range M,
        (ArithmeticFunction.vonMangoldt k : ℝ) * max (((n + 1 + h : ℕ) : ℝ) - k) 0)
      + (∑ k ∈ Finset.range M,
        (ArithmeticFunction.vonMangoldt k : ℝ) * max (((n + 1 : ℕ) : ℝ) - k) 0)
      = ∑ k ∈ Finset.range M, (ArithmeticFunction.vonMangoldt k : ℝ) *
        (max ((M : ℝ) - k) 0 - 2 * max (((n + 1 + h : ℕ) : ℝ) - k) 0
          + max (((n + 1 : ℕ) : ℝ) - k) 0) := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro k _
    ring
  rw [e1]
  have e2 : ∀ k ∈ Finset.range M, (ArithmeticFunction.vonMangoldt k : ℝ) *
        (max ((M : ℝ) - k) 0 - 2 * max (((n + 1 + h : ℕ) : ℝ) - k) 0
          + max (((n + 1 : ℕ) : ℝ) - k) 0)
      ≤ if (k ∈ Finset.Ioc 0 M ∧ ¬ k.Prime) then (h : ℝ) * ArithmeticFunction.vonMangoldt k
        else 0 := by
    intro k hk
    have hkM : k < M := Finset.mem_range.1 hk
    have hkM' : (k : ℝ) ≤ M := by exact_mod_cast hkM.le
    have hL : (0 : ℝ) ≤ ArithmeticFunction.vonMangoldt k :=
      ArithmeticFunction.vonMangoldt_nonneg
    have hMc : (M : ℝ) = ((n : ℝ) + 1) + 2 * h := by rw [hM]; push_cast; ring
    have c1 : (((n + 1 + h : ℕ) : ℝ)) = ((n : ℝ) + 1) + h := by push_cast; ring
    have c2 : (((n + 1 : ℕ) : ℝ)) = (n : ℝ) + 1 := by push_cast; ring
    rw [max_eq_left (by linarith : (0 : ℝ) ≤ (M : ℝ) - k), c1, c2, hMc]
    have hrhs : (0 : ℝ) ≤ if (k ∈ Finset.Ioc 0 M ∧ ¬ k.Prime)
        then (h : ℝ) * ArithmeticFunction.vonMangoldt k else 0 := by
      split_ifs
      · exact mul_nonneg hh0 hL
      · exact le_refl _
    rcases Nat.eq_zero_or_pos k with hk0 | hk0
    · subst hk0
      simpa using hrhs
    by_cases hp : k.Prime
    · have hkn : k ≤ n := by
        by_contra hc
        have := hno k hp (by omega)
        omega
      have hkn' : (k : ℝ) ≤ (n : ℝ) + 1 := by
        have : (k : ℝ) ≤ n := by exact_mod_cast hkn
        linarith
      rw [tent_zero (k : ℝ) ((n : ℝ) + 1) h hh0 hkn']
      simpa using hrhs
    · rw [if_pos ⟨Finset.mem_Ioc.2 ⟨hk0, hkM.le⟩, hp⟩, mul_comm (h : ℝ)]
      exact mul_le_mul_of_nonneg_left (tent_le (k : ℝ) ((n : ℝ) + 1) h hh0) hL
  refine (Finset.sum_le_sum e2).trans ?_
  have e3 : (∑ k ∈ Finset.range M, if (k ∈ Finset.Ioc 0 M ∧ ¬ k.Prime)
        then (h : ℝ) * ArithmeticFunction.vonMangoldt k else 0)
      ≤ ∑ k ∈ Finset.range (M + 1), if (k ∈ Finset.Ioc 0 M ∧ ¬ k.Prime)
        then (h : ℝ) * ArithmeticFunction.vonMangoldt k else 0 := by
    apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (by omega))
    intro k _ _
    split_ifs
    · exact mul_nonneg hh0 ArithmeticFunction.vonMangoldt_nonneg
    · exact le_refl _
  refine e3.trans (le_of_eq ?_)
  rw [← Finset.sum_filter, Finset.mul_sum]
  apply Finset.sum_congr
  · ext k
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ioc]
    constructor
    · rintro ⟨_, h2, h3⟩
      exact ⟨h2, h3⟩
    · rintro ⟨h2, h3⟩
      exact ⟨by omega, h2, h3⟩
  · intro k _
    rfl

lemma floor_cube (n : ℕ) (hn : 1 ≤ n) : ⌊(n : ℝ) ^ (33 / 50 : ℝ)⌋₊ ^ 3 ≤ n ^ 2 := by
  have hx1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hx0 : (0 : ℝ) ≤ n := by linarith
  have h1 : (⌊(n : ℝ) ^ (33 / 50 : ℝ)⌋₊ : ℝ) ≤ (n : ℝ) ^ (33 / 50 : ℝ) :=
    Nat.floor_le (by positivity)
  have h2 : ((n : ℝ) ^ (33 / 50 : ℝ)) ^ 3 ≤ (n : ℝ) ^ 2 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hx0]
    calc (n : ℝ) ^ ((33 / 50 : ℝ) * ((3 : ℕ) : ℝ)) ≤ (n : ℝ) ^ (2 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hx1 (by norm_num)
      _ = (n : ℝ) ^ 2 := by norm_num
  have h3 : ((⌊(n : ℝ) ^ (33 / 50 : ℝ)⌋₊ : ℝ)) ^ 3 ≤ (n : ℝ) ^ 2 :=
    (pow_le_pow_left₀ (Nat.cast_nonneg _) h1 3).trans h2
  exact_mod_cast h3

lemma analytic (n h : ℕ) (hh : h = ⌊(n : ℝ) ^ (33 / 50 : ℝ)⌋₊ / 2)
    (hbig : (2000 : ℝ) ≤ (n : ℝ) ^ (1 / 10 : ℝ)) :
    2 * √((n + 1 + 2 * h : ℕ) : ℝ) * Real.log ((n + 1 + 2 * h : ℕ) : ℝ) ≤ (h : ℝ) / 4 := by
  have hn : 1 ≤ n := by
    rcases Nat.eq_zero_or_pos n with h0 | h0
    · subst h0
      rw [Nat.cast_zero, Real.zero_rpow (by norm_num)] at hbig
      linarith
    · exact h0
  set x : ℝ := (n : ℝ) with hx
  have hx1 : (1 : ℝ) ≤ x := by rw [hx]; exact_mod_cast hn
  have hx0 : (0 : ℝ) < x := by linarith
  set F := ⌊x ^ (33 / 50 : ℝ)⌋₊ with hF
  have hF1 : (F : ℝ) ≤ x ^ (33 / 50 : ℝ) := Nat.floor_le (by positivity)
  have hF2 : x ^ (33 / 50 : ℝ) < (F : ℝ) + 1 := Nat.lt_floor_add_one _
  have h2h : 2 * h ≤ F := by omega
  have hFh : F ≤ 2 * h + 1 := by omega
  have h2h' : 2 * (h : ℝ) ≤ F := by exact_mod_cast h2h
  have hFh' : (F : ℝ) ≤ 2 * h + 1 := by exact_mod_cast hFh
  have hle1 : x ^ (33 / 50 : ℝ) ≤ x := by
    calc x ^ (33 / 50 : ℝ) ≤ x ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hx1 (by norm_num)
      _ = x := Real.rpow_one x
  have hMc : (((n + 1 + 2 * h : ℕ) : ℝ)) = x + 1 + 2 * h := by push_cast; ring
  rw [hMc]
  have hM1 : (1 : ℝ) ≤ x + 1 + 2 * h := by linarith [Nat.cast_nonneg (α := ℝ) h]
  have hx11 : x ^ (11 / 10 : ℝ) = x * x ^ (1 / 10 : ℝ) := by
    rw [show (11 / 10 : ℝ) = 1 + 1 / 10 by norm_num, Real.rpow_add hx0, Real.rpow_one]
  have hM2 : x + 1 + 2 * h ≤ x ^ (11 / 10 : ℝ) := by
    rw [hx11]
    nlinarith
  have hsq : √(x + 1 + 2 * h) ≤ x ^ (11 / 20 : ℝ) := by
    calc √(x + 1 + 2 * h) ≤ √(x ^ (11 / 10 : ℝ)) := Real.sqrt_le_sqrt hM2
      _ = x ^ (11 / 20 : ℝ) := by
        rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hx0.le]
        norm_num
  have hlog : Real.log (x + 1 + 2 * h) ≤ 110 * x ^ (1 / 100 : ℝ) := by
    calc Real.log (x + 1 + 2 * h) ≤ Real.log (x ^ (11 / 10 : ℝ)) :=
          Real.log_le_log (by linarith) hM2
      _ = (11 / 10 : ℝ) * Real.log x := Real.log_rpow hx0 _
      _ ≤ (11 / 10 : ℝ) * (x ^ (1 / 100 : ℝ) / (1 / 100 : ℝ)) := by
          apply mul_le_mul_of_nonneg_left (Real.log_le_rpow_div hx0.le (by norm_num))
          norm_num
      _ = 110 * x ^ (1 / 100 : ℝ) := by ring
  have hlog0 : 0 ≤ Real.log (x + 1 + 2 * h) := Real.log_nonneg hM1
  have hp56 : x ^ (11 / 20 : ℝ) * x ^ (1 / 100 : ℝ) = x ^ (14 / 25 : ℝ) := by
    rw [← Real.rpow_add hx0]
    norm_num
  have hp66 : x ^ (33 / 50 : ℝ) = x ^ (14 / 25 : ℝ) * x ^ (1 / 10 : ℝ) := by
    rw [← Real.rpow_add hx0]
    norm_num
  have hy1 : (1 : ℝ) ≤ x ^ (14 / 25 : ℝ) := Real.one_le_rpow hx1 (by norm_num)
  have hy0 : (0 : ℝ) ≤ x ^ (11 / 20 : ℝ) := by positivity
  have hmain : 2 * √(x + 1 + 2 * h) * Real.log (x + 1 + 2 * h)
      ≤ 220 * x ^ (14 / 25 : ℝ) := by
    calc 2 * √(x + 1 + 2 * h) * Real.log (x + 1 + 2 * h)
        ≤ 2 * x ^ (11 / 20 : ℝ) * Real.log (x + 1 + 2 * h) := by
          apply mul_le_mul_of_nonneg_right _ hlog0
          linarith
      _ ≤ 2 * x ^ (11 / 20 : ℝ) * (110 * x ^ (1 / 100 : ℝ)) := by
          apply mul_le_mul_of_nonneg_left hlog
          linarith
      _ = 220 * (x ^ (11 / 20 : ℝ) * x ^ (1 / 100 : ℝ)) := by ring
      _ = 220 * x ^ (14 / 25 : ℝ) := by rw [hp56]
  have h66 : 2000 * x ^ (14 / 25 : ℝ) ≤ x ^ (33 / 50 : ℝ) := by
    rw [hp66]
    nlinarith
  linarith

end OMA.Erdos687PrimeExtract

open OMA.Erdos687PrimeExtract in
theorem OMA.solution : OMA.R_Erdos687_erdos_687_parts_iii_R3_H1_R2.H3 := by
  have ht := ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 10)).comp
    tendsto_natCast_atTop_atTop).eventually (Filter.eventually_ge_atTop (2000 : ℝ))
  unfold OMA.R_Erdos687_erdos_687_parts_iii_R3_H1_R2.H3
  filter_upwards [ht] with n hbig
  change (2000 : ℝ) ≤ (n : ℝ) ^ (1 / 10 : ℝ) at hbig
  intro hlt
  obtain ⟨h, hh⟩ : ∃ h : ℕ, h = ⌊(n : ℝ) ^ (33 / 50 : ℝ)⌋₊ / 2 := ⟨_, rfl⟩
  have hlt' : (h : ℝ) ^ 2 / 4 < f (n + 1 + 2 * h) - 2 * f (n + 1 + h) + f (n + 1) := by
    rw [hh]
    exact hlt
  have hn : 1 ≤ n := by
    rcases Nat.eq_zero_or_pos n with h0 | h0
    · subst h0
      rw [Nat.cast_zero, Real.zero_rpow (by norm_num)] at hbig
      linarith
    · exact h0
  by_contra hcon
  have hno : ∀ p : ℕ, p.Prime → n < p → n + 2 * h < p := by
    intro p hp hnp
    by_contra hc
    apply hcon
    refine ⟨p, hp, hnp, ?_⟩
    have h1 : p - n ≤ ⌊(n : ℝ) ^ (33 / 50 : ℝ)⌋₊ := by omega
    exact (Nat.pow_le_pow_left h1 3).trans (floor_cube n hn)
  have h1 := key n h hno
  have h2 := Chebyshev.psi_sub_theta_le (x := ((n + 1 + 2 * h : ℕ) : ℝ))
    (by exact_mod_cast (by omega : 1 ≤ n + 1 + 2 * h))
  have h3 := analytic n h hh hbig
  have hh0 : (0 : ℝ) ≤ h := Nat.cast_nonneg h
  have h4 : (h : ℝ) * (Chebyshev.psi ((n + 1 + 2 * h : ℕ) : ℝ) -
      Chebyshev.theta ((n + 1 + 2 * h : ℕ) : ℝ)) ≤ (h : ℝ) * ((h : ℝ) / 4) :=
    mul_le_mul_of_nonneg_left (h2.trans h3) hh0
  nlinarith
