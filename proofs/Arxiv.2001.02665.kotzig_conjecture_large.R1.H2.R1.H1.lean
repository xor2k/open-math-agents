import OMAReductions.R_Arxiv_2001_02665_kotzig_conjecture_large_R1_H2_R1

namespace OMA.KotzigAdmissibleLen

lemma choose_k (s : ℕ) (hs : 3475 ≤ s) :
    ∃ k, 0 < k ∧ k ≤ s ∧ s < k + 8340 ∧ k % 12 = 7 ∧ k % 695 = 0 :=
  ⟨s - (s - 3475) % 8340, by omega, by omega, by omega, by omega, by omega⟩

lemma count (n L k : ℕ) (hk : 0 < k) (hkL : k ≤ L) (hn : 800 * L ≤ n) :
    n / (6400 * k) ≤ (n / (800 * L)) * ((L + 1) / (k + 1)) := by
  have hL : 0 < L := by omega
  have ha : 1 ≤ n / (800 * L) := (Nat.one_le_div_iff (by omega)).2 hn
  have hb : 1 ≤ (L + 1) / (k + 1) := (Nat.one_le_div_iff (by omega)).2 (by omega)
  have h1 : n < (800 * L) * (n / (800 * L) + 1) := Nat.lt_mul_div_succ n (by omega)
  have h2 : L + 1 < (k + 1) * ((L + 1) / (k + 1) + 1) :=
    Nat.lt_mul_div_succ (L + 1) (by omega)
  generalize n / (800 * L) = a at *
  generalize (L + 1) / (k + 1) = b at *
  apply Nat.le_of_lt_succ
  rw [Nat.div_lt_iff_lt_mul (by omega)]
  have h3 : (b + 1) * (k + 1) ≤ 4 * (b * k) := by nlinarith [Nat.mul_le_mul hb hk]
  have h4 : (a + 1) * (800 * L) ≤ 1600 * (a * L) := by nlinarith [Nat.mul_le_mul ha hL]
  have h5 : a * L ≤ a * (4 * (b * k)) := Nat.mul_le_mul_left a (by rw [Nat.mul_comm] at h2; omega)
  nlinarith

end OMA.KotzigAdmissibleLen

theorem OMA.solution : OMA.R_Arxiv_2001_02665_kotzig_conjecture_large_R1_H2_R1.H1 := by
  unfold OMA.R_Arxiv_2001_02665_kotzig_conjecture_large_R1_H2_R1.H1
  refine Filter.eventually_atTop.2 ⟨2 ^ 576, fun n hn => ?_⟩
  intro L
  have ht : 576 ≤ Nat.log 2 n := Nat.le_log_of_pow_le (by norm_num) hn
  have hm : 24 ≤ Nat.sqrt (Nat.log 2 n) := Nat.le_sqrt.2 (by omega)
  have hmm : Nat.sqrt (Nat.log 2 n) * Nat.sqrt (Nat.log 2 n) ≤ Nat.log 2 n := Nat.sqrt_le _
  have hn0 : n ≠ 0 := by
    have h0 : 0 < 2 ^ 576 := Nat.pos_of_ne_zero (by positivity)
    exact (lt_of_lt_of_le h0 hn).ne'
  have h2t : 2 ^ Nat.log 2 n ≤ n := Nat.pow_log_le_self 2 hn0
  have hLdef : L = 2 ^ Nat.sqrt (Nat.log 2 n) := rfl
  generalize Nat.log 2 n = t at *
  generalize Nat.sqrt t = m at *
  have hmt : m + 10 ≤ t := by nlinarith
  have hpow : 2 ^ (m + 10) ≤ 2 ^ t := Nat.pow_le_pow_right (by norm_num) hmt
  have hnL : 800 * L ≤ n := by
    rw [pow_add] at hpow
    rw [hLdef]
    have : (2:ℕ) ^ 10 = 1024 := by norm_num
    omega
  have h24 : 2 ^ 24 ≤ L := by
    rw [hLdef]; exact Nat.pow_le_pow_right (by norm_num) hm
  have hs : 3475 ≤ Nat.sqrt L := Nat.le_sqrt.2 (by norm_num at h24; omega)
  obtain ⟨k, k0, kle, klt, k12, k695⟩ := OMA.KotzigAdmissibleLen.choose_k _ hs
  have hkL : k ≤ L := le_trans kle (Nat.sqrt_le_self L)
  exact ⟨k, k0, kle, klt, k12, Nat.dvd_of_mod_eq_zero k695,
    OMA.KotzigAdmissibleLen.count n L k k0 hkL hnL⟩
