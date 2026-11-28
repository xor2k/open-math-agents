import OMAReductions.R_PerfectNumbers_odd_perfect_number_conjecture_R1_H3_R1_H2_R1

-- Step PerfectNumbers.odd_perfect_number_conjecture.R1.H3.R1.H2.R1.H1

/-! If every prime factor of `n` is at least `19` and there are at most `84` of them, then
`σ(n)/n ≤ ∏_{p ∣ n} p/(p-1) ≤ ∏_{p ∈ T} p/(p-1) < 2`, where `T` is the set of the `84` primes in
`[19, 467]`; so `n` is not perfect. -/

namespace OMA.OPNSmallOmegaH1

open Finset

/-- The `84` primes from `19` to `467`. -/
def L : List ℕ :=
  [19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89, 97, 101, 103, 107, 109,
   113, 127, 131, 137, 139, 149, 151, 157, 163, 167, 173, 179, 181, 191, 193, 197, 199, 211, 223,
   227, 229, 233, 239, 241, 251, 257, 263, 269, 271, 277, 281, 283, 293, 307, 311, 313, 317, 331,
   337, 347, 349, 353, 359, 367, 373, 379, 383, 389, 397, 401, 409, 419, 421, 431, 433, 439, 443,
   449, 457, 461, 463, 467]

def T : Finset ℕ := L.toFinset

def f (p : ℕ) : ℚ := (p : ℚ) / ((p : ℚ) - 1)

lemma card_T : T.card = 84 := by decide

lemma T_le {p : ℕ} (hp : p ∈ T) : 19 ≤ p ∧ p ≤ 467 := by
  simp only [T, L, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false] at hp
  omega

lemma mem_T {p : ℕ} (hp : p.Prime) (h19 : 19 ≤ p) (h467 : p ≤ 467) : p ∈ T := by
  have key : ∀ q < 468, 19 ≤ q → (q ∈ L ∨ q % 2 = 0 ∨ q % 3 = 0 ∨ q % 5 = 0 ∨ q % 7 = 0 ∨
      q % 11 = 0 ∨ q % 13 = 0 ∨ q % 17 = 0 ∨ q % 19 = 0) := by decide +kernel
  have hd : ∀ q : ℕ, 2 ≤ q → q < 19 → p % q = 0 → False := by
    intro q h2 h19' hq
    rcases (Nat.dvd_prime hp).mp (Nat.dvd_of_mod_eq_zero hq) with h | h <;> omega
  rw [T, List.mem_toFinset]
  rcases key p (by omega) h19 with h | h | h | h | h | h | h | h | h
  · exact h
  · exact (hd 2 (by norm_num) (by norm_num) h).elim
  · exact (hd 3 (by norm_num) (by norm_num) h).elim
  · exact (hd 5 (by norm_num) (by norm_num) h).elim
  · exact (hd 7 (by norm_num) (by norm_num) h).elim
  · exact (hd 11 (by norm_num) (by norm_num) h).elim
  · exact (hd 13 (by norm_num) (by norm_num) h).elim
  · exact (hd 17 (by norm_num) (by norm_num) h).elim
  · rcases (Nat.dvd_prime hp).mp (Nat.dvd_of_mod_eq_zero h) with h' | h'
    · omega
    · rw [← h']; decide

lemma prod_T : ∏ p ∈ T, f p < 2 := by
  have hnd : L.Nodup := by decide
  rw [T, List.prod_toFinset f hnd]
  simp only [L, List.map, List.prod_cons, List.prod_nil, f]
  norm_num

lemma f_ge {p : ℕ} (h2 : 2 ≤ p) (h : p ≤ 467) : (467 : ℚ) / 466 ≤ f p := by
  unfold f
  have h1 : (2 : ℚ) ≤ p := by exact_mod_cast h2
  have h3 : (p : ℚ) ≤ 467 := by exact_mod_cast h
  rw [div_le_div_iff₀ (by norm_num) (by linarith)]
  linarith

lemma f_le {p : ℕ} (h : 468 ≤ p) : f p ≤ (467 : ℚ) / 466 := by
  unfold f
  have h3 : (468 : ℚ) ≤ p := by exact_mod_cast h
  rw [div_le_div_iff₀ (by linarith) (by norm_num)]
  linarith

lemma f_nonneg {p : ℕ} (h2 : 2 ≤ p) : 0 ≤ f p := by
  unfold f
  have h1 : (2 : ℚ) ≤ p := by exact_mod_cast h2
  exact div_nonneg (by linarith) (by linarith)

lemma exchange (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime ∧ 19 ≤ p) (hc : S.card ≤ 84) :
    ∏ p ∈ S, f p ≤ ∏ p ∈ T, f p := by
  have e1 : ∏ p ∈ S, f p = (∏ p ∈ S \ T, f p) * ∏ p ∈ S ∩ T, f p :=
by
    rw [mul_comm]; exact (Finset.prod_inter_mul_prod_sdiff S T f).symm
  have e2 : ∏ p ∈ T, f p = (∏ p ∈ T \ S, f p) * ∏ p ∈ T ∩ S, f p :=
by
    rw [mul_comm]; exact (Finset.prod_inter_mul_prod_sdiff T S f).symm
  rw [e1, e2, Finset.inter_comm T S]
  have hcard : (S \ T).card ≤ (T \ S).card := by
    have a1 := Finset.card_sdiff_add_card_inter S T
    have a2 := Finset.card_sdiff_add_card_inter T S
    rw [Finset.inter_comm T S] at a2
    have := card_T
    omega
  have b1 : ∏ p ∈ S \ T, f p ≤ ((467 : ℚ) / 466) ^ (S \ T).card := by
    rw [← Finset.prod_const]
    apply Finset.prod_le_prod
    · intro p hp
      exact f_nonneg (by have := (hS p (Finset.mem_sdiff.mp hp).1).2; omega)
    · intro p hp
      obtain ⟨h1, h2⟩ := Finset.mem_sdiff.mp hp
      obtain ⟨hpr, h19⟩ := hS p h1
      apply f_le
      by_contra hlt
      exact h2 (mem_T hpr h19 (by omega))
  have b2 : ((467 : ℚ) / 466) ^ (T \ S).card ≤ ∏ p ∈ T \ S, f p := by
    rw [← Finset.prod_const]
    apply Finset.prod_le_prod
    · intro p hp
      norm_num
    · intro p hp
      obtain ⟨h1, h2⟩ := T_le (Finset.mem_sdiff.mp hp).1
      exact f_ge (by omega) h2
  have b3 : ((467 : ℚ) / 466) ^ (S \ T).card ≤ ((467 : ℚ) / 466) ^ (T \ S).card :=
    pow_le_pow_right₀ (by norm_num) hcard
  apply mul_le_mul_of_nonneg_right (b1.trans (b3.trans b2))
  apply Finset.prod_nonneg
  intro p hp
  exact f_nonneg (by have := (hS p (Finset.mem_inter.mp hp).1).2; omega)

lemma sigma_le {n : ℕ} (hn : n ≠ 0) :
    ((∑ d ∈ n.divisors, d : ℕ) : ℚ) ≤ (n : ℚ) * ∏ p ∈ n.primeFactors, f p := by
  have hn' : ((n : ℕ) : ℚ) = ∏ p ∈ n.primeFactors, ((p : ℚ) ^ (n.factorization p)) := by
    conv_lhs => rw [← Nat.prod_factorization_pow_eq_self hn]
    rw [Nat.prod_factorization_eq_prod_primeFactors]
    push_cast
    rfl
  rw [Nat.sum_divisors hn, hn', ← Finset.prod_mul_distrib]
  push_cast
  apply Finset.prod_le_prod
  · intro p hp
    positivity
  · intro p hp
    have hpr := Nat.prime_of_mem_primeFactors hp
    have h2 : (2 : ℚ) ≤ p := by exact_mod_cast hpr.two_le
    have hpos : (0 : ℚ) < (p : ℚ) - 1 := by linarith
    have hg := geom_sum_mul (p : ℚ) (n.factorization p + 1)
    unfold f
    rw [← mul_div_assoc, le_div_iff₀ hpos, hg, pow_succ]
    linarith

end OMA.OPNSmallOmegaH1

theorem OMA.solution : OMA.R_PerfectNumbers_odd_perfect_number_conjecture_R1_H3_R1_H2_R1.H1 := by
  intro n hperf _ _ hc
  by_contra hmin
  have hn0 : n ≠ 0 := hperf.2.ne'
  have hsum := (Nat.perfect_iff_sum_divisors_eq_two_mul hperf.2).mp hperf
  have hS : ∀ p ∈ n.primeFactors, p.Prime ∧ 19 ≤ p := by
    intro p hp
    have hpr := Nat.prime_of_mem_primeFactors hp
    have hd := Nat.dvd_of_mem_primeFactors hp
    have := Nat.minFac_le_of_dvd hpr.two_le hd
    exact ⟨hpr, by omega⟩
  have h1 := OMA.OPNSmallOmegaH1.sigma_le hn0
  have h2 := OMA.OPNSmallOmegaH1.exchange n.primeFactors hS hc
  have h3 := OMA.OPNSmallOmegaH1.prod_T
  rw [hsum] at h1
  push_cast at h1
  have hpos : (0 : ℚ) < n := by exact_mod_cast hperf.2
  have h4 : (n : ℚ) * ∏ p ∈ n.primeFactors, OMA.OPNSmallOmegaH1.f p < (n : ℚ) * 2 :=
    mul_lt_mul_of_pos_left (lt_of_le_of_lt h2 h3) hpos
  linarith
