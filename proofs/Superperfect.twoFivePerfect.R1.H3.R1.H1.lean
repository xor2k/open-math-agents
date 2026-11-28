import OMAReductions.R_Superperfect_twoFivePerfect_R1_H3_R1

-- Step Superperfect.twoFivePerfect.R1.H3.R1.H1: hypothesis H1 of reduction
-- Superperfect.twoFivePerfect.R1.H3.R1

/-! With `e + 1 = 4 j` the sum `σ(p^e)` factors as `(1+p)(1+p^2) T`, and `5 ∣ 1 + p^2`, so
`m = σ(p^e)/5` is a multiple of `1 + p`.
* `p` odd: write `m = 2^a m'` with `m'` odd; `σ(2^a) = 2^(a+1) - 1` divides `p^e`, so it is `p^b`,
  `b` is odd (mod `4`), hence `2^(a+1) ∣ p + 1 ∣ m`, contradicting `m'` odd.
* `p = 2`: `5 m = (4^j - 1)(4^j + 1)`; `j = 1` gives `m = 3`; for `j ≥ 2` a prime `q ∣ 4^j + 1`
  (so `q ≡ 1 mod 4`) divides `m`, and `σ(q^a)` cannot be a power of two. -/

namespace OMA.SuperperfectOrderFourH1

open ArithmeticFunction ArithmeticFunction.sigma

lemma geom4 (p : ℕ) : ∀ j : ℕ, ∑ i ∈ Finset.range (4 * j), p ^ i
    = (1 + p) * (1 + p ^ 2) * ∑ i ∈ Finset.range j, p ^ (4 * i) := by
  intro j
  induction j with
  | zero => simp
  | succ j ih =>
    have h : 4 * (j + 1) = 4 * j + 1 + 1 + 1 + 1 := by ring
    rw [h, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
      Finset.sum_range_succ, ih, Finset.sum_range_succ]
    ring

lemma geom2 (q : ℕ) : ∀ r : ℕ, ∑ i ∈ Finset.range (2 * r), q ^ i
    = (1 + q) * ∑ i ∈ Finset.range r, q ^ (2 * i) := by
  intro r
  induction r with
  | zero => simp
  | succ r ih =>
    have h : 2 * (r + 1) = 2 * r + 1 + 1 := by ring
    rw [h, Finset.sum_range_succ, Finset.sum_range_succ, ih, Finset.sum_range_succ]
    ring

lemma two_geom : ∀ n : ℕ, (∑ i ∈ Finset.range n, 2 ^ i) + 1 = 2 ^ n := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, pow_succ]
    omega

lemma oddpow (t : ℕ) : ∀ k : ℕ, ∃ Q : ℕ, Odd Q ∧
    (2 * t + 1) ^ (2 * k + 1) + 1 = (2 * t + 1 + 1) * Q := by
  intro k
  induction k with
  | zero => exact ⟨1, odd_one, by ring⟩
  | succ k ih =>
    obtain ⟨Q, hQ, hE⟩ := ih
    refine ⟨Q + (2 * t + 1) ^ (2 * k + 1) * (2 * t), ?_, ?_⟩
    · exact hQ.add_even (Even.mul_left (even_two_mul t) _)
    · calc (2 * t + 1) ^ (2 * (k + 1) + 1) + 1
          = ((2 * t + 1) ^ (2 * k + 1) + 1)
            + (2 * t + 1) ^ (2 * k + 1) * (4 * t * t + 4 * t) := by ring
        _ = (2 * t + 1 + 1) * Q + (2 * t + 1) ^ (2 * k + 1) * (4 * t * t + 4 * t) := by rw [hE]
        _ = (2 * t + 1 + 1) * (Q + (2 * t + 1) ^ (2 * k + 1) * (2 * t)) := by ring

/-- A prime `q ≡ 1 (mod 4)` dividing `m` prevents `σ(m)` from being a power of two. -/
lemma no_one_mod_four {q m E : ℕ} (hq : q.Prime) (hq4 : q % 4 = 1) (hm0 : m ≠ 0) (hqm : q ∣ m)
    (hs : σ 1 m = 2 ^ E) : False := by
  obtain ⟨a, m', hnd, hm⟩ := Nat.exists_eq_pow_mul_and_not_dvd hm0 q hq.ne_one
  have ha : a ≠ 0 := by
    rintro rfl
    rw [pow_zero, one_mul] at hm
    exact hnd (hm ▸ hqm)
  have hcop : Nat.Coprime (q ^ a) m' :=
    Nat.Coprime.pow_left a ((Nat.Prime.coprime_iff_not_dvd hq).mpr hnd)
  rw [hm, isMultiplicative_sigma.map_mul_of_coprime hcop, sigma_one_apply_prime_pow hq] at hs
  have hdvd : (∑ k ∈ Finset.range (a + 1), q ^ k) ∣ 2 ^ E := Dvd.intro _ hs
  obtain ⟨t, -, ht⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
  have hq1 : 1 < q := hq.one_lt
  obtain ⟨r, hr | hr⟩ := Nat.even_or_odd' a
  · -- a even: the sum is odd and bigger than one
    have hr0 : r ≠ 0 := by rintro rfl; exact ha (by simpa using hr)
    rw [hr, Finset.sum_range_succ, geom2] at ht
    have hbig : 1 < q ^ (2 * r) := Nat.one_lt_pow (by omega) hq1
    have hqodd : Odd q := Nat.odd_iff.mpr (by omega)
    have hpo : Odd (q ^ (2 * r)) := hqodd.pow
    have hev : Even ((1 + q) * ∑ i ∈ Finset.range r, q ^ (2 * i)) :=
      Even.mul_right (Nat.even_iff.mpr (by omega)) _
    have hodd : Odd (2 ^ t) := by rw [← ht]; exact hev.add_odd hpo
    rcases t with _ | t
    · rw [pow_zero] at ht; omega
    · rw [pow_succ] at hodd
      exact (Nat.not_even_iff_odd.mpr hodd) (even_two.mul_left _)
  · -- a odd: 1 + q divides a power of two
    have h2 : a + 1 = 2 * (r + 1) := by omega
    rw [h2, geom2] at ht
    have hd : (1 + q) ∣ 2 ^ t := Dvd.intro _ ht
    obtain ⟨s, -, hs2⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hd
    rcases s with _ | _ | s
    · rw [pow_zero] at hs2; omega
    · rw [zero_add, pow_one] at hs2; omega
    · have : (2 : ℕ) ^ (s + 1 + 1) = 4 * 2 ^ s := by ring
      omega

/-- The odd-prime case: the power of two in `m` gives a contradiction. -/
lemma odd_case {p t m e : ℕ} (hp : p.Prime) (hpt : p = 2 * t + 1) (hm0 : m ≠ 0)
    (hpm : (p + 1) ∣ m) (hs : σ 1 m = p ^ e) : False := by
  obtain ⟨a, m', hodd, hm⟩ := Nat.exists_eq_two_pow_mul_odd hm0
  have hcop : Nat.Coprime (2 ^ a) m' := Nat.Coprime.pow_left a (Nat.coprime_two_left.mpr hodd)
  have hs' := hs
  rw [hm, isMultiplicative_sigma.map_mul_of_coprime hcop,
    sigma_one_apply_prime_pow Nat.prime_two] at hs'
  have hdvd : (∑ k ∈ Finset.range (a + 1), 2 ^ k) ∣ p ^ e := Dvd.intro _ hs'
  obtain ⟨b, -, hb⟩ := (Nat.dvd_prime_pow hp).mp hdvd
  have hg := two_geom (a + 1)
  rw [hb] at hg
  -- hg : p ^ b + 1 = 2 ^ (a + 1)
  have h2m : 2 ∣ m := dvd_trans ⟨t + 1, by omega⟩ hpm
  have ha : a ≠ 0 := by
    rintro rfl
    rw [pow_zero, one_mul] at hm
    rw [hm] at h2m
    exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr h2m)
  obtain ⟨a', ha'⟩ : ∃ a', a = a' + 1 := ⟨a - 1, by omega⟩
  subst ha'
  have hpodd : Odd p := ⟨t, hpt⟩
  obtain ⟨r, hr | hr⟩ := Nat.even_or_odd' b
  · exfalso
    obtain ⟨w, hw⟩ := (hpodd.pow : Odd (p ^ r))
    have h1 : p ^ b = 4 * (w * w + w) + 1 := by
      rw [hr, pow_mul', hw]; ring
    have h3 : (2 : ℕ) ^ (a' + 1 + 1) = 4 * 2 ^ a' := by ring
    omega
  · obtain ⟨Q, hQ, hE⟩ := oddpow t r
    rw [← hpt, ← hr, hg] at hE
    have hc : Nat.Coprime (2 ^ (a' + 1 + 1)) Q :=
      Nat.Coprime.pow_left _ (Nat.coprime_two_left.mpr hQ)
    have hd1 : 2 ^ (a' + 1 + 1) ∣ p + 1 := hc.dvd_of_dvd_mul_right (by rw [← hE])
    have hd2 : 2 ^ (a' + 1) * 2 ∣ 2 ^ (a' + 1) * m' := by
      rw [← pow_succ, ← hm]; exact hd1.trans hpm
    have hd3 : 2 ∣ m' := Nat.dvd_of_mul_dvd_mul_left (by positivity) hd2
    exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr hd3)

/-- The case `p = 2`. -/
lemma two_case {j m e : ℕ} (he : e + 1 = 4 * j) (hm0 : m ≠ 0) (hN : 5 * m + 1 = 2 ^ (4 * j))
    (hs : σ 1 m = 2 ^ e) : False := by
  rcases j with _ | _ | j
  · omega
  · have hm3 : m = 3 := by norm_num at hN; omega
    have he3 : e = 3 := by omega
    subst hm3 he3
    have h3 : σ 1 (3 ^ 1) = ∑ k ∈ Finset.range (1 + 1), 3 ^ k :=
      sigma_one_apply_prime_pow Nat.prime_three
    rw [pow_one] at h3
    rw [h3] at hs
    norm_num [Finset.sum_range_succ] at hs
  · -- B = 4 ^ (j + 2) = 16 * X
    obtain ⟨X, hX⟩ : ∃ X, X = 4 ^ j := ⟨_, rfl⟩
    have hXpos : 0 < X := by rw [hX]; positivity
    have hB : (4 : ℕ) ^ (j + 1 + 1) = 16 * X := by rw [hX]; ring
    have hpow : (2 : ℕ) ^ (4 * (j + 1 + 1)) = (16 * X) * (16 * X) := by
      rw [← hB, ← pow_two, ← pow_mul]
      have : (4 : ℕ) = 2 ^ 2 := by norm_num
      rw [this, ← pow_mul]
      congr 1
      ring
    rw [hpow] at hN
    -- A = 16 X + 1
    have hA : 5 * m + (16 * X + 1) = (16 * X) * (16 * X + 1) := by
      have : (16 * X) * (16 * X + 1) = (16 * X) * (16 * X) + 16 * X := by ring
      omega
    have hAdvd : (16 * X + 1) ∣ 5 * m :=
      (Nat.dvd_add_left (dvd_refl _)).mp ⟨16 * X, by rw [hA]; ring⟩
    have key : ∃ q : ℕ, q.Prime ∧ q ∣ m ∧ q ∣ 16 * X + 1 := by
      by_cases h5 : 5 ∣ 16 * X + 1
      · obtain ⟨k, hk⟩ := h5
        have hk1 : k ≠ 1 := by rintro rfl; omega
        have hmk : m + k = (16 * X) * k := by
          rw [hk] at hA
          have : (16 * X) * (5 * k) = 5 * ((16 * X) * k) := by ring
          omega
        have hkm : k ∣ m := (Nat.dvd_add_left (dvd_refl _)).mp ⟨16 * X, by rw [hmk]; ring⟩
        refine ⟨k.minFac, Nat.minFac_prime hk1, (Nat.minFac_dvd k).trans hkm, ?_⟩
        exact (Nat.minFac_dvd k).trans ⟨5, by rw [hk]; ring⟩
      · have hne : 16 * X + 1 ≠ 1 := by omega
        have hqp := Nat.minFac_prime hne
        refine ⟨(16 * X + 1).minFac, hqp, ?_, Nat.minFac_dvd _⟩
        rcases (Nat.Prime.dvd_mul hqp).mp ((Nat.minFac_dvd _).trans hAdvd) with h | h
        · exfalso
          have := (Nat.prime_dvd_prime_iff_eq hqp Nat.prime_five).mp h
          exact h5 (this ▸ Nat.minFac_dvd _)
        · exact h
    obtain ⟨q, hq, hqm, hqA⟩ := key
    have hq2 : q ≠ 2 := by
      rintro rfl
      omega
    have hqodd : q % 2 = 1 := by
      rcases hq.eq_two_or_odd with h | h
      · exact absurd h hq2
      · exact h
    have : Fact q.Prime := ⟨hq⟩
    have hz : ((16 * X + 1 : ℕ) : ZMod q) = 0 := (ZMod.natCast_eq_zero_iff _ _).mpr hqA
    have hsq : ((2 : ZMod q) ^ (j + 1 + 1)) ^ 2 = -1 := by
      have h4 : ((2 : ZMod q) ^ (j + 1 + 1)) ^ 2 = ((4 ^ (j + 1 + 1) : ℕ) : ZMod q) := by
        push_cast
        rw [← pow_mul, mul_comm, pow_mul]
        norm_num
      rw [h4, hB]
      rw [Nat.cast_add, Nat.cast_one] at hz
      exact eq_neg_of_add_eq_zero_left hz
    have h43 : q % 4 ≠ 3 := ZMod.mod_four_ne_three_of_sq_eq_neg_one hsq
    exact no_one_mod_four hq (by omega) hm0 hqm hs

end OMA.SuperperfectOrderFourH1

open ArithmeticFunction ArithmeticFunction.sigma in
theorem OMA.solution : OMA.R_Superperfect_twoFivePerfect_R1_H3_R1.H1 := by
  intro p e hp hmod h4 hEq
  obtain ⟨j, hj⟩ := h4
  have hp5 : p % 5 = 2 ∨ p % 5 = 3 := by
    rcases hmod with h | h
    · left
      have := (ZMod.natCast_eq_natCast_iff' p 2 5).mp (by exact_mod_cast h)
      simpa using this
    · right
      have := (ZMod.natCast_eq_natCast_iff' p 3 5).mp (by exact_mod_cast h)
      simpa using this
  have h5 : (1 + p ^ 2) % 5 = 0 := by
    rcases hp5 with h | h <;> rw [Nat.add_mod, Nat.pow_mod, h]
  obtain ⟨c, hc⟩ := Nat.dvd_of_mod_eq_zero h5
  have hsum : σ 1 (p ^ e) = 5 * ((1 + p) * c * ∑ i ∈ Finset.range j, p ^ (4 * i)) := by
    rw [sigma_one_apply_prime_pow hp, hj, OMA.SuperperfectOrderFourH1.geom4, hc]
    ring
  have hdiv : σ 1 (p ^ e) / 5 = (1 + p) * c * ∑ i ∈ Finset.range j, p ^ (4 * i) := by
    rw [hsum]; exact Nat.mul_div_cancel_left _ (by norm_num)
  obtain ⟨m, hmdef⟩ : ∃ m, m = (1 + p) * c * ∑ i ∈ Finset.range j, p ^ (4 * i) := ⟨_, rfl⟩
  rw [hdiv, ← hmdef] at hEq
  rw [← hmdef] at hsum
  have hm0 : m ≠ 0 := by
    rintro rfl
    have hpos : 0 < p ^ e := pow_pos hp.pos e
    simp at hEq
    omega
  rcases hp.eq_two_or_odd' with h2 | hodd
  · subst h2
    rw [sigma_one_apply_prime_pow Nat.prime_two] at hsum
    have hg := OMA.SuperperfectOrderFourH1.two_geom (e + 1)
    rw [hsum, hj] at hg
    exact OMA.SuperperfectOrderFourH1.two_case hj hm0 hg hEq
  · obtain ⟨t, ht⟩ := hodd
    have hpm : (p + 1) ∣ m := by
      rw [hmdef, add_comm p 1, mul_assoc]
      exact Dvd.intro _ rfl
    exact OMA.SuperperfectOrderFourH1.odd_case hp ht hm0 hpm hEq
