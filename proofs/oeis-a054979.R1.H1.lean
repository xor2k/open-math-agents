import OMAReductions.R_oeis_a054979_R1
import Mathlib

/-!
Step oeis-a054979.R1.H1: every e-perfect number is divisible by 4.
Credit: @xor2k
If 4 does not divide k, the prime 2 has exponent at most 1 and contributes the ratio 1, a 2-adic count shows
at most one odd prime has exponent 2 (ratio at most 4/3), exponent 1 gives ratio 1, and exponent at least 3
gives ratio at most 1 + 1/(p(p-1)), whose product over odd numbers telescopes below 7/5; so the ratio
sigmaE(k)/k is at most 28/15 < 2.
-/

namespace OMA.StepEPerfFour

lemma S_one (p : ℕ) : ∑ b ∈ (1 : ℕ).divisors, p ^ b = p := by simp

lemma S_two (p : ℕ) : ∑ b ∈ (2 : ℕ).divisors, p ^ b = p + p ^ 2 := by
  rw [Nat.Prime.divisors Nat.prime_two]; simp

lemma S_bound (p a : ℕ) (hp : 2 ≤ p) (ha : 3 ≤ a) :
    ((∑ b ∈ a.divisors, p ^ b : ℕ) : ℚ) ≤ (p : ℚ) ^ a * (1 + 1 / ((p : ℚ) * ((p : ℚ) - 1))) := by
  obtain ⟨c, rfl⟩ : ∃ c, a = c + 3 := ⟨a - 3, by omega⟩
  have hp1 : (1 : ℚ) ≤ (p : ℚ) - 1 := by
    have : (2 : ℚ) ≤ p := by exact_mod_cast hp
    linarith
  have hp0 : (0 : ℚ) < p := by linarith
  rw [← Nat.cons_self_properDivisors (by omega), Finset.sum_cons]
  push_cast
  have hsub : (c + 3).properDivisors ⊆ Finset.range ((c + 3) / 2 + 1) := by
    intro b hb
    rw [Nat.mem_properDivisors] at hb
    obtain ⟨⟨d, hd⟩, hlt⟩ := hb
    rw [Finset.mem_range]
    rcases d with _ | _ | d
    · omega
    · omega
    · have : 2 * b ≤ c + 3 := by rw [hd]; nlinarith
      omega
  have h1 : ∑ i ∈ (c + 3).properDivisors, (p : ℚ) ^ i ≤ ∑ i ∈ Finset.range ((c + 3) / 2 + 1), (p : ℚ) ^ i :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub (fun i _ _ => by positivity)
  have h2 : (∑ i ∈ Finset.range ((c + 3) / 2 + 1), (p : ℚ) ^ i) * ((p : ℚ) - 1)
      = (p : ℚ) ^ ((c + 3) / 2 + 1) - 1 := geom_sum_mul _ _
  have h3 : (p : ℚ) ^ ((c + 3) / 2 + 1) ≤ (p : ℚ) ^ (c + 2) :=
    pow_le_pow_right₀ (by linarith) (by omega)
  have h4 : (∑ i ∈ Finset.range ((c + 3) / 2 + 1), (p : ℚ) ^ i) * ((p : ℚ) - 1) ≤ (p : ℚ) ^ (c + 2) := by
    rw [h2]; linarith
  have h5 : (p : ℚ) ^ (c + 3) * (1 + 1 / ((p : ℚ) * ((p : ℚ) - 1)))
      = (p : ℚ) ^ (c + 3) + (p : ℚ) ^ (c + 2) / ((p : ℚ) - 1) := by
    field_simp
    ring
  rw [h5]
  have h6 : ∑ i ∈ Finset.range ((c + 3) / 2 + 1), (p : ℚ) ^ i ≤ (p : ℚ) ^ (c + 2) / ((p : ℚ) - 1) := by
    rw [le_div_iff₀ (by linarith)]; exact h4
  linarith

lemma telescope (N : ℕ) :
    ∏ i ∈ Finset.range (N + 1), (1 + 1 / (((2 * i + 3 : ℕ) : ℚ) * (((2 * i + 3 : ℕ) : ℚ) - 1)))
      ≤ 7 / 5 * (1 - 1 / (4 * (N : ℚ) + 6)) := by
  induction N with
  | zero => norm_num
  | succ n ih =>
    rw [Finset.prod_range_succ]
    have hf : (0 : ℚ) ≤ 1 + 1 / (((2 * (n + 1) + 3 : ℕ) : ℚ) * (((2 * (n + 1) + 3 : ℕ) : ℚ) - 1)) := by
      push_cast
      have h : (0:ℚ) < (2*((n:ℚ)+1)+3)*(2*((n:ℚ)+1)+3-1) := by
        have : (0:ℚ) ≤ n := by positivity
        nlinarith
      exact add_nonneg zero_le_one (div_nonneg zero_le_one h.le)
    calc _ ≤ 7 / 5 * (1 - 1 / (4 * (n : ℚ) + 6)) *
          (1 + 1 / (((2 * (n + 1) + 3 : ℕ) : ℚ) * (((2 * (n + 1) + 3 : ℕ) : ℚ) - 1))) :=
          mul_le_mul_of_nonneg_right ih hf
      _ ≤ _ := by
        push_cast
        have hx : (0 : ℚ) ≤ n := by positivity
        have r : (2 * ((n : ℚ) + 1) + 3 - 1) = 2 * (n : ℚ) + 4 := by ring
        have r2 : (2 * ((n : ℚ) + 1) + 3) = 2 * (n : ℚ) + 5 := by ring
        have r3 : (4 * ((n : ℚ) + 1) + 6) = 4 * (n : ℚ) + 10 := by ring
        rw [r, r2, r3]
        have e1 : (4 * (n : ℚ) + 6) ≠ 0 := by positivity
        have e2 : (4 * (n : ℚ) + 10) ≠ 0 := by positivity
        have e3 : (2 * (n : ℚ) + 4) ≠ 0 := by positivity
        have e4 : (2 * (n : ℚ) + 5) ≠ 0 := by positivity
        have e5 : (2 * (n : ℚ) + 3) ≠ 0 := by positivity
        rw [← sub_nonneg]
        have key : 7 / 5 * (1 - 1 / (4 * (n : ℚ) + 10)) - 7 / 5 * (1 - 1 / (4 * (n : ℚ) + 6)) *
            (1 + 1 / ((2 * (n : ℚ) + 5) * (2 * (n : ℚ) + 4)))
            = 21 / (10 * ((2 * (n : ℚ) + 5) * (2 * (n : ℚ) + 3) * (2 * (n : ℚ) + 4))) := by
          field_simp
          ring
        rw [key]
        positivity

lemma prod_bound (U : Finset ℕ) (hU : ∀ p ∈ U, 3 ≤ p ∧ Odd p) :
    ∏ p ∈ U, (1 + 1 / ((p : ℚ) * ((p : ℚ) - 1))) ≤ 7 / 5 := by
  have hf1 : ∀ p : ℕ, 2 ≤ p → (1 : ℚ) ≤ 1 + 1 / ((p : ℚ) * ((p : ℚ) - 1)) := by
    intro p hp
    have : (2 : ℚ) ≤ p := by exact_mod_cast hp
    have : (0 : ℚ) < (p : ℚ) * ((p : ℚ) - 1) := by nlinarith
    have := div_nonneg zero_le_one this.le
    linarith
  set N := U.sup id
  set V : Finset ℕ := (Finset.range (N + 1)).image (fun i : ℕ => 2 * i + 3) with hV
  have hsub : U ⊆ V := by
    intro p hp
    obtain ⟨h3, ⟨j, hj⟩⟩ := hU p hp
    have hle : p ≤ N := Finset.le_sup (f := id) hp
    rw [Finset.mem_image]
    exact ⟨j - 1, Finset.mem_range.2 (by omega), by omega⟩
  have s1 : ∏ p ∈ U, (1 + 1 / ((p : ℚ) * ((p : ℚ) - 1)))
      ≤ ∏ p ∈ V, (1 + 1 / ((p : ℚ) * ((p : ℚ) - 1))) := by
    apply Finset.prod_le_prod_of_subset_of_one_le hsub
    · intro i hi
      have := hU i hi
      exact le_trans zero_le_one (hf1 i (by omega))
    · intro i hi _
      obtain ⟨j, _, rfl⟩ := Finset.mem_image.1 hi
      exact hf1 _ (by omega)
  have s2 : ∏ p ∈ V, (1 + 1 / ((p : ℚ) * ((p : ℚ) - 1)))
      = ∏ i ∈ Finset.range (N + 1), (1 + 1 / (((2 * i + 3 : ℕ) : ℚ) * (((2 * i + 3 : ℕ) : ℚ) - 1))) := by
    rw [hV, Finset.prod_image]
    intro x _ y _ h
    simp only at h
    omega
  have s3 := telescope N
  have s4 : (0 : ℚ) ≤ 1 / (4 * (N : ℚ) + 6) := by positivity
  rw [s2] at s1
  linarith

end OMA.StepEPerfFour

open OMA.StepEPerfFour in
theorem OMA.solution : OMA.R_oeis_a054979_R1.H1 := by
  intro k hk
  obtain ⟨hk0, hk⟩ := hk
  unfold OMA.S_oeis_a054979.sigmaE at hk
  by_contra h4
  have hkne : k ≠ 0 := hk0.ne'
  set F := k.primeFactors with hF
  set a := k.factorization with ha
  have ha2 : a 2 ≤ 1 := by
    by_contra h
    have h : 2 ≤ a 2 := by omega
    have := (pow_dvd_pow 2 h).trans (Nat.ordProj_dvd k 2)
    norm_num at this
    exact h4 this
  have hpos : ∀ p ∈ F, 1 ≤ a p := fun p hp => by
    have := Nat.mem_primeFactors.1 hp
    exact (Nat.Prime.dvd_iff_one_le_factorization this.1 hkne).1 this.2.1
  have hne2 : ∀ p ∈ F, 2 ≤ a p → p ≠ 2 := by
    rintro p hp h rfl
    omega
  have hS2 : ∀ r, a r = 2 → 2 ∣ ∑ b ∈ (a r).divisors, r ^ b := by
    intro r hr
    rw [hr, S_two]
    have := Nat.even_mul_succ_self r
    rw [show r + r ^ 2 = r * (r + 1) by ring]
    exact even_iff_two_dvd.mp this
  have hdvd : ∀ s ⊆ F, ∏ r ∈ s, ∑ b ∈ (a r).divisors, r ^ b ∣ 2 * k := fun s hs =>
    hk ▸ Finset.prod_dvd_prod_of_subset _ _ _ hs
  have hT : (F.filter (fun p => a p = 2)).card ≤ 1 := by
    rw [Finset.card_le_one]
    intro p hp q hq
    by_contra hpq
    rw [Finset.mem_filter] at hp hq
    have hpq2 : 2 * 2 ∣ (∑ b ∈ (a p).divisors, p ^ b) * ∑ b ∈ (a q).divisors, q ^ b :=
      mul_dvd_mul (hS2 p hp.2) (hS2 q hq.2)
    by_cases h2 : 2 ∣ k
    · have h2F : 2 ∈ F := Nat.mem_primeFactors.2 ⟨Nat.prime_two, h2, hkne⟩
      have ha2' : a 2 = 1 := le_antisymm ha2 (hpos 2 h2F)
      have hp2 : 2 ≠ p := fun h => by rw [← h] at hp; omega
      have hq2 : 2 ≠ q := fun h => by rw [← h] at hq; omega
      have h := hdvd {2, p, q} (by
        intro x hx
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl | rfl
        · exact h2F
        · exact hp.1
        · exact hq.1)
      rw [Finset.prod_insert (by simp [hp2, hq2]), Finset.prod_pair hpq, ha2', S_one] at h
      have : 2 * 4 ∣ 2 * k := (mul_dvd_mul_left 2 hpq2).trans h
      exact h4 (Nat.dvd_of_mul_dvd_mul_left two_pos this)
    · have h := hdvd {p, q} (by
        intro x hx
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl
        · exact hp.1
        · exact hq.1)
      rw [Finset.prod_pair hpq] at h
      have := hpq2.trans h
      omega
  have hkq : (k : ℚ) = ∏ p ∈ F, (p : ℚ) ^ (a p) := by
    conv_lhs => rw [← Nat.prod_factorization_pow_eq_self hkne]
    rw [Finsupp.prod, Nat.support_factorization]
    push_cast
    rfl
  have hσq : (2 : ℚ) * k = ∏ p ∈ F, ((∑ b ∈ (a p).divisors, p ^ b : ℕ) : ℚ) := by
    have := congrArg (fun x : ℕ => (x : ℚ)) hk
    simp only [Nat.cast_prod, Nat.cast_mul, Nat.cast_ofNat] at this
    exact this.symm
  have hR : (2 : ℚ) = ∏ p ∈ F, (((∑ b ∈ (a p).divisors, p ^ b : ℕ) : ℚ) / (p : ℚ) ^ (a p)) := by
    rw [Finset.prod_div_distrib, ← hσq, ← hkq]
    field_simp
  have hbound : ∀ p ∈ F, ((∑ b ∈ (a p).divisors, p ^ b : ℕ) : ℚ) / (p : ℚ) ^ (a p) ≤
      (if a p = 1 then 1 else if a p = 2 then 4 / 3 else 1 + 1 / ((p : ℚ) * ((p : ℚ) - 1))) := by
    intro p hp
    have hpp := (Nat.mem_primeFactors.1 hp).1
    have hp2 := hpp.two_le
    have hp0 : (0 : ℚ) < (p : ℚ) ^ (a p) := by
      have : (0 : ℚ) < p := by exact_mod_cast hpp.pos
      positivity
    split_ifs with h1 h2
    · rw [div_le_iff₀ hp0, h1, S_one]
      simp
    · have hp3 : 3 ≤ p := by
        have := hne2 p hp (by omega)
        omega
      rw [div_le_iff₀ hp0, h2, S_two]
      push_cast
      have : (3 : ℚ) ≤ p := by exact_mod_cast hp3
      nlinarith
    · rw [div_le_iff₀ hp0, mul_comm]
      exact S_bound p (a p) hp2 (by have := hpos p hp; omega)
  have hle : (2 : ℚ) ≤ ∏ p ∈ F,
      (if a p = 1 then 1 else if a p = 2 then 4 / 3 else 1 + 1 / ((p : ℚ) * ((p : ℚ) - 1))) := by
    rw [hR]
    exact Finset.prod_le_prod (fun p hp => by positivity) hbound
  rw [Finset.prod_ite, Finset.prod_ite] at hle
  simp only [Finset.prod_const_one, Finset.prod_const, one_mul] at hle
  have hc : ((F.filter (fun p => ¬ a p = 1)).filter (fun p => a p = 2)).card ≤ 1 := by
    refine le_trans (Finset.card_le_card ?_) hT
    intro x hx
    simp only [Finset.mem_filter] at hx ⊢
    exact ⟨hx.1.1, hx.2⟩
  have hpow : (4 / 3 : ℚ) ^ ((F.filter (fun p => ¬ a p = 1)).filter (fun p => a p = 2)).card ≤ 4 / 3 := by
    rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hc with h | h <;> rw [h] <;> norm_num
  have hprod := prod_bound ((F.filter (fun p => ¬ a p = 1)).filter (fun p => ¬ a p = 2)) (by
    intro p hp
    simp only [Finset.mem_filter] at hp
    have hpF := hp.1.1
    have hpp := (Nat.mem_primeFactors.1 hpF).1
    have h1 := hpos p hpF
    have hp2 : p ≠ 2 := hne2 p hpF (by omega)
    rcases hpp.eq_two_or_odd' with h | h
    · exact absurd h hp2
    · exact ⟨by have := hpp.two_le; omega, h⟩)
  have h0 : (0 : ℚ) ≤ ∏ p ∈ (F.filter (fun p => ¬ a p = 1)).filter (fun p => ¬ a p = 2),
      (1 + 1 / ((p : ℚ) * ((p : ℚ) - 1))) := by
    apply Finset.prod_nonneg
    intro p hp
    simp only [Finset.mem_filter] at hp
    have : (2 : ℚ) ≤ p := by exact_mod_cast (Nat.mem_primeFactors.1 hp.1.1).1.two_le
    have : (0 : ℚ) < (p : ℚ) * ((p : ℚ) - 1) := by nlinarith
    have := div_nonneg zero_le_one this.le
    linarith
  have h0' : (0 : ℚ) ≤ (4 / 3 : ℚ) ^ ((F.filter (fun p => ¬ a p = 1)).filter (fun p => a p = 2)).card := by
    positivity
  nlinarith [mul_le_mul hpow hprod h0 (by norm_num : (0 : ℚ) ≤ 4 / 3)]
