import OMAReductions.R_LonelyRunnerConjecture_lonely_runner_conjecture_variants_tao_2017_R1_H1_R1_H2_R1

namespace OMA.LRSmoothPartH2

lemma key {P T a p : ℕ} (hpP : p ∣ P) (hpa : p ∣ a / Nat.gcd a (P ^ T)) :
    p ^ (T + 1) ∣ a := by
  have hd : Nat.gcd a (P ^ T) ∣ a := Nat.gcd_dvd_left _ _
  have hmul : ∀ j, p ^ j ∣ Nat.gcd a (P ^ T) → p ^ (j + 1) ∣ a := by
    intro j hj
    have h := Nat.mul_dvd_mul hj hpa
    rwa [Nat.mul_div_cancel' hd, ← pow_succ] at h
  have hind : ∀ j, j ≤ T → p ^ j ∣ Nat.gcd a (P ^ T) := by
    intro j
    induction j with
    | zero => intro _; simp
    | succ j ih =>
      intro hj
      exact Nat.dvd_gcd (hmul j (ih (by omega)))
        ((pow_dvd_pow p hj).trans (pow_dvd_pow_of_dvd hpP T))
  exact hmul T (hind T le_rfl)

lemma count (P T A : ℕ) :
    ((Finset.Icc 2 P).biUnion
      (fun q => (Finset.Ioc 0 A).filter (fun x => q ^ (T + 1) ∣ x))).card
      ≤ P * (A / 2 ^ (T + 1)) := by
  refine Finset.card_biUnion_le.trans ?_
  have h : ∀ q ∈ Finset.Icc 2 P,
      ((Finset.Ioc 0 A).filter (fun x => q ^ (T + 1) ∣ x)).card ≤ A / 2 ^ (T + 1) := by
    intro q hq
    rw [Nat.Ioc_filter_dvd_card_eq_div]
    exact Nat.div_le_div_left (Nat.pow_le_pow_left (Finset.mem_Icc.mp hq).1 _) (by positivity)
  refine (Finset.sum_le_card_nsmul _ _ _ h).trans ?_
  rw [smul_eq_mul, Nat.card_Icc]
  exact Nat.mul_le_mul_right _ (by omega)

end OMA.LRSmoothPartH2

open OMA.LRSmoothPartH2 in
theorem OMA.solution : OMA.R_LonelyRunnerConjecture_lonely_runner_conjecture_variants_tao_2017_R1_H1_R1_H2_R1.H2 := by
  classical
  intro P hP ε hε
  obtain ⟨T, hT⟩ := pow_unbounded_of_one_lt ((P : ℝ) / ε) one_lt_two
  have hPε : (P : ℝ) / 2 ^ (T + 1) ≤ ε := by
    rw [div_lt_iff₀ hε] at hT
    rw [div_le_iff₀ (by positivity)]
    have e : (2 : ℝ) ^ (T + 1) = 2 * 2 ^ T := by ring
    have h2 : (0 : ℝ) < 2 ^ T := by positivity
    nlinarith
  refine ⟨P ^ T, pow_pos hP T, fun A => ?_⟩
  refine ⟨(Finset.Icc 1 A).filter (fun a => P.Coprime (a / Nat.gcd a (P ^ T))),
    Finset.filter_subset _ _, fun a => Nat.gcd a (P ^ T), fun a => a / Nat.gcd a (P ^ T), ?_, ?_⟩
  · intro a ha
    obtain ⟨ha1, hcop⟩ := Finset.mem_filter.mp ha
    obtain ⟨h1, h2⟩ := Finset.mem_Icc.mp ha1
    have hg : 0 < Nat.gcd a (P ^ T) := Nat.gcd_pos_of_pos_left _ h1
    have hd : Nat.gcd a (P ^ T) ∣ a := Nat.gcd_dvd_left _ _
    exact ⟨(Nat.mul_div_cancel' hd).symm, hg,
      Nat.le_of_dvd (pow_pos hP T) (Nat.gcd_dvd_right _ _),
      Finset.mem_Icc.mpr ⟨Nat.div_pos (Nat.le_of_dvd h1 hd) hg, (Nat.div_le_self _ _).trans h2⟩,
      hcop⟩
  · have hsub : Finset.Icc 1 A \ (Finset.Icc 1 A).filter
          (fun a => P.Coprime (a / Nat.gcd a (P ^ T))) ⊆
        (Finset.Icc 2 P).biUnion
          (fun q => (Finset.Ioc 0 A).filter (fun x => q ^ (T + 1) ∣ x)) := by
      intro a ha
      obtain ⟨ha1, hn⟩ := Finset.mem_sdiff.mp ha
      have hnc : ¬ P.Coprime (a / Nat.gcd a (P ^ T)) := fun h =>
        hn (Finset.mem_filter.mpr ⟨ha1, h⟩)
      obtain ⟨p, hp, hpP, hpa⟩ := Nat.Prime.not_coprime_iff_dvd.mp hnc
      obtain ⟨h1, h2⟩ := Finset.mem_Icc.mp ha1
      exact Finset.mem_biUnion.mpr ⟨p, Finset.mem_Icc.mpr ⟨hp.two_le, Nat.le_of_dvd hP hpP⟩,
        Finset.mem_filter.mpr ⟨Finset.mem_Ioc.mpr ⟨h1, h2⟩, key hpP hpa⟩⟩
    have hc := (Finset.card_le_card hsub).trans (count P T A)
    have hcR : (((Finset.Icc 1 A \ (Finset.Icc 1 A).filter
          (fun a => P.Coprime (a / Nat.gcd a (P ^ T)))).card : ℕ) : ℝ)
        ≤ (P : ℝ) * ((A / 2 ^ (T + 1) : ℕ) : ℝ) := by exact_mod_cast hc
    have hdiv : ((A / 2 ^ (T + 1) : ℕ) : ℝ) ≤ (A : ℝ) / 2 ^ (T + 1) := by
      have := Nat.cast_div_le (α := ℝ) (m := A) (n := 2 ^ (T + 1))
      simpa using this
    calc _ ≤ (P : ℝ) * ((A / 2 ^ (T + 1) : ℕ) : ℝ) := hcR
      _ ≤ (P : ℝ) * ((A : ℝ) / 2 ^ (T + 1)) := mul_le_mul_of_nonneg_left hdiv (by positivity)
      _ = (P : ℝ) / 2 ^ (T + 1) * A := by ring
      _ ≤ ε * A := mul_le_mul_of_nonneg_right hPε (by positivity)
