import OMAReductions.R_Erdos22_erdos_22_variants_fox_loh_zhao_R1

/-! Take a vertex `v` lying in at most `2e/n < n/4` edges, delete its edges and join it to the
whole other side (at least `n/3` vertices). Cliques through `v` live on the other side apart
from `v`, so no `K4` and no one-sided triangle appears; independent sets lose at most `v`. -/

open SimpleGraph
open scoped Classical

namespace OMA.FLZStepH2

variable {n : ℕ}

/-- Rewire `v`: drop its edges, join it to the other side. -/
def newGraph (G : SimpleGraph (Fin n)) (side : Fin n → Bool) (v : Fin n) :
    SimpleGraph (Fin n) where
  Adj a b := (a ≠ v ∧ b ≠ v ∧ G.Adj a b) ∨ (a = v ∧ side b = !side v) ∨
    (b = v ∧ side a = !side v)
  symm := ⟨by
    intro a b h
    rcases h with ⟨h1, h2, h3⟩ | h | h
    · exact Or.inl ⟨h2, h1, h3.symm⟩
    · exact Or.inr (Or.inr h)
    · exact Or.inr (Or.inl h)⟩
  loopless := ⟨by
    intro a h
    rcases h with ⟨_, _, h3⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact G.loopless.irrefl a h3
    · subst h1; simp at h2
    · subst h1; simp at h2⟩

lemma adj_of_ne (G : SimpleGraph (Fin n)) (side : Fin n → Bool) (v : Fin n) {a b : Fin n}
    (ha : a ≠ v) (hb : b ≠ v) : (newGraph G side v).Adj a b ↔ G.Adj a b := by
  constructor
  · intro h
    rcases h with ⟨_, _, h3⟩ | ⟨h1, _⟩ | ⟨h1, _⟩
    · exact h3
    · exact absurd h1 ha
    · exact absurd h1 hb
  · intro h
    exact Or.inl ⟨ha, hb, h⟩

lemma adj_v (G : SimpleGraph (Fin n)) (side : Fin n → Bool) (v : Fin n) {b : Fin n}
    (h : (newGraph G side v).Adj v b) : side b = !side v := by
  rcases h with ⟨h1, _, _⟩ | ⟨_, h2⟩ | ⟨h1, h2⟩
  · exact absurd rfl h1
  · exact h2
  · subst h1; exact h2

lemma clique_erase (G : SimpleGraph (Fin n)) (side : Fin n → Bool) (v : Fin n)
    {s : Finset (Fin n)} (hs : (newGraph G side v).IsClique (s : Set (Fin n))) :
    G.IsClique ((s.erase v : Finset (Fin n)) : Set (Fin n)) := by
  intro a ha b hb hab
  have ha' := Finset.mem_erase.mp (Finset.mem_coe.mp ha)
  have hb' := Finset.mem_erase.mp (Finset.mem_coe.mp hb)
  exact (adj_of_ne G side v ha'.1 hb'.1).mp
    (hs (Finset.mem_coe.mpr ha'.2) (Finset.mem_coe.mpr hb'.2) hab)

lemma clique_of_notMem (G : SimpleGraph (Fin n)) (side : Fin n → Bool) (v : Fin n)
    {s : Finset (Fin n)} (hs : (newGraph G side v).IsClique (s : Set (Fin n)))
    (hv : v ∉ s) : G.IsClique (s : Set (Fin n)) := by
  intro a ha b hb hab
  have ha' : a ≠ v := fun h => hv (h ▸ Finset.mem_coe.mp ha)
  have hb' : b ≠ v := fun h => hv (h ▸ Finset.mem_coe.mp hb)
  exact (adj_of_ne G side v ha' hb').mp (hs ha hb hab)

lemma side_of_clique (G : SimpleGraph (Fin n)) (side : Fin n → Bool) (v : Fin n)
    {s : Finset (Fin n)} (hs : (newGraph G side v).IsClique (s : Set (Fin n)))
    (hv : v ∈ s) {w : Fin n} (hw : w ∈ s.erase v) : side w = !side v := by
  have hw' := Finset.mem_erase.mp hw
  exact adj_v G side v (hs (Finset.mem_coe.mpr hv) (Finset.mem_coe.mpr hw'.2)
    (fun h => hw'.1 h.symm))

lemma cliqueFree4 (G : SimpleGraph (Fin n)) (side : Fin n → Bool) (v : Fin n)
    (hfree : G.CliqueFree 4) (htri : ∀ b, G.CliqueFreeOn {w | side w = b} 3) :
    (newGraph G side v).CliqueFree 4 := by
  intro s hs
  by_cases hv : v ∈ s
  · refine htri (!side v) (t := s.erase v) ?_ ⟨clique_erase G side v hs.isClique, ?_⟩
    · intro w hw
      exact side_of_clique G side v hs.isClique hv (Finset.mem_coe.mp hw)
    · have := Finset.card_erase_add_one hv
      have := hs.card_eq
      omega
  · exact hfree s ⟨clique_of_notMem G side v hs.isClique hv, hs.card_eq⟩

lemma cliqueFreeOn3 (G : SimpleGraph (Fin n)) (side : Fin n → Bool) (v : Fin n)
    (htri : ∀ b, G.CliqueFreeOn {w | side w = b} 3) (b : Bool) :
    (newGraph G side v).CliqueFreeOn {w | side w = b} 3 := by
  intro t ht hs
  by_cases hv : v ∈ t
  · have h1 := Finset.card_erase_add_one hv
    have h2 := hs.card_eq
    have hpos : 0 < (t.erase v).card := by omega
    obtain ⟨w, hw⟩ := Finset.card_pos.mp hpos
    have hw1 := side_of_clique G side v hs.isClique hv hw
    have hw2 : side w = b := ht (Finset.mem_coe.mpr (Finset.mem_erase.mp hw).2)
    have hv2 : side v = b := ht (Finset.mem_coe.mpr hv)
    rw [hw2, hv2] at hw1
    simp at hw1
  · exact htri b ht ⟨clique_of_notMem G side v hs.isClique hv, hs.card_eq⟩

lemma indepNum_le (G : SimpleGraph (Fin n)) (side : Fin n → Bool) (v : Fin n) :
    (newGraph G side v).indepNum ≤ G.indepNum + 1 := by
  obtain ⟨s, hs⟩ := (newGraph G side v).exists_isNIndepSet_indepNum
  have hind : G.IsIndepSet ((s.erase v : Finset (Fin n)) : Set (Fin n)) := by
    intro a ha b hb hab hadj
    have ha' := Finset.mem_erase.mp (Finset.mem_coe.mp ha)
    have hb' := Finset.mem_erase.mp (Finset.mem_coe.mp hb)
    exact hs.isIndepSet (Finset.mem_coe.mpr ha'.2) (Finset.mem_coe.mpr hb'.2) hab
      ((adj_of_ne G side v ha'.1 hb'.1).mpr hadj)
  have h1 := hind.card_le_indepNum
  have h2 : s.card ≤ (s.erase v).card + 1 := by
    by_cases hv : v ∈ s
    · exact (Finset.card_erase_add_one hv).ge
    · rw [Finset.erase_eq_of_notMem hv]; omega
  have h3 := hs.card_eq
  omega

lemma edges_ge (G : SimpleGraph (Fin n)) (side : Fin n → Bool) (v : Fin n)
    [Fintype G.edgeSet] [Fintype (newGraph G side v).edgeSet] :
    G.edgeFinset.card + (Finset.univ.filter fun w => side w = !side v).card ≤
      (newGraph G side v).edgeFinset.card + (G.edgeFinset.filter fun e => v ∈ e).card := by
  have hsplit := Finset.card_filter_add_card_filter_not (s := G.edgeFinset) (fun e => v ∈ e)
  set A := G.edgeFinset.filter fun e => ¬ v ∈ e with hA
  set B := (Finset.univ.filter fun w => side w = !side v).image fun w => s(v, w) with hB
  have hBcard : B.card = (Finset.univ.filter fun w => side w = !side v).card := by
    rw [hB]
    apply Finset.card_image_of_injective
    intro a b hab
    exact Sym2.congr_right.mp hab
  have hdisj : Disjoint A B := by
    rw [Finset.disjoint_left]
    intro e heA heB
    rw [hA, Finset.mem_filter] at heA
    rw [hB, Finset.mem_image] at heB
    obtain ⟨w, _, rfl⟩ := heB
    exact heA.2 (Sym2.mem_mk_left v w)
  have hsub : A ∪ B ⊆ (newGraph G side v).edgeFinset := by
    intro e he
    rcases Finset.mem_union.mp he with heA | heB
    · rw [hA, Finset.mem_filter] at heA
      obtain ⟨h1, h2⟩ := heA
      induction e using Sym2.ind with
      | _ a b =>
        rw [mem_edgeFinset, mem_edgeSet] at h1 ⊢
        rw [Sym2.mem_iff, not_or] at h2
        exact Or.inl ⟨fun h => h2.1 h.symm, fun h => h2.2 h.symm, h1⟩
    · rw [hB, Finset.mem_image] at heB
      obtain ⟨w, hw, rfl⟩ := heB
      rw [mem_edgeFinset, mem_edgeSet]
      exact Or.inr (Or.inl ⟨rfl, (Finset.mem_filter.mp hw).2⟩)
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_union_of_disjoint hdisj, hBcard] at hcard
  omega

lemma exists_low (G : SimpleGraph (Fin n)) [Fintype G.edgeSet] (hn : 0 < n) :
    ∃ v : Fin n, n * (G.edgeFinset.filter fun e => v ∈ e).card ≤ 2 * G.edgeFinset.card := by
  have hcount : ∑ v : Fin n, (G.edgeFinset.filter fun e => v ∈ e).card =
      2 * G.edgeFinset.card := by
    have h := Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow
      (s := (Finset.univ : Finset (Fin n))) (t := G.edgeFinset)
      (r := fun (v : Fin n) (e : Sym2 (Fin n)) => v ∈ e)
    have h2 : ∀ e ∈ G.edgeFinset,
        ((Finset.univ : Finset (Fin n)).bipartiteBelow (fun v e => v ∈ e) e).card = 2 := by
      intro e he
      induction e using Sym2.ind with
      | _ a b =>
        rw [mem_edgeFinset, mem_edgeSet] at he
        have hne : a ≠ b := he.ne
        have : (Finset.univ : Finset (Fin n)).bipartiteBelow (fun v e => v ∈ e) s(a, b) =
            {a, b} := by
          ext x
          simp [Finset.bipartiteBelow, Sym2.mem_iff]
        rw [this, Finset.card_pair hne]
    rw [Finset.sum_congr rfl h2] at h
    simp only [Finset.sum_const, smul_eq_mul] at h
    rw [mul_comm]
    exact h
  have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  obtain ⟨v, _, hv⟩ := Finset.exists_le_of_sum_le
    (s := (Finset.univ : Finset (Fin n))) Finset.univ_nonempty
    (f := fun v => n * (G.edgeFinset.filter fun e => v ∈ e).card)
    (g := fun _ => 2 * G.edgeFinset.card) (by
      rw [← Finset.mul_sum, hcount]
      simp)
  exact ⟨v, hv⟩

end OMA.FLZStepH2

theorem OMA.solution : OMA.R_Erdos22_erdos_22_variants_fox_loh_zhao_R1.H2 := by
  intro n hn G side hfree htri hparts hedges
  obtain ⟨v, hv⟩ := OMA.FLZStepH2.exists_low G hn
  refine ⟨OMA.FLZStepH2.newGraph G side v, OMA.FLZStepH2.cliqueFree4 G side v hfree htri,
    OMA.FLZStepH2.cliqueFreeOn3 G side v htri, OMA.FLZStepH2.indepNum_le G side v, ?_⟩
  have h1 := OMA.FLZStepH2.edges_ge G side v
  have h2 := hparts (!side v)
  have h1' : (G.edgeFinset.card : ℝ) +
      ((Finset.univ.filter fun w => side w = !side v).card : ℝ) ≤
      ((OMA.FLZStepH2.newGraph G side v).edgeFinset.card : ℝ) +
        ((G.edgeFinset.filter fun e => v ∈ e).card : ℝ) := by exact_mod_cast h1
  have h2' : (n : ℝ) ≤ 3 * ((Finset.univ.filter fun w => side w = !side v).card : ℝ) := by
    exact_mod_cast h2
  have hv' : (n : ℝ) * ((G.edgeFinset.filter fun e => v ∈ e).card : ℝ) ≤
      2 * (G.edgeFinset.card : ℝ) := by exact_mod_cast hv
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hc : ((G.edgeFinset.filter fun e => v ∈ e).card : ℝ) ≤ (n : ℝ) / 4 := by
    by_contra hcon
    have hcon' := not_le.mp hcon
    nlinarith
  linarith
