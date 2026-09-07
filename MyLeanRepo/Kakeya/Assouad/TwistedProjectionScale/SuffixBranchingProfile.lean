import MyLeanRepo.Kakeya.Assouad.TwistedProjectionScale.SuffixBranchingProfileStatement
import Mathlib.Tactic

/-!
# A uniformly large suffix of a branching profile

This proves the finite-sequence selection used in the spacing argument.  The
proof selects a global minimum of the cumulative excess over the target
dimension.  A tail estimate forces that minimum to occur before normalized
scale `1 - epsilon²`.
-/

noncomputable section

namespace Kakeya.Assouad

lemma suffixProfileCumulative_zero
    {N : ℕ}
    (a : Fin (N + 1) → ℝ)
    (t : Fin N → ℝ) :
    suffixProfileCumulative a t 0 = 0 := by
  simp [suffixProfileCumulative]

lemma suffixProfileCumulative_last
    {N : ℕ}
    (a : Fin (N + 1) → ℝ)
    (t : Fin N → ℝ) :
    suffixProfileCumulative a t (Fin.last N) =
      ∑ i : Fin N, t i * (a i.succ - a i.castSucc) := by
  simp [suffixProfileCumulative, Fin.val_last]

lemma suffixProfileCumulative_succ
    {N : ℕ}
    (a : Fin (N + 1) → ℝ)
    (t : Fin N → ℝ)
    (i : Fin N) :
    suffixProfileCumulative a t i.succ =
      suffixProfileCumulative a t i.castSucc +
        t i * (a i.succ - a i.castSucc) := by
  unfold suffixProfileCumulative
  have hsingle :
      (∑ q : Fin N,
          if q = i then
            t q * (a q.succ - a q.castSucc)
          else 0) =
        t i * (a i.succ - a i.castSucc) := by
    simp
  rw [← hsingle, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro q _
  by_cases hqi : q = i
  · subst q
    simp
  · by_cases hq : q.val < i.val
    · have hq' : q.val < i.val + 1 := by omega
      simp [hq, hq', hqi]
    · have hq_ge : i.val < q.val := by omega
      have hq' : ¬q.val < i.val + 1 := by omega
      simp [hq, hq', hqi]

private lemma profile_increment_pos
    {N : ℕ}
    {a : Fin (N + 1) → ℝ}
    (ha : ∀ i : Fin N, a i.castSucc < a i.succ)
    (i : Fin N) :
    0 < a i.succ - a i.castSucc := by
  linarith [ha i]

theorem suffix_branching_profile :
    SuffixBranchingProfileStatement := by
  intro N hN n d epsilon avgLow hd hdn hepsilon hepsilon_one hgap
    a t ha0 haN ha_strict ht htotal
  let excess : Fin (N + 1) → ℝ :=
    fun j => suffixProfileCumulative a t j - d * a j
  obtain ⟨q, _hq_mem, hq_min⟩ :=
    Finset.exists_min_image
      (Finset.univ : Finset (Fin (N + 1)))
      excess
      Finset.univ_nonempty
  have hq_le_zero : excess q ≤ 0 := by
    have hq0 := hq_min (0 : Fin (N + 1)) (Finset.mem_univ _)
    simpa [excess, suffixProfileCumulative_zero, ha0] using hq0
  let deficit : Fin (N + 1) → ℝ :=
    fun j => suffixProfileCumulative a t j - n * a j
  have hdeficit_antitone : Antitone deficit := by
    rw [Fin.antitone_iff_succ_le]
    intro i
    have hdelta_nonneg :
        0 ≤ a i.succ - a i.castSucc :=
      (profile_increment_pos ha_strict i).le
    have hcoefficient_nonpos : t i - n ≤ 0 := by
      linarith [(ht i).2]
    have hproduct_nonpos :
        (t i - n) * (a i.succ - a i.castSucc) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg
        hcoefficient_nonpos hdelta_nonneg
    dsimp only [deficit]
    rw [suffixProfileCumulative_succ]
    nlinarith
  have hlast_lower :
      avgLow ≤ suffixProfileCumulative a t (Fin.last N) := by
    rw [suffixProfileCumulative_last]
    exact htotal
  have hq_early : a q < 1 - epsilon ^ 2 := by
    by_contra hnot
    have haq : 1 - epsilon ^ 2 ≤ a q := le_of_not_gt hnot
    have hdeficit_tail :=
      hdeficit_antitone (Fin.le_last q)
    have htail :
        excess (Fin.last N) ≤
          excess q + (n - d) * (1 - a q) := by
      dsimp only [deficit] at hdeficit_tail
      dsimp only [excess]
      rw [haN] at hdeficit_tail ⊢
      nlinarith
    have hnd_nonneg : 0 ≤ n - d := by
      linarith
    have hscale :
        1 - a q ≤ epsilon ^ 2 := by
      linarith
    have hscaled :
        (n - d) * (1 - a q) ≤
          (n - d) * epsilon ^ 2 :=
      mul_le_mul_of_nonneg_left hscale hnd_nonneg
    have hlast_upper :
        excess (Fin.last N) ≤
          (n - d) * epsilon ^ 2 := by
      calc
        excess (Fin.last N)
            ≤ excess q + (n - d) * (1 - a q) := htail
        _ ≤ 0 + (n - d) * (1 - a q) := by
          gcongr
        _ ≤ (n - d) * epsilon ^ 2 := by
          simpa using hscaled
    have hlast_gap :
        avgLow - d ≤ excess (Fin.last N) := by
      dsimp only [excess]
      rw [haN]
      linarith
    linarith
  have hq_val : q.val < N := by
    by_contra hnot
    have hq_last : q = Fin.last N := by
      apply Fin.ext
      simp only [Fin.val_last]
      omega
    rw [hq_last, haN] at hq_early
    nlinarith [sq_pos_of_pos hepsilon]
  let k : Fin N := ⟨q.val, hq_val⟩
  have hk_cast : k.castSucc = q := by
    apply Fin.ext
    rfl
  refine ⟨k, ?_, ?_, ?_⟩
  · simpa [hk_cast] using hq_early
  · rw [hk_cast]
    dsimp only [excess] at hq_le_zero
    linarith
  · intro j hkj
    have hqj : excess q ≤ excess j :=
      hq_min j (Finset.mem_univ _)
    rw [show k.castSucc = q from hk_cast]
    dsimp only [excess] at hqj
    linarith

end Kakeya.Assouad
