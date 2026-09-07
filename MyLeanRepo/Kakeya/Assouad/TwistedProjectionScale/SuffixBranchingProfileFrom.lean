import MyLeanRepo.Kakeya.Assouad.TwistedProjectionScale.SuffixBranchingProfile
import MyLeanRepo.Kakeya.Assouad.TwistedProjectionScale.SuffixBranchingProfileFromStatement
import Mathlib.Tactic

/-!
# Restricted-minimum proof of the suffix profile
-/

noncomputable section

namespace Kakeya.Assouad

theorem suffix_branching_profile_from :
    SuffixBranchingProfileFromStatement := by
  intro N hN n d epsilon avgLow hd hdn
    hepsilon hepsilon_one a t ha0 haN
    ha_strict ht htotal start hgap
  let excess : Fin (N + 1) → ℝ := fun j =>
    suffixProfileCumulative a t j - d * a j
  let deficit : Fin (N + 1) → ℝ := fun j =>
    suffixProfileCumulative a t j - n * a j
  let allowed : Finset (Fin (N + 1)) :=
    Finset.univ.filter fun j =>
      start.val ≤ j.val
  have hstart_allowed :
      start.castSucc ∈ allowed := by
    simp [allowed]
  have hallowed_nonempty : allowed.Nonempty :=
    ⟨start.castSucc, hstart_allowed⟩
  obtain ⟨q, hq_allowed, hq_min⟩ :=
    Finset.exists_min_image
      allowed excess hallowed_nonempty
  have hstart_le_q :
      start.val ≤ q.val :=
    (Finset.mem_filter.mp hq_allowed).2
  have hdeficit_antitone :
      Antitone deficit := by
    rw [Fin.antitone_iff_succ_le]
    intro i
    have hdelta_nonneg :
        0 ≤ a i.succ - a i.castSucc := by
      linarith [ha_strict i]
    have hcoefficient_nonpos :
        t i - n ≤ 0 := by
      linarith [(ht i).2]
    have hproduct_nonpos :
        (t i - n) *
            (a i.succ - a i.castSucc) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg
        hcoefficient_nonpos hdelta_nonneg
    dsimp only [deficit]
    rw [suffixProfileCumulative_succ]
    nlinarith
  have hdeficit_start :
      deficit start.castSucc ≤ 0 := by
    have hzero :=
      hdeficit_antitone
        (Fin.zero_le start.castSucc)
    simpa [deficit,
      suffixProfileCumulative_zero, ha0]
      using hzero
  have hexcess_start :
      excess start.castSucc ≤
        (n - d) * a start.castSucc := by
    dsimp only [deficit] at hdeficit_start
    dsimp only [excess]
    linarith
  have hexcess_q :
      excess q ≤
        (n - d) * a start.castSucc := by
    have hq_le_start :=
      hq_min start.castSucc hstart_allowed
    exact hq_le_start.trans hexcess_start
  have hlast_lower :
      avgLow ≤
        suffixProfileCumulative
          a t (Fin.last N) := by
    rw [suffixProfileCumulative_last]
    exact htotal
  have hq_early :
      a q < 1 - epsilon ^ 2 := by
    by_contra hnot
    have haq :
        1 - epsilon ^ 2 ≤ a q :=
      le_of_not_gt hnot
    have hdeficit_tail :=
      hdeficit_antitone (Fin.le_last q)
    have htail :
        excess (Fin.last N) ≤
          excess q +
            (n - d) * (1 - a q) := by
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
      mul_le_mul_of_nonneg_left
        hscale hnd_nonneg
    have hlast_upper :
        excess (Fin.last N) ≤
          (n - d) *
            (a start.castSucc +
              epsilon ^ 2) := by
      calc
        excess (Fin.last N)
            ≤ excess q +
                (n - d) * (1 - a q) :=
          htail
        _ ≤
            (n - d) * a start.castSucc +
              (n - d) * epsilon ^ 2 := by
          gcongr
        _ =
            (n - d) *
              (a start.castSucc +
                epsilon ^ 2) := by ring
    have hlast_gap :
        avgLow - d ≤
          excess (Fin.last N) := by
      dsimp only [excess]
      rw [haN]
      linarith
    nlinarith
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
  refine ⟨k, ?_, ?_, ?_, ?_⟩
  · simpa [k] using hstart_le_q
  · simpa [hk_cast] using hq_early
  · rw [hk_cast]
    dsimp only [excess] at hexcess_q
    linarith
  · intro j hkj
    have hj_allowed : j ∈ allowed := by
      simp only [allowed, Finset.mem_filter,
        Finset.mem_univ, true_and]
      have hk_start :
          start.val ≤ k.val := by
        simpa [k] using hstart_le_q
      exact hk_start.trans hkj
    have hqj :
        excess q ≤ excess j :=
      hq_min j hj_allowed
    rw [show k.castSucc = q from hk_cast]
    dsimp only [excess] at hqj
    linarith

end Kakeya.Assouad
