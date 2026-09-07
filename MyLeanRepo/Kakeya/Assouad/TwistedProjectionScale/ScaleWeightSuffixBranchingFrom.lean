import MyLeanRepo.Kakeya.Assouad.TwistedProjectionScale.BranchingProfile
import MyLeanRepo.Kakeya.Assouad.TwistedProjectionScale.SuffixBranchingProfileFrom

/-!
# Scale-weight suffix selection after a prescribed level
-/

noncomputable section

namespace Kakeya.Assouad

theorem scaleWeight_suffix_branching_from
    (levels : ℕ)
    (hlevels : 0 < levels)
    (n d epsilon avgLow : ℝ)
    (hd : 0 ≤ d)
    (hdn : d < n)
    (hepsilon : 0 < epsilon)
    (hepsilon_one : epsilon < 1)
    (t : Fin levels → ℝ)
    (ht : ∀ i, 0 ≤ t i ∧ t i ≤ n)
    (havg :
      avgLow ≤
        ∑ i : Fin levels,
          t i *
            (scaleWeight levels i.succ -
              scaleWeight levels i.castSucc))
    (start : Fin levels)
    (hgap :
      (n - d) *
          (epsilon ^ 2 +
            scaleWeight levels start.castSucc) <
        avgLow - d) :
    ∃ k : Fin levels,
      start.val ≤ k.val ∧
      scaleWeight levels k.castSucc <
          1 - epsilon ^ 2 ∧
      suffixProfileCumulative
          (scaleWeight levels) t k.castSucc ≤
        d * scaleWeight levels k.castSucc +
          (n - d) *
            scaleWeight levels start.castSucc ∧
      ∀ j : Fin (levels + 1),
        k.val ≤ j.val →
          d *
              (scaleWeight levels j -
                scaleWeight levels k.castSucc) ≤
            suffixProfileCumulative
                (scaleWeight levels) t j -
              suffixProfileCumulative
                (scaleWeight levels) t k.castSucc := by
  letI : NeZero levels := NeZero.of_pos hlevels
  exact
    suffix_branching_profile_from
      levels hlevels n d epsilon avgLow
      hd hdn hepsilon hepsilon_one
      (scaleWeight levels) t
      scaleWeight_zero scaleWeight_last
      (fun _ => scaleWeight_strictMono)
      ht havg start hgap

end Kakeya.Assouad
