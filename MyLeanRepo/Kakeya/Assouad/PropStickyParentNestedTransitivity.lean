import MyLeanRepo.Kakeya.Assouad.PropStickyStatements

/-! # Transitive closure of adjacent nested parent maps -/

noncomputable section

namespace Kakeya.Assouad

theorem parent_nested_of_adjacent
    {delta : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {scaleCount : ℕ}
    {scale : Fin scaleCount →
      Kakeya.Streamlined.AdmissibleScale delta}
    {C : ENNReal}
    (scaleData :
      ∀ coordinate,
        WZ2PaperScaleCoverData family (scale coordinate) C)
    (adjacent :
      ∀ level,
        ∀ hnext : level + 1 < scaleCount,
          ∀ first second : Fin family.card,
            (scaleData ⟨level + 1, hnext⟩).cover.parent first =
                (scaleData ⟨level + 1, hnext⟩).cover.parent second →
              (scaleData
                  ⟨level, Nat.lt_of_succ_lt hnext⟩).cover.parent first =
                (scaleData
                  ⟨level, Nat.lt_of_succ_lt hnext⟩).cover.parent second)
    (coarse fine : Fin scaleCount)
    (hlevels : coarse.val ≤ fine.val) :
    ∀ first second : Fin family.card,
      (scaleData fine).cover.parent first =
          (scaleData fine).cover.parent second →
        (scaleData coarse).cover.parent first =
          (scaleData coarse).cover.parent second := by
  intro first second hparent
  let predicate :
      ∀ level : ℕ, coarse.val ≤ level → Prop :=
    fun level _ =>
      ∀ hlevel : level < scaleCount,
        (scaleData ⟨level, hlevel⟩).cover.parent first =
            (scaleData ⟨level, hlevel⟩).cover.parent second →
          (scaleData coarse).cover.parent first =
            (scaleData coarse).cover.parent second
  have hbase : predicate coarse.val le_rfl := by
    intro hlevel hparent'
    have hindex :
        (⟨coarse.val, hlevel⟩ : Fin scaleCount) = coarse := by
      apply Fin.ext
      rfl
    rwa [hindex] at hparent'
  have hstep :
      ∀ level (hcoarseLevel : coarse.val ≤ level),
        predicate level hcoarseLevel →
          predicate (level + 1) (Nat.le.step hcoarseLevel) := by
    intro level hcoarseLevel ih hnext hparent'
    have hcurrent : level < scaleCount :=
      Nat.lt_of_succ_lt hnext
    have hcurrentParent :
        (scaleData ⟨level, hcurrent⟩).cover.parent first =
          (scaleData ⟨level, hcurrent⟩).cover.parent second :=
      adjacent level hnext first second hparent'
    exact ih hcurrent hcurrentParent
  have hresult :
      predicate fine.val hlevels :=
    Nat.le_induction hbase hstep fine.val hlevels
  exact hresult fine.isLt hparent

end Kakeya.Assouad

end
