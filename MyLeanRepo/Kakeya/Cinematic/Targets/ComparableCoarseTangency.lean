import MyLeanRepo.Kakeya.Cinematic.Section5.CoarseInputs

/-!
# Transfer tangency to a comparable coarse parent
-/

namespace Kakeya.Cinematic

theorem comparable_coarse_tangency :
    ComparableCoarseTangencyStatement := by
  intro hTangency K D comparison hK hD hcomparison
  rcases hTangency K D hK hD with ⟨C, hC, hgeometry⟩
  let expansion : ℝ := 2 * Real.sqrt comparison
  let tangency : ℝ :=
    comparison +
      6 * K * (comparison + 5) +
        C * expansion ^ 2 * (comparison + 5)
  have hcomparison_nonneg : 0 ≤ comparison := by linarith
  have hexpansion_sq_nonneg : 0 ≤ expansion ^ 2 := sq_nonneg expansion
  have hlarge_term :
      0 ≤ C * expansion ^ 2 * (comparison + 5) := by positivity
  have hsmall_term :
      0 ≤ 6 * K * (comparison + 5) := by positivity
  have htangency : 5 ≤ tangency := by
    dsimp only [tangency]
    linarith
  refine ⟨tangency, htangency, ?_⟩
  intro family hfamily I hI delta t hdelta hdelta_t hadmissible
    R S hRfamily hSfamily hRquarter hSquarter hcomparable
    f hffamily hRtangent
  rcases hcomparable with ⟨U, hUfamily, hUcover⟩
  let delta' : ℝ := (comparison + 5) * delta
  have hdelta' : 0 < delta' := by positivity
  have hexpansion_one : 1 ≤ expansion := by
    have hsqrt_nonneg := Real.sqrt_nonneg comparison
    have hsqrt_sq := Real.sq_sqrt hcomparison_nonneg
    dsimp only [expansion]
    nlinarith
  have hRinterval : R.interval.carrier ⊆ U.interval.carrier := by
    intro x hx
    have hxR : (x, R.function x) ∈ R.carrier := by
      exact ⟨hx, by simp [hdelta.le]⟩
    exact (hUcover (Or.inl hxR)).1
  let leftPoint : UnitPoint :=
    ⟨R.interval.left, R.interval.left_mem⟩
  let rightPoint : UnitPoint :=
    ⟨R.interval.right, R.interval.right_mem⟩
  have hleftR : leftPoint ∈ R.interval.carrier := by
    exact ⟨le_rfl, R.interval.left_le_right⟩
  have hrightR : rightPoint ∈ R.interval.carrier := by
    exact ⟨R.interval.left_le_right, le_rfl⟩
  have hleftU := hRinterval hleftR
  have hrightU := hRinterval hrightR
  have hUlength :
      U.interval.length =
        Real.sqrt comparison * R.interval.length := by
    rw [U.interval_length, R.interval_length]
    have harg :
        comparison * delta / t = comparison * (delta / t) := by ring
    rw [harg, Real.sqrt_mul hcomparison_nonneg]
  have hU_dilates_R :
      ∀ x ∈ U.interval.carrier,
        x ∈ R.interval.centeredCarrier expansion := by
    intro x hxU
    have hdistance :
        |(x : ℝ) - R.interval.midpoint| ≤ U.interval.length := by
      rw [abs_le]
      dsimp only [leftPoint, rightPoint] at hleftU hrightU
      simp only [ParameterInterval.carrier, Set.mem_setOf_eq]
        at hleftU hrightU hxU
      dsimp only [ParameterInterval.length, ParameterInterval.midpoint]
        at hleftU hrightU hxU ⊢
      constructor <;> linarith
    change
      |(x : ℝ) - R.interval.midpoint| ≤
        expansion * R.interval.length / 2
    calc
      |(x : ℝ) - R.interval.midpoint| ≤ U.interval.length := hdistance
      _ = expansion * R.interval.length / 2 := by
        rw [hUlength]
        dsimp only [expansion]
        ring
  have hclose :
      ∀ x ∈ R.interval.carrier,
        |U.function x - f x| ≤ delta' := by
    intro x hx
    have hxR : (x, R.function x) ∈ R.carrier := by
      exact ⟨hx, by simp [hdelta.le]⟩
    have hxU := hUcover (Or.inl hxR)
    have hRf := hRtangent (x, R.function x) hxR
    calc
      |U.function x - f x| ≤
          |U.function x - R.function x| +
            |R.function x - f x| := abs_sub_le _ _ _
      _ = |R.function x - U.function x| +
            |R.function x - f x| := by rw [abs_sub_comm]
      _ ≤ comparison * delta + 5 * delta :=
        add_le_add hxU.2 hRf
      _ = delta' := by simp only [delta']; ring
  intro p hp
  have hpU := hUcover (Or.inr hp)
  have hpI : p.1 ∈ I.carrier :=
    I.centeredCarrier_subset_carrier (by norm_num) (by norm_num)
      (hSquarter hp.1)
  have hpExpanded : p.1 ∈ R.interval.centeredCarrier expansion :=
    hU_dilates_R p.1 hpU.1
  by_cases hfar :
      6 * K * delta' ≤ c2Distance U.function f
  · have hUf_ne : U.function ≠ f := by
      intro hUf
      have hzero : c2Distance U.function f = 0 := by
        rw [hUf, c2Distance_eq_dist, dist_self]
      rw [hzero] at hfar
      have : 0 < 6 * K * delta' := by positivity
      linarith
    have hscale :
        delta' ≤ c2Distance U.function f / (6 * K) := by
      apply (le_div_iff₀ (by positivity : 0 < 6 * K)).2
      calc
        delta' * (6 * K) = 6 * K * delta' := by ring
        _ ≤ c2Distance U.function f := hfar
    have hUf :=
      (hgeometry family hfamily I hI U.function hUfamily f hffamily
        hUf_ne delta' hdelta' hscale).2
        R.interval hRquarter hclose expansion hexpansion_one
        p.1 hpI hpExpanded
    have hcoefficient :
        comparison + C * expansion ^ 2 * (comparison + 5) ≤
          tangency := by
      dsimp only [tangency]
      linarith
    calc
      |p.2 - f p.1| ≤
          |p.2 - U.function p.1| +
            |U.function p.1 - f p.1| := abs_sub_le _ _ _
      _ ≤ comparison * delta + C * expansion ^ 2 * delta' :=
        add_le_add hpU.2 hUf
      _ =
          (comparison + C * expansion ^ 2 * (comparison + 5)) *
            delta := by simp only [delta']; ring
      _ ≤ tangency * delta :=
        mul_le_mul_of_nonneg_right hcoefficient hdelta.le
  · have hnear :
        c2Distance U.function f ≤ 6 * K * delta' := by linarith
    have hUf :=
      (abs_value_sub_le_c2Distance U.function f p.1).trans hnear
    have hcoefficient :
        comparison + 6 * K * (comparison + 5) ≤ tangency := by
      dsimp only [tangency]
      linarith
    calc
      |p.2 - f p.1| ≤
          |p.2 - U.function p.1| +
            |U.function p.1 - f p.1| := abs_sub_le _ _ _
      _ ≤ comparison * delta + 6 * K * delta' :=
        add_le_add hpU.2 hUf
      _ = (comparison + 6 * K * (comparison + 5)) * delta := by
        simp only [delta']
        ring
      _ ≤ tangency * delta :=
        mul_le_mul_of_nonneg_right hcoefficient hdelta.le

end Kakeya.Cinematic
