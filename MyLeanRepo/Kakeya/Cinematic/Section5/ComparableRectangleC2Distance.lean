import MyLeanRepo.Kakeya.Cinematic.Statements

/-!
# C² distance for comparable coarse rectangles

At small coarse scale, a common comparison rectangle and PYZ Lemma 17 give
scale-sensitive C² control.  At large coarse scale, the cinematic-family
diameter bound is already of the required size.
-/

noncomputable section

namespace Kakeya.Cinematic

private lemma tangencyParameterOn_nonneg_for_comparable
    {I : ParameterInterval} {f g : C2Function} :
    0 ≤ tangencyParameterOn I f g := by
  apply Real.sInf_nonneg
  intro r hr
  simp only [tangencyParameterOn, Set.mem_setOf_eq] at hr
  rcases hr with ⟨x, _, rfl⟩
  positivity

theorem comparable_rectangles_c2Distance_bound
    (hCommon : CommonTangentRectangleStatement) :
    ∀ K D : ℝ, 1 ≤ K → 1 ≤ D →
      ∃ C_c2 : ℝ, 1 ≤ C_c2 ∧
        ∀ {family : Set C2Function}
          {I : ParameterInterval}
          {delta t : ℝ},
          IsCinematicFamily family K D →
          I.IsControlled K →
          0 < delta →
          delta ≤ t →
          ∀ (R S : CurvilinearRectangle delta t),
            R.function ∈ family →
            S.function ∈ family →
            R.IsOverCentralQuarterOf I →
            S.IsOverCentralQuarterOf I →
            R.AreLambdaComparable S family 100 →
            c2Distance R.function S.function ≤ C_c2 * t := by
  intro K D hK hD
  rcases hCommon K D hK hD with ⟨C_common, hC_common, hCommon_main⟩
  let C_c2 : ℝ := max 1 (max (200 * C_common) (100 * K))
  have hC_c2 : 1 ≤ C_c2 := le_max_left _ _
  refine ⟨C_c2, hC_c2, ?_⟩
  intro family I delta t hfamily hI hdelta hdelta_t
    R S hR_family hS_family hR_quarter hS_quarter hComparable
  have ht : 0 < t := hdelta.trans_le hdelta_t
  rcases hComparable with ⟨W, hW_family, hcarrier⟩
  by_cases hsmall : 100 * t ≤ 1
  · have h_to_w :
        ∀ (Q : CurvilinearRectangle delta t),
          Q.function ∈ family →
          Q.IsOverCentralQuarterOf I →
          Q.carrier ⊆ W.carrier →
          c2Distance Q.function W.function ≤
            C_common * 100 * t := by
      intro Q hQ_family hQ_quarter hQ_carrier
      let delta' : ℝ := 100 * delta
      let t' : ℝ := 100 * t
      have hdelta' : 0 < delta' := by
        dsimp only [delta']
        positivity
      have hdelta'_t' : delta' ≤ t' := by
        dsimp only [delta', t']
        gcongr
      have ht'_one : t' ≤ 1 := by
        simpa [t'] using hsmall
      have hQ_value :
          ∀ x ∈ Q.interval.carrier,
            |Q.function x - W.function x| ≤ delta' := by
        intro x hx
        have hQ_graph : (x, Q.function x) ∈ Q.carrier := by
          exact ⟨hx, by simpa [delta'] using hdelta.le⟩
        have hW_graph := hQ_carrier hQ_graph
        have hbound : |Q.function x - W.function x| ≤ 100 * delta := by
          simpa [CurvilinearRectangle.carrier, verticalNeighborhoodOn,
            Set.mem_setOf_eq] using hW_graph.2
        simpa [delta'] using hbound
      let Q' : CurvilinearRectangle delta' t' :=
        { function := Q.function
          interval := Q.interval
          interval_length := by
            have hratio : delta' / t' = delta / t := by
              dsimp only [delta', t']
              field_simp [ht.ne']
            simpa [hratio] using Q.interval_length }
      have hQ'_quarter : Q'.IsOverCentralQuarterOf I := hQ_quarter
      have hQ'_tangent_self :
          Q'.IsLambdaTangent Q.function 5 := by
        intro p hp
        have hp' :
            p.1 ∈ Q.interval.carrier ∧
              |p.2 - Q.function p.1| ≤ delta' := hp
        exact hp'.2.trans (by nlinarith [hdelta'])
      have hQ'_tangent_w :
          Q'.IsLambdaTangent W.function 5 := by
        intro p hp
        have hp' :
            p.1 ∈ Q.interval.carrier ∧
              |p.2 - Q.function p.1| ≤ delta' := hp
        have hgap := hQ_value p.1 hp'.1
        calc
          |p.2 - W.function p.1| =
              |(p.2 - Q.function p.1) +
                (Q.function p.1 - W.function p.1)| := by
            congr 1
            ring
          _ ≤
              |p.2 - Q.function p.1| +
                |Q.function p.1 - W.function p.1| := by
            exact abs_add_le _ _
          _ ≤ delta' + delta' := add_le_add hp'.2 hgap
          _ ≤ 5 * delta' := by nlinarith
      by_cases hQW : Q.function = W.function
      · rw [hQW, c2Distance_eq_dist, dist_self]
        positivity
      · have hbound :=
          hCommon_main family hfamily I hI delta' t'
            hdelta' hdelta'_t' ht'_one Q' hQ_family hQ'_quarter
            Q.function hQ_family W.function hW_family hQW
            hQ'_tangent_self hQ'_tangent_w
        have htangent :
            0 ≤ tangencyParameterOn I Q.function W.function :=
          tangencyParameterOn_nonneg_for_comparable
        have hdistance :
            0 ≤ c2Distance Q.function W.function := by
          simp only [c2Distance_eq_dist]
          exact dist_nonneg
        have hscaled :
            delta' * c2Distance Q.function W.function ≤
              C_common * delta' * t' := by
          calc
            delta' * c2Distance Q.function W.function ≤
                (tangencyParameterOn I Q.function W.function + delta') *
                  c2Distance Q.function W.function := by
              nlinarith [mul_nonneg htangent hdistance]
            _ ≤ C_common * delta' * t' := hbound
        have hmain :
            c2Distance Q.function W.function ≤ C_common * t' := by
          nlinarith
        dsimp only [t'] at hmain
        convert hmain using 1 <;> ring
    have hR_w :
        c2Distance R.function W.function ≤ C_common * 100 * t :=
      h_to_w R hR_family hR_quarter
        (fun _ hp => hcarrier (Or.inl hp))
    have hS_w :
        c2Distance S.function W.function ≤ C_common * 100 * t :=
      h_to_w S hS_family hS_quarter
        (fun _ hp => hcarrier (Or.inr hp))
    have htriangle :
        c2Distance R.function S.function ≤
          c2Distance R.function W.function +
            c2Distance S.function W.function := by
      calc
        c2Distance R.function S.function =
            dist R.function S.function := rfl
        _ ≤ dist R.function W.function + dist W.function S.function :=
          dist_triangle _ _ _
        _ = c2Distance R.function W.function +
            c2Distance S.function W.function := by
          simp only [c2Distance_eq_dist, dist_comm]
    have hraw :
        c2Distance R.function S.function ≤ 200 * C_common * t := by
      calc
        c2Distance R.function S.function ≤
            c2Distance R.function W.function +
              c2Distance S.function W.function := htriangle
        _ ≤ C_common * 100 * t + C_common * 100 * t :=
          add_le_add hR_w hS_w
        _ = 200 * C_common * t := by ring
    have hcoefficient : 200 * C_common ≤ C_c2 := by
      exact (le_max_left _ _).trans (le_max_right _ _)
    exact hraw.trans (mul_le_mul_of_nonneg_right hcoefficient ht.le)
  · have hlarge : 1 < 100 * t := lt_of_not_ge hsmall
    have hdiameter :
        c2Distance R.function S.function ≤ K :=
      hfamily.1 hR_family hS_family
    have hK_scaled : K ≤ 100 * K * t := by
      nlinarith
    have hcoefficient : 100 * K ≤ C_c2 := by
      exact (le_max_right _ _).trans (le_max_right _ _)
    exact hdiameter.trans <|
      hK_scaled.trans (mul_le_mul_of_nonneg_right hcoefficient ht.le)

end Kakeya.Cinematic
