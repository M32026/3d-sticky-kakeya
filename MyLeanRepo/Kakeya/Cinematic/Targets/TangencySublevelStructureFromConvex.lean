import MyLeanRepo.Kakeya.Cinematic.Statements
import MyLeanRepo.Kakeya.Cinematic.TangencySublevelStructure.Basic
import MyLeanRepo.Kakeya.Cinematic.TangencySublevelStructure.MonotoneCase
import MyLeanRepo.Kakeya.Cinematic.TangencySublevelStructure.LowerBounds

/-!
# Assemble tangency sublevel structure from the convex core

The monotone, large-value, and lower-component arguments are closed modules.
This target only performs the case split and invokes the convex core supplied
as an ordinary input.
-/

namespace Kakeya.Cinematic

theorem tangency_sublevel_structure_from_convex :
    TangencySublevelStructureFromConvexStatement := by
  intro hApi _hScaling hDiameter hConvex
  intro K D hK hD
  rcases hDiameter K D hK hD with
    ⟨Cdiam, hCdiam_pos, hDiameter_bound⟩
  rcases hConvex K Cdiam hK hCdiam_pos with
    ⟨Cconvex, hCconvex_pos, hConvex_case⟩
  let C : ℝ := Cconvex + 100 * K
  have hK_pos : 0 < K := by linarith
  have hC_pos : 0 < C := by
    dsimp only [C]
    positivity
  have hCconvex_le : Cconvex ≤ C := by
    dsimp only [C]
    linarith
  have hC_large : 100 * K ≤ C := by
    dsimp only [C]
    linarith
  refine ⟨C, hC_pos, ?_⟩
  intro family hfamily I hI f hf g hg hfg delta hdelta hdelta_le
  set t := c2Distance f g with ht
  have ht_pos : 0 < t := by
    simpa [ht, c2Distance_eq_dist] using dist_pos.mpr hfg
  set Delta := tangencyParameterOn I f g with hDelta
  set scale := Real.sqrt ((Delta + delta) * t) with hscale
  set E := tangencySublevelSetOn I f g delta with hE
  set Ehalf := tangencySublevelSetOn I f g (delta / 2) with hEhalf
  have hApi_data := hApi I f g
  have hDelta_nonneg : 0 ≤ Delta := by
    simpa [hDelta] using hApi_data.1
  have hE_closed : IsClosed E := by
    simpa [hE] using hApi_data.2.2 delta
  have hscale_pos : 0 < scale := by
    rw [hscale]
    exact Real.sqrt_pos.mpr (mul_pos (by linarith) ht_pos)
  have hI_short : I.IsShort K := hI.2
  have hcurvature : ∀ x : UnitPoint, K⁻¹ * t ≤ jetGap f g x := by
    intro x
    simpa [ht] using hfamily.2.2 hf hg x
  have hdichotomy :=
    preliminary_dichotomy K D hK hD family hfamily I hI_short f hf g hg
  rcases hdichotomy with ⟨hdichotomy_h, hdichotomy_h', hdichotomy_h''⟩
  have hhalf_subset : Ehalf ⊆ E := by
    intro x hx
    simp only [hEhalf, hE, tangencySublevelSetOn, Set.mem_setOf_eq] at hx ⊢
    exact ⟨hx.1, by linarith [hx.2]⟩
  have hdiameter :
      ∀ x : UnitPoint, x ∈ E → ∀ y : UnitPoint, y ∈ E →
        |(x : ℝ) - y| ≤
          Cdiam * Real.sqrt ((Delta + delta) / t) := by
    simpa [hE, hDelta, ht] using
      hDiameter_bound family hfamily I hI_short f hf g hg hfg
        delta hdelta hdelta_le
  have hdelta_le' : delta ≤ (6 * K)⁻¹ * t := by
    simpa [ht, div_eq_mul_inv, mul_comm] using hdelta_le
  by_cases hE_empty : E = ∅
  · let pieces : IntervalFamily := ⟨0, Fin.elim0⟩
    have hcard : pieces.card ≤ 2 := by simp [pieces]
    have hunion : pieces.union = E := by
      simp [IntervalFamily.union, pieces, hE_empty]
    have hlengths : pieces.AllLengthsLE (C * delta / scale) := by
      intro i
      fin_cases i
    have hlower :
        ∀ x ∈ Ehalf,
          ∃ j : Fin pieces.card,
            x ∈ (pieces.interval j).carrier ∧
              delta ≤ C * scale * (pieces.interval j).length := by
      intro x hx
      have hxE : x ∈ E := hhalf_subset hx
      rw [hE_empty] at hxE
      exact False.elim hxE
    exact ⟨pieces, hcard, hunion.symm, hlengths, hlower⟩
  · have hE_nonempty : E.Nonempty := Set.nonempty_iff_ne_empty.mpr hE_empty
    rcases hdichotomy_h with (hsmall_h | hlarge_h)
    · rcases hdichotomy_h' with (hsmall_h' | hlarge_h')
      · have hlarge_h'' :
            ∀ x ∈ I.carrier,
              (6 * K)⁻¹ * t ≤
                |f.secondDeriv x - g.secondDeriv x| := by
          simpa [ht] using hdichotomy_h'' ⟨hsmall_h, hsmall_h'⟩
        have hconvex_result :=
          hConvex_case I hI f g hfg delta hdelta hdelta_le
            (by simpa [ht] using hsmall_h)
            (by simpa [ht] using hsmall_h')
            (by simpa [ht] using hlarge_h'')
            (by
              intro x hx y hy
              simpa [hE, hDelta, ht] using hdiameter x hx y hy)
        rcases hconvex_result with
          ⟨pieces, hcard, hunion, hlengths, hlower⟩
        have hlengths' :
            pieces.AllLengthsLE (C * delta / scale) := by
          intro i
          have hi := hlengths i
          have hbound :
              Cconvex * delta / scale ≤ C * delta / scale := by
            gcongr
          simpa [hscale, hDelta, ht] using hi.trans hbound
        have hlower' :
            ∀ x ∈ Ehalf,
              ∃ j : Fin pieces.card,
                x ∈ (pieces.interval j).carrier ∧
                  delta ≤ C * scale * (pieces.interval j).length := by
          intro x hx
          rcases hlower x (by simpa [hEhalf] using hx) with
            ⟨j, hxj, hj⟩
          refine ⟨j, hxj, hj.trans ?_⟩
          have hlength_nonneg :
              0 ≤ (pieces.interval j).length :=
            (pieces.interval j).length_nonneg
          have hscale_nonneg : 0 ≤ scale := hscale_pos.le
          have :
              Cconvex * scale * (pieces.interval j).length ≤
                C * scale * (pieces.interval j).length := by
            gcongr
          simpa [hscale, hDelta, ht] using this
        exact
          ⟨pieces, hcard, by simpa [hE] using hunion,
            hlengths', hlower'⟩
      · rcases
          monotone_case_length_bound hK ht_pos ht hdelta hI_short
            (by simpa [ht] using hlarge_h') hcurvature E rfl hE_closed
            hE_nonempty C hC_large hscale hdelta_le'
          with ⟨J, hJ, hJ_length⟩
        let pieces : IntervalFamily := ⟨1, fun _ => J⟩
        have hcard : pieces.card ≤ 2 := by simp [pieces]
        have hunion : pieces.union = E := by
          ext x
          simp [IntervalFamily.union, pieces, hJ]
        have hlengths :
            pieces.AllLengthsLE (C * delta / scale) := by
          intro i
          fin_cases i
          exact hJ_length
        have hlower :=
          lower_bound_monotone hK ht_pos rfl hdelta E Ehalf rfl rfl
            C hC_large hscale hI (by simpa [ht] using hlarge_h')
            hdelta_le' pieces (by simp [pieces]) hunion
        exact ⟨pieces, hcard, hunion.symm, hlengths, hlower⟩
    · rcases
        large_h_at_most_two_points hK ht_pos ht hI_short
          (by simpa [ht] using hlarge_h) hcurvature hdelta hdelta_le'
          E rfl
        with ⟨hE_finite, hE_card⟩
      have hEhalf_empty : Ehalf = ∅ := by
        apply Set.eq_empty_iff_forall_notMem.mpr
        intro x hx
        have hx_center : x ∈ I.centeredCarrier (1 / 4) :=
          (hEhalf ▸ hx).1
        have hx_carrier : x ∈ I.carrier :=
          I.centeredCarrier_subset_carrier (by norm_num) (by norm_num)
            hx_center
        have hx_upper : |f x - g x| ≤ delta / 2 :=
          (hEhalf ▸ hx).2
        have hx_lower : (6 * K)⁻¹ * t ≤ |f x - g x| :=
          hlarge_h x hx_carrier
        have hthreshold_pos : 0 < (6 * K)⁻¹ * t := by positivity
        have : delta / 2 < (6 * K)⁻¹ * t := by linarith
        linarith
      let Efin : Finset UnitPoint := hE_finite.toFinset
      have hEfin : (Efin : Set UnitPoint) = E :=
        hE_finite.coe_toFinset
      have hEfin_card : Efin.card ≤ 2 := by
        have hcard_eq : Set.ncard E = Efin.card :=
          Set.ncard_eq_toFinset_card E hE_finite
        omega
      have hEfin_card_pos : 0 < Efin.card := by
        apply Finset.card_pos.mpr
        rcases hE_nonempty with ⟨x, hx⟩
        refine ⟨x, ?_⟩
        change x ∈ (Efin : Set UnitPoint)
        rw [hEfin]
        exact hx
      have hEfin_cases : Efin.card = 1 ∨ Efin.card = 2 := by omega
      rcases hEfin_cases with (hcard_one | hcard_two)
      · rcases Finset.card_eq_one.mp hcard_one with ⟨x, hx⟩
        have hE_singleton : E = {x} := by
          rw [← hEfin, hx]
          simp
        let J : ParameterInterval :=
          ⟨(x : ℝ), (x : ℝ), x.prop, x.prop, le_rfl⟩
        have hJ : J.carrier = {x} := by
          ext y
          simp only [J, ParameterInterval.carrier, Set.mem_singleton_iff,
            Set.mem_setOf_eq]
          constructor
          · rintro ⟨hleft, hright⟩
            exact Subtype.ext (by linarith)
          · rintro rfl
            exact ⟨le_rfl, le_rfl⟩
        let pieces : IntervalFamily := ⟨1, fun _ => J⟩
        have hcard : pieces.card ≤ 2 := by simp [pieces]
        have hunion : pieces.union = E := by
          ext z
          simp [IntervalFamily.union, pieces, hJ, hE_singleton]
        have hlengths :
            pieces.AllLengthsLE (C * delta / scale) := by
          have hbound_nonneg : 0 ≤ C * delta / scale := by positivity
          intro i
          fin_cases i
          simpa [pieces, J, ParameterInterval.length] using hbound_nonneg
        have hlower :
            ∀ x ∈ Ehalf,
              ∃ j : Fin pieces.card,
                x ∈ (pieces.interval j).carrier ∧
                  delta ≤ C * scale * (pieces.interval j).length := by
          intro x hx
          rw [hEhalf_empty] at hx
          exact False.elim hx
        exact ⟨pieces, hcard, hunion.symm, hlengths, hlower⟩
      · rcases Finset.card_eq_two.mp hcard_two with ⟨x, y, hxy, hxy_set⟩
        have hE_pair : E = {x, y} := by
          rw [← hEfin, hxy_set]
          simp
        let Jx : ParameterInterval :=
          ⟨(x : ℝ), (x : ℝ), x.prop, x.prop, le_rfl⟩
        let Jy : ParameterInterval :=
          ⟨(y : ℝ), (y : ℝ), y.prop, y.prop, le_rfl⟩
        have hJx : Jx.carrier = {x} := by
          ext z
          simp only [Jx, ParameterInterval.carrier, Set.mem_singleton_iff,
            Set.mem_setOf_eq]
          constructor
          · rintro ⟨hleft, hright⟩
            exact Subtype.ext (by linarith)
          · rintro rfl
            exact ⟨le_rfl, le_rfl⟩
        have hJy : Jy.carrier = {y} := by
          ext z
          simp only [Jy, ParameterInterval.carrier, Set.mem_singleton_iff,
            Set.mem_setOf_eq]
          constructor
          · rintro ⟨hleft, hright⟩
            exact Subtype.ext (by linarith)
          · rintro rfl
            exact ⟨le_rfl, le_rfl⟩
        let pieces : IntervalFamily :=
          ⟨2, fun i => if i = 0 then Jx else Jy⟩
        have hcard : pieces.card ≤ 2 := by simp [pieces]
        have hunion : pieces.union = E := by
          ext z
          simp [IntervalFamily.union, pieces, hE_pair, hJx, hJy]
        have hlengths :
            pieces.AllLengthsLE (C * delta / scale) := by
          have hbound_nonneg : 0 ≤ C * delta / scale := by positivity
          have hJx_length : Jx.length = 0 := by
            simp [Jx, ParameterInterval.length]
          have hJy_length : Jy.length = 0 := by
            simp [Jy, ParameterInterval.length]
          intro i
          have hi : i.val = 0 ∨ i.val = 1 := by omega
          rcases hi with (hi | hi)
          · have hi0 : i = 0 := Fin.ext hi
            rw [hi0]
            simpa [pieces, hJx_length] using hbound_nonneg
          · have hi1 : i = 1 := Fin.ext hi
            rw [hi1]
            simpa [pieces, hJy_length] using hbound_nonneg
        have hlower :
            ∀ x ∈ Ehalf,
              ∃ j : Fin pieces.card,
                x ∈ (pieces.interval j).carrier ∧
                  delta ≤ C * scale * (pieces.interval j).length := by
          intro x hx
          rw [hEhalf_empty] at hx
          exact False.elim hx
        exact ⟨pieces, hcard, hunion.symm, hlengths, hlower⟩

end Kakeya.Cinematic
