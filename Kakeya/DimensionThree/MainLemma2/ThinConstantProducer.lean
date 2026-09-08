/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma2.ThinConfig
public import Kakeya.DimensionThree.MainLemma2.SetupThresholdsAssembly

/-!
# The thin-constant producer: `exists_thinConfig` with its constant exposed and sized
-/

@[expose] public section

namespace Kakeya.VeryNotSticky

open MeasureTheory Metric Set Topology Filter ShadedBody
open scoped NNReal ENNReal

universe u

/-- The core envelope of `Kakeya.VeryNotSticky.exists_thinConfig`, hoisted from its `let` so
that its size is nameable. -/
noncomputable def thinCoreEnvelope (cfg : VeryNotSticky.{u}) (bd : BallData cfg) : NNReal :=
  max
    (max (max (((Nat.log 2 ⌈bd.CF⌉₊ + 1 : ℕ) : NNReal))
        (ThinCase.ballNetLoss 3 ((bd.w₁ : ℝ) / 8) 2))
      (bd.bs.sup fun B =>
        ThinCase.thinEnvelopeTerm 3 (bd.segs B).card (bd.bodies B).card bd.CF bd.w₁))
    (bd.bs.sup fun B => max
      (ThinCase.factoringApplyCore 3 (bd.segs B).card (bd.bodies B).card cfg.δ)
      (ThinCase.factoringApplyCore 3 (bd.segs B).card (bd.bodies B).card (cfg.δ / bd.C₀)))

/-- `Kakeya.VeryNotSticky.exists_thinConfig` with its comparison constant exposed. Same proof;
the constant is `bd.Cg * thinSetupConstant … (thinCoreEnvelope cfg bd) …`. -/
theorem exists_thinConfig_C_le (cfg : VeryNotSticky.{u}) (bd : BallData cfg)
    (hδw₁ : cfg.δ ≤ bd.w₁) (hw₁one : bd.w₁ ≤ 1) :
    ∃ tc : ThinConfig cfg bd,
      tc.C ≤ bd.Cg * ThinCase.thinSetupConstant bd.C₀ bd.CF bd.c₁
        (thinCoreEnvelope cfg bd) bd.D bd.Cm := by
  -- Ball-uniformity of the core envelope: one `Ccore` for all balls, obtained as the supremum
  -- over the (finitely many) balls of the canonical envelope
  -- `Kakeya.ThinCase.factoringApplyCore` at that ball. `bd.bs` is a `Finset`, so this is
  -- mechanical, and each per-ball bound follows from
  -- `Kakeya.ThinCase.factoringApplyCore_spec` composed with `Finset.le_sup`.
  -- The fifth envelope bound of `Kakeya.ThinCase.factoringApply` mentions `CF` and no ball, so
  -- it is adjoined to the supremum rather than absorbed into it. Enlarging `Ccore` is free:
  -- all five bounds are *lower* bounds on the parameter, and `Kakeya.VeryNotSticky.ThinConfig.C`
  -- is existentially quantified data with no upper bound field. The adjoined term is
  -- `⌊log₂ ⌈CF⌉⌋ + 1`, a constant in `δ`, so the `⪅ 1` budget of
  -- `Kakeya.ThinCase.factoringApplyCore_leApprox_one` is not disturbed.
  -- The envelope is taken at the *discretization* scale `cfg.δ / bd.C₀` of the segments, not at
  -- `cfg.δ`: `Kakeya.ThinCase.factoringApply` runs the Proposition 5.1 pipeline at the scale at
  -- which `BallData.segs_thickness` discretizes the segments, and that is `cfg.δ / bd.C₀`. Both
  -- pipeline losses are antitone in the scale. Rather than rely on that antitonicity, the
  -- envelope below is the maximum of the two evaluations, which discharges the four
  -- `cfg.δ`-bounds and the two `cfg.δ / bd.C₀`-bounds from one supremum with no monotonicity
  -- lemma. Enlarging `Ccore` is free, all six bounds being *lower* bounds on the parameter.
  let Ccore : NNReal := thinCoreEnvelope cfg bd
  have hcore_le : ∀ B ∈ bd.bs,
      ThinCase.factoringApplyCore 3 (bd.segs B).card (bd.bodies B).card cfg.δ ≤ Ccore :=
    fun B hB => le_trans (le_trans (le_max_left _ _) (Finset.le_sup (f := fun B => max
      (ThinCase.factoringApplyCore 3 (bd.segs B).card (bd.bodies B).card cfg.δ)
      (ThinCase.factoringApplyCore 3 (bd.segs B).card (bd.bodies B).card (cfg.δ / bd.C₀))) hB))
      (le_max_right _ _)
  have hcore_le₀ : ∀ B ∈ bd.bs,
      ThinCase.factoringApplyCore 3 (bd.segs B).card (bd.bodies B).card (cfg.δ / bd.C₀)
        ≤ Ccore :=
    fun B hB => le_trans (le_trans (le_max_right _ _) (Finset.le_sup (f := fun B => max
      (ThinCase.factoringApplyCore 3 (bd.segs B).card (bd.bodies B).card cfg.δ)
      (ThinCase.factoringApplyCore 3 (bd.segs B).card (bd.bodies B).card (cfg.δ / bd.C₀))) hB))
      (le_max_right _ _)
  have hCcoreRef₀ : ∀ B ∈ bd.bs,
      (ShadedBody.outerFactoringFamily_refinement.c 3 (bd.segs B).card (cfg.δ / bd.C₀))⁻¹
        ≤ Ccore :=
    fun B hB => le_trans (ThinCase.inv_refinement_c_le_factoringApplyCore _ _ _ _)
      (hcore_le₀ B hB)
  have hCcoreMult₀ : ∀ B ∈ bd.bs,
      ShadedBody.outerFactoringFamily_outerConstMultFat.c 3 (bd.bodies B).card
        (cfg.δ / bd.C₀) ≤ Ccore :=
    fun B hB => le_trans (ThinCase.outerConstMultFat_c_le_factoringApplyCore _ _ _ _)
      (hcore_le₀ B hB)
  have hCcoreFrost : ((Nat.log 2 ⌈bd.CF⌉₊ + 1 : ℕ) : NNReal) ≤ Ccore :=
    le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) (le_max_left _ _)
  -- **the strengthened `hCcoreNet`, discharged by the compiler and not asserted**
  have hCcoreNet : ∀ B ∈ bd.bs,
      ThinCase.thinEnvelopeTerm 3 (bd.segs B).card (bd.bodies B).card bd.CF bd.w₁ ≤ Ccore :=
    fun B hB => le_trans
      (Finset.le_sup (f := fun B =>
        ThinCase.thinEnvelopeTerm 3 (bd.segs B).card (bd.bodies B).card bd.CF bd.w₁) hB)
      (le_trans (le_max_right _ _) (le_max_left _ _))
  have hCcore2 : (2 : NNReal) ≤ Ccore := by
    obtain ⟨B₀, hB₀⟩ := bd.bs_nonempty
    exact le_trans (ThinCase.two_le_factoringApplyCore _ _ _ _) (hcore_le B₀ hB₀)
  have hCcoreRef : ∀ B ∈ bd.bs,
      (ShadedBody.outerFactoringFamily_refinement.c 3 (bd.segs B).card cfg.δ)⁻¹ ≤ Ccore :=
    fun B hB => le_trans (ThinCase.inv_refinement_c_le_factoringApplyCore _ _ _ _)
      (hcore_le B hB)
  have hCcoreMult : ∀ B ∈ bd.bs,
      ShadedBody.outerFactoringFamily_outerConstMultFat.c 3 (bd.bodies B).card cfg.δ ≤ Ccore :=
    fun B hB => le_trans (ThinCase.outerConstMultFat_c_le_factoringApplyCore _ _ _ _)
      (hcore_le B hB)
  have hCcoreDyad : ∀ B ∈ bd.bs,
      ((Nat.log 2 (bd.bodies B).card + 1 : ℕ) : NNReal) ≤ Ccore :=
    fun B hB => le_trans (ThinCase.natLog_le_factoringApplyCore _ _ _ _) (hcore_le B hB)
  let C : NNReal := ThinCase.thinSetupConstant bd.C₀ bd.CF bd.c₁ Ccore bd.D bd.Cm
  have hbr₁ : cfg.b ≤ cfg.r₁ := by simpa [r₁] using cfg.hdims.2.2
  -- The localisation of the bodies, which `Kakeya.ThinCase.factoringApply` — and hence
  -- `Kakeya.ThinCase.perBall` and `Kakeya.ThinCase.thinSetupExists` — needs and which the
  -- refutations `Kakeya.ThinCase.Refute.factoringApply_refuted` and
  -- `Kakeya.ThinCase.PerBallRefute.perBall_refuted` show cannot be dispensed with. It is
  -- *available here*: the bodies of a ball lie in that ball, whose radius `r₁ = δ^exscal` is
  -- at most `1` because `δ ≤ 1` and `exscal > 0`.
  have hr₁one : cfg.r₁ ≤ 1 := by
    rw [r₁]
    exact NNReal.rpow_le_one cfg.hδ1 cfg.hexscal.le
  have hloc : ∀ B ∈ bd.bs, ∃ z : EuclideanSpace ℝ (Fin 3),
      ∀ j ∈ bd.bodies B, (bd.Wb j).carrier ⊆ closedBall z 1 := by
    intro B hB
    refine ⟨bd.ctr B, fun j hj => ?_⟩
    refine (bd.bodies_subset_ball B hB j hj).trans (Metric.closedBall_subset_closedBall ?_)
    exact_mod_cast hr₁one
  have hD : 1 ≤ bd.D := by
    rcases bd.bs_nonempty with ⟨B, hBbs⟩
    have hr₁ : (0 : ℝ) < (cfg.r₁ : ℝ) := NNReal.coe_pos.mpr (NNReal.rpow_pos cfg.hδ)
    have hx : bd.ctr B ∈ ball (bd.ctr B) (cfg.r₁ : ℝ) := by
      rw [mem_ball, dist_self]
      exact hr₁
    have hcard := bd.ballOverlap (bd.ctr B) ({B} : Finset bd.bι)
      (by intro t ht; rw [Finset.mem_singleton] at ht; subst ht; exact hBbs)
      (by intro B' hB'; rw [Finset.mem_singleton] at hB'; subst hB'; exact hx)
    simpa using hcard
  rcases ThinCase.thinSetupExists (E := EuclideanSpace ℝ (Fin 3))
      (finrank_euclideanSpace_fin : Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 3)
      (I := cfg.s) (Yg := bd.Yg)
      (hYgmeas := bd.Yg_measurable)
      (bs := bd.bs) (P := bd.P)
      (hPdisj := bd.P_disjoint) (hPmeas := bd.P_measurable) (hPcov := bd.P_cover)
      (segs := bd.segs) (Y := bd.Y) (fam := bd.fam)
      (hsegs := bd.segs_nonempty) (hfam := bd.fam_subset) (hfam_disj := bd.fam_disjoint)
      (hYb_piece := bd.Y_piece)
      (bodies := bd.bodies) (Wb := bd.Wb) (blk := bd.blk)
      (δ := cfg.δ) (a := cfg.a) (b := cfg.b) (r₁ := cfg.r₁) (w₁ := bd.w₁)
      (η := 2 * cfg.η) (C₀ := bd.C₀) (CF := bd.CF) (c₁ := bd.c₁) (D := bd.D)
      (hC₀ := bd.hC₀) (hCF := bd.hCF) (hc₁ := bd.hc₁) (hD := hD)
      (hδ := cfg.hδ) (hδa := cfg.hdims.1) (hab := cfg.hdims.2.1) (hbr₁ := hbr₁)
      (hδw₁ := hδw₁) (hw₁one := hw₁one) (hη := mul_nonneg (by norm_num) cfg.hη.le) (hloc := hloc)
       (Ccore := Ccore) (hCcore2 := hCcore2)
      (hCcoreRef := hCcoreRef) (hCcoreMult := hCcoreMult) (hCcoreDyad := hCcoreDyad)
      (hCcoreFrost := hCcoreFrost) (hCcoreNet := hCcoreNet)
      (hCcoreRef₀ := hCcoreRef₀) (hCcoreMult₀ := hCcoreMult₀)
      (hblk := bd.blk_mem) (hle := bd.segs_le) (hthick := bd.segs_thickness)
      (hdims := bd.segs_dims) (hbody := bd.bodies_thickness) (hw₁ := bd.bodies_w₁)
      (hFr := bd.frostman)
      (hdens := bd.segs_density) (hparent := bd.parent) (hinto := bd.into) (hback := bd.back)
      (m := bd.m) (Cm := bd.Cm) (hCm := bd.hCm) (hfibre := bd.fibre)
      (γ := bd.γ) (cov := bd.cov) (covCtr := bd.covCtr)
      (hcov := bd.cov_isCover) (hcovMeets := bd.cov_meets)
    with ⟨Y', hsub, hmeas, hYm, tb, hcompat⟩
  -- The loss `Cg` of the working shading against `Y` (`BallData.Yg_mass`) joins the comparison
  -- constant: `thinSetupExists` refines `Y_g`, and `(Cg · C)⁻¹ ∑|Y| ≤ C⁻¹ ∑|Y_g| ≤ ∑|Y'|`.
  -- The per-ball data are read at the larger constant by `ThinBall.mono`, which passes `Y'_B`
  -- and `𝕎'_B` through unchanged, so the compatibility clauses transport verbatim.
  have hCle : C ≤ bd.Cg * C := le_mul_of_one_le_left zero_le bd.hCg
  let tb' : ∀ B ∈ bd.bs, ThinCase.ThinBall (bd.Cg * C) bd.C₀ (bd.segs B) bd.Y (bd.bodies B)
      bd.Wb bd.blk cfg.δ cfg.a (2 * cfg.η) :=
    fun B hB ↦ ThinCase.ThinBall.mono hCle (tb B hB)
  have hYm' : ((bd.Cg * C : NNReal) : ENNReal)⁻¹ * ∑ i ∈ cfg.s, volume (cfg.T i).shade ≤
      ∑ i ∈ cfg.s, volume (Y' i) := by
    calc ((bd.Cg * C : NNReal) : ENNReal)⁻¹ * ∑ i ∈ cfg.s, volume (cfg.T i).shade
        = (C : ENNReal)⁻¹ * ((bd.Cg : ENNReal)⁻¹ * ∑ i ∈ cfg.s, volume (cfg.T i).shade) := by
          rw [ENNReal.coe_mul, ENNReal.mul_inv (Or.inr ENNReal.coe_ne_top)
            (Or.inl ENNReal.coe_ne_top), mul_comm (bd.Cg : ENNReal)⁻¹, mul_assoc]
      _ ≤ (C : ENNReal)⁻¹ * ∑ i ∈ cfg.s, volume (bd.Yg i) := by
          gcongr
          exact bd.Yg_mass
      _ ≤ ∑ i ∈ cfg.s, volume (Y' i) := hYm
  refine ⟨⟨bd.Cg * C, Y', hsub, hmeas, hYm', tb',
      fun B hB p hp i hi ↦ (hcompat B hB).1 p hp i hi,
      fun B hB p hp ↦ (hcompat B hB).2 p hp,
      segment_mass_of_compat cfg bd Y' hsub hmeas hYm' tb'
        fun B hB p hp i hi ↦ (hcompat B hB).1 p hp i hi⟩, le_rfl⟩

end Kakeya.VeryNotSticky

/-! ## Bit-budget sizing of the pipeline constants

Every loss constant of the thin-case pipeline is built from
`Kakeya.factoringStep1FiberPigeonholeConstant a b = (1 + log₂ (b / a))₊`, so a *bit budget* — a
natural number `m` with `x ≤ 2 ^ m` for every input `x` — turns each of them into a linear
function of `m`, and the whole envelope into a polynomial in `m + 1`. These lemmas carry out that
accounting; the only inputs are `2 ^ m` bounds. -/

namespace Kakeya.ThinSizing

open MeasureTheory Metric Set Topology Filter ShadedBody
open scoped NNReal ENNReal

/-- A bit-count bound for the fiber pigeonhole constant. -/
lemma fiber_le_of_le_two_pow {a b : NNReal} {m : ℕ} (h : b ≤ 2 ^ m * a) :
    Kakeya.factoringStep1FiberPigeonholeConstant a b ≤ ((m + 1 : ℕ) : NNReal) := by
  rw [Kakeya.factoringStep1FiberPigeonholeConstant, Real.toNNReal_le_iff_le_coe]
  have key : Real.logb 2 ((b : ℝ) / (a : ℝ)) ≤ (m : ℝ) := by
    rcases le_or_gt ((b : ℝ) / (a : ℝ)) 0 with hle | hpos
    · have h0 : (b : ℝ) / (a : ℝ) = 0 := le_antisymm hle (by positivity)
      simp [h0]
    · have ha : (0 : ℝ) < (a : ℝ) := by
        rcases eq_or_lt_of_le (a.coe_nonneg) with h' | h'
        · exfalso
          rw [← h'] at hpos
          simp at hpos
        · exact h'
      have hba : (b : ℝ) / (a : ℝ) ≤ (2 : ℝ) ^ m := by
        rw [div_le_iff₀ ha]
        have := h
        rw [← NNReal.coe_le_coe] at this
        push_cast at this
        linarith
      calc Real.logb 2 ((b : ℝ) / (a : ℝ))
          ≤ Real.logb 2 ((2 : ℝ) ^ m) := Real.logb_le_logb_of_le (by norm_num) hpos hba
        _ = (m : ℝ) := by
            rw [Real.logb_pow]
            simp
  push_cast
  linarith

lemma pigeon_le_of_le_two_pow {a b : NNReal} {m : ℕ} (h : b ≤ 2 ^ m * a) :
    Kakeya.factoringStep1PigeonholeConstant a b ≤ 2 * ((m + 1 : ℕ) : NNReal) := by
  rw [Kakeya.factoringStep1PigeonholeConstant_eq]
  exact mul_le_mul' le_rfl (fiber_le_of_le_two_pow h)

lemma natLog_le_of_le_two_pow {x m : ℕ} (h : ((x : ℕ) : NNReal) ≤ 2 ^ m) :
    Nat.log 2 x ≤ m := by
  have hx : x ≤ 2 ^ m := by
    have : ((x : ℕ) : NNReal) ≤ ((2 ^ m : ℕ) : NNReal) := by push_cast at h ⊢; exact h
    exact_mod_cast this
  calc Nat.log 2 x ≤ Nat.log 2 (2 ^ m) := Nat.log_mono_right hx
    _ = m := Nat.log_pow (by norm_num) m

lemma natLog_succ_le_of_le_two_pow {x m : ℕ} (h : ((x : ℕ) : NNReal) ≤ 2 ^ m) :
    ((Nat.log 2 x + 1 : ℕ) : NNReal) ≤ ((m + 1 : ℕ) : NNReal) := by
  have := natLog_le_of_le_two_pow h
  exact_mod_cast Nat.succ_le_succ this

/-- `⌈x⌉₊ ≤ 2 ^ m` from `x ≤ 2 ^ m`. -/
lemma ceil_le_two_pow {x : NNReal} {m : ℕ} (h : x ≤ 2 ^ m) : ⌈(x : ℝ)⌉₊ ≤ 2 ^ m := by
  refine Nat.ceil_le.2 ?_
  have : (x : ℝ) ≤ ((2 ^ m : NNReal) : ℝ) := NNReal.coe_le_coe.2 h
  push_cast at this ⊢
  exact this

lemma twoPowExponent_le_of_le_two_pow {x : NNReal} {m : ℕ} (h : x ≤ 2 ^ m) :
    Kakeya.ThinCase.twoPowExponent x ≤ m + 1 := by
  rw [Kakeya.ThinCase.twoPowExponent]
  refine Nat.succ_le_succ ?_
  calc Nat.log 2 ⌈(x : ℝ)⌉₊ ≤ Nat.log 2 (2 ^ m) := Nat.log_mono_right (ceil_le_two_pow h)
    _ = m := Nat.log_pow (by norm_num) m

lemma lin_le_mul_succ (a b m : ℕ) : a * m + b ≤ (a + b) * (m + 1) := by
  calc a * m + b ≤ (a + b) * m + (a + b) :=
        Nat.add_le_add (Nat.mul_le_mul_right m (Nat.le_add_right a b))
          (Nat.le_add_left b a)
    _ = (a + b) * (m + 1) := by ring

/-- Linear-in-`m` natural bounds fold into `c * (m+1)`. -/
lemma cast_lin_le {a b c m : ℕ} (ha : a ≤ c) (hb : b ≤ c) :
    ((a * m + b : ℕ) : NNReal) ≤ ((c : ℕ) : NNReal) * ((m + 1 : ℕ) : NNReal) := by
  have h : a * m + b ≤ c * (m + 1) := by
    calc a * m + b ≤ c * m + c := Nat.add_le_add (Nat.mul_le_mul_right m ha) hb
      _ = c * (m + 1) := by ring
  calc ((a * m + b : ℕ) : NNReal) ≤ ((c * (m + 1) : ℕ) : NNReal) := by exact_mod_cast h
    _ = ((c : ℕ) : NNReal) * ((m + 1 : ℕ) : NNReal) := by push_cast; ring

lemma netCardBound_le {w₁ : NNReal} {m : ℕ} (hw : w₁⁻¹ ≤ 2 ^ m) :
    ((Kakeya.ThinCase.netCardBound 3 ((w₁ : ℝ) / 8) 2 : ℕ) : NNReal) ≤ 2 ^ (3 * m + 18) * 1 := by
  rw [mul_one, Kakeya.ThinCase.netCardBound]
  have hwr : (1 : ℝ) / (w₁ : ℝ) ≤ (2 : ℝ) ^ m := by
    have : ((w₁⁻¹ : NNReal) : ℝ) ≤ ((2 ^ m : NNReal) : ℝ) := NNReal.coe_le_coe.2 hw
    push_cast at this
    rcases eq_or_lt_of_le w₁.coe_nonneg with h0 | h0
    · rw [← h0]; simp
    · rw [one_div]; simpa [h0] using this
  have h1 : (1 : ℝ) ≤ (2 : ℝ) ^ m := one_le_pow₀ (by norm_num)
  have hstep : (1 : ℝ) + 2 * 2 / ((w₁ : ℝ) / 8) ≤ (2 : ℝ) ^ (m + 6) := by
    have hd : (2 : ℝ) * 2 / ((w₁ : ℝ) / 8) = 32 * (1 / (w₁ : ℝ)) := by
      rw [div_div_eq_mul_div]
      ring
    rw [hd, pow_add]
    have : (32 : ℝ) * (1 / (w₁ : ℝ)) ≤ 32 * (2 : ℝ) ^ m := by nlinarith
    nlinarith
  have hpos : (0 : ℝ) ≤ 1 + 2 * 2 / ((w₁ : ℝ) / 8) := by positivity
  have hcube : ((1 : ℝ) + 2 * 2 / ((w₁ : ℝ) / 8)) ^ 3 ≤ ((2 : ℝ) ^ (m + 6)) ^ 3 :=
    pow_le_pow_left₀ hpos hstep 3
  have hval : (((2 : ℝ) ^ (m + 6)) ^ 3) = (((2 ^ (3 * m + 18) : ℕ) : ℝ)) := by
    push_cast
    rw [← pow_mul]
    congr 1
    ring
  have hceil : ⌈((1 : ℝ) + 2 * 2 / ((w₁ : ℝ) / 8)) ^ 3⌉₊ ≤ 2 ^ (3 * m + 18) := by
    refine Nat.ceil_le.2 ?_
    calc ((1 : ℝ) + 2 * 2 / ((w₁ : ℝ) / 8)) ^ 3 ≤ ((2 : ℝ) ^ (m + 6)) ^ 3 := hcube
      _ = (((2 ^ (3 * m + 18) : ℕ) : ℝ)) := hval
  calc ((⌈((1 : ℝ) + 2 * 2 / ((w₁ : ℝ) / 8)) ^ 3⌉₊ : ℕ) : NNReal)
      ≤ ((2 ^ (3 * m + 18) : ℕ) : NNReal) := by exact_mod_cast hceil
    _ = 2 ^ (3 * m + 18) := by push_cast; ring

lemma ballNetLoss_le {w₁ : NNReal} {m : ℕ} (hw : w₁⁻¹ ≤ 2 ^ m) :
    Kakeya.ThinCase.ballNetLoss 3 ((w₁ : ℝ) / 8) 2 ≤ 4750 * ((m + 1 : ℕ) : NNReal) := by
  rw [Kakeya.ThinCase.ballNetLoss]
  have hf := fiber_le_of_le_two_pow (netCardBound_le (w₁ := w₁) (m := m) hw)
  have hlin : (((3 * m + 18 + 1 : ℕ)) : NNReal) ≤ ((19 : ℕ) : NNReal) * ((m + 1 : ℕ) : NNReal) := by
    have h := cast_lin_le (a := 3) (b := 19) (c := 19) (m := m) (by norm_num) le_rfl
    push_cast at h ⊢
    linarith
  calc (5 : NNReal) ^ 3 * (2 * Kakeya.factoringStep1FiberPigeonholeConstant 1
        (Kakeya.ThinCase.netCardBound 3 ((w₁ : ℝ) / 8) 2))
      ≤ 5 ^ 3 * (2 * (((3 * m + 18 + 1 : ℕ)) : NNReal)) := by gcongr
    _ ≤ 5 ^ 3 * (2 * (((19 : ℕ) : NNReal) * ((m + 1 : ℕ) : NNReal))) := by gcongr
    _ = 4750 * ((m + 1 : ℕ) : NNReal) := by push_cast; ring

lemma logb_le_of_le_two_pow {x : ℝ} {m : ℕ} (hx0 : 0 ≤ x) (hx : x ≤ (2 : ℝ) ^ m) :
    Real.logb 2 x ≤ (m : ℝ) := by
  rcases eq_or_lt_of_le hx0 with h0 | h0
  · rw [← h0]; simp
  · calc Real.logb 2 x ≤ Real.logb 2 ((2 : ℝ) ^ m) :=
        Real.logb_le_logb_of_le (by norm_num) h0 hx
      _ = (m : ℝ) := by rw [Real.logb_pow]; simp

/-- Three `2 ^ m` bounds multiply to a `2 ^ (3 * m)` bound. -/
lemma mul_three_le {x y z : NNReal} {m : ℕ} (hx : x ≤ 2 ^ m) (hy : y ≤ 2 ^ m)
    (hz : z ≤ 2 ^ m) : x * y * z ≤ 2 ^ (3 * m) := by
  calc x * y * z ≤ 2 ^ m * 2 ^ m * 2 ^ m := by gcongr
    _ = 2 ^ (3 * m) := by rw [← pow_add, ← pow_add]; congr 1; ring

lemma fibreDensityBandLoss_le {CF : NNReal} {ns m : ℕ}
    (hns : ((ns : ℕ) : NNReal) ≤ 2 ^ m) (hCF : CF ≤ 2 ^ m)
    (hV : Metric.volume_comparison.C 3 ≤ 2 ^ m) :
    (Kakeya.ThinCase.fibreDensityBandLoss 3 CF ns).toNNReal ≤
      ((3 : ℕ) : NNReal) * ((m + 1 : ℕ) : NNReal) := by
  rw [Kakeya.ThinCase.fibreDensityBandLoss, ENNReal.ofReal, ENNReal.toNNReal_coe,
    Real.toNNReal_le_iff_le_coe]
  have hprod : ((ns : ℕ) : NNReal) * (Metric.volume_comparison.C 3 * CF) ≤ 2 ^ (3 * m) := by
    have := mul_three_le (x := ((ns : ℕ) : NNReal)) (y := Metric.volume_comparison.C 3)
      (z := CF) (m := m) hns hV hCF
    calc ((ns : ℕ) : NNReal) * (Metric.volume_comparison.C 3 * CF)
        = ((ns : ℕ) : NNReal) * Metric.volume_comparison.C 3 * CF := by ring
      _ ≤ 2 ^ (3 * m) := this
  have hprodr : ((ns : ℕ) : ℝ) * ((Metric.volume_comparison.C 3 * CF : NNReal) : ℝ) ≤
      (2 : ℝ) ^ (3 * m) := by
    have := NNReal.coe_le_coe.2 hprod
    push_cast at this ⊢
    exact this
  have hlog := logb_le_of_le_two_pow (x := ((ns : ℕ) : ℝ) *
    ((Metric.volume_comparison.C 3 * CF : NNReal) : ℝ)) (m := 3 * m) (by positivity) hprodr
  push_cast at hlog ⊢
  linarith

lemma thinEccentricityExponent_le {CF : NNReal} {ns m : ℕ}
    (hns : ((ns : ℕ) : NNReal) ≤ 2 ^ m) (hCF : CF ≤ 2 ^ m)
    (hV : Metric.volume_comparison.C 3 ≤ 2 ^ m) :
    Kakeya.ThinCase.thinEccentricityExponent 3 ns CF ≤ 3 * m + 1 := by
  rw [Kakeya.ThinCase.thinEccentricityExponent]
  exact twoPowExponent_le_of_le_two_pow (mul_three_le hCF hns hV)

lemma step2Step3_le {ns m : ℕ} (hns : ((ns : ℕ) : NNReal) ≤ 2 ^ m) :
    ((Kakeya.factoringStep2Step3Constant ns : ℕ) : NNReal) ≤
      4 * ((m + 1 : ℕ) : NNReal) ^ 4 := by
  rw [Kakeya.factoringStep2Step3Constant_eq]
  have h := natLog_succ_le_of_le_two_pow hns
  push_cast
  push_cast at h
  gcongr

lemma coverCardBound_le {w₁ : NNReal} {m : ℕ} (hw1 : w₁ ≤ 1) (hw : w₁⁻¹ ≤ 2 ^ m) :
    ShadedBody.factoringCoreAtScaleCoverCardBound 3 w₁ ≤ 2 ^ (3 * m + 6) := by
  rw [ShadedBody.factoringCoreAtScaleCoverCardBound]
  have h1 : (1 : ℝ) ≤ (2 : ℝ) ^ m := one_le_pow₀ (by norm_num)
  have hwr : (1 : ℝ) / (w₁ : ℝ) ≤ (2 : ℝ) ^ m := by
    have : ((w₁⁻¹ : NNReal) : ℝ) ≤ ((2 ^ m : NNReal) : ℝ) := NNReal.coe_le_coe.2 hw
    push_cast at this
    rcases eq_or_lt_of_le w₁.coe_nonneg with h0 | h0
    · rw [← h0]; simp
    · rw [one_div]; simpa [h0] using this
  have hw1r : (w₁ : ℝ) ≤ 1 := NNReal.coe_le_coe.2 hw1
  have hstep : (2 : ℝ) * (1 + (w₁ : ℝ)) / (w₁ : ℝ) ≤ (2 : ℝ) ^ (m + 2) := by
    have hle : (2 : ℝ) * (1 + (w₁ : ℝ)) / (w₁ : ℝ) ≤ 4 * (1 / (w₁ : ℝ)) := by
      rcases eq_or_lt_of_le w₁.coe_nonneg with h0 | h0
      · rw [← h0]; simp
      · rw [div_le_iff₀ h0]
        rw [one_div]
        field_simp
        nlinarith
    rw [pow_add]
    nlinarith
  have hpos : (0 : ℝ) ≤ 2 * (1 + (w₁ : ℝ)) / (w₁ : ℝ) := by positivity
  have hcube : ((2 : ℝ) * (1 + (w₁ : ℝ)) / (w₁ : ℝ)) ^ 3 ≤ ((2 : ℝ) ^ (m + 2)) ^ 3 :=
    pow_le_pow_left₀ hpos hstep 3
  rw [← NNReal.coe_le_coe]
  rw [Real.coe_toNNReal _ (by positivity)]
  push_cast
  calc ((2 : ℝ) * (1 + (w₁ : ℝ)) / (w₁ : ℝ)) ^ 3 ≤ ((2 : ℝ) ^ (m + 2)) ^ 3 := hcube
    _ = (2 : ℝ) ^ (3 * m + 6) := by rw [← pow_mul]; congr 1; ring

lemma step5Self_le {K : NNReal} {k : ℕ} (hK : K ≤ 2 ^ k) :
    ShadedBody.Kakeya.factoringStep5SelfPigeonholeConstant 3 K ≤
      1000 * ((k + 1 : ℕ) : NNReal) := by
  rw [ShadedBody.Kakeya.factoringStep5SelfPigeonholeConstant]
  have hf : Kakeya.factoringStep1FiberPigeonholeConstant 1 K ≤ ((k + 1 : ℕ) : NNReal) :=
    fiber_le_of_le_two_pow (by simpa using hK)
  have hov : ((Kakeya.factoringStep5OverlapConstant 3 : ℕ) : NNReal) = 125 := by
    rw [Kakeya.factoringStep5OverlapConstant]
    push_cast
    norm_num
  rw [hov]
  calc (4 : NNReal) * 125 * (2 * Kakeya.factoringStep1FiberPigeonholeConstant 1 K)
      ≤ 4 * 125 * (2 * ((k + 1 : ℕ) : NNReal)) := by gcongr
    _ = 1000 * ((k + 1 : ℕ) : NNReal) := by ring

lemma pigeon_le_of_div_le {a b : NNReal} {m : ℕ} (ha : a ≠ 0) (h : b / a ≤ 2 ^ m) :
    Kakeya.factoringStep1PigeonholeConstant a b ≤ 2 * ((m + 1 : ℕ) : NNReal) := by
  refine pigeon_le_of_le_two_pow ?_
  calc b = b / a * a := by rw [div_mul_cancel₀ _ ha]
    _ ≤ 2 ^ m * a := by gcongr

/-- `2 ^ m` bounds multiply. -/
lemma mul_two_pow_le {x y : NNReal} {j k : ℕ} (hx : x ≤ 2 ^ j) (hy : y ≤ 2 ^ k) :
    x * y ≤ 2 ^ (j + k) := by
  calc x * y ≤ 2 ^ j * 2 ^ k := by gcongr
    _ = 2 ^ (j + k) := by rw [← pow_add]

lemma pow_le_two_pow {x : NNReal} {j n : ℕ} (hx : x ≤ 2 ^ j) : x ^ n ≤ 2 ^ (j * n) := by
  calc x ^ n ≤ (2 ^ j) ^ n := by gcongr
    _ = 2 ^ (j * n) := by rw [← pow_mul]

lemma weightedStep1_le {ns N m : ℕ} (hns : ((ns : ℕ) : NNReal) ≤ 2 ^ m)
    (hV : Metric.volume_comparison.C 3 ≤ 2 ^ m) (hN : N ≤ 3 * m + 1) :
    ShadedBody.FactorFamily.weightedStep1AtScaleConstant 3 ns N ≤
      10 * ((m + 1 : ℕ) : NNReal) := by
  rw [ShadedBody.FactorFamily.weightedStep1AtScaleConstant]
  have hz : Metric.volume_comparison.C 3 * 2 ^ N ≠ 0 := by
    have := (Metric.volume_comparison.C_pos 3).ne'
    positivity
  have hkey : Kakeya.weightedStep1UpperBd ns ≤
      2 ^ (5 * m + 1) * Kakeya.weightedStep1LowerBd 3 N := by
    rw [Kakeya.weightedStep1UpperBd, Kakeya.weightedStep1LowerBd]
    have hprod : ((ns : ℕ) : NNReal) * (Metric.volume_comparison.C 3 * 2 ^ N) ≤
        2 ^ (5 * m + 1) := by
      have h2N : (2 : NNReal) ^ N ≤ 2 ^ (3 * m + 1) := by
        exact pow_le_pow_right₀ (by norm_num) hN
      calc ((ns : ℕ) : NNReal) * (Metric.volume_comparison.C 3 * 2 ^ N)
          ≤ 2 ^ m * (2 ^ m * 2 ^ (3 * m + 1)) := by gcongr
        _ = 2 ^ (5 * m + 1) := by rw [← pow_add, ← pow_add]; congr 1; ring
    calc ((ns : ℕ) : NNReal)
        = ((ns : ℕ) : NNReal) * (Metric.volume_comparison.C 3 * 2 ^ N) *
            (Metric.volume_comparison.C 3 * 2 ^ N)⁻¹ := by
          rw [mul_inv_cancel_right₀ hz]
      _ ≤ 2 ^ (5 * m + 1) * (Metric.volume_comparison.C 3 * 2 ^ N)⁻¹ := by gcongr
  have h := pigeon_le_of_le_two_pow hkey
  refine h.trans ?_
  have hlin : ((5 * m + 1 + 1 : ℕ) : NNReal) ≤ ((5 : ℕ) : NNReal) * ((m + 1 : ℕ) : NNReal) := by
    have hh := cast_lin_le (a := 5) (b := 5) (c := 5) (m := m) le_rfl le_rfl
    push_cast at hh ⊢
    linarith
  calc (2 : NNReal) * ((5 * m + 1 + 1 : ℕ) : NNReal)
      ≤ 2 * (((5 : ℕ) : NNReal) * ((m + 1 : ℕ) : NNReal)) := by gcongr
    _ = 10 * ((m + 1 : ℕ) : NNReal) := by push_cast; ring

lemma uniformRefinement_inv_le {ns N m : ℕ} {w₁ : NNReal}
    (hns : ((ns : ℕ) : NNReal) ≤ 2 ^ m) (hV : Metric.volume_comparison.C 3 ≤ 2 ^ m)
    (hN : N ≤ 3 * m + 1) (hw1 : w₁ ≤ 1) (hw : w₁⁻¹ ≤ 2 ^ m) :
    (ShadedBody.factoringCoreAtScaleUniformRefinementConstant 3 ns N w₁)⁻¹ ≤
      280000 * ((m + 1 : ℕ) : NNReal) ^ 6 := by
  rw [ShadedBody.factoringCoreAtScaleUniformRefinementConstant,
    ShadedBody.Kakeya.factoringWeightedPipelineSelfRefinementConstant]
  simp only [mul_inv, inv_inv]
  have hW := weightedStep1_le hns hV hN
  have hS23 := step2Step3_le hns
  have hS5 : ShadedBody.Kakeya.factoringStep5SelfPigeonholeConstant 3
      (ShadedBody.factoringCoreAtScaleCoverCardBound 3 w₁) ≤
      1000 * ((3 * m + 6 + 1 : ℕ) : NNReal) := step5Self_le (coverCardBound_le hw1 hw)
  have hlin : ((3 * m + 6 + 1 : ℕ) : NNReal) ≤ ((7 : ℕ) : NNReal) * ((m + 1 : ℕ) : NNReal) := by
    have hh := cast_lin_le (a := 3) (b := 7) (c := 7) (m := m) (by norm_num) le_rfl
    push_cast at hh ⊢
    linarith
  set M : NNReal := ((m + 1 : ℕ) : NNReal) with hM
  calc ShadedBody.FactorFamily.weightedStep1AtScaleConstant 3 ns N *
        ((Kakeya.factoringStep2Step3Constant ns : ℕ) : NNReal) *
        ShadedBody.Kakeya.factoringStep5SelfPigeonholeConstant 3
          (ShadedBody.factoringCoreAtScaleCoverCardBound 3 w₁)
      ≤ (10 * M) * (4 * M ^ 4) * (1000 * (((7 : ℕ) : NNReal) * M)) := by
        gcongr
        exact hS5.trans (by gcongr)
    _ = 280000 * M ^ 6 := by push_cast; ring

lemma thinRetentionLoss_le {ns nb m : ℕ} {w₁ : NNReal}
    (hns : ((ns : ℕ) : NNReal) ≤ 2 ^ m) (hnb : ((nb : ℕ) : NNReal) ≤ 2 ^ m)
    (hw : w₁⁻¹ ≤ 2 ^ m) :
    Kakeya.ThinCase.thinRetentionLoss 3 ns nb ((w₁ : ℝ) / 8) 2 ≤
      2375000 * ((m + 1 : ℕ) : NNReal) ^ 3 := by
  rw [Kakeya.ThinCase.thinRetentionLoss]
  set M : NNReal := ((m + 1 : ℕ) : NNReal) with hM
  have h1 : ((Nat.log 2 ns + 1 : ℕ) : NNReal) ≤ M := natLog_succ_le_of_le_two_pow hns
  have h2 : ((Nat.log 2 nb + 1 : ℕ) : NNReal) ≤ M := natLog_succ_le_of_le_two_pow hnb
  have h3 := ballNetLoss_le (w₁ := w₁) (m := m) hw
  rw [← hM] at h3
  calc ((Nat.log 2 ns + 1 : ℕ) : NNReal) * (4 * Kakeya.ThinCase.ballNetLoss 3 ((w₁ : ℝ) / 8) 2) *
        ((5 : NNReal) ^ 3 * ((Nat.log 2 nb + 1 : ℕ) : NNReal))
      ≤ M * (4 * (4750 * M)) * ((5 : NNReal) ^ 3 * M) := by gcongr
    _ = 2375000 * M ^ 3 := by ring

lemma collarCompare_eq {w₁ : NNReal} (hw0 : 0 < w₁) :
    Kakeya.ThinCase.collarCompareConstant 3 (2 * ((w₁ : ℝ) / 8)) (4 * (w₁ : ℝ)) = 46656 := by
  rw [Kakeya.ThinCase.collarCompareConstant]
  have hw : (w₁ : ℝ) ≠ 0 := ne_of_gt hw0
  have : (2 * (4 * (w₁ : ℝ) + 2 * (2 * ((w₁ : ℝ) / 8))) / (2 * ((w₁ : ℝ) / 8))) ^ 3
      = (46656 : ℝ) := by
    field_simp
    ring
  rw [this]
  rw [← NNReal.coe_inj, Real.coe_toNNReal _ (by norm_num)]
  norm_num

lemma bound_absorb {x c C M : NNReal} {k K : ℕ} (hM : 1 ≤ M) (h : x ≤ c * M ^ k)
    (hc : c ≤ C) (hk : k ≤ K) : x ≤ C * M ^ K := by
  refine h.trans ?_
  have hpow : M ^ k ≤ M ^ K := pow_le_pow_right₀ hM hk
  gcongr

lemma one_le_M (m : ℕ) : (1 : NNReal) ≤ ((m + 1 : ℕ) : NNReal) := by
  push_cast
  simp

lemma globalRetention_inv_le {ns nb N m : ℕ} {CF w₁ : NNReal}
    (hns : ((ns : ℕ) : NNReal) ≤ 2 ^ m) (hnb : ((nb : ℕ) : NNReal) ≤ 2 ^ m)
    (hCF : CF ≤ 2 ^ m) (hV : Metric.volume_comparison.C 3 ≤ 2 ^ m)
    (hN : N ≤ 3 * m + 1) (hw1 : w₁ ≤ 1) (hw : w₁⁻¹ ≤ 2 ^ m) :
    (Kakeya.ThinCase.thinGlobalRetention 3 ns nb CF w₁ N)⁻¹ ≤
      1995000000000 * ((m + 1 : ℕ) : NNReal) ^ 10 := by
  rw [Kakeya.ThinCase.thinGlobalRetention]
  simp only [mul_inv, inv_inv]
  set M : NNReal := ((m + 1 : ℕ) : NNReal) with hM
  have hc := uniformRefinement_inv_le (ns := ns) (N := N) (m := m) (w₁ := w₁) hns hV hN hw1 hw
  have hL := thinRetentionLoss_le (ns := ns) (nb := nb) (m := m) (w₁ := w₁) hns hnb hw
  have hB := fibreDensityBandLoss_le (CF := CF) (ns := ns) (m := m) hns hCF hV
  rw [← hM] at hc hL hB
  have hB' : (Kakeya.ThinCase.fibreDensityBandLoss 3 CF ns).toNNReal ≤ 3 * M := by
    refine hB.trans ?_
    push_cast
    exact le_rfl
  calc (ShadedBody.factoringCoreAtScaleUniformRefinementConstant 3 ns N w₁)⁻¹ *
        (Kakeya.ThinCase.thinRetentionLoss 3 ns nb ((w₁ : ℝ) / 8) 2 *
          (Kakeya.ThinCase.fibreDensityBandLoss 3 CF ns).toNNReal)
      ≤ (280000 * M ^ 6) * ((2375000 * M ^ 3) * (3 * M)) := by gcongr
    _ = 1995000000000 * M ^ 10 := by ring

/-- The `δ`-free constant of the envelope bound. -/
noncomputable def envConst : NNReal :=
  18522 + 665000000000 + 1995000000000 +
    2 * ShadedBody.lambdaInducedSingleWUniform.C * 3 * (46656 * 16000) *
      1995000000000 ^ 2 * (Metric.volume_comparison.C 3)⁻¹

lemma thinEnvelopeTerm_le {ns nb m : ℕ} {CF w₁ : NNReal}
    (hns : ((ns : ℕ) : NNReal) ≤ 2 ^ m) (hnb : ((nb : ℕ) : NNReal) ≤ 2 ^ m)
    (hCF : CF ≤ 2 ^ m) (hV : Metric.volume_comparison.C 3 ≤ 2 ^ m)
    (hw0 : 0 < w₁) (hw1 : w₁ ≤ 1) (hw : w₁⁻¹ ≤ 2 ^ m) :
    Kakeya.ThinCase.thinEnvelopeTerm 3 ns nb CF w₁ ≤
      envConst * ((m + 1 : ℕ) : NNReal) ^ 21 := by
  set M : NNReal := ((m + 1 : ℕ) : NNReal) with hM
  have hM1 : (1 : NNReal) ≤ M := by rw [hM]; exact one_le_M m
  set N : ℕ := Kakeya.ThinCase.thinEccentricityExponent 3 ns CF with hNdef
  have hN : N ≤ 3 * m + 1 := thinEccentricityExponent_le hns hCF hV
  have hc := uniformRefinement_inv_le (ns := ns) (N := N) (m := m) (w₁ := w₁) hns hV hN hw1 hw
  have hL := thinRetentionLoss_le (ns := ns) (nb := nb) (m := m) (w₁ := w₁) hns hnb hw
  have hθ := globalRetention_inv_le (ns := ns) (nb := nb) (N := N) (m := m) (CF := CF)
    (w₁ := w₁) hns hnb hCF hV hN hw1 hw
  rw [← hM] at hc hL hθ
  have hNM : ((N : NNReal) + 1) ≤ 3 * M := by
    have h1 : (N : NNReal) ≤ ((3 * m + 1 : ℕ) : NNReal) := by exact_mod_cast hN
    have h2 : ((3 * m + 1 : ℕ) : NNReal) + 1 ≤ 3 * M := by
      rw [hM]; push_cast; ring_nf; nlinarith [Nat.cast_nonneg (α := NNReal) m]
    calc (N : NNReal) + 1 ≤ ((3 * m + 1 : ℕ) : NNReal) + 1 := by gcongr
      _ ≤ 3 * M := h2
  rw [Kakeya.ThinCase.thinEnvelopeTerm]
  refine max_le ?_ (max_le ?_ (max_le ?_ ?_))
  · -- branch (iv): a purely dimensional constant
    rw [Kakeya.ThinCase.equalRadiusMultConstant]
    refine bound_absorb (k := 0) hM1 (c := 18522) ?_ ?_ (Nat.zero_le _)
    · norm_num
    · rw [envConst]
      exact le_add_of_le_of_nonneg (le_add_of_le_of_nonneg
        (le_add_of_le_of_nonneg le_rfl zero_le) zero_le) zero_le
  · -- branch: `c⁻¹ · L`
    refine bound_absorb (k := 9) (c := 665000000000) hM1 ?_ ?_ (by norm_num)
    · calc (ShadedBody.factoringCoreAtScaleUniformRefinementConstant 3 ns N w₁)⁻¹ *
            Kakeya.ThinCase.thinRetentionLoss 3 ns nb ((w₁ : ℝ) / 8) 2
          ≤ (280000 * M ^ 6) * (2375000 * M ^ 3) := by gcongr
        _ = 665000000000 * M ^ 9 := by ring
    · rw [envConst]
      exact le_add_of_le_of_nonneg (le_add_of_le_of_nonneg
        (le_add_of_nonneg_of_le zero_le le_rfl) zero_le) zero_le
  · -- branch (vi): `θ⁻¹`
    refine bound_absorb (k := 10) (c := 1995000000000) hM1 hθ ?_ (by norm_num)
    rw [envConst]
    exact le_add_of_le_of_nonneg (le_add_of_nonneg_of_le zero_le le_rfl) zero_le
  · -- branch (i): quadratic in the retention loss
    rw [collarCompare_eq hw0, Kakeya.ThinCase.cellCollarConstant]
    have hcell : ((2 * 20 ^ 3 : ℕ) : NNReal) = 16000 := by push_cast; norm_num
    rw [hcell, div_eq_mul_inv, mul_inv, ← inv_pow]
    refine bound_absorb (k := 21)
      (c := 2 * ShadedBody.lambdaInducedSingleWUniform.C * 3 * (46656 * 16000) *
        1995000000000 ^ 2 * (Metric.volume_comparison.C 3)⁻¹) hM1 ?_ ?_ le_rfl
    · calc 2 * ShadedBody.lambdaInducedSingleWUniform.C * ((N : NNReal) + 1) *
              (46656 * 16000) *
            ((Kakeya.ThinCase.thinGlobalRetention 3 ns nb CF w₁ N)⁻¹ ^ 2 *
              (Metric.volume_comparison.C 3)⁻¹)
          ≤ 2 * ShadedBody.lambdaInducedSingleWUniform.C * (3 * M) * (46656 * 16000) *
              ((1995000000000 * M ^ 10) ^ 2 * (Metric.volume_comparison.C 3)⁻¹) := by
            gcongr
        _ = 2 * ShadedBody.lambdaInducedSingleWUniform.C * 3 * (46656 * 16000) *
              1995000000000 ^ 2 * (Metric.volume_comparison.C 3)⁻¹ * M ^ 21 := by ring
    · rw [envConst]
      exact le_add_of_nonneg_of_le zero_le le_rfl

lemma ratio_bound {k m : ℕ} {ρ : NNReal} (hk : ((k : ℕ) : NNReal) ≤ 2 ^ m)
    (hρ : ρ⁻¹ ≤ 2 ^ m) :
    (2 : NNReal) ^ 3 * 6 * ((k : ℕ) : NNReal) * ((ρ : NNReal) ^ 3)⁻¹ ≤ 2 ^ (4 * m + 6) := by
  have hinvpow : ((ρ : NNReal) ^ 3)⁻¹ ≤ 2 ^ (3 * m) := by
    rw [← inv_pow]
    have h := pow_le_two_pow (x := ρ⁻¹) (j := m) (n := 3) hρ
    simpa [Nat.mul_comm] using h
  have hnum : (2 : NNReal) ^ 3 * 6 ≤ 2 ^ 6 := by norm_num
  calc (2 : NNReal) ^ 3 * 6 * ((k : ℕ) : NNReal) * ((ρ : NNReal) ^ 3)⁻¹
      ≤ 2 ^ 6 * 2 ^ m * 2 ^ (3 * m) := by
        exact mul_le_mul' (mul_le_mul' hnum hk) hinvpow
    _ = 2 ^ (4 * m + 6) := by rw [← pow_add, ← pow_add]; congr 1; ring

lemma step1AtScale_le {ns m : ℕ} {ρ : NNReal} (hρ0 : 0 < ρ) (hρ : ρ⁻¹ ≤ 2 ^ m)
    (hns : ((ns : ℕ) : NNReal) ≤ 2 ^ m) :
    Kakeya.factoringStep1AtScaleConstant 3 ns ρ ≤ 14 * ((m + 1 : ℕ) : NNReal) := by
  rw [Kakeya.factoringStep1AtScaleConstant_def]
  have hlow : Kakeya.step1LowerBdAtScale 3 ρ ≠ 0 := (Kakeya.step1LowerBdAtScale_pos 3 hρ0).ne'
  have hdiv : Kakeya.step1UpperBdAtScale 3 ns / Kakeya.step1LowerBdAtScale 3 ρ ≤
      2 ^ (4 * m + 6) := by
    rw [Kakeya.step1UpperBdAtScale_div_step1LowerBdAtScale 3 ns hρ0]
    have hfac : ((Nat.factorial 3 : ℕ) : NNReal) = 6 := by norm_num
    rw [hfac]
    exact ratio_bound hns hρ
  have h := pigeon_le_of_div_le hlow hdiv
  refine h.trans ?_
  have hlin : ((4 * m + 6 + 1 : ℕ) : NNReal) ≤ ((7 : ℕ) : NNReal) * ((m + 1 : ℕ) : NNReal) := by
    have hh := cast_lin_le (a := 4) (b := 7) (c := 7) (m := m) (by norm_num) le_rfl
    push_cast at hh ⊢
    linarith
  calc (2 : NNReal) * ((4 * m + 6 + 1 : ℕ) : NNReal)
      ≤ 2 * (((7 : ℕ) : NNReal) * ((m + 1 : ℕ) : NNReal)) := by gcongr
    _ = 14 * ((m + 1 : ℕ) : NNReal) := by push_cast; ring

lemma packingRatio_le {ns m : ℕ} {ρ : NNReal} (hρ0 : 0 < ρ) (hρ : ρ⁻¹ ≤ 2 ^ m)
    (hns : ((ns : ℕ) : NNReal) ≤ 2 ^ m) :
    ShadedBody.step5PackingRatio 3 ns ρ ≤ 2 ^ (4 * m + 9) := by
  rw [ShadedBody.step5PackingRatio, mul_div_assoc,
    Kakeya.step1UpperBdAtScale_div_step1LowerBdAtScale 3 (max 1 ns) hρ0]
  have hfac : ((Nat.factorial 3 : ℕ) : NNReal) = 6 := by norm_num
  rw [hfac]
  have hmax : ((max 1 ns : ℕ) : NNReal) ≤ 2 ^ m := by
    rw [Nat.cast_max]
    refine max_le ?_ hns
    push_cast
    exact one_le_pow₀ (by norm_num : (1 : NNReal) ≤ 2)
  have hA := ratio_bound (k := max 1 ns) (m := m) (ρ := ρ) hmax hρ
  calc (2 : NNReal) ^ 3 * ((2 : NNReal) ^ 3 * 6 * ((max 1 ns : ℕ) : NNReal) *
        ((ρ : NNReal) ^ 3)⁻¹)
      ≤ 2 ^ 3 * 2 ^ (4 * m + 6) := mul_le_mul' le_rfl hA
    _ = 2 ^ (4 * m + 9) := by rw [← pow_add]; congr 1; ring

lemma refinement_inv_le {ns m : ℕ} {ρ : NNReal} (hρ0 : 0 < ρ) (hρ : ρ⁻¹ ≤ 2 ^ m)
    (hns : ((ns : ℕ) : NNReal) ≤ 2 ^ m) :
    (ShadedBody.outerFactoringFamily_refinement.c 3 ns ρ)⁻¹ ≤
      560000 * ((m + 1 : ℕ) : NNReal) ^ 6 := by
  rw [ShadedBody.outerFactoringFamily_refinement.c,
    ShadedBody.Kakeya.factoringPipelineSelfRefinementConstant]
  simp only [mul_inv, inv_inv]
  set M : NNReal := ((m + 1 : ℕ) : NNReal) with hM
  have h1 := step1AtScale_le (ns := ns) (m := m) (ρ := ρ) hρ0 hρ hns
  have h23 := step2Step3_le (ns := ns) (m := m) hns
  have h5 : ShadedBody.Kakeya.factoringStep5SelfPigeonholeConstant 3
      (ShadedBody.step5PackingRatio 3 ns ρ) ≤ 1000 * ((4 * m + 9 + 1 : ℕ) : NNReal) :=
    step5Self_le (packingRatio_le hρ0 hρ hns)
  have hlin : ((4 * m + 9 + 1 : ℕ) : NNReal) ≤ ((10 : ℕ) : NNReal) * M := by
    have hh := cast_lin_le (a := 4) (b := 10) (c := 10) (m := m) (by norm_num) le_rfl
    rw [hM]
    push_cast at hh ⊢
    linarith
  rw [← hM] at h1 h23
  calc Kakeya.factoringStep1AtScaleConstant 3 ns ρ *
        ((Kakeya.factoringStep2Step3Constant ns : ℕ) : NNReal) *
        ShadedBody.Kakeya.factoringStep5SelfPigeonholeConstant 3
          (ShadedBody.step5PackingRatio 3 ns ρ)
      ≤ (14 * M) * (4 * M ^ 4) * (1000 * (((10 : ℕ) : NNReal) * M)) := by
        gcongr
        exact h5.trans (by gcongr)
    _ = 560000 * M ^ 6 := by push_cast; ring

lemma factoringApplyCore_le {ns nb m : ℕ} {ρ : NNReal} (hρ0 : 0 < ρ) (hρ : ρ⁻¹ ≤ 2 ^ m)
    (hns : ((ns : ℕ) : NNReal) ≤ 2 ^ m) (hnb : ((nb : ℕ) : NNReal) ≤ 2 ^ m) :
    Kakeya.ThinCase.factoringApplyCore 3 ns nb ρ ≤ 560000 * ((m + 1 : ℕ) : NNReal) ^ 6 := by
  set M : NNReal := ((m + 1 : ℕ) : NNReal) with hM
  have hM1 : (1 : NNReal) ≤ M := by rw [hM]; exact one_le_M m
  have hM6 : (1 : NNReal) ≤ M ^ 6 := one_le_pow₀ hM1
  have hbig : (560000 : NNReal) ≤ 560000 * M ^ 6 :=
    le_mul_of_one_le_right zero_le hM6
  rw [Kakeya.ThinCase.factoringApplyCore]
  refine max_le ?_ (max_le ?_ (max_le ?_ ?_))
  · exact le_trans (by norm_num) hbig
  · exact refinement_inv_le hρ0 hρ hns
  · rw [ShadedBody.outerFactoringFamily_outerConstMultFat.c]
    refine le_trans ?_ (le_trans (by norm_num : (1 : NNReal) ≤ 560000) hbig)
    rw [inv_le_one₀]
    · exact_mod_cast Nat.succ_le_succ (Nat.zero_le _)
    · exact_mod_cast Nat.succ_pos _
  · refine le_trans (natLog_succ_le_of_le_two_pow hnb) ?_
    rw [← hM]
    calc M = 1 * M ^ 1 := by ring
      _ ≤ 560000 * M ^ 6 := by
          gcongr
          · norm_num
          · norm_num

/-! ### The thin-setup constant is quadratic in the core envelope -/

noncomputable def sc1 (CF c₁ : NNReal) : NNReal :=
  1 + 2 * Metric.volume_comparison.C 3 * CF * c₁⁻¹ ^ 2

noncomputable def sc2 (C₀ CF c₁ : NNReal) : NNReal := 1 + sc1 CF c₁ * (32 * C₀ ^ 2) ^ 3

noncomputable def sc3 (C₀ CF c₁ : NNReal) (D : ℕ) : NNReal :=
  1 + 2 * sc1 CF c₁ + sc2 C₀ CF c₁ +
    2 * ((D : NNReal) + 1) * Kakeya.ThinCase.tubeSegmentNbhdConstant C₀ * c₁⁻¹ *
      sc2 C₀ CF c₁

lemma one_le_sc1 (CF c₁ : NNReal) : 1 ≤ sc1 CF c₁ := by
  rw [sc1]; exact le_add_of_le_of_nonneg le_rfl zero_le

lemma factoringApplyConstant_le {CF c₁ Ccore : NNReal} (hCcore : 1 ≤ Ccore) :
    Kakeya.ThinCase.factoringApplyConstant CF c₁⁻¹ Ccore ≤ sc1 CF c₁ * Ccore := by
  rw [Kakeya.ThinCase.factoringApplyConstant, sc1]
  refine max_le ?_ (max_le ?_ ?_)
  · calc (1 : NNReal) ≤ Ccore := hCcore
      _ = 1 * Ccore := by ring
      _ ≤ (1 + 2 * Metric.volume_comparison.C 3 * CF * c₁⁻¹ ^ 2) * Ccore := by
          gcongr
          exact le_add_of_le_of_nonneg le_rfl zero_le
  · calc Ccore = 1 * Ccore := by ring
      _ ≤ (1 + 2 * Metric.volume_comparison.C 3 * CF * c₁⁻¹ ^ 2) * Ccore := by
          gcongr
          exact le_add_of_le_of_nonneg le_rfl zero_le
  · gcongr
    exact le_add_of_nonneg_of_le zero_le le_rfl

lemma centredMultConstant_le {C₀ CF c₁ Ccore : NNReal} (hCcore : 1 ≤ Ccore) :
    Kakeya.ThinCase.centredMultConstant
        (Kakeya.ThinCase.factoringApplyConstant CF c₁⁻¹ Ccore) (8 * C₀ ^ 2) 3 ≤
      sc2 C₀ CF c₁ * Ccore := by
  rw [Kakeya.ThinCase.centredMultConstant, sc2]
  refine max_le ?_ ?_
  · calc (1 : NNReal) ≤ Ccore := hCcore
      _ = 1 * Ccore := by ring
      _ ≤ (1 + sc1 CF c₁ * (32 * C₀ ^ 2) ^ 3) * Ccore := by
          gcongr
          exact le_add_of_le_of_nonneg le_rfl zero_le
  · have hF := factoringApplyConstant_le (CF := CF) (c₁ := c₁) hCcore
    have hpow : (4 * (8 * C₀ ^ 2)) ^ 3 = (32 * C₀ ^ 2) ^ 3 := by ring_nf
    rw [hpow]
    calc Kakeya.ThinCase.factoringApplyConstant CF c₁⁻¹ Ccore * (32 * C₀ ^ 2) ^ 3
        ≤ (sc1 CF c₁ * Ccore) * (32 * C₀ ^ 2) ^ 3 := by gcongr
      _ = (sc1 CF c₁ * (32 * C₀ ^ 2) ^ 3) * Ccore := by ring
      _ ≤ (1 + sc1 CF c₁ * (32 * C₀ ^ 2) ^ 3) * Ccore := by
          gcongr
          exact le_add_of_nonneg_of_le zero_le le_rfl

lemma perBallConstant_le {C₀ CF c₁ Ccore : NNReal} {D : ℕ} (hCcore : 1 ≤ Ccore) :
    Kakeya.ThinCase.perBallConstant C₀ CF c₁ Ccore D ≤ sc3 C₀ CF c₁ D * Ccore := by
  have hF := factoringApplyConstant_le (CF := CF) (c₁ := c₁) hCcore
  have hcM := centredMultConstant_le (C₀ := C₀) (CF := CF) (c₁ := c₁) hCcore
  rw [Kakeya.ThinCase.perBallConstant, sc3]
  set A := sc1 CF c₁ with hA
  set B := sc2 C₀ CF c₁ with hB
  set T := Kakeya.ThinCase.tubeSegmentNbhdConstant C₀ with hT
  refine max_le ?_ (max_le ?_ (max_le ?_ ?_))
  · calc (1 : NNReal) ≤ Ccore := hCcore
      _ = 1 * Ccore := by ring
      _ ≤ (1 + 2 * A + B + 2 * ((D : NNReal) + 1) * T * c₁⁻¹ * B) * Ccore := by
          gcongr
          exact le_add_of_le_of_nonneg (le_add_of_le_of_nonneg
            (le_add_of_le_of_nonneg le_rfl zero_le) zero_le) zero_le
  · calc 2 * Kakeya.ThinCase.factoringApplyConstant CF c₁⁻¹ Ccore
        ≤ 2 * (A * Ccore) := by gcongr
      _ = (2 * A) * Ccore := by ring
      _ ≤ (1 + 2 * A + B + 2 * ((D : NNReal) + 1) * T * c₁⁻¹ * B) * Ccore := by
          gcongr
          exact le_add_of_le_of_nonneg (le_add_of_le_of_nonneg
            (le_add_of_nonneg_of_le zero_le le_rfl) zero_le) zero_le
  · calc Kakeya.ThinCase.centredMultConstant
          (Kakeya.ThinCase.factoringApplyConstant CF c₁⁻¹ Ccore) (8 * C₀ ^ 2) 3
        ≤ B * Ccore := hcM
      _ ≤ (1 + 2 * A + B + 2 * ((D : NNReal) + 1) * T * c₁⁻¹ * B) * Ccore := by
          gcongr
          exact le_add_of_le_of_nonneg (le_add_of_nonneg_of_le zero_le le_rfl) zero_le
  · calc 2 * ((D : NNReal) + 1) * T * c₁⁻¹ *
          Kakeya.ThinCase.centredMultConstant
            (Kakeya.ThinCase.factoringApplyConstant CF c₁⁻¹ Ccore) (8 * C₀ ^ 2) 3
        ≤ 2 * ((D : NNReal) + 1) * T * c₁⁻¹ * (B * Ccore) := by gcongr
      _ = (2 * ((D : NNReal) + 1) * T * c₁⁻¹ * B) * Ccore := by ring
      _ ≤ (1 + 2 * A + B + 2 * ((D : NNReal) + 1) * T * c₁⁻¹ * B) * Ccore := by
          gcongr
          exact le_add_of_nonneg_of_le zero_le le_rfl

lemma thinSetupConstant_le {C₀ CF c₁ Ccore : NNReal} {D : ℕ} (hCcore : 1 ≤ Ccore) :
    Kakeya.ThinCase.thinSetupConstant C₀ CF c₁ Ccore D 1 ≤
      sc3 C₀ CF c₁ D ^ 2 * Ccore ^ 2 := by
  rw [Kakeya.ThinCase.thinSetupConstant]
  have h := perBallConstant_le (C₀ := C₀) (CF := CF) (c₁ := c₁) (D := D) hCcore
  calc Kakeya.ThinCase.perBallConstant C₀ CF c₁ Ccore D ^ 2 * (1 : NNReal) ^ 2
      = Kakeya.ThinCase.perBallConstant C₀ CF c₁ Ccore D ^ 2 := by ring
    _ ≤ (sc3 C₀ CF c₁ D * Ccore) ^ 2 := by gcongr
    _ = sc3 C₀ CF c₁ D ^ 2 * Ccore ^ 2 := by ring

noncomputable def coreConst : NNReal := envConst + 4750 + 560000 + 1

lemma one_le_coreConst : 1 ≤ coreConst := by
  rw [coreConst]
  exact le_add_of_nonneg_of_le zero_le le_rfl


/-! ### Absorption of a polylogarithmic factor into `δ ^ (-ε)` -/

/-- Local copy of the `∀ᶠ`-free threshold form of
`Tube.exists_threshold_polylog_pow_ssfGridLen_le` at a fixed power. -/
theorem polylog_pow_le (A : ℝ) (hA : 1 ≤ A) (K₀ k : ℕ) (α : ℝ) (hα : 0 < α) :
    ∃ δ₀ : NNReal, 0 < δ₀ ∧ δ₀ ≤ 1 ∧ ∀ {δ : NNReal}, 0 < δ → δ ≤ δ₀ →
      ∀ c : ℝ, 0 ≤ c → c ≤ (δ : ℝ) ^ (-(K₀ : ℝ)) →
        (A * ((⌊Real.logb 2 c⌋₊ : ℝ) + 1)) ^ k ≤ (δ : ℝ) ^ (-α) := by
  obtain ⟨δ₀, h0, h1, h⟩ := Tube.exists_threshold_polylog_pow_ssfGridLen_le A hA K₀ k α hα
  refine ⟨δ₀, h0, h1, fun {δ} hδ hδ0 c hc hcK => ?_⟩
  obtain ⟨-, -, h3⟩ := h hδ hδ0
  have hbase : 1 ≤ A * ((⌊Real.logb 2 c⌋₊ : ℝ) + 1) := by
    have h' : (1 : ℝ) ≤ (⌊Real.logb 2 c⌋₊ : ℝ) + 1 := by
      have := Nat.cast_nonneg (α := ℝ) ⌊Real.logb 2 c⌋₊
      linarith
    calc (1 : ℝ) = 1 * 1 := by ring
      _ ≤ A * ((⌊Real.logb 2 c⌋₊ : ℝ) + 1) := mul_le_mul hA h' zero_le_one (by linarith)
  calc (A * ((⌊Real.logb 2 c⌋₊ : ℝ) + 1)) ^ k
      ≤ (A * ((⌊Real.logb 2 c⌋₊ : ℝ) + 1)) ^ (k * Tube.ssfGridLen δ + k) :=
        pow_le_pow_right₀ hbase (by nlinarith [Nat.zero_le (k * Tube.ssfGridLen δ)])
    _ ≤ (δ : ℝ) ^ (-α) := h3 c hc hcK

/-- The canonical bit budget for `δ⁻¹`: `⌊log₂ δ⁻¹⌋ + 1`. -/
lemma inv_le_two_pow_floor_logb {δ : NNReal} (hδ : 0 < δ) :
    δ⁻¹ ≤ 2 ^ (⌊Real.logb 2 ((δ⁻¹ : NNReal) : ℝ)⌋₊ + 1) := by
  set x : ℝ := ((δ⁻¹ : NNReal) : ℝ) with hx
  have hxpos : 0 < x := by
    rw [hx]
    exact NNReal.coe_pos.2 (inv_pos.2 hδ)
  have hlt : Real.logb 2 x < ((⌊Real.logb 2 x⌋₊ + 1 : ℕ) : ℝ) := by
    have := Nat.lt_floor_add_one (Real.logb 2 x)
    push_cast
    linarith
  have hpow : x < (2 : ℝ) ^ ((⌊Real.logb 2 x⌋₊ + 1 : ℕ) : ℝ) := by
    calc x = (2 : ℝ) ^ Real.logb 2 x := (Real.rpow_logb (by norm_num) (by norm_num) hxpos).symm
      _ < (2 : ℝ) ^ ((⌊Real.logb 2 x⌋₊ + 1 : ℕ) : ℝ) :=
          (Real.rpow_lt_rpow_left_iff (by norm_num)).2 hlt
  have hcast : (2 : ℝ) ^ ((⌊Real.logb 2 x⌋₊ + 1 : ℕ) : ℝ) =
      (((2 : NNReal) ^ (⌊Real.logb 2 x⌋₊ + 1) : NNReal) : ℝ) := by
    rw [Real.rpow_natCast]
    push_cast
    ring
  rw [hcast] at hpow
  rw [← NNReal.coe_le_coe, ← hx]
  exact hpow.le

end Kakeya.ThinSizing

namespace Kakeya.VeryNotSticky

open MeasureTheory Metric Set Topology Filter ShadedBody
open scoped NNReal ENNReal
open Kakeya.ThinSizing

lemma two_le_thinCoreEnvelope (cfg : VeryNotSticky.{u}) (bd : BallData cfg) :
    2 ≤ thinCoreEnvelope cfg bd := by
  obtain ⟨B₀, hB₀⟩ := bd.bs_nonempty
  rw [thinCoreEnvelope]
  refine le_trans ?_ (le_max_right _ _)
  refine le_trans (Kakeya.ThinCase.two_le_factoringApplyCore 3 (bd.segs B₀).card
    (bd.bodies B₀).card cfg.δ) ?_
  refine le_trans (le_max_left _ (Kakeya.ThinCase.factoringApplyCore 3 (bd.segs B₀).card
    (bd.bodies B₀).card (cfg.δ / bd.C₀))) ?_
  exact Finset.le_sup (f := fun B => max
    (Kakeya.ThinCase.factoringApplyCore 3 (bd.segs B).card (bd.bodies B).card cfg.δ)
    (Kakeya.ThinCase.factoringApplyCore 3 (bd.segs B).card (bd.bodies B).card
      (cfg.δ / bd.C₀))) hB₀

lemma thinCoreEnvelope_le {cfg : VeryNotSticky.{u}} {bd : BallData cfg} {m : ℕ}
    (hCF : bd.CF ≤ 2 ^ m) (hV : Metric.volume_comparison.C 3 ≤ 2 ^ m)
    (hw0 : 0 < bd.w₁) (hw1 : bd.w₁ ≤ 1) (hw : bd.w₁⁻¹ ≤ 2 ^ m)
    (hδinv : cfg.δ⁻¹ ≤ 2 ^ m) (hδC₀ : (cfg.δ / bd.C₀)⁻¹ ≤ 2 ^ m) (hC₀0 : 0 < bd.C₀)
    (hsegs : ∀ B ∈ bd.bs, (((bd.segs B).card : ℕ) : NNReal) ≤ 2 ^ m)
    (hbodies : ∀ B ∈ bd.bs, (((bd.bodies B).card : ℕ) : NNReal) ≤ 2 ^ m) :
    thinCoreEnvelope cfg bd ≤ coreConst * ((m + 1 : ℕ) : NNReal) ^ 21 := by
  set M : NNReal := ((m + 1 : ℕ) : NNReal) with hM
  have hM1 : (1 : NNReal) ≤ M := by rw [hM]; exact one_le_M m
  have hδ0 : 0 < cfg.δ := cfg.hδ
  have hδC₀0 : 0 < cfg.δ / bd.C₀ := div_pos hδ0 hC₀0
  rw [thinCoreEnvelope]
  refine max_le (max_le (max_le ?_ ?_) ?_) ?_
  · -- `⌊log₂ ⌈CF⌉⌋ + 1`
    refine bound_absorb (k := 1) (c := 1) hM1 ?_ ?_ (by norm_num)
    · have h := natLog_succ_le_of_le_two_pow (x := ⌈(bd.CF : ℝ)⌉₊) (m := m)
        (by exact_mod_cast ceil_le_two_pow hCF)
      rw [pow_one, one_mul, hM]
      exact h
    · rw [coreConst]
      exact le_add_of_nonneg_of_le zero_le le_rfl
  · -- the ball net loss
    refine bound_absorb (k := 1) (c := 4750) hM1 ?_ ?_ (by norm_num)
    · have h := ballNetLoss_le (w₁ := bd.w₁) (m := m) hw
      rw [pow_one, hM]
      exact h
    · rw [coreConst]
      exact le_add_of_le_of_nonneg (le_add_of_le_of_nonneg
        (le_add_of_nonneg_of_le zero_le le_rfl) zero_le) zero_le
  · -- the envelope term, ball-uniformly
    refine Finset.sup_le fun B hB => ?_
    refine bound_absorb (k := 21) (c := envConst) hM1 ?_ ?_ le_rfl
    · rw [hM]
      exact thinEnvelopeTerm_le (hsegs B hB) (hbodies B hB) hCF hV hw0 hw1 hw
    · rw [coreConst]
      exact le_add_of_le_of_nonneg (le_add_of_le_of_nonneg
        (le_add_of_le_of_nonneg le_rfl zero_le) zero_le) zero_le
  · -- the two `factoringApplyCore` evaluations
    refine Finset.sup_le fun B hB => ?_
    refine max_le ?_ ?_ <;>
      refine bound_absorb (k := 6) (c := 560000) hM1 ?_ ?_ (by norm_num)
    · rw [hM]
      exact factoringApplyCore_le hδ0 hδinv (hsegs B hB) (hbodies B hB)
    · rw [coreConst]
      exact le_add_of_le_of_nonneg (le_add_of_nonneg_of_le zero_le le_rfl) zero_le
    · rw [hM]
      exact factoringApplyCore_le hδC₀0 hδC₀ (hsegs B hB) (hbodies B hB)
    · rw [coreConst]
      exact le_add_of_le_of_nonneg (le_add_of_nonneg_of_le zero_le le_rfl) zero_le

lemma eventually_le_nhdsGT' {c : NNReal} (hc : 0 < c) :
    ∀ᶠ (δ : NNReal) in 𝓝[>] 0, δ ≤ c := by
  filter_upwards [mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds hc)] with δ hδ
  exact le_of_lt hδ

set_option maxHeartbeats 1000000 in
-- the proof threads one bit budget through eleven pipeline constants and closes with a
-- fourteen-step `calc` in `ℝ`; the default budget is not enough for a declaration of this size
/-- **The thin-constant obligation, reduced to the two per-ball cardinality bounds.**

For every `ε > 0`, every pinned `δ`-free constant bundle, and every polynomial bound
`#segs B, #bodies B ≤ C · δ⁻⁴` at each ball, the thin configuration produced by
`Kakeya.VeryNotSticky.exists_thinConfig_C_le` has comparison constant at most `δ^{-ε}`
eventually as `δ → 0⁺`. The two cardinality hypotheses are  -/
theorem exists_thinConfig_le_of_card_bounds (ε : ℝ) (hε : 0 < ε)
    (C₀bd CF c₁ Cg Csegs Cbodies : NNReal) (D Ksegs Kbodies : ℕ) :
    ∀ᶠ δ : NNReal in 𝓝[>] 0, ∀ (cfg : VeryNotSticky.{u}) (bd : BallData cfg),
      cfg.δ = δ → bd.C₀ = C₀bd → bd.CF = CF → bd.c₁ = c₁ → bd.D = D → bd.Cg = Cg →
      bd.Cm = 1 → cfg.δ ≤ bd.w₁ → bd.w₁ ≤ 1 →
      (∀ B ∈ bd.bs, (((bd.segs B).card : ℕ) : NNReal) ≤ Csegs * cfg.δ⁻¹ ^ Ksegs) →
      (∀ B ∈ bd.bs, (((bd.bodies B).card : ℕ) : NNReal) ≤ Cbodies * cfg.δ⁻¹ ^ Kbodies) →
      ∃ tc : ThinConfig cfg bd, tc.C ≤ cfg.δ ^ (-ε) := by
  classical
  set A : NNReal := Cg * ThinSizing.sc3 C₀bd CF c₁ D ^ 2 * ThinSizing.coreConst ^ 2 with hAdef
  set K : ℕ := ThinCase.twoPowExponent CF + ThinCase.twoPowExponent (volume_comparison.C 3)
      + ThinCase.twoPowExponent C₀bd + ThinCase.twoPowExponent Csegs
      + ThinCase.twoPowExponent Cbodies with hKdef
  set J : ℕ := Ksegs + Kbodies + 1 with hJdef
  set A' : ℝ := max 1 ((A : ℝ) * ((K + J + 1 : ℕ) : ℝ) ^ 42) with hA'def
  obtain ⟨δ₀, hδ₀pos, hδ₀one, habs⟩ :=
    ThinSizing.polylog_pow_le A' (le_max_left _ _) 1 42 ε hε
  filter_upwards [eventually_le_nhdsGT' hδ₀pos] with δ hδle
  intro cfg bd hδeq hC₀ hCF hc₁ hD hCg hCm hδw₁ hw₁one hsegs hbodies
  have hδ0 : 0 < cfg.δ := cfg.hδ
  have hδle' : cfg.δ ≤ δ₀ := by rw [hδeq]; exact hδle
  -- the bit budget
  set c : ℝ := ((cfg.δ⁻¹ : NNReal) : ℝ) with hc
  set Λ : ℕ := ⌊Real.logb 2 c⌋₊ + 1 with hΛdef
  have hΛ : cfg.δ⁻¹ ≤ 2 ^ Λ := ThinSizing.inv_le_two_pow_floor_logb hδ0
  set m : ℕ := J * Λ + K with hmdef
  have hJ1 : 1 ≤ J := by rw [hJdef]; omega
  have hΛ1 : 1 ≤ Λ := by rw [hΛdef]; omega
  have hJΛ : Λ ≤ J * Λ := by
    calc Λ = 1 * Λ := by ring
      _ ≤ J * Λ := Nat.mul_le_mul_right Λ hJ1
  have hKm : K ≤ m := by rw [hmdef]; omega
  have hsegsΛ : Ksegs * Λ ≤ J * Λ := Nat.mul_le_mul_right Λ (by rw [hJdef]; omega)
  have hbodiesΛ : Kbodies * Λ ≤ J * Λ := Nat.mul_le_mul_right Λ (by rw [hJdef]; omega)
  have hpow_mono : ∀ {j : ℕ}, j ≤ m → (2 : NNReal) ^ j ≤ 2 ^ m :=
    fun {j} hj => pow_le_pow_right₀ (by norm_num) hj
  have hΛm : Λ ≤ m := by rw [hmdef]; exact le_trans hJΛ (Nat.le_add_right _ _)
  have hδm : cfg.δ⁻¹ ≤ 2 ^ m := hΛ.trans (hpow_mono hΛm)
  have hCFm : bd.CF ≤ 2 ^ m := by
    rw [hCF]
    refine (ThinCase.le_two_pow_twoPowExponent CF).trans (hpow_mono ?_)
    refine le_trans ?_ hKm
    rw [hKdef]; omega
  have hVm : volume_comparison.C 3 ≤ 2 ^ m := by
    refine (ThinCase.le_two_pow_twoPowExponent _).trans (hpow_mono ?_)
    refine le_trans ?_ hKm
    rw [hKdef]; omega
  have hw0 : 0 < bd.w₁ := lt_of_lt_of_le hδ0 hδw₁
  have hwm : bd.w₁⁻¹ ≤ 2 ^ m := le_trans (inv_anti₀ hδ0 hδw₁) hδm
  have hC₀0 : 0 < bd.C₀ := lt_of_lt_of_le zero_lt_one bd.hC₀
  have hδC₀m : (cfg.δ / bd.C₀)⁻¹ ≤ 2 ^ m := by
    rw [inv_div]
    have h1 : bd.C₀ / cfg.δ = bd.C₀ * cfg.δ⁻¹ := by rw [div_eq_mul_inv]
    rw [h1, hC₀]
    have h2 : C₀bd * cfg.δ⁻¹ ≤ 2 ^ ThinCase.twoPowExponent C₀bd * 2 ^ Λ := by
      exact mul_le_mul' (ThinCase.le_two_pow_twoPowExponent C₀bd) hΛ
    refine h2.trans ?_
    rw [← pow_add]
    refine hpow_mono ?_
    rw [hmdef]
    calc ThinCase.twoPowExponent C₀bd + Λ ≤ K + J * Λ :=
          Nat.add_le_add (by rw [hKdef]; omega) hJΛ
      _ = J * Λ + K := Nat.add_comm _ _
  have hcard : ∀ (C : NNReal) (K' : ℕ) (x : NNReal), x ≤ C * cfg.δ⁻¹ ^ K' →
      ThinCase.twoPowExponent C + K' * Λ ≤ m → x ≤ 2 ^ m := by
    intro C K' x hx hle
    refine hx.trans ?_
    have h4 : cfg.δ⁻¹ ^ K' ≤ 2 ^ (K' * Λ) := by
      have := ThinSizing.pow_le_two_pow (x := cfg.δ⁻¹) (j := Λ) (n := K') hΛ
      simpa [Nat.mul_comm] using this
    refine le_trans (mul_le_mul' (ThinCase.le_two_pow_twoPowExponent C) h4) ?_
    rw [← pow_add]
    exact hpow_mono hle
  have hsegsm : ∀ B ∈ bd.bs, (((bd.segs B).card : ℕ) : NNReal) ≤ 2 ^ m := by
    intro B hB
    refine hcard Csegs Ksegs _ (hsegs B hB) ?_
    rw [hmdef]
    calc ThinCase.twoPowExponent Csegs + Ksegs * Λ ≤ K + J * Λ :=
          Nat.add_le_add (by rw [hKdef]; omega) hsegsΛ
      _ = J * Λ + K := Nat.add_comm _ _
  have hbodiesm : ∀ B ∈ bd.bs, (((bd.bodies B).card : ℕ) : NNReal) ≤ 2 ^ m := by
    intro B hB
    refine hcard Cbodies Kbodies _ (hbodies B hB) ?_
    rw [hmdef]
    calc ThinCase.twoPowExponent Cbodies + Kbodies * Λ ≤ K + J * Λ :=
          Nat.add_le_add (by rw [hKdef]; omega) hbodiesΛ
      _ = J * Λ + K := Nat.add_comm _ _
  -- the envelope is polylogarithmic
  have hcore := thinCoreEnvelope_le (cfg := cfg) (bd := bd) (m := m) hCFm hVm hw0 hw₁one hwm
    hδm hδC₀m hC₀0 hsegsm hbodiesm
  have h2core : (2 : NNReal) ≤ thinCoreEnvelope cfg bd := two_le_thinCoreEnvelope cfg bd
  have h1core : (1 : NNReal) ≤ thinCoreEnvelope cfg bd := le_trans one_le_two h2core
  obtain ⟨tc, htc⟩ := exists_thinConfig_C_le cfg bd hδw₁ hw₁one
  refine ⟨tc, ?_⟩
  set M : NNReal := ((m + 1 : ℕ) : NNReal) with hMdef
  have hM1 : (1 : NNReal) ≤ M := by rw [hMdef]; exact ThinSizing.one_le_M m
  -- the comparison constant is `A · M ^ 42`
  have hchain : tc.C ≤ A * M ^ 42 := by
    refine htc.trans ?_
    have hsetup : ThinCase.thinSetupConstant bd.C₀ bd.CF bd.c₁ (thinCoreEnvelope cfg bd) bd.D
        bd.Cm ≤ ThinSizing.sc3 bd.C₀ bd.CF bd.c₁ bd.D ^ 2 * thinCoreEnvelope cfg bd ^ 2 := by
      rw [hCm]
      exact ThinSizing.thinSetupConstant_le h1core
    calc bd.Cg * ThinCase.thinSetupConstant bd.C₀ bd.CF bd.c₁ (thinCoreEnvelope cfg bd) bd.D bd.Cm
        ≤ bd.Cg * (ThinSizing.sc3 bd.C₀ bd.CF bd.c₁ bd.D ^ 2 * thinCoreEnvelope cfg bd ^ 2) := by
          gcongr
      _ ≤ bd.Cg * (ThinSizing.sc3 bd.C₀ bd.CF bd.c₁ bd.D ^ 2 *
            (ThinSizing.coreConst * M ^ 21) ^ 2) := by
          gcongr
      _ = Cg * ThinSizing.sc3 C₀bd CF c₁ D ^ 2 * ThinSizing.coreConst ^ 2 * M ^ 42 := by
          rw [hCg, hC₀, hCF, hc₁, hD]
          ring
      _ = A * M ^ 42 := by rw [hAdef]
  -- absorption
  have hcnn : (0 : ℝ) ≤ c := by rw [hc]; exact NNReal.coe_nonneg _
  have hcK : c ≤ (cfg.δ : ℝ) ^ (-((1 : ℕ) : ℝ)) := by
    rw [Nat.cast_one, Real.rpow_neg_one, hc]
    push_cast
    exact le_rfl
  have hfinal := habs hδ0 hδle' c hcnn hcK
  have hMreal : ((M : NNReal) : ℝ) ≤ ((K + J + 1 : ℕ) : ℝ) * (Λ : ℝ) := by
    have hnat : m + 1 ≤ (K + J + 1) * Λ := by
      have hKΛ : K ≤ K * Λ := by
        calc K = K * 1 := by ring
          _ ≤ K * Λ := Nat.mul_le_mul_left K hΛ1
      calc m + 1 = J * Λ + K + 1 := by rw [hmdef]
        _ ≤ J * Λ + K * Λ + Λ := Nat.add_le_add (Nat.add_le_add_left hKΛ _) hΛ1
        _ = (K + J + 1) * Λ := by ring
    have := (Nat.cast_le (α := ℝ)).2 hnat
    rw [hMdef]
    push_cast at this ⊢
    linarith
  have hApos : (0 : ℝ) ≤ (A : ℝ) := NNReal.coe_nonneg _
  have hAbig : (A : ℝ) * ((K + J + 1 : ℕ) : ℝ) ^ 42 ≤ A' := by rw [hA'def]; exact le_max_right _ _
  have hA'1 : (1 : ℝ) ≤ A' := by rw [hA'def]; exact le_max_left _ _
  have hkey : ((tc.C : NNReal) : ℝ) ≤ (cfg.δ : ℝ) ^ (-ε) := by
    refine le_trans (NNReal.coe_le_coe.2 hchain) ?_
    have hMr : (0 : ℝ) ≤ ((M : NNReal) : ℝ) := NNReal.coe_nonneg _
    have hΛr : (0 : ℝ) ≤ (Λ : ℝ) := Nat.cast_nonneg _
    calc ((A * M ^ 42 : NNReal) : ℝ) = (A : ℝ) * ((M : NNReal) : ℝ) ^ 42 := by push_cast; ring
      _ ≤ (A : ℝ) * (((K + J + 1 : ℕ) : ℝ) * (Λ : ℝ)) ^ 42 := by
          gcongr
      _ = ((A : ℝ) * ((K + J + 1 : ℕ) : ℝ) ^ 42) * (Λ : ℝ) ^ 42 := by ring
      _ ≤ A' * (Λ : ℝ) ^ 42 := by gcongr
      _ ≤ A' ^ 42 * (Λ : ℝ) ^ 42 := by
          gcongr
          calc A' = A' ^ 1 := by ring
            _ ≤ A' ^ 42 := pow_le_pow_right₀ hA'1 (by norm_num)
      _ = (A' * (Λ : ℝ)) ^ 42 := by ring
      _ = (A' * ((⌊Real.logb 2 c⌋₊ : ℝ) + 1)) ^ 42 := by rw [hΛdef]; push_cast; ring
      _ ≤ (cfg.δ : ℝ) ^ (-ε) := hfinal
  rw [← NNReal.coe_le_coe, NNReal.coe_rpow]
  exact hkey

/-! ### The segment count is polynomially bounded -/

/-- **The segment count is polynomially bounded**: `#segs B ≤ δ^{-4}` eventually, for every
`cfg` at density exponent `η ≤ 1` and every `bd`. -/
theorem eventually_card_segs_le {η : ℝ} (hη1 : η ≤ 1) :
    ∀ᶠ δ : NNReal in 𝓝[>] 0, ∀ (cfg : VeryNotSticky.{u}) (bd : BallData cfg),
      cfg.δ = δ → cfg.η = η → ∀ B ∈ bd.bs,
        (((bd.segs B).card : ℕ) : NNReal) ≤ 1 * cfg.δ⁻¹ ^ 4 := by
  filter_upwards [Kakeya.VeryNotSticky.eventually_ennreal_le_rpow_neg
      (K := ((Kakeya.Tube.card_le_of_densityIn_le.C 3 : NNReal) : ENNReal))
      ENNReal.coe_ne_top (ν := (1 : ℝ)) one_pos] with δ hδC
  intro cfg bd hδeq hηeq B hB
  have hδ0 : 0 < cfg.δ := cfg.hδ
  have hδ1 : cfg.δ ≤ 1 := cfg.hδ1
  have hδC' : ((Kakeya.Tube.card_le_of_densityIn_le.C 3 : NNReal) : ENNReal) ≤
      (cfg.δ : ENNReal) ^ (-1 : ℝ) := by rw [hδeq]; exact hδC
  have hmax : Kakeya.maxDensity cfg.s (fun i => (cfg.T i).toConvexSpaceBody) ≤
      (cfg.δ : ENNReal) ^ (-η) := by rw [← hηeq]; exact cfg.maxDensity_le
  have hcard := Kakeya.ML2Assembly.card_le_rpow_neg_four hδ0 hδ1 hδC' cfg.s cfg.T
    cfg.contained hη1 hmax
  have hseg : ((bd.segs B).card : ℝ) ≤ (cfg.s.card : ℝ) := by
    exact_mod_cast card_segs_le_card_tubes cfg bd hB
  have hchain : ((bd.segs B).card : ℝ) ≤ (cfg.δ : ℝ) ^ (-4 : ℝ) := le_trans hseg hcard
  have hrw : (cfg.δ : ℝ) ^ (-4 : ℝ) = ((1 * cfg.δ⁻¹ ^ 4 : NNReal) : ℝ) := by
    push_cast
    rw [one_mul, ← Real.rpow_natCast ((cfg.δ : ℝ))⁻¹ 4, ← Real.rpow_neg_one (cfg.δ : ℝ),
      ← Real.rpow_mul (le_of_lt (NNReal.coe_pos.2 hδ0))]
    norm_num
  rw [hrw] at hchain
  rw [← NNReal.coe_le_coe]
  push_cast at hchain ⊢
  exact hchain


/-! ### The obligation, modulo the body count -/

/-- **`Kakeya.VeryNotSticky.ThinConstantObligation`, modulo the per-ball body count.**

The two inputs are  The segment count is discharged here
(`eventually_card_segs_le`); the body count is the remaining hypothesis `hbodies`, the packing
bound `#bodies B ≤ C(C₀) · δ^{-K}` for the pairwise essentially distinct `(r₁, δ, δ)`-bodies of
a ball (equivalently, an incidence field `bodies_hit`, which would give
`#bodies B ≤ #segs B` outright).

The side condition `η ≤ 1` is not a binder of `ThinConstantObligation`; it is discharged at the
call site from `Kakeya.VeryNotSticky.CaseParams` (`slabDensity : 6 η < exscal` together with
`scale : exscal < 1/2` gives `η < 1/12`). -/
theorem thinConstantObligation_of_card_bodies (β exscal ϱ η ε : ℝ) (hε : 0 < ε) (hη1 : η ≤ 1)
    (C₀bd Cbias CF Cdil c₁ Cg Cbodies : NNReal) (D Kbodies : ℕ)
    (hbodies : ∀ (cfg : VeryNotSticky.{u}) (bd : BallData cfg), ∀ B ∈ bd.bs,
      (((bd.bodies B).card : ℕ) : NNReal) ≤ Cbodies * cfg.δ⁻¹ ^ Kbodies) :
    ThinConstantObligation.{u} β exscal ϱ η ε C₀bd Cbias CF Cdil c₁ Cg D := by
  rw [ThinConstantObligation]
  filter_upwards [exists_thinConfig_le_of_card_bounds ε hε C₀bd CF c₁ Cg 1 Cbodies D 4 Kbodies,
    eventually_card_segs_le (η := η) hη1] with δ hred hseg
  intro cfg bd hδ hβ hη hexscal hϱ ha hb hC₀ hCbias hCF hCdil hc₁ hD hCg hm hCm hδw₁ hw₁one
  exact hred cfg bd hδ hC₀ hCF hc₁ hD hCg hCm hδw₁ hw₁one (hseg cfg bd hδ hη)
    (fun B hB => hbodies cfg bd B hB)

/-- **The one-line composition with `sideDataObligations_conjunct2_of_thinConstant`.**

Conjunct 2 of `Kakeya.VeryNotSticky.SideDataObligations` follows from the producer in its
`∀ ε > 0` form, at the exponent `Kakeya.VeryNotSticky.thresholdExponent β exscal η τ`. This
records mechanically that the producer's shape is exactly the one the existing reduction
consumes. -/
theorem sideDataObligations_conjunct2_of_producer {β ζ exscal ϱ η τ τ' : ℝ}
    (hexscal : 0 < exscal) (hϱ : 0 < ϱ) (hη : 0 < η)
    (params : CaseParams β ζ exscal ϱ η τ τ')
    {C₀bd Cbias CF Cdil c₁ Cg : NNReal} (hC₀bd : 1 ≤ C₀bd) {D : ℕ}
    (h : ∀ ε : ℝ, 0 < ε →
      ThinConstantObligation.{u} β exscal ϱ η ε C₀bd Cbias CF Cdil c₁ Cg D) :
    ∀ᶠ δ : NNReal in 𝓝[>] 0, ∀ (cfg : VeryNotSticky.{u}) (bd : BallData cfg),
    cfg.δ = δ → cfg.β = β → cfg.η = η → cfg.exscal = exscal → cfg.ϱ = ϱ →
    cfg.a = cfg.δ → cfg.b = cfg.δ →
    bd.C₀ = C₀bd → bd.Cbias = Cbias → bd.CF = CF → bd.Cdil = Cdil → bd.c₁ = c₁ → bd.D = D →
    bd.Cg = Cg → bd.m = 1 → bd.Cm = 1 → cfg.δ ≤ bd.w₁ → bd.w₁ ≤ 1 →
    ∃ (tc : ThinConfig cfg bd) (thr₀ : ScaleThresholds),
      SlabScale cfg bd tc τ ∧
      CaseScale cfg bd τ τ' (τ' * cfg.β / 2) tc.C thr₀ ∧
      ((tangentialSlabDecompConstant tc.C : NNReal) : ENNReal) ≤ (cfg.δ : ENNReal) ^ (-cfg.η) :=
  sideDataObligations_conjunct2_of_thinConstant hexscal hϱ hη params hC₀bd
    (h _ (thresholdExponent_pos hη params))

/-- `Kakeya.VeryNotSticky.CaseParams` gives `η < 1`, so the side condition of
`thinConstantObligation_of_card_bodies` is available wherever conjunct 2 is proved. -/
lemma CaseParams.eta_le_one {β ζ exscal ϱ η τ τ' : ℝ} (hη : 0 < η)
    (params : CaseParams β ζ exscal ϱ η τ τ') : η ≤ 1 := by
  have h1 := params.slabDensity
  have h2 := params.scale
  linarith

/-- **Conjunct 2 of `Kakeya.VeryNotSticky.SideDataObligations` follows from the per-ball body
count alone.**

This is the whole chain of this file, composed: the sizing of
`Kakeya.VeryNotSticky.thinCoreEnvelope`, the absorption
`Kakeya.ThinSizing.polylog_pow_le`, the segment count
`Kakeya.VeryNotSticky.eventually_card_segs_le`, and the existing reduction
`Kakeya.VeryNotSticky.sideDataObligations_conjunct2_of_thinConstant`. The single remaining
input is `hbodies`, the packing bound for the pairwise essentially distinct `(r₁, δ, δ)`-bodies
of a ball. -/
theorem sideDataObligations_conjunct2_of_card_bodies {β ζ exscal ϱ η τ τ' : ℝ}
    (hexscal : 0 < exscal) (hϱ : 0 < ϱ) (hη : 0 < η)
    (params : CaseParams β ζ exscal ϱ η τ τ')
    {C₀bd Cbias CF Cdil c₁ Cg Cbodies : NNReal} (hC₀bd : 1 ≤ C₀bd) {D Kbodies : ℕ}
    (hbodies : ∀ (cfg : VeryNotSticky.{u}) (bd : BallData cfg), ∀ B ∈ bd.bs,
      (((bd.bodies B).card : ℕ) : NNReal) ≤ Cbodies * cfg.δ⁻¹ ^ Kbodies) :
    ∀ᶠ δ : NNReal in 𝓝[>] 0, ∀ (cfg : VeryNotSticky.{u}) (bd : BallData cfg),
    cfg.δ = δ → cfg.β = β → cfg.η = η → cfg.exscal = exscal → cfg.ϱ = ϱ →
    cfg.a = cfg.δ → cfg.b = cfg.δ →
    bd.C₀ = C₀bd → bd.Cbias = Cbias → bd.CF = CF → bd.Cdil = Cdil → bd.c₁ = c₁ → bd.D = D →
    bd.Cg = Cg → bd.m = 1 → bd.Cm = 1 → cfg.δ ≤ bd.w₁ → bd.w₁ ≤ 1 →
    ∃ (tc : ThinConfig cfg bd) (thr₀ : ScaleThresholds),
      SlabScale cfg bd tc τ ∧
      CaseScale cfg bd τ τ' (τ' * cfg.β / 2) tc.C thr₀ ∧
      ((tangentialSlabDecompConstant tc.C : NNReal) : ENNReal) ≤ (cfg.δ : ENNReal) ^ (-cfg.η) :=
  sideDataObligations_conjunct2_of_thinConstant hexscal hϱ hη params hC₀bd
    (thinConstantObligation_of_card_bodies β exscal ϱ η
      (thresholdExponent β exscal η τ) (thresholdExponent_pos hη params)
      (CaseParams.eta_le_one hη params) C₀bd Cbias CF Cdil c₁ Cg Cbodies D Kbodies hbodies)

end Kakeya.VeryNotSticky

end
