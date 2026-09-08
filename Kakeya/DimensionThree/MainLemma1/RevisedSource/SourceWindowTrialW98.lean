module

public import Kakeya.DimensionThree.MainLemma1.RevisedSource.SourcePreparedNormalizationW98
public import Kakeya.DimensionThree.MainLemma1.RevisedSource.SourceEligibleCallsW97

@[expose] public section

open MeasureTheory ConvexSpaceBody ShadedBody
open scoped ENNReal NNReal

namespace Kakeya.ml1Boot.TrialRestartW94

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
attribute [local instance] Classical.propDecidable

universe uE uI

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace Real E]
  [FiniteDimensional Real E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E]

open RevisedLiteralProfileInterfaceFormalizerW87

/-- The stronger output is from the actual P1 construction. Its projection
is the unchanged literal Drop used by all independently proved old helpers. -/
structure WindowDetailedTrialDropW98
    {iota : Type uI} [DecidableEq iota] {d : NNReal}
    {F : Finset iota} {Y : iota -> ShadedTube d E} {L : Nat}
    {rho : Nat -> NNReal} {Ctw Ccell : NNReal}
    (cells : DetailedTrialCellsW94 F Y L rho Ctw Ccell)
    (epsilon zetaPlus : Real) (Ktr : Nat) extends DetailedTrialDropW94 cells epsilon zetaPlus Ktr where
  window_lower : (d : ENNReal) ^ (1 - 3 * epsilon / 2) <= (rho level.val : ENNReal)
  window_upper : (rho level.val : ENNReal) <= (d : ENNReal) ^ (3 * epsilon / 2)
  stronger_per_cell : ∀ P ∈ nodes,
    Kakeya.maxDensity (completeFibreW94 Fplus assignPlus P)
      (fun i => (Yplus i).toConvexSpaceBody) <=
        (d : ENNReal) ^ (epsilon * zetaPlus / 2) *
          allExactTubeNsW87 F (fun i => (Y i).toTube) (rho level.val)

def windowDetailedTrialAtThresholdW98
    (gamma epsilon xi zetaPlus : Real) (Ctw Ccell : NNReal) (L : Nat)
    (etaLambda : Real) (d0 : NNReal) (Ktr : Nat) : Prop :=
  ∀ {d : NNReal}, 0 < d -> d < d0 ->
    ∀ {iota : Type uI} [DecidableEq iota]
      (F : Finset iota) (Y : iota -> ShadedTube d E) (rho : Nat -> NNReal)
      (cells : DetailedTrialCellsW94 F Y L rho Ctw Ccell),
      DetailedTrialInputW94 cells epsilon xi zetaPlus etaLambda ->
      detailedInnerGoodW94 F Y gamma epsilon xi ∨
        Nonempty (WindowDetailedTrialDropW98 cells epsilon zetaPlus Ktr)

/-- Same generic P1 hypotheses and threshold order. Retain the real working
window and pay the actual stronger gap before forgetting to ordinary Drop. -/
theorem exists_literal_window_trial_threshold_w98
    (hdim : Module.finrank Real E = 3)
    (beta gamma epsilon xi zetaPlus : Real)
    (hbeta : 0 < beta) (hbeta_gamma : beta < gamma) (hgamma : gamma <= 1)
    (hepsilon : 0 < epsilon) (hepsilon_lt : epsilon < 1 / 3)
    (hgap : 3 * epsilon / 2 <= (gamma - beta) / 1000)
    (hxi : 0 < xi) (hxi_upper : xi <= 4 * epsilon ^ 3 * beta / 25000)
    (hzetaPlus : 4000 * xi / (epsilon ^ 2 * beta) <= zetaPlus)
    (Ctw Ccell : NNReal) (hCtw : 1 <= Ctw) (hCcell : 1 <= Ccell)
    (L : Nat) (hL : 1 <= L)
    (hLmin : (1 : Real) / L <= min xi epsilon / 100)
    (hLzeta : (160000 : Real) / (epsilon * zetaPlus) <= L)
    (hKT : KatzTaoEstimate.{uI} E beta) (hKF : FrostmanEstimate.{uI} E gamma) :
    ∃ (etaLambda : Real) (d0 : NNReal) (Ktr : Nat),
      0 < etaLambda ∧ 0 < d0 ∧ d0 < 1 ∧ 1 <= Ktr ∧
      windowDetailedTrialAtThresholdW98.{uE, uI} (E := E) gamma epsilon xi zetaPlus Ctw Ccell L
        etaLambda d0 Ktr := by
  set_option maxHeartbeats 4000000 in
    have hgamma_pos : 0 < gamma := hbeta.trans hbeta_gamma
    have hdenom : 0 < epsilon ^ 2 * beta := mul_pos (sq_pos_of_pos hepsilon) hbeta
    have hzeta_pos : 0 < zetaPlus :=
      (div_pos (mul_pos (by norm_num) hxi) hdenom).trans_le hzetaPlus
    let etaP : Real := min (epsilon * zetaPlus / 20000) (xi / 100)
    have hetaP : 0 < etaP := lt_min (by positivity) (by positivity)
    have hetaP_bound : etaP <= epsilon * zetaPlus / 20000 := min_le_left _ _
    have hLpos : (0 : Real) < L := by exact_mod_cast Nat.zero_lt_of_lt hL
    have hstep : (16 : Real) / L <= epsilon * zetaPlus / 10000 := by
      have hscale := (div_le_iff₀ (mul_pos hepsilon hzeta_pos)).mp hLzeta
      apply (div_le_iff₀ hLpos).mpr
      nlinarith
    let kappa : Real := (40 * xi / epsilon + 6 * xi) / (3 * gamma)
    have hkappa_eq : kappa = (40 + 6 * epsilon) * xi / (3 * epsilon * gamma) := by
      dsimp [kappa]
      field_simp
    have hkappa_bound : kappa <= epsilon * zetaPlus / 200 := by
      have hxi_budget := (div_le_iff₀ hdenom).mp hzetaPlus
      have hmon : epsilon ^ 2 * beta * zetaPlus <= epsilon ^ 2 * gamma * zetaPlus := by
        gcongr
      have hcoeff : (40 + 6 * epsilon) * xi <= 42 * xi := by
        apply mul_le_mul_of_nonneg_right _ hxi.le
        linarith
      rw [hkappa_eq]
      apply (div_le_iff₀ (mul_pos (mul_pos (by norm_num) hepsilon) hgamma_pos)).mpr
      nlinarith
    have hdrop_budget : 2 * etaP + 16 / (L : Real) + kappa <= epsilon * zetaPlus / 100 := by
      nlinarith [mul_pos hepsilon hzeta_pos]
    have hworking_step : (2 : Real) / L <= epsilon / 2 := by
      have hmin := min_le_right xi epsilon
      have hbound : (1 : Real) / L <= epsilon / 100 :=
        hLmin.trans (div_le_div_of_nonneg_right hmin (by norm_num))
      calc
        (2 : Real) / L = 2 * ((1 : Real) / L) := by ring
        _ <= 2 * (epsilon / 100) := mul_le_mul_of_nonneg_left hbound (by norm_num)
        _ <= epsilon / 2 := by linarith
    have working_level : ∀ (d : NNReal), 0 < d -> d < 1 ->
        ∀ (rho : Nat -> NNReal), rho 0 = 1 -> rho L = d ->
          (∀ l, l <= L -> 0 < rho l) ->
          (∀ l, l < L -> (rho l : ENNReal) / (rho (l + 1) : ENNReal) <=
            (d : ENNReal) ^ (-(2 : Real) / (L : Real))) ->
          ∀ (b : NNReal), (d : ENNReal) ^ (1 - 3 * epsilon / 2) < b ->
            (b : ENNReal) <= (d : ENNReal) ^ (2 * epsilon) ->
            ∃ l : Fin (L + 1),
              (b : ENNReal) <= rho l.val ∧
              (rho l.val : ENNReal) < (d : ENNReal) ^ (-(2 : Real) / (L : Real)) * b ∧
              (d : ENNReal) ^ (1 - 3 * epsilon / 2) <= rho l.val ∧
              (rho l.val : ENNReal) <= (d : ENNReal) ^ (3 * epsilon / 2) := by
      intro d hd hd1 rho hr0 hrL hrpos hrstep b hblower hbupper
      have hdE : (0 : ENNReal) < d := by exact_mod_cast hd
      have hdE1 : (d : ENNReal) < 1 := by exact_mod_cast hd1
      have hdroot : (d : ENNReal) <= (d : ENNReal) ^ (1 - 3 * epsilon / 2) := by
        simpa only [ENNReal.rpow_one] using ENNReal.rpow_le_rpow_of_exponent_ge hdE1.le
          (show 1 - 3 * epsilon / 2 <= (1 : Real) by linarith)
      have hb1 : (b : ENNReal) < 1 := hbupper.trans_lt
        (ENNReal.rpow_lt_one hdE1 (by positivity : 0 < 2 * epsilon))
      have hbottom : (rho L : ENNReal) < b := by rw [hrL]; exact hdroot.trans_lt hblower
      have hex : ∃ l : Nat, (rho l : ENNReal) < b := ⟨L, hbottom⟩
      let j := Nat.find hex
      have hjL : j <= L := Nat.find_min' hex hbottom
      have hj : (rho j : ENNReal) < b := Nat.find_spec hex
      have hjpos : 0 < j := by
        by_contra hn
        have hj0 : j = 0 := by omega
        rw [hj0, hr0] at hj
        exact (not_lt_of_ge hb1.le) hj
      let l : Nat := j - 1
      have hlL : l < L := by dsimp [l]; omega
      have hlj : l + 1 = j := by dsimp [l]; omega
      have hbl : (b : ENNReal) <= rho l := by
        apply le_of_not_gt
        exact Nat.find_min hex (show l < j by dsimp [l]; omega)
      have hnext : (rho (l + 1) : ENNReal) < b := hlj ▸ hj
      have hnextpos : (0 : ENNReal) < rho (l + 1) := by
        exact_mod_cast hrpos (l + 1) (by omega)
      have hmul : (rho l : ENNReal) <=
          (d : ENNReal) ^ (-(2 : Real) / (L : Real)) * rho (l + 1) := by
        exact (ENNReal.div_le_iff hnextpos.ne' (by simp)).mp (hrstep l hlL)
      have hfactorpos : (d : ENNReal) ^ (-(2 : Real) / (L : Real)) ≠ 0 :=
        (ENNReal.rpow_pos hdE (by simp)).ne'
      have hfactorfin : (d : ENNReal) ^ (-(2 : Real) / (L : Real)) ≠ ⊤ :=
        ENNReal.rpow_ne_top_of_ne_zero hdE.ne' (by simp)
      have hshort : (rho l : ENNReal) <
          (d : ENNReal) ^ (-(2 : Real) / (L : Real)) * b :=
        hmul.trans_lt ((ENNReal.mul_lt_mul_iff_right hfactorpos hfactorfin).mpr hnext)
      refine ⟨⟨l, by omega⟩, hbl, hshort, hblower.le.trans hbl, ?_⟩
      calc
        (rho l : ENNReal) <= (d : ENNReal) ^ (-(2 : Real) / (L : Real)) * b := hshort.le
        _ <= (d : ENNReal) ^ (-(2 : Real) / (L : Real)) *
            (d : ENNReal) ^ (2 * epsilon) := mul_le_mul' le_rfl hbupper
        _ = (d : ENNReal) ^ (-(2 : Real) / (L : Real) + 2 * epsilon) :=
          (ENNReal.rpow_add _ _ hdE.ne' (by simp)).symm
        _ <= (d : ENNReal) ^ (3 * epsilon / 2) :=
          ENNReal.rpow_le_rpow_of_exponent_ge hdE1.le (by rw [neg_div]; linarith)
    have old_complete_geometric_cell :
        ∀ {iota : Type uI} [DecidableEq iota] {d : NNReal}
          (F : Finset iota) (Y : iota -> ShadedTube d E) (rho : Nat -> NNReal)
          (cells : DetailedTrialCellsW94 F Y L rho Ctw Ccell) (etaLambda : Real),
          DetailedTrialInputW94 cells epsilon xi zetaPlus etaLambda ->
          ∀ l, l <= L -> (d : ENNReal) ^ (1 - 3 * epsilon / 2) <= rho l ->
            (rho l : ENNReal) <= (d : ENNReal) ^ (3 * epsilon / 2) ->
            ∀ R ∈ cells.parentSet l,
              (1 / (4 * (Ccell : ENNReal))) *
                  ((rho l : ENNReal) / (d : ENNReal)) ^ zetaPlus <
                frostmanConstIn (exactTubeCellW87 F (fun i => (Y i).toTube) (cells.parentTube l R))
                  (fun i => (Y i).toConvexSpaceBody) (cells.parentTube l R).toConvexSpaceBody := by
      intro iota _ d F Y rho cells etaLambda input l hl hlow hupp R hR
      let A := completeFibreW94 F (cells.assign l) R
      let B := exactTubeCellW87 F (fun i => (Y i).toTube) (cells.parentTube l R)
      have hAB : A ⊆ B := by
        intro i hi
        obtain ⟨hiF, hiR⟩ := Finset.mem_filter.mp hi
        apply Finset.mem_filter.mpr
        refine ⟨hiF, ?_⟩
        simpa only [hiR] using cells.assigned_containment l hl i hiF
      have hApos : (0 : NNReal) < A.card :=
        (cells.D_pos l hl).trans_le (cells.assigned_lower l hl R hR)
      have hA : A.Nonempty := Finset.card_pos.mp (by exact_mod_cast hApos)
      have hB : B.Nonempty := hA.mono hAB
      have hcontained : ∀ i ∈ B, (Y i).toConvexSpaceBody <=
          (cells.parentTube l R).toConvexSpaceBody := fun i hi => (Finset.mem_filter.mp hi).2
      obtain ⟨i0, hi0⟩ := hB
      have hvol : ∀ i ∈ B, volume (Y i).carrier = volume (Y i0).carrier :=
        fun i _ => Tube.volume_carrier_eq_volume_carrier (Y i).toTube (Y i0).toTube
      have hC : (0 : ENNReal) < Ccell := by
        exact_mod_cast (lt_of_lt_of_le (by norm_num : (0 : NNReal) < 1) hCcell)
      have hC2 : (2 * (Ccell : ENNReal)) ≠ 0 := by positivity
      have hC2top : (2 * (Ccell : ENNReal)) ≠ ⊤ :=
        ENNReal.mul_ne_top (by norm_num) ENNReal.coe_ne_top
      have hBcard : (B.card : ENNReal) <= 2 * (Ccell : ENNReal) * A.card := by
        have hupper : (B.card : ENNReal) < 2 * (Ccell : ENNReal) * (cells.D l : ENNReal) := by
          exact_mod_cast cells.geometric_upper l hl R hR
        apply hupper.le.trans
        exact mul_le_mul' le_rfl (by exact_mod_cast cells.assigned_lower l hl R hR)
      have hretain : (2 * (Ccell : ENNReal))⁻¹ * (B.card : ENNReal) <= A.card :=
        (ENNReal.inv_mul_le_iff hC2 hC2top).mpr hBcard
      have hCF := frostmanConstIn_subfamily_le ⟨i0, hi0⟩ hvol hcontained hAB
        (show (2 * (Ccell : ENNReal))⁻¹ ≠ 0 by simp [hC2top]) hretain
      rw [inv_inv] at hCF
      have hstrict := (input.complete_cell_lower l hl hlow hupp R hR).trans_le hCF
      have hcoef : (2 * (Ccell : ENNReal)) * (1 / (4 * (Ccell : ENNReal))) = 1 / 2 := by
        rw [show 4 * (Ccell : ENNReal) = 2 * (2 * (Ccell : ENNReal)) by ring, one_div,
          ENNReal.mul_inv (Or.inl (by norm_num)) (Or.inl (by norm_num)),
          mul_left_comm, ENNReal.mul_inv_cancel hC2 hC2top, mul_one]
        rw [one_div]
      apply (ENNReal.mul_lt_mul_iff_right hC2 hC2top).mp
      rw [← mul_assoc, hcoef]
      exact hstrict
    have density_gap_payment : ∀ Cstar : NNReal, 1 <= Cstar ->
        ∃ d0 : NNReal, 0 < d0 ∧ d0 < 1 ∧
          ∀ d : NNReal, 0 < d -> d < d0 -> ∀ s : NNReal,
            (d : ENNReal) ^ (1 - 3 * epsilon / 2) <= s ->
            ((Cstar : ENNReal) * (d : ENNReal) ^ (-(2 * etaP + 16 / (L : Real) + kappa))) /
                ((1 / (4 * (Ccell : ENNReal))) * ((s : ENNReal) / (d : ENNReal)) ^ zetaPlus) <=
              (d : ENNReal) ^ (epsilon * zetaPlus / 2) := by
      intro Cstar hCstar
      have hCstarpos : (0 : NNReal) < Cstar := zero_lt_one.trans_le hCstar
      have hCcellpos : (0 : NNReal) < Ccell := zero_lt_one.trans_le hCcell
      obtain ⟨cutoff, hcutoff, hconst⟩ := exists_threshold_ofReal_le_rpow
        (C := ((Cstar * (4 * Ccell) : NNReal) : Real)) (by positivity)
        (a := epsilon * zetaPlus / 100) (by positivity)
      refine ⟨min cutoff (1 / 2), lt_min hcutoff (by norm_num),
        (min_le_right _ _).trans_lt (by norm_num), ?_⟩
      intro d hd hdc s hs
      have hd1 : d <= 1 := (hdc.trans_le (min_le_right _ _)).le.trans (by norm_num)
      have hdE : (0 : ENNReal) < d := by exact_mod_cast hd
      have hdE1 : (d : ENNReal) <= 1 := by exact_mod_cast hd1
      have hsE : (0 : ENNReal) < s := (ENNReal.rpow_pos hdE (by simp)).trans_le hs
      have hratioPos : (0 : ENNReal) < (s : ENNReal) / (d : ENNReal) := by
        exact ENNReal.div_pos hsE.ne' (by simp)
      have hratioTop : (s : ENNReal) / (d : ENNReal) ≠ ⊤ :=
        ENNReal.div_ne_top (by simp) hdE.ne'
      have hC4 : (4 * (Ccell : ENNReal)) ≠ 0 := by positivity
      have hC4top : (4 * (Ccell : ENNReal)) ≠ ⊤ :=
        ENNReal.mul_ne_top (by norm_num) ENNReal.coe_ne_top
      have hLambda0 : (1 / (4 * (Ccell : ENNReal))) *
          ((s : ENNReal) / (d : ENNReal)) ^ zetaPlus ≠ 0 := by
        exact mul_ne_zero (by simp [hC4top]) (ENNReal.rpow_pos hratioPos hratioTop).ne'
      have hLambdaTop : (1 / (4 * (Ccell : ENNReal))) *
          ((s : ENNReal) / (d : ENNReal)) ^ zetaPlus ≠ ⊤ :=
        ENNReal.mul_ne_top (by simp [hC4])
          (ENNReal.rpow_ne_top_of_ne_zero hratioPos.ne' hratioTop)
      apply (ENNReal.div_le_iff hLambda0 hLambdaTop).mpr
      apply (ENNReal.mul_le_mul_iff_left hC4 hC4top).mp
      have hconstant : (Cstar : ENNReal) * (4 * (Ccell : ENNReal)) <=
          (d : ENNReal) ^ (-(epsilon * zetaPlus / 100)) := by
        simpa only [NNReal.coe_mul, NNReal.coe_ofNat, ENNReal.ofReal_mul
            (by positivity : (0 : Real) <= Cstar), ENNReal.ofReal_mul
            (by norm_num : (0 : Real) <= 4), ENNReal.ofReal_coe_nnreal,
            ENNReal.ofReal_ofNat] using hconst d hd (hdc.trans_le (min_le_left _ _))
      have hratio : (d : ENNReal) ^ (-(3 * epsilon / 2)) <= (s : ENNReal) / (d : ENNReal) := by
        apply (ENNReal.le_div_iff_mul_le (Or.inl hdE.ne') (Or.inl (by simp))).mpr
        calc
          _ = (d : ENNReal) ^ (-(3 * epsilon / 2)) * (d : ENNReal) ^ (1 : Real) := by
            rw [ENNReal.rpow_one]
          _ = (d : ENNReal) ^ (1 - 3 * epsilon / 2) := by
            rw [← ENNReal.rpow_add _ _ hdE.ne' (by simp)]
            congr 1
            ring
          _ <= s := hs
      calc
        ((Cstar : ENNReal) * (d : ENNReal) ^ (-(2 * etaP + 16 / (L : Real) + kappa))) *
            (4 * (Ccell : ENNReal)) = ((Cstar : ENNReal) * (4 * (Ccell : ENNReal))) *
              (d : ENNReal) ^ (-(2 * etaP + 16 / (L : Real) + kappa)) := by ring
        _ <= (d : ENNReal) ^ (-(epsilon * zetaPlus / 100)) *
            (d : ENNReal) ^ (-(2 * etaP + 16 / (L : Real) + kappa)) := mul_le_mul' hconstant le_rfl
        _ = (d : ENNReal) ^ (-(epsilon * zetaPlus / 100) -
            (2 * etaP + 16 / (L : Real) + kappa)) := by
          rw [← ENNReal.rpow_add _ _ hdE.ne' (by simp)]
          congr 1
        _ <= (d : ENNReal) ^ (epsilon * zetaPlus / 2 + (-(3 * epsilon / 2)) * zetaPlus) :=
          ENNReal.rpow_le_rpow_of_exponent_ge hdE1 (by nlinarith)
        _ = (d : ENNReal) ^ (epsilon * zetaPlus / 2) *
            ((d : ENNReal) ^ (-(3 * epsilon / 2))) ^ zetaPlus := by
          rw [ENNReal.rpow_add _ _ hdE.ne' (by simp), ENNReal.rpow_mul]
        _ <= (d : ENNReal) ^ (epsilon * zetaPlus / 2) *
            ((s : ENNReal) / (d : ENNReal)) ^ zetaPlus :=
          mul_le_mul' le_rfl (ENNReal.rpow_le_rpow hratio hzeta_pos.le)
        _ = ((d : ENNReal) ^ (epsilon * zetaPlus / 2) *
            ((1 / (4 * (Ccell : ENNReal))) * ((s : ENNReal) / (d : ENNReal)) ^ zetaPlus)) *
              (4 * (Ccell : ENNReal)) := by
          rw [one_div]
          calc
            _ = (d : ENNReal) ^ (epsilon * zetaPlus / 2) *
                ((s : ENNReal) / (d : ENNReal)) ^ zetaPlus *
                  ((4 * (Ccell : ENNReal))⁻¹ * (4 * (Ccell : ENNReal))) := by
              rw [ENNReal.inv_mul_cancel hC4 hC4top, mul_one]
            _ = _ := by ring
    have central_pairwise_selection : ∀ (d : NNReal), 0 < d -> d <= 1 ->
        ∀ {iota : Type uI} [DecidableEq iota]
          (F : Finset iota) (Y : iota -> ShadedTube d E) (rho : Nat -> NNReal)
          (cells : DetailedTrialCellsW94 F Y L rho Ctw Ccell),
          (∀ i ∈ F, (Y i).carrier ⊆ Metric.closedBall 0 1) ->
          lineEssentiallyDistinctW94 F (fun i => (Y i).toTube) Ctw ->
          0 < (∑ i ∈ F, volume (Y i).shade) ->
          ∀ l, l <= L ->
            ∃ (q J : Finset iota),
              q ⊆ F ∧ q.Nonempty ∧ J = q.image (cells.assign l) ∧
              J ⊆ cells.parentSet l ∧ J.Nonempty ∧
              (q : Set iota).Pairwise (fun i j =>
                IsEssentiallyDistinct (Y i).carrier (Y j).carrier) ∧
              (J : Set iota).Pairwise (fun P Q =>
                IsEssentiallyDistinct (cells.parentTube l P).carrier
                  (cells.parentTube l Q).carrier) ∧
              (∀ i ∈ q, (Y i).toConvexSpaceBody <=
                (cells.parentTube l (cells.assign l i)).toConvexSpaceBody) ∧
              (∑ i ∈ F, volume (Y i).shade) <=
                (lineSelectionMultiplicityW95 (Module.finrank Real E) 1
                  (Nat.floor (Ctw : Real)) : ENNReal) *
                (lineSelectionMultiplicityW95 (Module.finrank Real E) 2
                  (Nat.floor (Ctw : Real)) : ENNReal) *
                (∑ i ∈ q, volume (Y i).shade) := by
      intro d hd hd1 iota _ F Y rho cells hball hline hmass l hl
      classical
      let A := Nat.floor (Ctw : Real)
      have hA : 1 <= A := (Nat.one_le_floor_iff _).mpr (by exact_mod_cast hCtw)
      let Mf := lineSelectionMultiplicityW95 (Module.finrank Real E) 1 A
      let Mp := lineSelectionMultiplicityW95 (Module.finrank Real E) 2 A
      have hF : F.Nonempty := by
        by_contra hn
        simpa [Finset.not_nonempty_iff_eq_empty.mp hn] using hmass
      have hcenter : ∀ i ∈ F, ‖(Y i).center‖ <= (1 : Real) := by
        intro i hi
        have hmem := (Y i).toTube.mem_carrier_of_mem_segment
          (midpoint_mem_segment (𝕜 := Real) (Y i).x (Y i).y)
        simpa only [Metric.mem_closedBall, dist_zero_right] using hball i hi hmem
      have hlineA := (pointwise_lineED_iff_library_floor_w95 F
        (fun i => (Y i).toTube) Ctw).mp hline
      obtain ⟨qf, hqfF, hqf, hqfED, hqfMass, hqfCard, hqfFull, hqfCF, hqfMax, hqfMult⟩ :=
        exists_pairwise_lineED_paid_w95 hd hd1 F Y hF 1 (by norm_num) hcenter A hA
          hlineA ConvexSpaceBody.closedUnitBall hball hmass
      change (∑ i ∈ F, volume (Y i).shade) <=
        (Mf : ENNReal) * (∑ i ∈ qf, volume (Y i).shade) at hqfMass
      have hrho1 : ∀ j, j <= L -> rho j <= 1 := by
        intro j
        induction j with
        | zero => intro _; exact cells.rho_zero.le
        | succ j ih =>
          intro hj
          exact (cells.rho_nonincreasing j (by omega)).trans (ih (by omega))
      have hpcenter : ∀ P ∈ cells.parentSet l,
          ‖(cells.parentTube l P).center‖ <= (2 : Real) := by
        intro P hP
        have hmem := (cells.parentTube l P).mem_carrier_of_mem_segment
          (midpoint_mem_segment (𝕜 := Real) (cells.parentTube l P).x (cells.parentTube l P).y)
        simpa only [Metric.mem_closedBall, dist_zero_right] using cells.parent_ball l hl P hP hmem
      have hpline := (pointwise_lineED_iff_library_floor_w95 (cells.parentSet l)
        (cells.parentTube l) Ctw).mp (cells.parent_line_ed l hl)
      have hplineBig := lineED_five_implies_lineEDAt_w95 (cells.rho_pos l hl) (hrho1 l hl)
        (cells.parentSet l) (cells.parentTube l) A hpline 2
        (Kakeya.Tube.tubeOverlapCoreClose.C (Module.finrank Real E)) (by norm_num)
        (Kakeya.Tube.tubeOverlapCoreClose.one_lt_C _).le hpcenter
      have hMp : 1 <= Mp := by
        apply Nat.mul_pos _ (by omega)
        apply Nat.ceil_pos.mpr
        have hK : 0 <= Kakeya.Tube.tubeOverlapCoreClose.C (Module.finrank Real E) - 1 :=
          sub_nonneg.mpr (Kakeya.Tube.tubeOverlapCoreClose.one_lt_C _).le
        positivity
      let weight := fun P => ∑ i ∈ qf.filter (fun i => cells.assign l i = P), volume (Y i).shade
      obtain ⟨J0, hJ0, hJ0ED, hJ0Mass, hJ0Card⟩ :=
        VeryNotSticky.exists_pairwise_of_isLineEssDistinctAt (cells.rho_pos l hl)
          (hrho1 l hl) hplineBig weight
      change (∑ P ∈ cells.parentSet l, weight P) <=
        ((Mp - 1 + 1 : Nat) : ENNReal) * (∑ P ∈ J0, weight P) at hJ0Mass
      rw [Nat.sub_add_cancel hMp] at hJ0Mass
      have hmaps : ∀ i ∈ qf, cells.assign l i ∈ cells.parentSet l := by
        intro i hi
        rw [← cells.assign_image l hl]
        exact Finset.mem_image_of_mem _ (hqfF hi)
      have hmassFibres : (∑ P ∈ cells.parentSet l, weight P) =
          ∑ i ∈ qf, volume (Y i).shade := Finset.sum_fiberwise_of_maps_to hmaps _
      let q := qf.filter (fun i => cells.assign l i ∈ J0)
      have hmassSelected : (∑ P ∈ J0, weight P) =
          ∑ i ∈ q, volume (Y i).shade := Finset.sum_fiberwise_eq_sum_filter qf J0 _ _
      rw [hmassFibres, hmassSelected] at hJ0Mass
      have hqsub : q ⊆ qf := Finset.filter_subset _ _
      have htotal : (∑ i ∈ F, volume (Y i).shade) <=
          (Mf : ENNReal) * (Mp : ENNReal) * (∑ i ∈ q, volume (Y i).shade) := by
        exact hqfMass.trans (by simpa only [mul_assoc] using mul_le_mul' le_rfl hJ0Mass)
      have hq : q.Nonempty := by
        by_contra hn
        have hzero : q = ∅ := Finset.not_nonempty_iff_eq_empty.mp hn
        have hbad : (∑ i ∈ F, volume (Y i).shade) <= 0 := by simpa [hzero] using htotal
        exact (not_lt_of_ge hbad) hmass
      let J := q.image (cells.assign l)
      have hJJ0 : J ⊆ J0 := by
        intro P hP
        obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hP
        exact (Finset.mem_filter.mp hi).2
      refine ⟨q, J, hqsub.trans hqfF, hq, rfl, hJJ0.trans hJ0,
        hq.image _, ?_, ?_, ?_, htotal⟩
      · exact hqfED.mono (by exact_mod_cast hqsub)
      · exact hJ0ED.mono (by exact_mod_cast hJJ0)
      · intro i hi
        exact cells.assigned_containment l hl i (hqfF (hqsub hi))
    have complete_cell_drop : ∀ Cstar : NNReal, 1 <= Cstar ->
        ∃ d0 : NNReal, 0 < d0 ∧ d0 < 1 ∧
          ∀ d : NNReal, 0 < d -> d < d0 ->
            ∀ {iota : Type uI} [DecidableEq iota]
              (F q : Finset iota) (Y : iota -> ShadedTube d E) (rho : Nat -> NNReal)
              (cells : DetailedTrialCellsW94 F Y L rho Ctw Ccell) (etaLambda : Real),
              DetailedTrialInputW94 cells epsilon xi zetaPlus etaLambda -> q ⊆ F ->
              ∀ l, l <= L ->
                (d : ENNReal) ^ (1 - 3 * epsilon / 2) <= rho l ->
                (rho l : ENNReal) <= (d : ENNReal) ^ (3 * epsilon / 2) ->
                ∀ P ∈ cells.parentSet l,
                  frostmanConstIn (exactTubeCellW87 q (fun i => (Y i).toTube) (cells.parentTube l P))
                      (fun i => (Y i).toConvexSpaceBody) (cells.parentTube l P).toConvexSpaceBody <=
                    (Cstar : ENNReal) * (d : ENNReal) ^ (-(2 * etaP + 16 / (L : Real) + kappa)) ->
                  Kakeya.maxDensity (exactTubeCellW87 q (fun i => (Y i).toTube) (cells.parentTube l P))
                      (fun i => (Y i).toConvexSpaceBody) <=
                    (d : ENNReal) ^ (epsilon * zetaPlus / 2) *
                      allExactTubeNsW87 F (fun i => (Y i).toTube) (rho l) := by
      intro Cstar hCstar
      obtain ⟨d0, hd0, hd01, hpayment⟩ := density_gap_payment Cstar hCstar
      refine ⟨d0, hd0, hd01, ?_⟩
      intro d hd hdd0 iota _ F q Y rho cells etaLambda input hq l hl hlow hupp P hP hnew
      let old := exactTubeCellW87 F (fun i => (Y i).toTube) (cells.parentTube l P)
      let new := exactTubeCellW87 q (fun i => (Y i).toTube) (cells.parentTube l P)
      let Lambda := (1 / (4 * (Ccell : ENNReal))) *
        ((rho l : ENNReal) / (d : ENNReal)) ^ zetaPlus
      let upper := (Cstar : ENNReal) *
        (d : ENNReal) ^ (-(2 * etaP + 16 / (L : Real) + kappa))
      have holdpos : (0 : NNReal) < old.card :=
        (cells.D_pos l hl).trans_le (cells.geometric_lower l hl P hP)
      have hold : old.Nonempty := Finset.card_pos.mp (by exact_mod_cast holdpos)
      have hsub : new ⊆ old := by
        intro i hi
        exact Finset.mem_filter.mpr ⟨hq (Finset.mem_filter.mp hi).1, (Finset.mem_filter.mp hi).2⟩
      have hcontained : ∀ i ∈ old, (Y i).toConvexSpaceBody <=
          (cells.parentTube l P).toConvexSpaceBody := fun i hi => (Finset.mem_filter.mp hi).2
      have hdE : (0 : ENNReal) < d := by exact_mod_cast hd
      have hrE : (0 : ENNReal) < rho l := by exact_mod_cast cells.rho_pos l hl
      have hratio : (0 : ENNReal) < (rho l : ENNReal) / (d : ENNReal) :=
        ENNReal.div_pos hrE.ne' (by simp)
      have hratiotop : (rho l : ENNReal) / (d : ENNReal) ≠ ⊤ :=
        ENNReal.div_ne_top (by simp) hdE.ne'
      have hC4 : (4 * (Ccell : ENNReal)) ≠ 0 := by
        have hC : (0 : NNReal) < Ccell := zero_lt_one.trans_le hCcell
        positivity
      have hC4top : (4 * (Ccell : ENNReal)) ≠ ⊤ :=
        ENNReal.mul_ne_top (by norm_num) ENNReal.coe_ne_top
      have hLambda : 0 < Lambda :=
        ENNReal.mul_pos_iff.mpr ⟨by simpa only [one_div] using ENNReal.inv_pos.mpr hC4top,
          ENNReal.rpow_pos hratio hratiotop⟩
      have hLambdaTop : Lambda < ⊤ := by
        apply lt_top_iff_ne_top.mpr
        exact ENNReal.mul_ne_top (by simpa only [one_div] using ENNReal.inv_ne_top.mpr hC4)
          (ENNReal.rpow_ne_top_of_ne_zero hratio.ne' hratiotop)
      have hupperTop : upper < ⊤ := by
        apply lt_top_iff_ne_top.mpr
        exact ENNReal.mul_ne_top ENNReal.coe_ne_top
          (ENNReal.rpow_ne_top_of_ne_zero hdE.ne' (by simp))
      have hrho1 : rho l <= 1 := by
        apply ENNReal.coe_le_coe.mp
        exact hupp.trans (ENNReal.rpow_le_one
          (by exact_mod_cast (hdd0.trans hd01).le) (by positivity))
      have hparentVol : 0 < volume (cells.parentTube l P).carrier :=
        (Tube.volume_pos_and_lt_top (cells.rho_pos l hl) hrho1 (cells.parentTube l P)).1
      have hparentTop : volume (cells.parentTube l P).carrier < ⊤ :=
        (cells.parentTube l P).toConvexSpaceBody.isCompact.measure_lt_top
      have hlower := (old_complete_geometric_cell F Y rho cells etaLambda input l hl hlow hupp P hP).le
      have hdrop := maxDensity_drop_of_complete_cell_frostman_gap_w94 old new
        (fun i => (Y i).toConvexSpaceBody) (cells.parentTube l P).toConvexSpaceBody Lambda upper
        hold hsub hcontained hparentVol hparentTop hLambda hLambdaTop hupperTop hlower hnew
      exact hdrop.trans (mul_le_mul' (hpayment d hd hdd0 (rho l) hlow)
        (maxDensity_exactTubeCell_le_allExactTubeNs_w87 (cells.parentTube l P) hold))
    have fixed_polylog_payment : ∀ (C alpha : Real), 1 <= C -> 0 < alpha ->
        ∃ d0 : NNReal, 0 < d0 ∧ d0 < 1 ∧
          ∀ d : NNReal, 0 < d -> d < d0 ->
            ENNReal.ofReal (C * (1 + Real.log (1 / (d : Real))) ^ 7) <=
                (d : ENNReal) ^ (-alpha) ∧
            trialRetainedFractionW94 d 8 *
                ENNReal.ofReal (C * (1 + Real.log (1 / (d : Real))) ^ 7) <= 1 := by
      intro C alpha hC halpha
      obtain ⟨u, hu, hpoly⟩ := mem_nhdsGT_iff_exists_Ioc_subset.mp
        (ENNReal.eventually_ofReal_one_add_logb_pow_le_rpow_neg
          (show 0 < alpha / 2 by positivity) 7)
      obtain ⟨v, hv, hconst⟩ := exists_threshold_ofReal_le_rpow
        (C := C) (zero_lt_one.trans_le hC) (a := alpha / 2) (by positivity)
      let w : NNReal := ⟨Real.exp (-C), (Real.exp_pos _).le⟩
      have hw : 0 < w := Real.exp_pos _
      refine ⟨min (min u v) (min w (1 / 2)),
        lt_min (lt_min hu hv) (lt_min hw (by norm_num)),
        ((min_le_right _ _).trans (min_le_right _ _)).trans_lt (by norm_num), ?_⟩
      intro d hd hdd0
      have hdu : d < u := hdd0.trans_le ((min_le_left _ _).trans (min_le_left _ _))
      have hdv : d < v := hdd0.trans_le ((min_le_left _ _).trans (min_le_right _ _))
      have hdw : d < w := hdd0.trans_le ((min_le_right _ _).trans (min_le_left _ _))
      have hd1 : (d : Real) <= 1 := by
        exact_mod_cast (hdd0.trans_le
          ((min_le_right _ _).trans (min_le_right _ _))).le.trans
            (by norm_num : (1 / 2 : NNReal) <= 1)
      have hdR : (0 : Real) < d := by exact_mod_cast hd
      have hdE : (0 : ENNReal) < d := by exact_mod_cast hd
      have hinv : (1 : Real) <= 1 / (d : Real) := (le_div_iff₀ hdR).mpr (by simpa)
      have hlog : 0 <= Real.log (1 / (d : Real)) := Real.log_nonneg hinv
      have hbase : 0 < 1 + Real.log (1 / (d : Real)) := by linarith
      have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
      have hlog21 : Real.log 2 <= 1 := by
        convert Real.log_le_sub_one_of_pos (by norm_num : (0 : Real) < 2) using 1 <;> norm_num
      have hlogb : Real.log (1 / (d : Real)) <= Real.logb 2 (1 / (d : Real)) := by
        rw [Real.logb]
        exact (le_div_iff₀ hlog2).mpr (mul_le_of_le_one_right hlog hlog21)
      have hnatural : ENNReal.ofReal ((1 + Real.log (1 / (d : Real))) ^ 7) <=
          (d : ENNReal) ^ (-(alpha / 2)) := by
        calc
          _ = ENNReal.ofReal (1 + Real.log (1 / (d : Real))) ^ 7 :=
            ENNReal.ofReal_pow hbase.le 7
          _ <= ENNReal.ofReal (1 + Real.logb 2 (1 / (d : Real))) ^ 7 := by
            gcongr
          _ <= _ := hpoly ⟨hd, hdu.le⟩
      have hCbase : C <= 1 + Real.log (1 / (d : Real)) := by
        have hdexp : (d : Real) <= Real.exp (-C) := by exact_mod_cast hdw.le
        have hlogd := Real.log_le_log hdR hdexp
        rw [Real.log_exp] at hlogd
        rw [one_div, Real.log_inv]
        linarith
      constructor
      · rw [ENNReal.ofReal_mul (zero_le_one.trans hC)]
        calc
          _ <= (d : ENNReal) ^ (-(alpha / 2)) *
              (d : ENNReal) ^ (-(alpha / 2)) := mul_le_mul' (hconst d hd hdv) hnatural
          _ = (d : ENNReal) ^ (-alpha) := by
            rw [← ENNReal.rpow_add _ _ hdE.ne' (by simp)]
            congr 1
            ring
      · unfold trialRetainedFractionW94
        rw [← ENNReal.ofReal_mul (Real.rpow_nonneg hbase.le _)]
        apply (ENNReal.ofReal_le_one).mpr
        rw [Real.rpow_neg hbase.le, Real.rpow_natCast]
        have hpowpos : 0 < (1 + Real.log (1 / (d : Real))) ^ 8 := pow_pos hbase _
        calc
          _ <= ((1 + Real.log (1 / (d : Real))) ^ 8)⁻¹ *
              ((1 + Real.log (1 / (d : Real))) *
                (1 + Real.log (1 / (d : Real))) ^ 7) := by gcongr
          _ = 1 := by
            rw [← pow_succ']
            exact inv_mul_cancel₀ hpowpos.ne'
    have aggregate_budget : ∀ C : Real, 1 <= C ->
        ∃ d0 : NNReal, 0 < d0 ∧ d0 < 1 ∧
          ∀ etaLambda : Real, etaLambda <= etaP / 4 ->
          ∀ d : NNReal, 0 < d -> d < d0 -> ∀ LD MLF : ENNReal,
            2 * LD * MLF <= ENNReal.ofReal (C * (1 + Real.log (1 / (d : Real))) ^ 7) ->
            2 * (d : ENNReal) ^ etaP * LD * MLF <= (d : ENNReal) ^ etaLambda := by
      intro C hC
      obtain ⟨d0, hd0, hd01, hpay⟩ := fixed_polylog_payment C (etaP / 2) hC (by positivity)
      refine ⟨d0, hd0, hd01, ?_⟩
      intro etaLambda hetaLambda d hd hdd0 LD MLF hcost
      have hdE : (0 : ENNReal) < d := by exact_mod_cast hd
      have hdE1 : (d : ENNReal) <= 1 := by exact_mod_cast (hdd0.trans hd01).le
      calc
        _ = (d : ENNReal) ^ etaP * (2 * LD * MLF) := by ring
        _ <= (d : ENNReal) ^ etaP * (d : ENNReal) ^ (-(etaP / 2)) :=
          mul_le_mul' le_rfl (hcost.trans (hpay d hd hdd0).1)
        _ = (d : ENNReal) ^ (etaP / 2) := by
          rw [← ENNReal.rpow_add _ _ hdE.ne' (by simp)]
          congr 1
          ring
        _ <= _ := ENNReal.rpow_le_rpow_of_exponent_ge hdE1 (by linarith)
    have whole_block_reserve :
        ∀ {iota : Type uI} [DecidableEq iota] {d : NNReal}
          (F : Finset iota) (Y : iota -> ShadedTube d E)
          (J : Finset iota) (parent : iota -> iota) (U : iota -> Finset iota)
          (lambda h LD MLF : ENNReal),
          0 < d -> d <= 1 -> F.Nonempty ->
          (∀ S ∈ J, U S ⊆ completeFibreW94 F parent S) ->
          lambda <= fullness' F (fun i => (Y i).toShadedBody) ->
          0 < MLF -> MLF < ⊤ ->
          (∑ i ∈ F, volume (Y i).shade) <= MLF * ∑ S ∈ J, ∑ i ∈ U S, volume (Y i).shade ->
          2 * h * LD * MLF <= lambda ->
          2 * h * LD * (∑ S ∈ J, ∑ i ∈ U S, volume (Y i).carrier) <=
            ∑ S ∈ J, ∑ i ∈ U S, volume (Y i).shade := by
      intro iota _ d F Y J parent U lambda h LD MLF hd hd1 hF hU hfull hMLF hMLFtop hmass hbudget
      have hdisjoint : (J : Set iota).PairwiseDisjoint U := by
        intro S hS S' hS' hne
        apply Finset.disjoint_left.mpr
        intro i hi hi'
        exact hne (((Finset.mem_filter.mp (hU S hS hi)).2).symm.trans
          (Finset.mem_filter.mp (hU S' hS' hi')).2)
      have hUF : J.biUnion U ⊆ F := by
        intro i hi
        obtain ⟨S, hS, hiU⟩ := Finset.mem_biUnion.mp hi
        exact (Finset.mem_filter.mp (hU S hS hiU)).1
      have hcarrier : (∑ S ∈ J, ∑ i ∈ U S, volume (Y i).carrier) <=
          ∑ i ∈ F, volume (Y i).carrier := by
        rw [← Finset.sum_biUnion hdisjoint]
        exact Finset.sum_le_sum_of_subset hUF
      have hvolpos : 0 < ∑ i ∈ F, volume (Y i).carrier := by
        obtain ⟨i, hi⟩ := hF
        exact ((Tube.volume_pos_and_lt_top hd hd1 (Y i).toTube).1).trans_le
          (Finset.single_le_sum (f := fun j => volume (Y j).carrier) (fun j hj => zero_le) hi)
      have hvoltop : (∑ i ∈ F, volume (Y i).carrier) ≠ ⊤ := by
        apply ENNReal.sum_ne_top.mpr
        intro i hi
        exact (Y i).toConvexSpaceBody.isCompact.measure_ne_top
      have hbase : lambda * (∑ i ∈ F, volume (Y i).carrier) <=
          ∑ i ∈ F, volume (Y i).shade := by
        rw [fullness'] at hfull
        exact (ENNReal.le_div_iff_mul_le (Or.inl hvolpos.ne') (Or.inl hvoltop)).mp hfull
      apply (ENNReal.mul_le_mul_iff_right hMLF.ne' hMLFtop.ne).mp
      calc
        _ = (2 * h * LD * MLF) * (∑ S ∈ J, ∑ i ∈ U S, volume (Y i).carrier) := by ring
        _ <= lambda * (∑ i ∈ F, volume (Y i).carrier) := mul_le_mul' hbudget hcarrier
        _ <= ∑ i ∈ F, volume (Y i).shade := hbase
        _ <= _ := hmass
    have original_family_transfer :
        ∀ {iota : Type uI} [DecidableEq iota] {d : NNReal}
          (F H : Finset iota) (Y : iota -> ShadedTube d E) (rho : Nat -> NNReal)
          (cells : DetailedTrialCellsW94 F Y L rho Ctw Ccell) (etaLambda : Real) (P : ENNReal),
          0 < d -> d <= 1 -> DetailedTrialInputW94 cells epsilon xi zetaPlus etaLambda ->
          H ⊆ F -> 0 < P -> P < ⊤ ->
          (∑ i ∈ F, volume (Y i).shade) <= P * ∑ i ∈ H, volume (Y i).shade ->
          H.Nonempty ∧
            P⁻¹ * (d : ENNReal) ^ etaLambda <= fullness' H (fun i => (Y i).toShadedBody) ∧
            (P⁻¹ * (d : ENNReal) ^ etaLambda) * (F.card : ENNReal) <= (H.card : ENNReal) ∧
            frostmanConstIn H (fun i => (Y i).toConvexSpaceBody) ConvexSpaceBody.closedUnitBall <=
              P * ((d : ENNReal) ^ etaLambda)⁻¹ * (d : ENNReal) ^ (-xi / 160) ∧
            ShadedBody.multiplicity F (fun i => (Y i).toShadedBody) <=
              P * ShadedBody.multiplicity H (fun i => (Y i).toShadedBody) := by
      intro iota _ d F H Y rho cells etaLambda P hd hd1 input hHF hP hPtop hmass
      obtain ⟨i0, hi0⟩ := input.nonempty
      let v := volume (Y i0).carrier
      have hv : 0 < v := (Tube.volume_pos_and_lt_top hd hd1 (Y i0).toTube).1
      have hvtop : v < ⊤ := (Tube.volume_pos_and_lt_top hd hd1 (Y i0).toTube).2
      have hdE : (0 : ENNReal) < d := by exact_mod_cast hd
      have hretained : P⁻¹ * (∑ i ∈ F, volume (Y i).shade) <=
          ∑ i ∈ H, volume (Y i).shade :=
        (ENNReal.inv_mul_le_iff hP.ne' hPtop.ne).mpr hmass
      obtain ⟨hH, hfull, hcard, hCF⟩ := retained_state_fullness_card_frostman_w94 F H
        (fun i => (Y i).toShadedBody) (fun i => (Y i).toShadedBody)
        ConvexSpaceBody.closedUnitBall v ((d : ENNReal) ^ etaLambda)
        ((d : ENNReal) ^ (-xi / 160)) P⁻¹ ⟨i0, hi0⟩ hHF hv hvtop
        (fun i hi => Tube.volume_carrier_eq_volume_carrier (Y i).toTube (Y i0).toTube)
        input.ball ConvexSpaceBody.closedUnitBall_volume_pos
        ConvexSpaceBody.closedUnitBall.isCompact.measure_lt_top
        (fun i hi => rfl) (fun i hi => Set.Subset.refl _)
        (ENNReal.rpow_pos hdE (by simp))
        (lt_top_iff_ne_top.mpr (ENNReal.rpow_ne_top_of_ne_zero hdE.ne' (by simp)))
        input.fullness input.frostman
        (lt_top_iff_ne_top.mpr (ENNReal.rpow_ne_top_of_ne_zero hdE.ne' (by simp)))
        (ENNReal.inv_pos.mpr hPtop.ne) (ENNReal.inv_lt_top.mpr hP) hretained
      refine ⟨hH, hfull, hcard, ?_, ?_⟩
      · simpa only [ENNReal.mul_inv (Or.inl (ENNReal.inv_ne_zero.mpr hPtop.ne))
          (Or.inl (ENNReal.inv_ne_top.mpr hP.ne')), inv_inv] using hCF
      · apply ShadedBody.multiplicity_le_mul_of_sum_shade_le_of_biUnion_subset F
          (fun i => (Y i).toShadedBody) H (fun i => (Y i).toShadedBody) P _ hmass
        intro x hx
        obtain ⟨i, hi, hxi⟩ := Set.mem_iUnion₂.mp hx
        exact Set.mem_iUnion₂.mpr ⟨i, hHF hi, hxi⟩
    have central_level : ∀ (d : NNReal), 0 < d -> d < 1 ->
        ∀ {iota : Type uI} [DecidableEq iota]
          (F : Finset iota) (Y : iota -> ShadedTube d E) (rho : Nat -> NNReal)
          (cells : DetailedTrialCellsW94 F Y L rho Ctw Ccell),
          ∃ c : Fin (L + 1), 0 < c.val ∧ d <= rho c.val ∧
            (d : ENNReal) ^ (2 * epsilon + 2 / (L : Real)) < rho c.val ∧
            (rho c.val : ENNReal) <= (d : ENNReal) ^ (2 * epsilon) := by
      intro d hd hd1 iota _ F Y rho cells
      have hdE : (0 : ENNReal) < d := by exact_mod_cast hd
      have hdE1 : (d : ENNReal) < 1 := by exact_mod_cast hd1
      have hbottom : (rho L : ENNReal) <= (d : ENNReal) ^ (2 * epsilon) := by
        rw [cells.rho_bottom]
        simpa only [ENNReal.rpow_one] using ENNReal.rpow_le_rpow_of_exponent_ge hdE1.le
          (show 2 * epsilon <= (1 : Real) by linarith)
      have hex : ∃ j : Nat, (rho j : ENNReal) <= (d : ENNReal) ^ (2 * epsilon) := ⟨L, hbottom⟩
      let c := Nat.find hex
      have hcL : c <= L := Nat.find_min' hex hbottom
      have hc : (rho c : ENNReal) <= (d : ENNReal) ^ (2 * epsilon) := Nat.find_spec hex
      have hcpos : 0 < c := by
        by_contra hn
        have hc0 : c = 0 := by omega
        rw [hc0, cells.rho_zero] at hc
        exact (not_lt_of_ge hc) (ENNReal.rpow_lt_one hdE1 (by positivity))
      have hprev : (d : ENNReal) ^ (2 * epsilon) < rho (c - 1) :=
        lt_of_not_ge (Nat.find_min hex (by omega : c - 1 < c))
      have hprevstep := cells.rho_step (c - 1) (by omega)
      have hsucc : c - 1 + 1 = c := by omega
      rw [hsucc] at hprevstep
      have hrcpos : (0 : ENNReal) < rho c := by exact_mod_cast cells.rho_pos c hcL
      have hmul : (rho (c - 1) : ENNReal) <=
          (d : ENNReal) ^ (-(2 : Real) / (L : Real)) * rho c :=
        (ENNReal.div_le_iff hrcpos.ne' (by simp)).mp hprevstep
      have hfac0 : (d : ENNReal) ^ (-(2 : Real) / (L : Real)) ≠ 0 :=
        (ENNReal.rpow_pos hdE (by simp)).ne'
      have hfactop : (d : ENNReal) ^ (-(2 : Real) / (L : Real)) ≠ ⊤ :=
        ENNReal.rpow_ne_top_of_ne_zero hdE.ne' (by simp)
      have hlow : (d : ENNReal) ^ (2 * epsilon + 2 / (L : Real)) < rho c := by
        apply (ENNReal.mul_lt_mul_iff_right hfac0 hfactop).mp
        calc
          _ = (d : ENNReal) ^ (2 * epsilon) := by
            rw [← ENNReal.rpow_add _ _ hdE.ne' (by simp)]
            congr 1
            ring
          _ < _ := hprev.trans_le hmul
      refine ⟨⟨c, by omega⟩, hcpos, ?_, hlow, hc⟩
      apply ENNReal.coe_le_coe.mp
      exact (show (d : ENNReal) <= (d : ENNReal) ^ (2 * epsilon + 2 / (L : Real)) by
        simpa only [ENNReal.rpow_one] using ENNReal.rpow_le_rpow_of_exponent_ge hdE1.le
          (show 2 * epsilon + 2 / (L : Real) <= (1 : Real) by linarith)).trans hlow.le
    have actual_full_factored_family :
        ∃ (Ccost : Real) (d0 : NNReal), 1 <= Ccost ∧ 0 < d0 ∧ d0 < 1 ∧
          ∀ etaLambda : Real, 0 < etaLambda -> etaLambda <= etaP / 4 ->
          ∀ d : NNReal, 0 < d -> d < d0 ->
          ∀ {iota : Type uI} [DecidableEq iota]
            (F : Finset iota) (Y : iota -> ShadedTube d E) (rho : Nat -> NNReal)
            (cells : DetailedTrialCellsW94 F Y L rho Ctw Ccell),
            DetailedTrialInputW94 cells epsilon xi zetaPlus etaLambda ->
            ∃ (c : Fin (L + 1)) (H J : Finset iota) (a b : NNReal)
              (U : iota -> Finset iota) (D0 P : ENNReal)
              (Fz : (S : iota) -> ConvexSpaceBody.Factorization
                (completeFibreW94 H (cells.assign c.val) S)
                (fun i => (Y i).toConvexSpaceBody) 2),
              0 < c.val ∧ d <= a ∧ a <= b ∧ b <= rho c.val ∧ rho c.val <= 1 ∧
              (d : ENNReal) ^ (2 * epsilon + 2 / (L : Real)) < rho c.val ∧
              (rho c.val : ENNReal) <= (d : ENNReal) ^ (2 * epsilon) ∧
              H.Nonempty ∧ H ⊆ F ∧ J.Nonempty ∧ J ⊆ cells.parentSet c.val ∧
              H.image (cells.assign c.val) = J ∧
              (H : Set iota).Pairwise
                (fun i j => IsEssentiallyDistinct (Y i).carrier (Y j).carrier) ∧
              FlatPrismParentPresentation (D := 1) H Y J (cells.parentTube c.val) (cells.assign c.val) ∧
              0 < D0 ∧ D0 < ⊤ ∧
              (∀ S ∈ J, U S ⊆ completeFibreW94 F (cells.assign c.val) S) ∧
              (∀ i ∈ H, i ∈ U (cells.assign c.val i)) ∧
              (∀ S ∈ J, D0 <= maxDensity (U S) (fun i => (Y i).toConvexSpaceBody) ∧
                maxDensity (U S) (fun i => (Y i).toConvexSpaceBody) <= 2 * D0) ∧
              (∀ S ∈ J, (Fz S).parts.Nonempty) ∧
              (∀ S ∉ J, (Fz S).parts = ∅) ∧
              H = J.biUnion (fun S => (Fz S).parts.biUnion id) ∧
              (∀ S ∈ J, ∀ q ∈ (Fz S).parts, q.Nonempty ∧ q ⊆ U S ∧
                (d : ENNReal) ^ etaP * (∑ i ∈ q, volume (Y i).carrier) <=
                  ∑ i ∈ q, volume (Y i).shade ∧
                IsPlankOfDimensions plankPigeonhole.C a b
                  (q.convexHull_biUnion (fun i => (Y i).toConvexSpaceBody)) ∧
                (plankPigeonhole.C_vol : ENNReal)⁻¹ * (a : ENNReal) * (b : ENNReal) <=
                  volume (q.convexHull_biUnion (fun i => (Y i).toConvexSpaceBody)).carrier ∧
                (D0 / 2) * volume (q.convexHull_biUnion (fun i => (Y i).toConvexSpaceBody)).carrier <=
                  ∑ i ∈ q, volume (Y i).carrier) ∧
              ((J.biUnion (fun S => (Fz S).parts) : Finset (Finset iota)) : Set (Finset iota)).Pairwise Disjoint ∧
              1 <= P ∧ P < ⊤ ∧
              P <= ENNReal.ofReal (Ccost * (1 + Real.log (1 / (d : Real))) ^ 7) ∧
              (∑ i ∈ F, volume (Y i).shade) <= P * ∑ i ∈ H, volume (Y i).shade := by
      let M := trialEDPreparationCostW96 3 Ctw
      obtain ⟨Cpoly, hCpoly, hpoly⟩ := trial_factoring_loss_le_fixed_polylog_w96
        (cardBound.C : Real) (by exact_mod_cast cardBound.one_le_C)
      let Ccost : Real := max 1 (2 * (M : Real) * Cpoly)
      have hCcost : 1 <= Ccost := le_max_left _ _
      obtain ⟨cutoff, hcutoff, hcutoff1, hbudget⟩ := aggregate_budget Ccost hCcost
      refine ⟨Ccost, min cutoff (1 / 4), hCcost, lt_min hcutoff (by norm_num),
        (min_le_right _ _).trans_lt (by norm_num), ?_⟩
      intro etaLambda hetaLambda hetaLambdaP d hd hdd0 iota _ F Y rho cells input
      have hdcut : d < cutoff := hdd0.trans_le (min_le_left _ _)
      have hdquarter : d <= 1 / 4 := (hdd0.trans_le (min_le_right _ _)).le
      have hdhalf : d <= 1 / 2 := hdquarter.trans (by
        exact_mod_cast (by norm_num : (1 / 4 : Real) <= 1 / 2))
      have hd1 : d <= 1 := hdhalf.trans (by norm_num)
      have hdE : (0 : ENNReal) < d := by exact_mod_cast hd
      have hdE1 : (d : ENNReal) <= 1 := by exact_mod_cast hd1
      have hmass : 0 < ∑ i ∈ F, volume (Y i).shade := by
        by_contra hn
        have hz : (∑ i ∈ F, volume (Y i).shade) = 0 := le_antisymm (le_of_not_gt hn) zero_le
        have hfull := input.fullness
        rw [fullness', hz, ENNReal.zero_div] at hfull
        exact (not_le_of_gt (ENNReal.rpow_pos hdE (by simp))) hfull
      obtain ⟨c, hcpos, hdrc, hclow, hcupp⟩ := central_level d hd (hdcut.trans hcutoff1) F Y rho cells
      have hcL : c.val <= L := by omega
      have hrc1 : rho c.val <= 1 := by
        apply ENNReal.coe_le_coe.mp
        exact hcupp.trans (ENNReal.rpow_le_one hdE1 (by positivity))
      obtain ⟨E0, E1, J1, hE0, hE0F, hE1, hE1E0, hJ1, hJ1sub, hE1eq,
        himage1, hfibres, hE0ED, hE0card, hE0mass, hE1ED, hJ1ED, hpresentation,
        huniform, hpaid1, hfull1, hCF1, hmult1⟩ :=
        exists_actual_fine_and_parent_ED_preparation_w96 hd hdrc hdquarter hrc1 F Y
          (cells.parentSet c.val) (cells.parentTube c.val) (cells.assign c.val)
          Ctw hCtw input.nonempty hmass input.ball (cells.parent_ball c.val hcL)
          input.line_ed (cells.parent_line_ed c.val hcL)
          (cells.assign_image c.val hcL).subset (cells.assigned_containment c.val hcL)
      have hE1F : E1 ⊆ F := hE1E0.trans hE0F
      have hJ1old : J1 ⊆ cells.parentSet c.val := by
        rw [← cells.assign_image c.val hcL]
        exact hJ1sub.trans (Finset.image_subset_image hE0F)
      have hpaid : (∑ i ∈ F, volume (Y i).shade) <= (M : ENNReal) *
          ∑ i ∈ E1, volume (Y i).shade := by simpa only [hdim, M] using hpaid1
      have hmass1 : 0 < ∑ i ∈ E1, volume (Y i).shade := by
        by_contra hn
        have hz : (∑ i ∈ E1, volume (Y i).shade) = 0 := le_antisymm (le_of_not_gt hn) zero_le
        exact (not_le_of_gt hmass) (by simpa only [hz, mul_zero] using hpaid)
      have hparent : IsParentFamily E1 (fun i => (Y i).toTube) J1
          (cells.parentTube c.val) (cells.assign c.val) := by
        refine ⟨hpresentation.mapsTo, ?_, fun i hi => cells.assigned_containment c.val hcL i (hE1F hi)⟩
        intro S hS S' hS' heq
        by_contra hne
        have hED := hJ1ED hS hS' hne
        dsimp only at hED
        have hcarrier := congrArg ConvexSpaceBody.carrier heq
        change (cells.parentTube c.val S).carrier = (cells.parentTube c.val S').carrier at hcarrier
        rw [hcarrier] at hED
        exact not_isEssentiallyDistinct_self
          (Tube.volume_pos_and_lt_top (cells.rho_pos c.val hcL) hrc1 (cells.parentTube c.val S')).1.ne'
          (cells.parentTube c.val S').toConvexSpaceBody.isCompact.measure_ne_top hED
      obtain ⟨Jd, U, Fbase, D0, hJd, hJdJ1, hD0, hD0top, hU, hUne,
        hDbounds, hbandmass, hranges⟩ := exists_weighted_whole_cell_density_band_w96
        hdim hd hdhalf hdrc hrc1 E1 Y J1 (cells.parentTube c.val) (cells.assign c.val)
        hE1 hmass1 (fun i hi => input.ball i (hE1F hi)) hparent himage1
      let LF := trialWeightedDensityBandLossW96 d E1.card
      let LD := trialDimensionBandLossW96 d (rho c.val)
      let MLF : ENNReal := (M : ENNReal) * LF
      have hUoriginal : ∀ S ∈ Jd, U S ⊆ completeFibreW94 F (cells.assign c.val) S := by
        intro S hS i hi
        obtain ⟨hiE1, hiS⟩ := Finset.mem_filter.mp (hU S (hJdJ1 hS) hi)
        exact Finset.mem_filter.mpr ⟨hE1F hiE1, hiS⟩
      have hbandpaid : (∑ i ∈ F, volume (Y i).shade) <=
          MLF * ∑ S ∈ Jd, ∑ i ∈ U S, volume (Y i).shade := by
        exact hpaid.trans (by simpa only [MLF, LF, mul_assoc] using mul_le_mul' (le_refl (M : ENNReal)) hbandmass)
      have hMLFpos : 0 < MLF := by
        by_contra hn
        have hz : MLF = 0 := le_antisymm (le_of_not_gt hn) zero_le
        exact (not_le_of_gt hmass) (by simpa only [hz, zero_mul] using hbandpaid)
      have hMLFtop : MLF < ⊤ := by
        apply ENNReal.mul_lt_top (ENNReal.natCast_lt_top M)
        exact ENNReal.mul_lt_top
          (ENNReal.mul_lt_top ENNReal.ofReal_lt_top (ENNReal.pow_lt_top ENNReal.ofReal_lt_top))
          ENNReal.ofReal_lt_top
      have hcardE := card_le hdim hd hd1 E1 (fun i => (Y i).toTube)
        (fun i hi => input.ball i (hE1F hi)) hE1ED
      have hcardR : (E1.card : Real) <= (cardBound.C : Real) * (d : Real) ^ (-4 : Real) := by
        have hreal := ENNReal.toReal_mono
          (ENNReal.mul_ne_top ENNReal.coe_ne_top
            (ENNReal.rpow_ne_top_of_ne_zero hdE.ne' ENNReal.coe_ne_top)) hcardE
        simpa only [ENNReal.toReal_natCast, ENNReal.toReal_mul,
          ← ENNReal.toReal_rpow, ENNReal.coe_toReal] using hreal
      have hcost : 2 * LD * MLF <=
          ENNReal.ofReal (Ccost * (1 + Real.log (1 / (d : Real))) ^ 7) := by
        have hp := hpoly d (rho c.val) E1.card hd hdhalf hdrc hrc1 hE1.card_pos hcardR
        have hlog : 0 <= Real.log (1 / (d : Real)) := Real.log_nonneg
          ((one_le_div (by exact_mod_cast hd : (0 : Real) < d)).mpr (by exact_mod_cast hd1))
        calc
          _ = (2 * (M : ENNReal)) * (LF * LD) := by ring
          _ <= (2 * (M : ENNReal)) *
              ENNReal.ofReal (Cpoly * (1 + Real.log (1 / (d : Real))) ^ 7) := mul_le_mul' le_rfl hp
          _ = ENNReal.ofReal ((2 * (M : Real) * Cpoly) *
              (1 + Real.log (1 / (d : Real))) ^ 7) := by
            rw [ENNReal.ofReal_mul (by positivity : 0 <= 2 * (M : Real) * Cpoly),
              ENNReal.ofReal_mul (by positivity : 0 <= 2 * (M : Real)),
              ENNReal.ofReal_mul (by norm_num : (0 : Real) <= 2),
              ENNReal.ofReal_ofNat, ENNReal.ofReal_natCast,
              ENNReal.ofReal_mul (zero_le_one.trans hCpoly)]
            ring
          _ <= _ := ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity))
      have hreserve := whole_block_reserve F Y Jd (cells.assign c.val) U
        ((d : ENNReal) ^ etaLambda) ((d : ENNReal) ^ etaP) LD MLF hd hd1 input.nonempty
        hUoriginal input.fullness hMLFpos hMLFtop hbandpaid
        (hbudget etaLambda hetaLambdaP d hd hdcut LD MLF hcost)
      obtain ⟨J2, a, b, parts, H, Fout, hJ2, hJ2Jd, hda, hab, hbrc, hparts,
        hoff, hFout, hHunion, hH, hHE1, himageH, hpaidH, hblocks, hdisjoint⟩ :=
        exists_full_weighted_factored_blocks_w96 hdim hd hdrc hrc1 E1 Y Jd (cells.assign c.val) U hJd
          (fun S hS => hU S (hJdJ1 hS)) (fun S hS => (hUne S (hJdJ1 hS)).1)
          Fbase (fun S hS => (hUne S (hJdJ1 hS)).2) hranges D0 ((d : ENNReal) ^ etaP)
          hD0 hD0top (ENNReal.rpow_pos hdE (by simp))
          (lt_top_iff_ne_top.mpr (ENNReal.rpow_ne_top_of_ne_zero hdE.ne' (by simp))) hDbounds hreserve
      let P : ENNReal := max 1 (2 * LD * MLF)
      have hPcost : P <= ENNReal.ofReal (Ccost * (1 + Real.log (1 / (d : Real))) ^ 7) := by
        apply max_le _ hcost
        apply ENNReal.one_le_ofReal.mpr
        have hlog : 0 <= Real.log (1 / (d : Real)) := Real.log_nonneg
          ((one_le_div (by exact_mod_cast hd : (0 : Real) < d)).mpr (by exact_mod_cast hd1))
        exact one_le_mul_of_one_le_of_one_le hCcost (one_le_pow₀ (by linarith))
      have hHF : H ⊆ F := hHE1.trans hE1F
      refine ⟨c, H, J2, a, b, U, D0, P, Fout, hcpos, hda, hab, hbrc, hrc1,
        hclow, hcupp, hH, hHF, hJ2, hJ2Jd.trans (hJdJ1.trans hJ1old), himageH,
        hE1ED.mono (by exact_mod_cast hHE1), ?_, hD0, hD0top,
        fun S hS => hUoriginal S (hJ2Jd hS), ?_, fun S hS => hDbounds S (hJ2Jd hS),
        ?_, ?_, ?_, ?_, ?_, le_max_left _ _, hPcost.trans_lt (by simp), hPcost, ?_⟩
      · exact { one_le := le_rfl
                mapsTo := fun i hi => himageH ▸ Finset.mem_image_of_mem _ hi
                le_parent_dilate := fun i hi => (cells.assigned_containment c.val hcL i (hHF hi)).trans
                  (Tube.subset_dilate (cells.parentTube c.val (cells.assign c.val i)) (le_refl (1 : Real)))
                pairwise := hJ1ED.mono (by exact_mod_cast hJ2Jd.trans hJdJ1) }
      · intro i hi
        rw [hHunion] at hi
        obtain ⟨S, hS, hiParts⟩ := Finset.mem_biUnion.mp hi
        obtain ⟨q, hq, hiq⟩ := Finset.mem_biUnion.mp hiParts
        have hiU := (hblocks S hS q hq).2.1 hiq
        have hiS := (Finset.mem_filter.mp (hUoriginal S (hJ2Jd hS) hiU)).2
        simpa only [hiS] using hiU
      · intro S hS
        rw [hFout S]
        exact (hparts S hS).1
      · intro S hS
        rw [hFout S]
        exact hoff S hS
      · simpa only [hFout] using hHunion
      · intro S hS q hq
        rw [hFout S] at hq
        obtain ⟨hne, hsub, hfull, hfullmass, hdims, hvlow, hvupp, hvdensity⟩ := hblocks S hS q hq
        exact ⟨hne, hsub, hfullmass, hdims, hvlow, hvdensity⟩
      · simpa only [hFout] using hdisjoint
      · calc
          _ <= MLF * (2 * LD * ∑ i ∈ H, volume (Y i).shade) :=
            hbandpaid.trans (mul_le_mul' le_rfl hpaidH)
          _ = (2 * LD * MLF) * (∑ i ∈ H, volume (Y i).shade) := by ring
          _ <= _ := mul_le_mul' (le_max_right _ _) le_rfl
    have actual_drop_of_complete_cell_bound :
        ∀ (Cstar : NNReal) (Cret : Real), 1 <= Cstar -> 1 <= Cret ->
        ∃ d0 : NNReal, 0 < d0 ∧ d0 < 1 ∧
          ∀ d : NNReal, 0 < d -> d < d0 ->
          ∀ {iota : Type uI} [DecidableEq iota]
            (F G : Finset iota) (Y : iota -> ShadedTube d E) (rho : Nat -> NNReal)
            (cells : DetailedTrialCellsW94 F Y L rho Ctw Ccell) (etaLambda : Real),
            DetailedTrialInputW94 cells epsilon xi zetaPlus etaLambda ->
            G.Nonempty -> G ⊆ F -> ∀ l : Fin (L + 1),
            d <= rho l.val -> rho l.val <= 1 ->
            (d : ENNReal) ^ (1 - 3 * epsilon / 2) <= rho l.val ->
            (rho l.val : ENNReal) <= (d : ENNReal) ^ (3 * epsilon / 2) ->
            (∀ R ∈ G.image (cells.assign l.val),
              frostmanConstIn (exactTubeCellW87 G (fun i => (Y i).toTube) (cells.parentTube l.val R))
                (fun i => (Y i).toConvexSpaceBody) (cells.parentTube l.val R).toConvexSpaceBody <=
                (Cstar : ENNReal) * (d : ENNReal) ^ (-(2 * etaP + 16 / (L : Real) + kappa))) ->
            (∑ i ∈ F, volume (Y i).shade) <=
              ENNReal.ofReal (Cret * (1 + Real.log (1 / (d : Real))) ^ 7) *
                (∑ i ∈ G, volume (Y i).shade) ->
            Nonempty (WindowDetailedTrialDropW98 cells epsilon zetaPlus 8) := by
      intro Cstar Cret hCstar hCret
      obtain ⟨dg, hdg, hdg1, hgapPay⟩ := density_gap_payment Cstar hCstar
      obtain ⟨dm, hdm, hdm1, hmassPay⟩ := fixed_polylog_payment Cret etaP hCret hetaP
      let N := trialNearbyParentCountW96 Ctw
      obtain ⟨dc, hdc, hcoverPay⟩ := exists_threshold_ofReal_le_rpow
        (C := max 1 (N : Real)) (zero_lt_one.trans_le (le_max_left _ _))
        (a := epsilon * zetaPlus / 4) (by positivity)
      refine ⟨min dg (min dm dc), lt_min hdg (lt_min hdm hdc),
        (min_le_left _ _).trans_lt hdg1, ?_⟩
      intro d hd hdd0 iota _ F G Y rho cells etaLambda input hG hGF l hds hs hlow hupp hnew hpaid
      have hdg' : d < dg := hdd0.trans_le (min_le_left _ _)
      have hdm' : d < dm := hdd0.trans_le ((min_le_right _ _).trans (min_le_left _ _))
      have hdc' : d < dc := hdd0.trans_le ((min_le_right _ _).trans (min_le_right _ _))
      have hl : l.val <= L := by omega
      have hdE : (0 : ENNReal) < d := by exact_mod_cast hd
      have hdR : (0 : Real) < d := by exact_mod_cast hd
      have hsE : (0 : ENNReal) < rho l.val := by exact_mod_cast cells.rho_pos l.val hl
      have hCpos : (0 : ENNReal) < Ccell := by exact_mod_cast zero_lt_one.trans_le hCcell
      let J := G.image (cells.assign l.val)
      let Lambda : ENNReal := (1 / (4 * (Ccell : ENNReal))) *
        ((rho l.val : ENNReal) / (d : ENNReal)) ^ zetaPlus
      let u : ENNReal := (Cstar : ENNReal) *
        (d : ENNReal) ^ (-(2 * etaP + 16 / (L : Real) + kappa))
      have hJold : J ⊆ cells.parentSet l.val := by
        rw [← cells.assign_image l.val hl]
        exact Finset.image_subset_image hGF
      have hLambda : 0 < Lambda := by
        dsimp [Lambda]
        exact ENNReal.mul_pos_iff.mpr ⟨ENNReal.div_pos one_ne_zero
          (ENNReal.mul_ne_top (by norm_num) ENNReal.coe_ne_top),
          ENNReal.rpow_pos (ENNReal.div_pos hsE.ne' ENNReal.coe_ne_top)
            (ENNReal.div_ne_top ENNReal.coe_ne_top hdE.ne')⟩
      have hLambdatop : Lambda < ⊤ := by
        dsimp [Lambda]
        apply ENNReal.mul_lt_top
        · exact ENNReal.div_lt_top (by norm_num) (by positivity)
        · exact lt_top_iff_ne_top.mpr (ENNReal.rpow_ne_top_of_ne_zero
            (ENNReal.div_pos hsE.ne' ENNReal.coe_ne_top).ne'
            (ENNReal.div_ne_top ENNReal.coe_ne_top hdE.ne'))
      have hutop : u < ⊤ := ENNReal.mul_lt_top ENNReal.coe_lt_top
        (lt_top_iff_ne_top.mpr (ENNReal.rpow_ne_top_of_ne_zero hdE.ne' ENNReal.coe_ne_top))
      have hline : lineEssentiallyDistinctW94 J (cells.parentTube l.val) Ctw := by
        intro o v hv
        apply le_trans _ (cells.parent_line_ed l.val hl o v hv)
        exact_mod_cast Finset.card_le_card (Finset.filter_subset_filter _ hJold)
      have hcover : (N : ENNReal) * (d : ENNReal) ^ (epsilon * zetaPlus / 2) <=
          (d : ENNReal) ^ (epsilon * zetaPlus / 4) := by
        have hN : (N : ENNReal) <= (d : ENNReal) ^ (-(epsilon * zetaPlus / 4)) := by
          apply le_trans _ (hcoverPay d hd hdc')
          simpa only [ENNReal.ofReal_natCast] using ENNReal.ofReal_le_ofReal (le_max_right 1 (N : Real))
        calc
          _ <= (d : ENNReal) ^ (-(epsilon * zetaPlus / 4)) *
              (d : ENNReal) ^ (epsilon * zetaPlus / 2) := mul_le_mul' hN le_rfl
          _ = _ := by
            rw [← ENNReal.rpow_add _ _ hdE.ne' ENNReal.coe_ne_top]
            congr 1
            ring
      have hpow : ∀ t : Real, ENNReal.ofReal ((d : Real) ^ t) = (d : ENNReal) ^ t := by
        intro t
        rw [← ENNReal.ofReal_rpow_of_pos hdR, ENNReal.ofReal_coe_nnreal]
      have hhalf : epsilon * (2 * zetaPlus) / 4 = epsilon * zetaPlus / 2 := by ring
      have hquarter : epsilon * (2 * zetaPlus) / 8 = epsilon * zetaPlus / 4 := by ring
      obtain ⟨hlocal, hglobal⟩ := actual_old_cell_gap_gives_assigned_and_exact_drop_w96
        hdim hd hds hs F G (fun i => (Y i).toTube) hGF J (cells.parentTube l.val)
        (cells.assign l.val) rfl (fun i hi => cells.assigned_containment l.val hl i (hGF hi))
        input.ball (fun R hR => cells.parent_ball l.val hl R (hJold hR)) Ctw hCtw hline
        epsilon (2 * zetaPlus) Lambda u hLambda hLambdatop hutop
        (fun R hR => (old_complete_geometric_cell F Y rho cells etaLambda input l.val hl hlow hupp R (hJold hR)).le)
        hnew (by
          rw [hpow, hhalf]
          exact hgapPay d hd hdg' (rho l.val) hlow)
        (by
          rw [hpow, hpow, hhalf, hquarter]
          exact hcover)
      simp only [hhalf, hquarter, hpow] at hlocal hglobal
      have hdE1 : (d : ENNReal) <= 1 := by exact_mod_cast (hdg'.trans hdg1).le
      have hweakenHalf : (d : ENNReal) ^ (epsilon * zetaPlus / 2) <=
          (d : ENNReal) ^ (epsilon * zetaPlus / 4) :=
        ENNReal.rpow_le_rpow_of_exponent_ge hdE1 (by nlinarith [mul_pos hepsilon hzeta_pos])
      have hweakenQuarter : (d : ENNReal) ^ (epsilon * zetaPlus / 4) <=
          (d : ENNReal) ^ (epsilon * zetaPlus / 8) :=
        ENNReal.rpow_le_rpow_of_exponent_ge hdE1 (by nlinarith [mul_pos hepsilon hzeta_pos])
      refine ⟨{ level := l
                Fplus := G
                Yplus := Y
                Fplus_nonempty := hG
                Fplus_subset := hGF
                same_tube := fun i hi => rfl
                subshade := fun i hi => Set.Subset.refl _
                nodes := J
                nodes_nonempty := hG.image _
                nodes_subset := hJold
                assignPlus := cells.assign l.val
                assignPlus_image := rfl
                assigned_cover := ?_
                assigned_disjoint := ?_
                assigned_containment := ?_
                card_le := Finset.card_le_card hGF
                mass_retention := ?_
                per_cell_density_drop := ?_
                exact_Ns_drop := ?_
                window_lower := hlow
                window_upper := hupp
                stronger_per_cell := hlocal }⟩
      · ext i
        constructor
        · intro hi
          exact Finset.mem_biUnion.mpr ⟨cells.assign l.val i, Finset.mem_image_of_mem _ hi,
            Finset.mem_filter.mpr ⟨hi, rfl⟩⟩
        · intro hi
          obtain ⟨R, hR, hiR⟩ := Finset.mem_biUnion.mp hi
          exact (Finset.mem_filter.mp hiR).1
      · intro R hR S hS hne
        apply Finset.disjoint_left.mpr
        intro i hiR hiS
        exact hne ((Finset.mem_filter.mp hiR).2.symm.trans (Finset.mem_filter.mp hiS).2)
      · intro R hR i hi
        obtain ⟨hiG, hiR⟩ := Finset.mem_filter.mp hi
        exact Finset.mem_filter.mpr ⟨hGF hiG, hiR ▸ cells.assigned_containment l.val hl i (hGF hiG)⟩
      · calc
          _ <= trialRetainedFractionW94 d 8 *
              (ENNReal.ofReal (Cret * (1 + Real.log (1 / (d : Real))) ^ 7) *
                (∑ i ∈ G, volume (Y i).shade)) := mul_le_mul' le_rfl hpaid
          _ = (trialRetainedFractionW94 d 8 *
              ENNReal.ofReal (Cret * (1 + Real.log (1 / (d : Real))) ^ 7)) *
                (∑ i ∈ G, volume (Y i).shade) := (mul_assoc _ _ _).symm
          _ <= 1 * (∑ i ∈ G, volume (Y i).shade) := mul_le_mul' (hmassPay d hd hdm').2 le_rfl
          _ = _ := one_mul _
      · intro R hR
        exact (hlocal R hR).trans (mul_le_mul_right' hweakenHalf _)
      · exact hglobal.trans (mul_le_mul_right' hweakenQuarter _)
    let kB : NNReal := trialComparableCarrierScaleW96 plankPigeonhole.C
    let Mblock : Nat := trialBlockParentCountW96 Ctw kB
    let CV : NNReal := plankPigeonhole.C_vol
    let Cvol : NNReal := Tube.volume_le.C 3
    let Cstar : NNReal := max 1
      (4 * (trialNearbyParentCountW96 Ctw : NNReal) * (Mblock : NNReal) * CV * Cvol)
    have hkB : 1 <= kB := by
      dsimp [kB, trialComparableCarrierScaleW96]
      exact le_add_of_nonneg_left zero_le
    have hCw : 1 <= plankPigeonhole.C := by
      have hc : (1 : NNReal) <= Metric.volume_comparison.C 3 := by
        norm_num [Metric.volume_comparison.C, Metric.lt_volume_convexHull.c]
      exact (by norm_num : (1 : NNReal) <= 16).trans
        (le_mul_of_one_le_right (by norm_num) hc)
    have hCV : (0 : NNReal) < CV := by
      have hCw0 : (0 : NNReal) < plankPigeonhole.C := zero_lt_one.trans_le hCw
      dsimp [CV, plankPigeonhole.C_vol]
      positivity
    have hCvol : (0 : NNReal) < Cvol := by norm_num [Cvol, Tube.volume_le.C]
    have actual_working_refinement :
        ∀ d : NNReal, 0 < d -> d < 1 ->
        ∀ {iota : Type uI} [DecidableEq iota]
          (F H J : Finset iota) (Y : iota -> ShadedTube d E) (rho : Nat -> NNReal)
          (cells : DetailedTrialCellsW94 F Y L rho Ctw Ccell) (etaLambda : Real),
          DetailedTrialInputW94 cells epsilon xi zetaPlus etaLambda ->
          H.Nonempty -> H ⊆ F -> J.Nonempty ->
          ∀ (c : Fin (L + 1)) (a b : NNReal) (U : iota -> Finset iota) (D0 : ENNReal),
          d <= a -> a <= b -> b <= rho c.val -> rho c.val <= 1 ->
          (b : ENNReal) <= (d : ENNReal) ^ (2 * epsilon) ->
          (d : ENNReal) ^ (1 - 3 * epsilon / 2) < b ->
          (b : ENNReal) / (a : ENNReal) <= (d : ENNReal) ^ (-kappa) ->
          kB * b <= 1 -> J ⊆ cells.parentSet c.val ->
          (∀ S ∈ J, U S ⊆ completeFibreW94 F (cells.assign c.val) S) ->
          (∀ i ∈ H, i ∈ U (cells.assign c.val i)) -> H.image (cells.assign c.val) = J ->
          0 < D0 -> D0 < ⊤ ->
          (∀ S ∈ J, maxDensity (U S) (fun i => (Y i).toConvexSpaceBody) <= 2 * D0) ->
          ∀ Fz : (S : iota) -> ConvexSpaceBody.Factorization
            (completeFibreW94 H (cells.assign c.val) S) (fun i => (Y i).toConvexSpaceBody) 2,
          (∀ S ∈ J, (Fz S).parts.Nonempty) ->
          H = J.biUnion (fun S => (Fz S).parts.biUnion id) ->
          ((J.biUnion (fun S => (Fz S).parts) : Finset (Finset iota)) : Set (Finset iota)).Pairwise Disjoint ->
          (∀ S ∈ J, ∀ q ∈ (Fz S).parts,
            (d : ENNReal) ^ etaP * (∑ i ∈ q, volume (Y i).carrier) <= ∑ i ∈ q, volume (Y i).shade ∧
            IsPlankOfDimensions plankPigeonhole.C a b
              (q.convexHull_biUnion (fun i => (Y i).toConvexSpaceBody)) ∧
            (CV : ENNReal)⁻¹ * (a : ENNReal) * (b : ENNReal) <=
              volume (q.convexHull_biUnion (fun i => (Y i).toConvexSpaceBody)).carrier ∧
            (D0 / 2) * volume (q.convexHull_biUnion (fun i => (Y i).toConvexSpaceBody)).carrier <=
              ∑ i ∈ q, volume (Y i).carrier) ->
          ∃ (l : Fin (L + 1)) (G : Finset iota),
            G.Nonempty ∧ G ⊆ H ∧ d <= rho l.val ∧ rho l.val <= 1 ∧
            (d : ENNReal) ^ (1 - 3 * epsilon / 2) <= rho l.val ∧
            (rho l.val : ENNReal) <= (d : ENNReal) ^ (3 * epsilon / 2) ∧
            (∑ i ∈ H, volume (Y i).shade) <= (Mblock : ENNReal) * ∑ i ∈ G, volume (Y i).shade ∧
            (∀ R ∈ G.image (cells.assign l.val),
              frostmanConstIn (exactTubeCellW87 G (fun i => (Y i).toTube) (cells.parentTube l.val R))
                (fun i => (Y i).toConvexSpaceBody) (cells.parentTube l.val R).toConvexSpaceBody <=
                (Cstar : ENNReal) * (d : ENNReal) ^ (-(2 * etaP + 16 / (L : Real) + kappa))) := by
      intro d hd hd1 iota _ F H J Y rho cells etaLambda input hH hHF hJ c a b U D0
        hda hab hbrho hrho hbupper hblower hecc hsmall hJold hU hreference himage hD0 hD0top
        hUdensity Fz hparts hHunion hdisjoint hblocks
      have hcL : c.val <= L := by omega
      have ha : 0 < a := hd.trans_le hda
      have hb : 0 < b := ha.trans_le hab
      have hdE : (0 : ENNReal) < d := by exact_mod_cast hd
      have haE : (0 : ENNReal) < a := by exact_mod_cast ha
      have hbE : (0 : ENNReal) < b := by exact_mod_cast hb
      obtain ⟨l, hbsE, hadj, hlow, hupp⟩ := working_level d hd hd1 rho cells.rho_zero cells.rho_bottom
        cells.rho_pos cells.rho_step b hblower hbupper
      have hl : l.val <= L := by omega
      have hbs : b <= rho l.val := by exact_mod_cast hbsE
      have hds : d <= rho l.val := hda.trans (hab.trans hbs)
      have hs : rho l.val <= 1 := by
        apply ENNReal.coe_le_coe.mp
        exact hupp.trans (ENNReal.rpow_le_one (by exact_mod_cast hd1.le) (by positivity))
      let Q := J.biUnion (fun S => (Fz S).parts)
      have hQ : Q.Nonempty := by
        obtain ⟨S, hS⟩ := hJ
        obtain ⟨q, hq⟩ := hparts S hS
        exact ⟨q, Finset.mem_biUnion.mpr ⟨S, hS, hq⟩⟩
      have hqnonempty : ∀ q ∈ Q, q.Nonempty := by
        intro q hq
        obtain ⟨S, hS, hqS⟩ := Finset.mem_biUnion.mp hq
        exact (Fz S).nonempty_of_mem_parts hqS
      have hqsub : ∀ q ∈ Q, q ⊆ H := by
        intro q hq
        obtain ⟨S, hS, hqS⟩ := Finset.mem_biUnion.mp hq
        exact ((Fz S).le hqS).trans (Finset.filter_subset _ _)
      have hQunion : Q.biUnion id = H := by
        rw [hHunion]
        exact Finset.biUnion_biUnion _ _ _
      obtain ⟨i0, hi0⟩ := hH
      have hcarrier : ∀ q : Finset iota, ∃ B : Tube (kB * b) E,
          q ∈ Q -> q.convexHull_biUnion (fun i => (Y i).toConvexSpaceBody) <= B.toConvexSpaceBody := by
        intro q
        by_cases hq : q ∈ Q
        · obtain ⟨S, hS, hqS⟩ := Finset.mem_biUnion.mp hq
          obtain ⟨o, v, hv, henv, i, hi, hcentre, hx, hy, hcontain, hvol⟩ :=
            exists_comparable_centred_attached_carrier_w96 hdim hd hda hab plankPigeonhole.C hCw
              hsmall q (fun i => (Y i).toTube) (hqnonempty q hq)
              (by
                intro i hi
                simpa only [centredTubeW94, Tube.IsCentred, Tube.center, midpoint_eq_smul_add,
                  Tube.midpoint, invOf_eq_inv, one_div]
                  using input.centred i (hHF (hqsub q hq hi)))
              (fun i hi => input.ball i (hHF (hqsub q hq hi))) (hblocks S hS q hqS).2.1
          exact ⟨(Y i).toTube.rescale (kB * b), fun _ => hcontain⟩
        · exact ⟨(Y i0).toTube.rescale (kB * b), fun hq' => (hq hq').elim⟩
      choose B hB using hcarrier
      let v := volume (Y i0).carrier
      have hv : 0 < v := (Tube.volume_pos_and_lt_top hd hd1.le (Y i0).toTube).1
      have hvtop : v < ⊤ := (Y i0).toConvexSpaceBody.isCompact.measure_lt_top
      have hvol : ∀ i ∈ H, volume (Y i).carrier = v :=
        fun i hi => Tube.volume_carrier_eq_volume_carrier (Y i).toTube (Y i0).toTube
      have hqvol : ∀ q ∈ Q, (∑ i ∈ q, volume (Y i).carrier) = (q.card : ENNReal) * v := by
        intro q hq
        calc
          _ = ∑ i ∈ q, v := Finset.sum_congr rfl (fun i hi => hvol i (hqsub q hq hi))
          _ = _ := by simp
      have hfullq : ∀ q ∈ Q, (d : ENNReal) ^ etaP * ((q.card : ENNReal) * v) <=
          ∑ i ∈ q, volume (Y i).shade := by
        intro q hq
        obtain ⟨S, hS, hqS⟩ := Finset.mem_biUnion.mp hq
        rw [← hqvol q hq]
        exact (hblocks S hS q hqS).1
      have hmassq : ∀ q ∈ Q, D0 * (a : ENNReal) * (b : ENNReal) / (2 * (CV : ENNReal)) <=
          (q.card : ENNReal) * v := by
        intro q hq
        obtain ⟨S, hS, hqS⟩ := Finset.mem_biUnion.mp hq
        rw [← hqvol q hq]
        calc
          _ = (D0 / 2) * ((CV : ENNReal)⁻¹ * (a : ENNReal) * (b : ENNReal)) := by
            simp only [div_eq_mul_inv, ENNReal.mul_inv
              (Or.inl (by norm_num : (2 : ENNReal) ≠ 0)) (Or.inl (by norm_num : (2 : ENNReal) ≠ ⊤))]
            ring
          _ <= (D0 / 2) * volume (q.convexHull_biUnion (fun i => (Y i).toConvexSpaceBody)).carrier :=
            mul_le_mul' le_rfl (hblocks S hS q hqS).2.2.1
          _ <= _ := (hblocks S hS q hqS).2.2.2
      obtain ⟨chosen, qPlus, G, hchosen, hqPlusEq, hqPlus, hcount, hblockpaid, hcardplus,
        hmassplus, hGunion, hG, hGH, hpaidG, hcontained, hoccupied⟩ :=
        exists_actual_working_parent_subblocks_w96 hdim hd hda hab hbs hs kB Ctw hkB hCtw H Y Q hQ
          hqnonempty hqsub hdisjoint B
          (fun q hq i hi => (Finset.le_convexHull_biUnion _ hi).trans (hB q hq))
          (cells.parentSet l.val) (cells.parentTube l.val) (cells.assign l.val)
          (by rw [← cells.assign_image l.val hl]; exact Finset.image_subset_image hHF)
          (fun i hi => cells.assigned_containment l.val hl i (hHF hi))
          (fun i hi => input.ball i (hHF hi)) (cells.parent_ball l.val hl) (cells.parent_line_ed l.val hl)
          v ((d : ENNReal) ^ etaP) D0 CV hv hvtop
          (ENNReal.rpow_pos hdE ENNReal.coe_ne_top)
          (lt_top_iff_ne_top.mpr (ENNReal.rpow_ne_top_of_ne_zero hdE.ne' ENNReal.coe_ne_top))
          hD0 hD0top (by exact_mod_cast hCV) ENNReal.coe_lt_top hvol hfullq hmassq
      have hGF : G ⊆ F := hGH.trans hHF
      have hGcover : G ⊆ J.biUnion U := by
        intro i hi
        exact Finset.mem_biUnion.mpr ⟨cells.assign c.val i,
          himage ▸ Finset.mem_image_of_mem _ (hGH hi), hreference i (hGH hi)⟩
      have hline : lineEssentiallyDistinctW94 J (cells.parentTube c.val) Ctw := by
        intro o v hv
        apply le_trans _ (cells.parent_line_ed c.val hcL o v hv)
        exact_mod_cast Finset.card_le_card (Finset.filter_subset_filter _ hJold)
      have hadjE : (rho l.val : ENNReal) / (b : ENNReal) <=
          (d : ENNReal) ^ (-2 / (L : Real)) :=
        (ENNReal.div_le_iff hbE.ne' ENNReal.coe_ne_top).mpr hadj.le
      have hadjR : (rho l.val : Real) / (b : Real) <= (d : Real) ^ (-2 / (L : Real)) := by
        have hreal := ENNReal.toReal_mono
          (ENNReal.rpow_ne_top_of_ne_zero hdE.ne' ENNReal.coe_ne_top) hadjE
        simpa only [ENNReal.toReal_div, ← ENNReal.toReal_rpow, ENNReal.coe_toReal] using hreal
      have heccR : (b : Real) / (a : Real) <= (d : Real) ^ (-kappa) := by
        have hreal := ENNReal.toReal_mono
          (ENNReal.rpow_ne_top_of_ne_zero hdE.ne' ENNReal.coe_ne_top) hecc
        simpa only [ENNReal.toReal_div, ← ENNReal.toReal_rpow, ENNReal.coe_toReal] using hreal
      have hscale := complete_cell_scale_payment_w96 (by exact_mod_cast hd) (by exact_mod_cast hd1.le)
        (by exact_mod_cast ha) (by exact_mod_cast hab) (by exact_mod_cast hbrho) (by exact_mod_cast hbs)
        L (by omega) etaP kappa hetaP.le hadjR heccR
      have hscaleE : ((d : ENNReal) ^ etaP)⁻¹ *
          ENNReal.ofReal ((max 1 ((rho l.val : Real) / (rho c.val : Real))) ^ (6 : Nat)) *
          ((rho l.val : ENNReal) / (b : ENNReal)) ^ (2 : Nat) * ((b : ENNReal) / (a : ENNReal)) <=
          (d : ENNReal) ^ (-2 * etaP - 16 / (L : Real) - kappa) := by
        apply (ENNReal.toReal_le_toReal (by finiteness)
          (ENNReal.rpow_ne_top_of_ne_zero hdE.ne' ENNReal.coe_ne_top)).mp
        simp only [ENNReal.toReal_mul, ENNReal.toReal_inv, ← ENNReal.toReal_rpow,
          ENNReal.coe_toReal, ENNReal.toReal_ofReal (by positivity : 0 <= (max 1
            ((rho l.val : Real) / (rho c.val : Real))) ^ (6 : Nat)),
          ENNReal.toReal_pow, ENNReal.toReal_div]
        exact hscale.2.2.1.trans hscale.2.2.2
      have hCstar : trialCompleteCellConstantW96 Ctw kB CV Cvol <= (Cstar : ENNReal) := by
        dsimp [Cstar, trialCompleteCellConstantW96, Mblock]
        exact_mod_cast le_max_right (1 : NNReal)
          (4 * (trialNearbyParentCountW96 Ctw : NNReal) *
            (trialBlockParentCountW96 Ctw kB : NNReal) * CV * Cvol)
      refine ⟨l, G, hG, hGH, hds, hs, hlow, hupp, ?_, ?_⟩
      · simpa only [hQunion, Mblock] using hpaidG
      · intro R hR
        obtain ⟨q, hq, hchosenR, hqR⟩ := hoccupied R hR
        have hsub : qPlus q ⊆ exactTubeCellW87 G (fun i => (Y i).toTube) (cells.parentTube l.val R) := by
          intro i hi
          obtain ⟨hiG, hiR⟩ := Finset.mem_filter.mp (hqR hi)
          exact Finset.mem_filter.mpr ⟨hiG, hiR ▸ cells.assigned_containment l.val hl i (hGF hiG)⟩
        have hbound := complete_refined_cell_frostman_bound_w96 hdim hd hda hab hbrho hrho hbs F G
          (fun i => (Y i).toTube) hGF J (cells.parentTube c.val) U
          (fun S hS => (hU S hS).trans (Finset.filter_subset _ _))
          (by
            intro S hS i hi
            obtain ⟨hiF, hiS⟩ := Finset.mem_filter.mp (hU S hS hi)
            exact hiS ▸ cells.assigned_containment c.val hcL i hiF)
          hGcover input.ball (fun S hS => cells.parent_ball c.val hcL S (hJold hS))
          Ctw kB hCtw hkB hline D0 ((d : ENNReal) ^ etaP) CV Cvol hD0 hD0top
          (ENNReal.rpow_pos hdE ENNReal.coe_ne_top)
          (lt_top_iff_ne_top.mpr (ENNReal.rpow_ne_top_of_ne_zero hdE.ne' ENNReal.coe_ne_top))
          (by exact_mod_cast hCV) ENNReal.coe_lt_top (by exact_mod_cast hCvol) ENNReal.coe_lt_top
          hUdensity (cells.parentTube l.val R) (qPlus q) (hqPlus q hq).1 hsub (hmassplus q hq)
          (by simpa only [hdim, Cvol, show 3 - 1 = 2 from rfl] using Tube.volume_le hs (cells.parentTube l.val R))
        calc
          _ <= trialCompleteCellConstantW96 Ctw kB CV Cvol *
              (((d : ENNReal) ^ etaP)⁻¹ *
                ENNReal.ofReal ((max 1 ((rho l.val : Real) / (rho c.val : Real))) ^ (6 : Nat)) *
                ((rho l.val : ENNReal) / (b : ENNReal)) ^ (2 : Nat) * ((b : ENNReal) / (a : ENNReal))) := by
            simpa only [mul_assoc] using hbound.2.2.2.2
          _ <= (Cstar : ENNReal) * (d : ENNReal) ^ (-2 * etaP - 16 / (L : Real) - kappa) :=
            mul_le_mul' hCstar hscaleE
          _ = _ := by congr 2; ring
    have actual_wide_drop : ∀ Ccost : Real, 1 <= Ccost ->
        ∃ d0 : NNReal, 0 < d0 ∧ d0 < 1 ∧
          ∀ d : NNReal, 0 < d -> d < d0 ->
          ∀ {iota : Type uI} [DecidableEq iota]
            (F H J : Finset iota) (Y : iota -> ShadedTube d E) (rho : Nat -> NNReal)
            (cells : DetailedTrialCellsW94 F Y L rho Ctw Ccell) (etaLambda : Real),
            DetailedTrialInputW94 cells epsilon xi zetaPlus etaLambda ->
            H.Nonempty -> H ⊆ F -> J.Nonempty ->
            ∀ (c : Fin (L + 1)) (a b : NNReal) (U : iota -> Finset iota) (D0 P : ENNReal),
            d <= a -> a <= b -> b <= rho c.val -> rho c.val <= 1 ->
            (b : ENNReal) <= (d : ENNReal) ^ (2 * epsilon) ->
            (d : ENNReal) ^ (1 - 3 * epsilon / 2) < b ->
            (b : ENNReal) / (a : ENNReal) <= (d : ENNReal) ^ (-kappa) ->
            J ⊆ cells.parentSet c.val ->
            (∀ S ∈ J, U S ⊆ completeFibreW94 F (cells.assign c.val) S) ->
            (∀ i ∈ H, i ∈ U (cells.assign c.val i)) -> H.image (cells.assign c.val) = J ->
            0 < D0 -> D0 < ⊤ ->
            (∀ S ∈ J, maxDensity (U S) (fun i => (Y i).toConvexSpaceBody) <= 2 * D0) ->
            ∀ Fz : (S : iota) -> ConvexSpaceBody.Factorization
              (completeFibreW94 H (cells.assign c.val) S) (fun i => (Y i).toConvexSpaceBody) 2,
            (∀ S ∈ J, (Fz S).parts.Nonempty) ->
            H = J.biUnion (fun S => (Fz S).parts.biUnion id) ->
            ((J.biUnion (fun S => (Fz S).parts) : Finset (Finset iota)) : Set (Finset iota)).Pairwise Disjoint ->
            (∀ S ∈ J, ∀ q ∈ (Fz S).parts,
              (d : ENNReal) ^ etaP * (∑ i ∈ q, volume (Y i).carrier) <= ∑ i ∈ q, volume (Y i).shade ∧
              IsPlankOfDimensions plankPigeonhole.C a b
                (q.convexHull_biUnion (fun i => (Y i).toConvexSpaceBody)) ∧
              (CV : ENNReal)⁻¹ * (a : ENNReal) * (b : ENNReal) <=
                volume (q.convexHull_biUnion (fun i => (Y i).toConvexSpaceBody)).carrier ∧
              (D0 / 2) * volume (q.convexHull_biUnion (fun i => (Y i).toConvexSpaceBody)).carrier <=
                ∑ i ∈ q, volume (Y i).carrier) ->
            P <= ENNReal.ofReal (Ccost * (1 + Real.log (1 / (d : Real))) ^ 7) ->
            (∑ i ∈ F, volume (Y i).shade) <= P * ∑ i ∈ H, volume (Y i).shade ->
            Nonempty (WindowDetailedTrialDropW98 cells epsilon zetaPlus 8) := by
      intro Ccost hCcost
      let Cret : Real := max 1 (Ccost * (Mblock : Real))
      obtain ⟨dt, hdt, hdt1, hdrop⟩ := actual_drop_of_complete_cell_bound
        Cstar Cret (le_max_left _ _) (le_max_left _ _)
      obtain ⟨dc, hdc, hcarrierPay⟩ := exists_threshold_ofReal_le_rpow
        (C := (kB : Real)) (by exact_mod_cast zero_lt_one.trans_le hkB) (a := epsilon) hepsilon
      refine ⟨min dt dc, lt_min hdt hdc, (min_le_left _ _).trans_lt hdt1, ?_⟩
      intro d hd hdd0 iota _ F H J Y rho cells etaLambda input hH hHF hJ c a b U D0 P
        hda hab hbrho hrho hbupper hblower hecc hJold hU hreference himage hD0 hD0top
        hUdensity Fz hparts hHunion hdisjoint hblocks hPcost hpaid
      have hdt' : d < dt := hdd0.trans_le (min_le_left _ _)
      have hdc' : d < dc := hdd0.trans_le (min_le_right _ _)
      have hd1 : d < 1 := hdt'.trans hdt1
      have hdE : (0 : ENNReal) < d := by exact_mod_cast hd
      have hsmall : kB * b <= 1 := by
        apply ENNReal.coe_le_coe.mp
        push_cast
        have hkbpay : (kB : ENNReal) <= (d : ENNReal) ^ (-epsilon) := by
          simpa only [ENNReal.ofReal_coe_nnreal] using hcarrierPay d hd hdc'
        calc
          _ <= (d : ENNReal) ^ (-epsilon) * (d : ENNReal) ^ (2 * epsilon) :=
            mul_le_mul' hkbpay hbupper
          _ = (d : ENNReal) ^ epsilon := by
            rw [← ENNReal.rpow_add _ _ hdE.ne' ENNReal.coe_ne_top]
            congr 1
            ring
          _ <= 1 := ENNReal.rpow_le_one (by exact_mod_cast hd1.le) hepsilon.le
      obtain ⟨l, G, hG, hGH, hds, hs, hlow, hupp, hpaidG, hnew⟩ := actual_working_refinement
        d hd hd1 F H J Y rho cells etaLambda input hH hHF hJ c a b U D0 hda hab hbrho hrho
        hbupper hblower hecc hsmall hJold hU hreference himage hD0 hD0top hUdensity
        Fz hparts hHunion hdisjoint hblocks
      have hlog : 0 <= Real.log (1 / (d : Real)) := Real.log_nonneg
        ((one_le_div (by exact_mod_cast hd : (0 : Real) < d)).mpr (by exact_mod_cast hd1.le))
      have hcost : P * (Mblock : ENNReal) <=
          ENNReal.ofReal (Cret * (1 + Real.log (1 / (d : Real))) ^ 7) := by
        calc
          _ <= ENNReal.ofReal (Ccost * (1 + Real.log (1 / (d : Real))) ^ 7) *
              (Mblock : ENNReal) := mul_le_mul' hPcost le_rfl
          _ = ENNReal.ofReal ((Ccost * (Mblock : Real)) *
              (1 + Real.log (1 / (d : Real))) ^ 7) := by
            simp only [ENNReal.ofReal_mul (by positivity : 0 <= Ccost * (Mblock : Real)),
              ENNReal.ofReal_mul (zero_le_one.trans hCcost), ENNReal.ofReal_natCast]
            ring
          _ <= _ := ENNReal.ofReal_le_ofReal
            (mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity))
      apply hdrop d hd hdt' F G Y rho cells etaLambda input hG (hGH.trans hHF)
        l hds hs hlow hupp hnew
      calc
        _ <= P * ((Mblock : ENNReal) * ∑ i ∈ G, volume (Y i).shade) :=
          hpaid.trans (mul_le_mul' le_rfl hpaidG)
        _ = (P * (Mblock : ENNReal)) * ∑ i ∈ G, volume (Y i).shade := (mul_assoc _ _ _).symm
        _ <= _ := mul_le_mul' hcost le_rfl
    have fixed_raw_small_cost_payment : ∀ (Ccost etaRaw nu : Real),
        1 <= Ccost -> 0 < etaRaw -> 0 < nu ->
        ∃ d0 : NNReal, 0 < d0 ∧ d0 < 1 ∧
          ∀ d : NNReal, 0 < d -> d < d0 -> ∀ P : ENNReal,
            P <= ENNReal.ofReal (Ccost * (1 + Real.log (1 / (d : Real))) ^ 7) ->
            P <= (d : ENNReal) ^ (-etaRaw) ∧
            P ^ (1 + (1 - gamma / 2)) <= (d : ENNReal) ^ (-xi / 10) ∧
            P <= (d : ENNReal) ^ (-nu) := by
      intro Ccost etaRaw nu hCcost hetaRaw hnu
      let alpha : Real := min etaRaw (min nu (xi / 20))
      have halpha : 0 < alpha := lt_min hetaRaw (lt_min hnu (by positivity))
      have halphaRaw : alpha <= etaRaw := min_le_left _ _
      have halphaNu : alpha <= nu := (min_le_right _ _).trans (min_le_left _ _)
      have halphaXi : alpha <= xi / 20 := (min_le_right _ _).trans (min_le_right _ _)
      obtain ⟨d0, hd0, hd01, hpay⟩ := fixed_polylog_payment Ccost alpha hCcost halpha
      refine ⟨d0, hd0, hd01, ?_⟩
      intro d hd hdd0 P hPcost
      have hdE1 : (d : ENNReal) <= 1 := by exact_mod_cast (hdd0.trans hd01).le
      have hP : P <= (d : ENNReal) ^ (-alpha) := hPcost.trans (hpay d hd hdd0).1
      have hpowpos : 0 <= 1 + (1 - gamma / 2) := by linarith
      have hpowle : 1 + (1 - gamma / 2) <= 2 := by linarith
      have hpaid : alpha * (1 + (1 - gamma / 2)) <= xi / 10 := by
        exact (mul_le_mul_of_nonneg_left hpowle halpha.le).trans (by linarith)
      refine ⟨hP.trans (ENNReal.rpow_le_rpow_of_exponent_ge hdE1 (by linarith)), ?_,
        hP.trans (ENNReal.rpow_le_rpow_of_exponent_ge hdE1 (by linarith))⟩
      calc
        _ <= ((d : ENNReal) ^ (-alpha)) ^ (1 + (1 - gamma / 2)) :=
          ENNReal.rpow_le_rpow hP hpowpos
        _ = (d : ENNReal) ^ (-alpha * (1 + (1 - gamma / 2))) := (ENNReal.rpow_mul _ _ _).symm
        _ <= _ := ENNReal.rpow_le_rpow_of_exponent_ge hdE1 (by nlinarith)
    obtain ⟨Ccost, dFull, hCcost, hdFull, hdFull1, hfamily⟩ := actual_full_factored_family
    obtain ⟨etaRaw, hetaRaw, hetaRawXi, hraw⟩ :=
      actual_raw_eccentricity_good_transfer_w97 hdim beta gamma epsilon xi
        hbeta hbeta_gamma hgamma hepsilon hxi hKT hKF
    obtain ⟨etaSmall, nu, hetaSmall, hnu, hsmall⟩ :=
      actual_small_width_good_from_factored_family_w97 hdim beta gamma epsilon xi
        hbeta hbeta_gamma hgamma hepsilon hepsilon_lt hgap hxi hxi_upper
        L hL hLmin Ctw hCtw hKT hKF
    let etaLambda : Real := min (etaP / 4) (min etaRaw etaSmall)
    have hetaLambda : 0 < etaLambda := lt_min (by positivity) (lt_min hetaRaw hetaSmall)
    have hetaLambdaP : etaLambda <= etaP / 4 := min_le_left _ _
    have hetaLambdaRaw : etaLambda <= etaRaw := (min_le_right _ _).trans (min_le_left _ _)
    have hetaLambdaSmall : etaLambda <= etaSmall := (min_le_right _ _).trans (min_le_right _ _)
    obtain ⟨dRaw, hdRaw, hrawAt⟩ := mem_nhdsGT_iff_exists_Ioc_subset.mp
      (hraw etaLambda hetaLambda hetaLambdaRaw)
    obtain ⟨dSmall, hdSmall, hsmallAt⟩ := mem_nhdsGT_iff_exists_Ioc_subset.mp
      (hsmall etaLambda hetaLambda hetaLambdaSmall)
    obtain ⟨dCost, hdCost, hdCost1, hcostAt⟩ :=
      fixed_raw_small_cost_payment Ccost etaRaw nu hCcost hetaRaw hnu
    obtain ⟨dWide, hdWide, hdWide1, hwideAt⟩ := actual_wide_drop Ccost hCcost
    let d0 : NNReal := min dFull (min dRaw (min dSmall (min dCost dWide)))
    have hd0 : 0 < d0 := lt_min hdFull (lt_min hdRaw (lt_min hdSmall (lt_min hdCost hdWide)))
    have hd01 : d0 < 1 := (min_le_left _ _).trans_lt hdFull1
    refine ⟨etaLambda, d0, 8, hetaLambda, hd0, hd01, by norm_num, ?_⟩
    intro d hd hdd0 iota _ F Y rho cells input
    have hdFull' : d < dFull := hdd0.trans_le (min_le_left _ _)
    have hdRaw' : d < dRaw := hdd0.trans_le ((min_le_right _ _).trans (min_le_left _ _))
    have hdSmall' : d < dSmall := hdd0.trans_le
      ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
    have hdCost' : d < dCost := hdd0.trans_le
      ((min_le_right _ _).trans ((min_le_right _ _).trans
        ((min_le_right _ _).trans (min_le_left _ _))))
    have hdWide' : d < dWide := hdd0.trans_le
      ((min_le_right _ _).trans ((min_le_right _ _).trans
        ((min_le_right _ _).trans (min_le_right _ _))))
    by_cases hgood : detailedInnerGoodW94 F Y gamma epsilon xi
    · exact Or.inl hgood
    obtain ⟨c, H, J, a, b, U, D0, P, Fz, hcpos, hda, hab, hbrho, hrho,
      hrholow, hrhoupper, hH, hHF, hJ, hJold, himage, hED, hpresentation,
      hD0, hD0top, hU, hreference, hUdensity, hparts, hpartsEmpty, hHunion,
      hblocks, hdisjoint, hP, hPtop, hPcost, hpaid⟩ :=
      hfamily etaLambda hetaLambda hetaLambdaP d hd hdFull' F Y rho cells input
    have hcL : c.val <= L := Nat.le_of_lt_succ c.isLt
    have hFzdims : ∀ S ∈ J, IsPlankFamilyOfDimensions plankPigeonhole.C a b (Fz S).parts
        (fun q => q.convexHull_biUnion (fun i => (Y i).toConvexSpaceBody)) := by
      intro S hS q hq
      exact (hblocks S hS q hq).2.2.2.1
    obtain ⟨hPraw, hPpow, hPsmall⟩ := hcostAt d hd hdCost' P hPcost
    have hrawResult := hrawAt ⟨hd, hdRaw'.le⟩ F H Y a b (rho c.val) J
      (cells.parentTube c.val) (cells.assign c.val) P input.nonempty hH hHF
      hda hab hbrho hrho input.ball hED hpresentation
      (fun S hS => ⟨Fz S, hFzdims S hS⟩) hP hPtop hPraw hPpow hpaid
      input.fullness input.frostman
    have hecc : (b : ENNReal) / (a : ENNReal) <
        (d : ENNReal) ^ (-trialSourceKappaW97 gamma epsilon xi) :=
      hrawResult.2.2.2.2.2.2 hgood
    by_cases hbsmall : b <= d ^ (1 - 3 * epsilon / 2)
    · apply Or.inl
      apply hsmallAt ⟨hd, hdSmall'.le⟩ F H Y a b (rho c.val) J
        (cells.parentTube c.val) (cells.assign c.val) U D0 P input.nonempty hH hHF
        hda hab hbrho hrho
        (by
          apply ENNReal.coe_lt_coe.mp
          simpa only [ENNReal.coe_rpow_of_ne_zero hd.ne'] using hrholow)
        (by
          apply ENNReal.coe_le_coe.mp
          simpa only [ENNReal.coe_rpow_of_ne_zero hd.ne'] using hrhoupper) hbsmall hecc
        input.ball _ hED himage hpresentation
        (fun S hS => cells.parent_ball c.val hcL S (hJold hS)) _ hD0 hD0top hreference _
        (fun S hS => (hUdensity S hS).2) Fz hFzdims
        (fun S hS q hq => (hblocks S hS q hq).2.2.2.2.2)
        hP hPtop hPsmall hpaid input.fullness input.frostman
      · intro i hi
        simpa only [centredTubeW94, Tube.IsCentred, Tube.center,
          midpoint_eq_smul_add, Tube.midpoint, invOf_eq_inv, one_div]
          using input.centred i (hHF hi)
      · intro o v hv
        apply le_trans _ (cells.parent_line_ed c.val hcL o v hv)
        exact_mod_cast Finset.card_le_card (Finset.filter_subset_filter _ hJold)
      · intro S hS i hi
        obtain ⟨hiF, hiS⟩ := Finset.mem_filter.mp (hU S hS hi)
        exact hiS ▸ cells.assigned_containment c.val hcL i hiF
    · apply Or.inr
      apply hwideAt d hd hdWide' F H J Y rho cells etaLambda input hH hHF hJ
        c a b U D0 P hda hab hbrho hrho (le_trans (by exact_mod_cast hbrho) hrhoupper)
        (by
          rw [← ENNReal.coe_rpow_of_ne_zero hd.ne']
          exact_mod_cast lt_of_not_ge hbsmall)
        (by simpa only [trialSourceKappaW97, kappa] using hecc.le)
        hJold hU hreference himage hD0 hD0top (fun S hS => (hUdensity S hS).2)
        Fz hparts hHunion hdisjoint _ hPcost hpaid
      intro S hS q hq
      exact (hblocks S hS q hq).2.2

/-- Corrected C6 on the actually prepared tree. The old calls data remains
literal, preserving the independent conditional Good and fine-lift proofs. -/
theorem exists_prepared_eligible_window_trial_calls_w98
    (hdim : Module.finrank Real E = 3)
    {p : Params} {beta gammaZero xiMin : Real} {xi : Fin (p.N + 1) -> Real}
    {M : Nat} (hp : SourcePassNumericsW95 p beta gammaZero xi xiMin M)
    (gamma : Real) (hgammaZero : gammaZero <= gamma) (hgamma : gamma <= 1)
    (Ctw Ccell : NNReal) (hCtw : 1 <= Ctw) (hCcell : 1 <= Ccell)
    (hKT : KatzTaoEstimate.{uI} E beta) (hKF : FrostmanEstimate.{uI} E gamma) :
    ∃ (Rnorm Cext Cnorm CtwNorm CcellNorm : NNReal)
      (full : LabelledDetailedTrialThresholdsW94.{uE, uI} (E := E) p xi gamma CtwNorm CcellNorm M)
      (aux : AuxiliaryHalfEtaThresholdsW97.{uE, uI} (E := E) p xi gamma CtwNorm CcellNorm M)
      (eFull : Real) (delta0 : NNReal) (Kmax : Nat),
      1 <= Rnorm ∧ 1 <= Cext ∧ 1 <= Cnorm ∧ 1 <= CtwNorm ∧ 1 <= CcellNorm ∧
      Ctw <= CtwNorm ∧ Ccell <= CcellNorm ∧
      0 < eFull ∧ 0 < delta0 ∧ delta0 < 1 ∧ 1 <= Kmax ∧
      (∀ m : Fin (p.N + 1), m.val < p.N ->
        eFull < p.ε * min (full.inner m) (aux.inner m) / 10 ∧
        full.Ktr m <= Kmax ∧ aux.Ktr m <= Kmax ∧
        windowDetailedTrialAtThresholdW98.{uE, uI} (E := E) gamma p.ε (xi m)
          (p.η (m.val + 1) / 2) CtwNorm CcellNorm M (aux.inner m) (aux.cutoff m) (aux.Ktr m)) ∧
      ∀ {delta : NNReal}, 0 < delta -> delta < delta0 ->
      ∀ {iota : Type uI} [DecidableEq iota]
        {A : Finset iota} {Y : iota -> ShadedTube delta E} {Ccan BF loss : NNReal}
        (U : CanonicalProfileNetW87 A (fun i => (Y i).toTube) M Ccan)
        (Uext : CanonicalProfileNetW87 A (fun i => (Y i).toTube) (M * M) Ccan),
        A.Nonempty -> (∀ i ∈ A, (Y i).carrier ⊆ Metric.closedBall 0 1) ->
        VisibleExtendedRestrictionW97 U Uext ->
        SourceRegularizedWorkingTowerW95 U Ctw Ccell ->
        SourceRegularizedWorkingTowerW95 Uext Ctw Ccell ->
        ActualTreeParameterMarginW98 Uext.cover normalizationParameterMarginW98 ->
      ∀ (block : ActualSourceDividingBlockW95 U p BF)
        (selections : ActualSameMassSelectionsW95 block loss),
        (delta : ENNReal) ^ eFull <= fullness' (U.cover.indexSet block.b.val)
          (fun Q => (actualSecondAmbientW97 selections Q).toShadedBody) ->
        ∃ calls : ActualEligibleTrialCallsW97 Uext block selections xi gamma
          Rnorm Cext Cnorm CtwNorm CcellNorm aux,
          ∀ R (hR : R ∈ actualEligibleThetaParentsW97 selections Cext (aux.inner block.label)),
            detailedInnerGoodW94 (actualDescendantsW95 A U.cover.assign block.a.val block.b.val R)
              (calls.normalization R hR).normalized gamma p.ε (xi block.label) ∨
            Nonempty (WindowDetailedTrialDropW98 (calls.normalization R hR).cells p.ε
              (p.η (block.label.val + 1) / 2) (aux.Ktr block.label)) := by
  obtain ⟨Rnorm, Cext, Cnorm, CtwNorm, CcellNorm, hRnorm, hCext, hCnorm, hCtwNorm,
    hCcellNorm, htw, hcell, hnormalize⟩ :=
    exists_prepared_centred_unit_normalization_w98 hdim M hp.M_pos Ctw Ccell hCtw hCcell
  have hSchedules :
      ∃ (full : LabelledDetailedTrialThresholdsW94.{uE, uI} (E := E) p xi gamma CtwNorm CcellNorm M)
        (aux : AuxiliaryHalfEtaThresholdsW97.{uE, uI} (E := E) p xi gamma CtwNorm CcellNorm M)
        (eFull : Real) (delta0 : NNReal) (Kmax : Nat),
        0 < eFull ∧ 0 < delta0 ∧ delta0 < 1 ∧ 1 <= Kmax ∧
        (∀ m : Fin (p.N + 1), m.val < p.N ->
          eFull < p.ε * min (full.inner m) (aux.inner m) / 10 ∧
          delta0 ^ p.ε <= min (full.cutoff m) (aux.cutoff m) ∧
          full.Ktr m <= Kmax ∧ aux.Ktr m <= Kmax ∧
          windowDetailedTrialAtThresholdW98.{uE, uI} (E := E) gamma p.ε (xi m)
            (p.η (m.val + 1) / 2) CtwNorm CcellNorm M
              (aux.inner m) (aux.cutoff m) (aux.Ktr m)) := by
    have hbetagamma : beta < gamma := hp.gammaZero_gt.trans_le hgammaZero
    have hgap : 3 * p.ε / 2 <= (gamma - beta) / 1000 := by
      linarith only [hp.gap, hgammaZero]
    have heps32 : 32 * p.ε <= 1 := by
      linarith only [hp.gap, hp.gammaZero_le, hp.beta_pos]
    have heps1 : p.ε <= 1 := hp.epsilon_small.le.trans (by norm_num)
    have hMpos : (0 : Real) < M := by exact_mod_cast hp.M_pos
    have hdenom : 0 < p.ε ^ 2 * beta := mul_pos (sq_pos_of_pos hp.epsilon_pos) hp.beta_pos
    have hnext : ∀ m : Fin (p.N + 1), m.val < p.N ->
        4000 * xi m / (p.ε ^ 2 * beta) <= p.η (m.val + 1) / 2 := by
      intro m hm
      apply (div_le_iff₀ hdenom).mpr
      nlinarith only [hp.xi_next m hm]
    have hMmin : ∀ m : Fin (p.N + 1), m.val < p.N ->
        (1 : Real) / M <= min (xi m) p.ε / 100 := by
      intro m hm
      have hxiMin1 : xiMin <= 1 := by
        obtain ⟨k, hk, hkMin⟩ := hp.xiMin_attained
        have hbeta1 : beta <= 1 := hp.gammaZero_gt.le.trans hp.gammaZero_le
        have heps3 : p.ε ^ 3 <= 1 := pow_le_one₀ hp.epsilon_pos.le heps1
        have hprod : p.ε ^ 3 * beta <= 1 := mul_le_one₀ heps3 hp.beta_pos.le hbeta1
        rw [← hkMin]
        nlinarith only [hp.xi_beta k hk, hprod]
      have hleft : p.ε * xiMin / 200 <= xi m / 100 := by
        have hprod : p.ε * xiMin <= xiMin := mul_le_of_le_one_left hp.xiMin_pos.le heps1
        linarith only [hprod, hp.xiMin_lower m hm, hp.xi_pos m hm]
      have hright : p.ε * xiMin / 200 <= p.ε / 100 := by
        have hprod : p.ε * xiMin <= p.ε := mul_le_of_le_one_right hp.epsilon_pos.le hxiMin1
        linarith only [hprod, hp.epsilon_pos]
      rw [← min_div_div_right (by norm_num : (0 : Real) <= 100)]
      exact le_min (hp.M_xi.trans hleft) (hp.M_xi.trans hright)
    have hMhalf : ∀ m : Fin (p.N + 1), m.val < p.N ->
        (160000 : Real) / (p.ε * (p.η (m.val + 1) / 2)) <= M := by
      intro m hm
      have hz : 0 < p.η (m.val + 1) := hp.zeta_pos _ (by omega)
      have hzero : p.η 0 <= p.ε * p.η (m.val + 1) / 100 :=
        (hp.zeta_mono 0 m.val (Nat.zero_le _) (by omega)).trans (hp.rung_next m.val hm)
      have hmul := mul_le_mul_of_nonneg_left hzero hp.epsilon_pos.le
      have hmargin := mul_le_mul_of_nonneg_right heps32 (mul_nonneg hp.epsilon_pos.le hz.le)
      have hsmall : (1 : Real) / M <= p.ε * p.η (m.val + 1) / 320000 := by
        nlinarith only [hp.M_zeta, hmul, hmargin]
      apply (div_le_iff₀ (mul_pos hp.epsilon_pos (half_pos hz))).mpr
      have hsmall' := (div_le_iff₀ hMpos).mp hsmall
      nlinarith only [hsmall']
    obtain ⟨full⟩ := exists_labelled_detailed_trial_thresholds_w94 hdim p beta gamma xi
      hp.beta_pos hbetagamma hgamma hp.epsilon_pos hp.epsilon_small hgap
      (fun m hm => ⟨hp.xi_pos m hm, hp.xi_beta m hm⟩)
      (fun m hm => (hnext m hm).trans (by linarith only [hp.zeta_pos (m.val + 1) (by omega)]))
      CtwNorm CcellNorm hCtwNorm hCcellNorm M hp.M_pos hMmin
      (fun m hm => by
        have hz : 0 < p.η (m.val + 1) := hp.zeta_pos _ (by omega)
        apply le_trans _ (hMhalf m hm)
        exact div_le_div_of_nonneg_left (by norm_num)
          (mul_pos hp.epsilon_pos (half_pos hz)) (by nlinarith only [mul_pos hp.epsilon_pos hz]))
      hKT hKF
    have hlabel : ∀ m : Fin (p.N + 1), ∃ (inner : Real) (cutoff : NNReal) (Ktr : Nat),
        0 < inner ∧ 0 < cutoff ∧ cutoff < 1 ∧ 1 <= Ktr ∧
        (m.val < p.N -> windowDetailedTrialAtThresholdW98.{uE, uI} (E := E)
          gamma p.ε (xi m) (p.η (m.val + 1) / 2) CtwNorm CcellNorm M inner cutoff Ktr) := by
      intro m
      by_cases hm : m.val < p.N
      · obtain ⟨inner, cutoff, Ktr, hinner, hcutoff, hcutoff1, hKtr, htrial⟩ :=
          exists_literal_window_trial_threshold_w98 hdim beta gamma p.ε (xi m)
            (p.η (m.val + 1) / 2) hp.beta_pos hbetagamma hgamma hp.epsilon_pos
            hp.epsilon_small hgap (hp.xi_pos m hm) (hp.xi_beta m hm) (hnext m hm)
            CtwNorm CcellNorm hCtwNorm hCcellNorm M hp.M_pos (hMmin m hm) (hMhalf m hm) hKT hKF
        exact ⟨inner, cutoff, Ktr, hinner, hcutoff, hcutoff1, hKtr, fun _ => htrial⟩
      · exact ⟨1, 1 / 2, 1, by norm_num, by norm_num, by norm_num, le_rfl,
          fun hm' => (hm hm').elim⟩
    choose inner cutoff Ktr hinner hcutoff hcutoff1 hKtr htrial using hlabel
    let aux : AuxiliaryHalfEtaThresholdsW97.{uE, uI} (E := E) p xi gamma CtwNorm CcellNorm M :=
      { inner := inner, cutoff := cutoff, Ktr := Ktr, inner_pos := hinner,
        cutoff_pos := hcutoff, cutoff_lt_one := hcutoff1, Ktr_pos := hKtr,
        actual_trial := by
          intro m hm d hd hd0 iota inst F Y rho cells input
          rcases htrial m hm hd hd0 F Y rho cells input with hg | hdrop
          · exact Or.inl hg
          · exact Or.inr (hdrop.map fun drop => drop.toDetailedTrialDropW94) }
    let e : Fin (p.N + 1) -> Real := fun m => p.ε * min (full.inner m) (aux.inner m) / 20
    obtain ⟨mE, hmE, hminE⟩ := Finset.exists_min_image Finset.univ e Finset.univ_nonempty
    let cut : Fin (p.N + 1) -> NNReal := fun m => min (full.cutoff m) (aux.cutoff m)
    obtain ⟨mD, hmD, hminD⟩ := Finset.exists_min_image Finset.univ cut Finset.univ_nonempty
    let degrees : Fin (p.N + 1) -> Nat := fun m => max (full.Ktr m) (aux.Ktr m)
    obtain ⟨mK, hmK, hmaxK⟩ := Finset.exists_max_image Finset.univ degrees Finset.univ_nonempty
    let delta0 : NNReal := min (1 / 2) (cut mD ^ p.ε⁻¹)
    have hcut : 0 < cut mD := lt_min (full.cutoff_pos mD) (aux.cutoff_pos mD)
    have he : ∀ m, 0 < e m := fun m =>
      div_pos (mul_pos hp.epsilon_pos (lt_min (full.inner_pos m) (aux.inner_pos m))) (by norm_num)
    refine ⟨full, aux, e mE, delta0, degrees mK, he mE, ?_, ?_, ?_, ?_⟩
    · exact lt_min (by norm_num) (NNReal.rpow_pos hcut)
    · exact (min_le_left _ _).trans_lt (by norm_num)
    · exact (full.Ktr_pos mK).trans (le_max_left _ _)
    · intro m hm
      refine ⟨?_, ?_, (le_max_left _ _).trans (hmaxK m (Finset.mem_univ m)),
        (le_max_right _ _).trans (hmaxK m (Finset.mem_univ m)), htrial m hm⟩
      · have hmpos := he m
        have hmle := hminE m (Finset.mem_univ m)
        dsimp only [e] at hmpos hmle ⊢
        linarith only [hmpos, hmle]
      · apply le_trans _ (hminD m (Finset.mem_univ m))
        exact (NNReal.le_rpow_inv_iff hp.epsilon_pos).mp (min_le_right _ _)

  obtain ⟨full, aux, eFull, dSchedule, Kmax, heFull, hdSchedule, hdSchedule1, hKmax,
    hSchedule⟩ := hSchedules
  obtain ⟨Cinterp, hCinterp, hinterp⟩ := extended_trial_window_cf_lower_w97 hdim
  let Cpay := Cnorm * Cinterp
  have hCpay : 1 <= Cpay := by
    dsimp [Cpay]
    nlinarith only [hCnorm, hCinterp]
  have hCnormPay : Cnorm <= Cpay := le_mul_of_one_le_right Cnorm.coe_nonneg hCinterp
  obtain ⟨dPay, hdPay, hdPay1, hPay⟩ := exists_quotient_half_eta_payment_w97 hp Cpay hCpay
  have heventually : ∀ᶠ delta : NNReal in nhdsWithin 0 (Set.Ioi 0),
      (2 * (Cext : ENNReal)) <= (delta : ENNReal) ^ (-eFull) :=
    eventually_finite_const_le_rpow_neg (by finiteness) heFull
  obtain ⟨dMass, hdMass, hMass⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp heventually
  let dGrid : NNReal := (16 : NNReal) ^ (-((M * M : Nat) : Real))
  have hdGrid : 0 < dGrid := NNReal.rpow_pos (by norm_num)
  let delta0 := min (min dSchedule dPay) (min dMass dGrid)
  have hd0pos : 0 < delta0 := lt_min (lt_min hdSchedule hdPay) (lt_min hdMass hdGrid)
  have hd0schedule : delta0 <= dSchedule := (min_le_left _ _).trans (min_le_left _ _)
  refine ⟨Rnorm, Cext, Cnorm, CtwNorm, CcellNorm, full, aux, eFull, delta0, Kmax,
    hRnorm, hCext, hCnorm, hCtwNorm, hCcellNorm, htw, hcell, heFull, hd0pos,
    hd0schedule.trans_lt hdSchedule1, hKmax, ?_, ?_⟩
  · intro m hm
    obtain ⟨he, hcut, hK, hKaux, htrial⟩ := hSchedule m hm
    exact ⟨he, hK, hKaux, htrial⟩
  · intro delta hd hd0 iota inst A Y Ccan BF loss U Uext hA hball restriction reg regext
      margin block selections hfull
    have hdSchedule' : delta < dSchedule := hd0.trans_le hd0schedule
    have hd1 : delta < 1 := hdSchedule'.trans hdSchedule1
    have hdPay' : delta < dPay := hd0.trans_le ((min_le_left _ _).trans (min_le_right _ _))
    have hdMass' : delta < dMass := hd0.trans_le ((min_le_right _ _).trans (min_le_left _ _))
    have hdGrid' : delta <= dGrid := hd0.le.trans ((min_le_right _ _).trans (min_le_right _ _))
    have hMM : 1 <= M * M := Nat.mul_pos hp.M_pos hp.M_pos
    have hgrid : 16 * Tube.gridScale delta (M * M) 1 <= 1 := by
      simpa only [Tube.gridScale_zero] using
        Tube.sixteen_mul_gridScale_le hd hd1.le hdGrid' (by omega : 0 < 1) hMM
    have hgrid4 : 4 * Tube.gridScale delta (M * M) 1 <= 1 := by
      nlinarith only [hgrid, (Tube.gridScale delta (M * M) 1).coe_nonneg]
    let a := block.a.val
    let b := block.b.val
    let d := Tube.gridScale delta M b / Tube.gridScale delta M a
    let F := actualDescendantsW95 A U.cover.assign a b
    let Z := actualSecondAmbientW97 selections
    let eligible := actualEligibleThetaParentsW97 selections Cext (aux.inner block.label)
    have ha : a <= M := Nat.le_of_lt_succ block.a.isLt
    have hb : b <= M := Nat.le_of_lt_succ block.b.isLt
    have hdpos : 0 < d := div_pos (Tube.gridScale_pos hd M b) (Tube.gridScale_pos hd M a)
    have hdd : delta <= d := by
      calc
        delta <= Tube.gridScale delta M b := by
          simpa only [Tube.gridScale_self delta hp.M_pos] using
            Tube.gridScale_antitone hd hd1.le M hb
        _ <= d := le_div_self (by positivity) (Tube.gridScale_pos hd M a)
          (Tube.gridScale_le_one hd1.le M a)
    have hdCut : d < aux.cutoff block.label := by
      apply block.block_long.trans_lt
      exact (NNReal.rpow_lt_rpow hdSchedule' hp.epsilon_pos).trans_le
        ((hSchedule block.label block.label_active).2.1.trans (min_le_right _ _))
    have hpaidMass : (Cext : ENNReal) * (d : ENNReal) ^ (aux.inner block.label) <=
        (1 / 2 : ENNReal) * (delta : ENNReal) ^ eFull := by
      have hbudget : 2 * eFull <= p.ε * aux.inner block.label := by
        have h := (hSchedule block.label block.label_active).1
        have hmin := min_le_right (full.inner block.label) (aux.inner block.label)
        have hmul := mul_le_mul_of_nonneg_left hmin hp.epsilon_pos.le
        linarith
      have hpay := hMass ⟨hd, hdMass'⟩
      have hdelta : (delta : ENNReal) ≠ 0 := ENNReal.coe_ne_zero.mpr hd.ne'
      have hdeltaTop : (delta : ENNReal) ≠ ⊤ := ENNReal.coe_ne_top
      have hdouble : 2 * ((Cext : ENNReal) * (d : ENNReal) ^ (aux.inner block.label)) <=
          (delta : ENNReal) ^ eFull := by
        calc
          _ <= (delta : ENNReal) ^ (-eFull) * (d : ENNReal) ^ (aux.inner block.label) := by
            rw [← mul_assoc]
            exact mul_le_mul_right' hpay _
          _ <= (delta : ENNReal) ^ (-eFull) *
              ((delta ^ p.ε : NNReal) : ENNReal) ^ (aux.inner block.label) := by
            gcongr
            · exact (aux.inner_pos _).le
            · exact_mod_cast block.block_long
          _ = (delta : ENNReal) ^ (p.ε * aux.inner block.label - eFull) := by
            rw [ENNReal.coe_rpow_of_ne_zero hd.ne', ← ENNReal.rpow_mul,
              ← ENNReal.rpow_add _ _ hdelta hdeltaTop]
            congr 1
            ring
          _ <= (delta : ENNReal) ^ eFull :=
            ENNReal.rpow_le_rpow_of_exponent_ge (by exact_mod_cast hd1.le) (by linarith)
      calc
        _ = (1 / 2 : ENNReal) * (2 * ((Cext : ENNReal) *
              (d : ENNReal) ^ (aux.inner block.label))) := by
          rw [← mul_assoc, one_div, ENNReal.inv_mul_cancel (by norm_num) (by norm_num), one_mul]
        _ <= _ := mul_le_mul_left' hdouble _
    have hsecondTube : ∀ Q ∈ selections.secondFamily,
        (selections.secondShading Q).toTube = U.cover.tube b Q := by
      intro Q hQ
      exact (selections.second.child_shade Q hQ).1.trans
        (zeroExtend_toTube selections.middle_tube Q)
    have hZtube : ∀ Q, (Z Q).toTube = U.cover.tube b Q :=
      zeroExtend_toTube hsecondTube
    have hF : ∀ R, F R =
        (U.cover.indexSet b).filter (fun Q => selections.coarseAssign Q = R) := by
      intro R
      ext Q
      constructor
      · intro hQ
        obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hQ
        obtain ⟨hiA, hiR⟩ := Finset.mem_filter.mp hi
        exact Finset.mem_filter.mpr ⟨U.cover.assign_mem b hb i hiA,
          (selections.parent_compatibility i hiA).trans hiR⟩
      · intro hQ
        obtain ⟨hQb, hQR⟩ := Finset.mem_filter.mp hQ
        rw [← reg.surjective b hb] at hQb
        obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hQb
        exact Finset.mem_image.mpr ⟨i, Finset.mem_filter.mpr
          ⟨hi, (selections.parent_compatibility i hi).symm.trans hQR⟩, rfl⟩
    have hparentMap : ∀ Q ∈ U.cover.indexSet b,
        selections.coarseAssign Q ∈ U.cover.indexSet a := by
      intro Q hQ
      rw [← reg.surjective b hb] at hQ
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hQ
      rw [selections.parent_compatibility i hi]
      exact U.cover.assign_mem a ha i hi
    have hpartition (w : iota -> ENNReal) :
        (∑ R ∈ U.cover.indexSet a, ∑ Q ∈ F R, w Q) =
          ∑ Q ∈ U.cover.indexSet b, w Q := by
      simp_rw [hF]
      exact Finset.sum_fiberwise_of_maps_to hparentMap w
    let weight := fun R => ∑ Q ∈ F R, volume (Z Q).shade
    let total := ∑ Q ∈ U.cover.indexSet b, volume (Z Q).shade
    let den := ∑ Q ∈ U.cover.indexSet b, volume (U.cover.tube b Q).carrier
    have hdenEq : (∑ Q ∈ U.cover.indexSet b, volume (Z Q).carrier) = den := by
      apply Finset.sum_congr rfl
      intro Q hQ
      exact congrArg (fun T => volume T.carrier) (hZtube Q)
    have hbNonempty : (U.cover.indexSet b).Nonempty := by
      obtain ⟨i, hi⟩ := hA
      exact ⟨U.cover.assign b i, U.cover.assign_mem b hb i hi⟩
    have hdenPos : 0 < den := by
      obtain ⟨Q, hQ⟩ := hbNonempty
      exact (Tube.volume_pos_and_lt_top (Tube.gridScale_pos hd M b)
        (Tube.gridScale_le_one hd1.le M b) (U.cover.tube b Q)).1.trans_le
        (Finset.single_le_sum (f := fun Q => volume (U.cover.tube b Q).carrier)
          (fun _ _ => bot_le) hQ)
    have hdenFinite : den < ⊤ := by
      apply ENNReal.sum_lt_top.mpr
      intro Q hQ
      exact (U.cover.tube b Q).toConvexSpaceBody.isCompact.measure_lt_top
    have htotalFinite : total < ⊤ := by
      apply ENNReal.sum_lt_top.mpr
      intro Q hQ
      exact (measure_mono (Z Q).shade_subset).trans_lt (Z Q).toTube.isCompact.measure_lt_top
    have hfunded : (delta : ENNReal) ^ eFull * den <= total := by
      change (delta : ENNReal) ^ eFull <= fullness' (U.cover.indexSet b)
        (fun Q => (Z Q).toShadedBody) at hfull
      rw [fullness', hdenEq] at hfull
      exact (ENNReal.le_div_iff_mul_le (Or.inl hdenPos.ne') (Or.inl hdenFinite.ne)).mp hfull
    have htotalPos : 0 < total := by
      apply lt_of_lt_of_le _ hfunded
      exact ENNReal.mul_pos
        (ENNReal.rpow_pos (by exact_mod_cast hd) ENNReal.coe_ne_top).ne' hdenPos.ne'
    have heligibleSubset : eligible ⊆ U.cover.indexSet a := Finset.filter_subset _ _
    have hbad : (∑ R ∈ U.cover.indexSet a \ eligible, weight R) <=
        (1 / 2 : ENNReal) * total := by
      calc
        _ <= ∑ R ∈ U.cover.indexSet a \ eligible,
            (Cext : ENNReal) * (d : ENNReal) ^ (aux.inner block.label) *
              (∑ Q ∈ F R, volume (U.cover.tube b Q).carrier) := by
          apply Finset.sum_le_sum
          intro R hR
          obtain ⟨hRa, hRe⟩ := Finset.mem_sdiff.mp hR
          apply le_of_lt
          exact lt_of_not_ge (fun h => hRe (Finset.mem_filter.mpr ⟨hRa, h⟩))
        _ <= ∑ R ∈ U.cover.indexSet a,
            (Cext : ENNReal) * (d : ENNReal) ^ (aux.inner block.label) *
              (∑ Q ∈ F R, volume (U.cover.tube b Q).carrier) :=
          Finset.sum_le_sum_of_subset_of_nonneg Finset.sdiff_subset (fun _ _ _ => bot_le)
        _ = (Cext : ENNReal) * (d : ENNReal) ^ (aux.inner block.label) * den := by
          rw [← Finset.mul_sum, hpartition]
        _ <= ((1 / 2 : ENNReal) * (delta : ENNReal) ^ eFull) * den :=
          mul_le_mul_right' hpaidMass _
        _ <= (1 / 2 : ENNReal) * total := by
          rw [mul_assoc]
          exact mul_le_mul_left' hfunded _
    have hretention : (1 / 2 : ENNReal) * total <= ∑ R ∈ eligible, weight R := by
      apply ENNReal.le_of_add_le_add_right (by finiteness :
        (1 / 2 : ENNReal) * total ≠ ⊤)
      calc
        (1 / 2 : ENNReal) * total + (1 / 2 : ENNReal) * total = total := by
          rw [← add_mul, one_div, ENNReal.inv_two_add_inv_two, one_mul]
        _ = (∑ R ∈ eligible, weight R) +
            ∑ R ∈ U.cover.indexSet a \ eligible, weight R := by
          rw [add_comm, Finset.sum_sdiff heligibleSubset]
          exact (hpartition _).symm
        _ <= _ := add_le_add_right hbad _
    have heligible : eligible.Nonempty := by
      by_contra hn
      have hz : ∑ R ∈ eligible, weight R = 0 := by
        rw [Finset.not_nonempty_iff_eq_empty.mp hn, Finset.sum_empty]
      rw [hz] at hretention
      exact (not_le_of_gt (ENNReal.mul_pos (by norm_num) htotalPos.ne')) hretention
    have hnorm : ∀ R ∈ eligible,
        ∃ normalization : ActualAssignedUnitNormalizationW97 U Uext a b R Z
          Rnorm Cext Cnorm CtwNorm CcellNorm, True := by
      intro R hR
      obtain ⟨normalization, hdir, hcentre⟩ :=
        hnormalize hd hd1 hgrid U Uext hA restriction reg regext margin a b
          block.a_lt_b hb R (heligibleSubset hR) Z (fun Q hQ => hZtube Q)
      exact ⟨normalization, trivial⟩
    choose normalization hnormalization using hnorm
    have hinput : ∀ R (hR : R ∈ eligible),
        DetailedTrialInputW94 (normalization R hR).cells p.ε (xi block.label)
          (p.η (block.label.val + 1) / 2) (aux.inner block.label) := by
      intro R hR
      let n := normalization R hR
      have hFnonempty : (F R).Nonempty := by
        have hRa := heligibleSubset hR
        rw [← reg.surjective a ha] at hRa
        obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hRa
        exact ⟨U.cover.assign b i, Finset.mem_image.mpr
          ⟨i, Finset.mem_filter.mpr ⟨hi, rfl⟩, rfl⟩⟩
      refine {
        nonempty := hFnonempty
        ball := n.ball
        centred := n.centred
        line_ed := n.line_ed
        fullness := ?_
        frostman := ?_
        complete_cell_lower := ?_ }
      · have heligibleAt := (Finset.mem_filter.mp hR).2
        have hdenF : 0 < ∑ Q ∈ F R, volume (Z Q).carrier := by
          obtain ⟨Q, hQ⟩ := hFnonempty
          have hvol : 0 < volume (Z Q).carrier := by
            change 0 < volume (Z Q).toTube.carrier
            rw [hZtube]
            exact (Tube.volume_pos_and_lt_top (Tube.gridScale_pos hd M b)
              (Tube.gridScale_le_one hd1.le M b) _).1
          exact hvol.trans_le (Finset.single_le_sum (f := fun Q => volume (Z Q).carrier)
            (fun _ _ => bot_le) hQ)
        have hdenFfin : (∑ Q ∈ F R, volume (Z Q).carrier) < ⊤ := by
          apply ENNReal.sum_lt_top.mpr
          intro Q hQ
          exact (Z Q).toConvexSpaceBody.isCompact.measure_lt_top
        have hFfull : (Cext : ENNReal) * (d : ENNReal) ^ (aux.inner block.label) <=
            fullness' (F R) (fun Q => (Z Q).toShadedBody) := by
          rw [fullness', ENNReal.le_div_iff_mul_le
            (Or.inl hdenF.ne') (Or.inl hdenFfin.ne)]
          convert heligibleAt using 1
          congr 2
          funext Q
          exact congrArg (fun T => volume T.carrier) (hZtube Q)
        calc
          (d : ENNReal) ^ (aux.inner block.label) =
              (Cext : ENNReal)⁻¹ * ((Cext : ENNReal) *
                (d : ENNReal) ^ (aux.inner block.label)) := by
            rw [← mul_assoc, ENNReal.inv_mul_cancel
              (by exact_mod_cast (zero_lt_one.trans_le hCext).ne') ENNReal.coe_ne_top, one_mul]
          _ <= (Cext : ENNReal)⁻¹ * fullness' (F R) (fun Q => (Z Q).toShadedBody) :=
            mul_le_mul_left' hFfull _
          _ <= _ := n.fullness
      · have hdsmall : d <= 1 :=
          block.block_long.trans (NNReal.rpow_le_one hd1.le hp.epsilon_pos.le)
        have hlow : (d : ENNReal) ^ (1 - 3 * p.ε / 2) <=
            ((d ^ (1 / 2 : Real) : NNReal) : ENNReal) := by
          rw [ENNReal.coe_rpow_of_ne_zero hdpos.ne']
          exact ENNReal.rpow_le_rpow_of_exponent_ge (by exact_mod_cast hdsmall)
            (by linarith only [hp.epsilon_small])
        have hupp : ((d ^ (1 / 2 : Real) : NNReal) : ENNReal) <=
            (d : ENNReal) ^ (3 * p.ε / 2) := by
          rw [ENNReal.coe_rpow_of_ne_zero hdpos.ne']
          exact ENNReal.rpow_le_rpow_of_exponent_ge (by exact_mod_cast hdsmall)
            (by linarith only [hp.epsilon_small])
        have hpay := (hPay hd hdPay' hdd block.block_long hlow hupp
          block.label block.label_active).2
        calc
          _ <= (Cnorm : ENNReal) * actualRelativeFrostmanW95 A U.cover.assign U.cover.tube a b R :=
            n.whole_cf.2
          _ <= (Cnorm : ENNReal) * (d : ENNReal) ^ (-p.η block.label.val) := by
            apply mul_le_mul_left'
            convert block.middle_upper R (heligibleSubset hR) using 1
            rw [ENNReal.coe_div (Tube.gridScale_pos hd M a).ne', ENNReal.rpow_neg,
              ← ENNReal.inv_rpow, ENNReal.inv_div]
            · exact Or.inl ENNReal.coe_ne_top
            · exact Or.inl (ENNReal.coe_ne_zero.mpr (Tube.gridScale_pos hd M a).ne')
          _ <= (Cpay : ENNReal) * (d : ENNReal) ^ (-p.η block.label.val) :=
            mul_le_mul_right' (by exact_mod_cast hCnormPay) _
          _ <= _ := hpay
      · intro l hl hlow hupp S hS
        have hparentS : S ∈ Uext.cover.indexSet (quotientGridIndexW97 M a b l) := by
          rw [n.parents_eq l hl] at hS
          obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hS
          exact Uext.cover.assign_mem _ ((quotient_grid_index_w97 M a b hp.M_pos
            block.a_lt_b hb delta hd hd1).2.2.1 l hl).2.2 i (Finset.mem_filter.mp hi).1
        have hlower := hinterp hp hd hd1 hgrid4 U Uext hA hball restriction reg regext block
          l hl hlow hupp S hparentS
        have hpay := (hPay hd hdPay' hdd block.block_long hlow hupp
          block.label block.label_active).1
        calc
          _ < (Cpay : ENNReal)⁻¹ * (delta : ENNReal) ^ ((2 : Real) / M) *
              ((Tube.gridScale d M l : ENNReal) / (d : ENNReal)) ^
                p.η (block.label.val + 1) := hpay
          _ = (Cnorm : ENNReal)⁻¹ * ((Cinterp : ENNReal)⁻¹ *
              (delta : ENNReal) ^ ((2 : Real) / M) *
                ((Tube.gridScale d M l : ENNReal) / (d : ENNReal)) ^
                  p.η (block.label.val + 1)) := by
            rw [show (Cpay : ENNReal) = (Cnorm : ENNReal) * Cinterp from ENNReal.coe_mul _ _,
              ENNReal.mul_inv (Or.inl (by exact_mod_cast (zero_lt_one.trans_le hCnorm).ne'))
                (Or.inl ENNReal.coe_ne_top)]
            ac_rfl
          _ <= (Cnorm : ENNReal)⁻¹ * actualRelativeFrostmanW95 A Uext.cover.assign Uext.cover.tube
              (quotientGridIndexW97 M a b l) (b * M) S := mul_le_mul_left' hlower _
          _ <= _ := (n.assigned_cf l hl S hS).1
    have houtcome : ∀ R (hR : R ∈ eligible),
        detailedInnerGoodW94 (F R) (normalization R hR).normalized gamma p.ε (xi block.label) ∨
        Nonempty (WindowDetailedTrialDropW98 (normalization R hR).cells p.ε
          (p.η (block.label.val + 1) / 2) (aux.Ktr block.label)) := by
      intro R hR
      exact (hSchedule block.label block.label_active).2.2.2.2 hdpos hdCut (F R)
        (normalization R hR).normalized (Tube.gridScale d M) (normalization R hR).cells (hinput R hR)
    let calls : ActualEligibleTrialCallsW97 Uext block selections xi gamma
        Rnorm Cext Cnorm CtwNorm CcellNorm aux :=
      { eligible_nonempty := heligible, mass_retention := hretention,
        normalization := normalization, input := hinput, outcome := by
          intro R hR
          rcases houtcome R hR with hg | hdrop
          · exact Or.inl hg
          · exact Or.inr (hdrop.map fun drop => drop.toDetailedTrialDropW94) }
    exact ⟨calls, houtcome⟩

end

end Kakeya.ml1Boot.TrialRestartW94
