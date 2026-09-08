module

public import Kakeya.Shading
public import Kakeya.Frostman

@[expose] public section

open MeasureTheory ConvexSpaceBody ShadedBody
open scoped ENNReal

namespace Kakeya.ml1Boot.TrialRestartW94

noncomputable section
set_option autoImplicit false
attribute [local instance] Classical.propDecidable

universe uE uI uQ

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace Real E]
  [FiniteDimensional Real E] [MeasurableSpace E] [BorelSpace E]

/-- The complete fibre of the actual finite family at a named parent. -/
def completeFibreW94 {iota : Type uI} {Q : Type uQ} [DecidableEq Q]
    (F : Finset iota) (parent : iota -> Q) (q : Q) : Finset iota :=
  F.filter (fun i => parent i = q)

/-- The eligible parents are defined from the actual induced fibre fullness. -/
def eligibleParentsW94 {iota : Type uI} {Q : Type uQ} [DecidableEq Q]
    (F : Finset iota) (parent : iota -> Q) (Y : iota -> ShadedBody E)
    (h : ENNReal) : Finset Q :=
  (F.image parent).filter (fun q => h <= fullness' (completeFibreW94 F parent q) Y)

/-- Selection retains complete fibres, without changing any shading. -/
def eligibleSaturatedFamilyW94 {iota : Type uI} {Q : Type uQ} [DecidableEq Q]
    (F : Finset iota) (parent : iota -> Q) (Y : iota -> ShadedBody E)
    (h : ENNReal) : Finset iota :=
  F.filter (fun i => parent i ∈ eligibleParentsW94 F parent Y h)

/-- P0a: a doubled aggregate fullness reserve pays for discarding every
ineligible fibre while retaining at least half of the actual shaded mass. -/
theorem exists_eligible_saturated_family_w94
    {iota : Type uI} {Q : Type uQ} [DecidableEq Q]
    (F : Finset iota) (parent : iota -> Q) (Y : iota -> ShadedBody E)
    (h : ENNReal) (hF : F.Nonempty) (hh : 0 < h) (hh_top : h < ⊤)
    (hcarrier_pos : ∀ i ∈ F, 0 < volume (Y i).carrier)
    (hcarrier_finite : ∀ i ∈ F, volume (Y i).carrier < ⊤)
    (haggregate : 2 * h * (∑ i ∈ F, volume (Y i).carrier) <=
      ∑ i ∈ F, volume (Y i).shade) :
    let t := eligibleParentsW94 F parent Y h
    let A := eligibleSaturatedFamilyW94 F parent Y h
    t.Nonempty ∧ A.Nonempty ∧ A ⊆ F ∧ A.image parent = t ∧
      (∀ q ∈ t, completeFibreW94 A parent q = completeFibreW94 F parent q) ∧
      (∀ q ∈ t,
        0 < ∑ i ∈ completeFibreW94 F parent q, volume (Y i).carrier) ∧
      (∀ q ∈ t,
        (∑ i ∈ completeFibreW94 F parent q, volume (Y i).carrier) < ⊤) ∧
      (∀ q ∈ t, h <= fullness' (completeFibreW94 F parent q) Y) ∧
      (1 / 2 : ENNReal) * (∑ i ∈ F, volume (Y i).shade) <=
        ∑ i ∈ A, volume (Y i).shade := by
  classical
  let S := F.image parent
  let t := eligibleParentsW94 F parent Y h
  let A := eligibleSaturatedFamilyW94 F parent Y h
  let c : Q -> ENNReal := fun q => ∑ i ∈ completeFibreW94 F parent q, volume (Y i).carrier
  let w : Q -> ENNReal := fun q => ∑ i ∈ completeFibreW94 F parent q, volume (Y i).shade
  let C : ENNReal := ∑ i ∈ F, volume (Y i).carrier
  let M : ENNReal := ∑ i ∈ F, volume (Y i).shade
  have htmem : ∀ q, q ∈ t ↔ q ∈ S ∧ h <= fullness' (completeFibreW94 F parent q) Y := by
    intro q
    simp [t, S, eligibleParentsW94]
  have htS : t ⊆ S := fun q hq => ((htmem q).mp hq).1
  have hAF : A ⊆ F := Finset.filter_subset _ _
  have hcpos : ∀ q ∈ S, 0 < c q := by
    intro q hq
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hq
    apply (hcarrier_pos i hi).trans_le
    exact Finset.single_le_sum (f := fun i => volume (Y i).carrier)
      (fun _ _ => zero_le) (show i ∈ completeFibreW94 F parent (parent i) from
        Finset.mem_filter.mpr ⟨hi, rfl⟩)
  have hcfin : ∀ q, c q < ⊤ := by
    intro q
    exact ENNReal.sum_lt_top.mpr fun i hi => hcarrier_finite i (Finset.mem_filter.mp hi).1
  have hCpos : 0 < C := by
    obtain ⟨i, hi⟩ := hF
    apply (hcarrier_pos i hi).trans_le
    exact Finset.single_le_sum (f := fun i => volume (Y i).carrier) (fun _ _ => zero_le) hi
  have hMfin : M < ⊤ := by
    apply ENNReal.sum_lt_top.mpr
    intro i hi
    exact (measure_mono (Y i).shade_subset).trans_lt (hcarrier_finite i hi)
  have hCpart : ∑ q ∈ S, c q = C := by
    exact Finset.sum_fiberwise_of_maps_to (fun i hi => Finset.mem_image_of_mem parent hi) _
  have hMpart : ∑ q ∈ S, w q = M := by
    exact Finset.sum_fiberwise_of_maps_to (fun i hi => Finset.mem_image_of_mem parent hi) _
  have hApart : ∑ q ∈ t, w q = ∑ i ∈ A, volume (Y i).shade := by
    exact Finset.sum_fiberwise_eq_sum_filter _ _ _ _
  have hbad : ∑ q ∈ S \ t, w q <= h * C := by
    calc
      ∑ q ∈ S \ t, w q <= ∑ q ∈ S \ t, h * c q := by
        apply Finset.sum_le_sum
        intro q hq
        obtain ⟨hqS, hqt⟩ := Finset.mem_sdiff.mp hq
        have hqfull : fullness' (completeFibreW94 F parent q) Y <= h := by
          apply le_of_lt
          apply lt_of_not_ge
          intro hqfull
          exact hqt ((htmem q).mpr ⟨hqS, hqfull⟩)
        exact (ENNReal.div_le_iff (hcpos q hqS).ne' (hcfin q).ne).mp hqfull
      _ = h * ∑ q ∈ S \ t, c q := by rw [Finset.mul_sum]
      _ <= h * ∑ q ∈ S, c q := mul_le_mul' le_rfl
        (Finset.sum_le_sum_of_subset Finset.sdiff_subset)
      _ = h * C := by rw [hCpart]
  have htwo : (1 / 2 : ENNReal) * 2 = 1 := ENNReal.div_mul_cancel (by norm_num) (by simp)
  have hhalf : h * C <= (1 / 2 : ENNReal) * M := by
    calc
      h * C = (1 / 2 : ENNReal) * (2 * h * C) := by
        rw [← mul_assoc, ← mul_assoc, htwo, one_mul]
      _ <= (1 / 2 : ENNReal) * M := mul_le_mul' le_rfl haggregate
  have hmass : (1 / 2 : ENNReal) * M <= ∑ i ∈ A, volume (Y i).shade := by
    apply ENNReal.le_of_add_le_add_right (a := (1 / 2 : ENNReal) * M)
      (ENNReal.mul_ne_top (by simp) hMfin.ne)
    calc
      (1 / 2 : ENNReal) * M + (1 / 2 : ENNReal) * M = M := by
        rw [← two_mul, ← mul_assoc, mul_comm 2, htwo, one_mul]
      _ = (∑ q ∈ t, w q) + ∑ q ∈ S \ t, w q := by
        rw [add_comm, Finset.sum_sdiff htS, hMpart]
      _ <= (∑ i ∈ A, volume (Y i).shade) + (1 / 2 : ENNReal) * M := by
        rw [hApart]
        exact add_le_add le_rfl (hbad.trans hhalf)
  have hMpos : 0 < M :=
    (ENNReal.mul_pos_iff.mpr ⟨ENNReal.mul_pos_iff.mpr ⟨by norm_num, hh⟩, hCpos⟩).trans_le haggregate
  have hA : A.Nonempty := by
    by_contra hA
    have hz : A = ∅ := Finset.not_nonempty_iff_eq_empty.mp hA
    have hp : 0 < (1 / 2 : ENNReal) * M := ENNReal.mul_pos_iff.mpr ⟨by simp, hMpos⟩
    simpa [hz] using hp.trans_le hmass
  have himage : A.image parent = t := by
    ext q
    constructor
    · rintro hq
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hq
      exact (Finset.mem_filter.mp hi).2
    · intro hq
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp (htS hq)
      exact Finset.mem_image.mpr ⟨i, Finset.mem_filter.mpr ⟨hi, hq⟩, rfl⟩
  change t.Nonempty ∧ A.Nonempty ∧ A ⊆ F ∧ A.image parent = t ∧ _
  refine ⟨by rw [← himage]; exact hA.image parent, hA, hAF, himage, ?_, ?_, ?_, ?_, hmass⟩
  · intro q hq
    ext i
    simp only [completeFibreW94, Finset.mem_filter]
    constructor
    · rintro ⟨hi, hip⟩
      exact ⟨hAF hi, hip⟩
    · rintro ⟨hi, hip⟩
      exact ⟨Finset.mem_filter.mpr ⟨hi, hip ▸ hq⟩, hip⟩
  · exact fun q hq => hcpos q (htS hq)
  · exact fun q _ => hcfin q
  · exact fun q hq => ((htmem q).mp hq).2

/-- P0b: actual retained mass supplies the fullness and cardinality reserve
that pays for the Frostman constant of the actual current subfamily. -/
theorem retained_state_fullness_card_frostman_w94
    {iota : Type uI} (B A : Finset iota) (V Y : iota -> ShadedBody E)
    (K : ConvexSpaceBody E) (v lambda0 F0 r : ENNReal)
    (hB : B.Nonempty) (hAB : A ⊆ B)
    (hv : 0 < v) (hv_top : v < ⊤)
    (hvol : ∀ i ∈ B, volume (V i).carrier = v)
    (hcontained : ∀ i ∈ B, (V i).toConvexSpaceBody <= K)
    (hK : 0 < volume K.carrier) (hK_top : volume K.carrier < ⊤)
    (hsame : ∀ i ∈ A, (Y i).toConvexSpaceBody = (V i).toConvexSpaceBody)
    (hshade : ∀ i ∈ A, (Y i).shade ⊆ (V i).shade)
    (hlambda0 : 0 < lambda0) (hlambda0_top : lambda0 < ⊤)
    (hfull : lambda0 <= fullness' B V)
    (hF0 : frostmanConstIn B (fun i => (V i).toConvexSpaceBody) K <= F0)
    (hF0_top : F0 < ⊤) (hr : 0 < r) (hr_top : r < ⊤)
    (hmass : r * (∑ i ∈ B, volume (V i).shade) <=
      ∑ i ∈ A, volume (Y i).shade) :
    A.Nonempty ∧
      r * lambda0 <= fullness' A Y ∧
      (r * lambda0) * (B.card : ENNReal) <= (A.card : ENNReal) ∧
      frostmanConstIn A (fun i => (Y i).toConvexSpaceBody) K <=
        (r * lambda0)⁻¹ * F0 := by
  classical
  have hvolY : ∀ i ∈ A, volume (Y i).carrier = v := by
    intro i hi
    change volume (Y i).toConvexSpaceBody.carrier = v
    rw [hsame i hi]
    exact hvol i (hAB hi)
  have hsumB : ∑ i ∈ B, volume (V i).carrier = (B.card : ENNReal) * v := by
    calc
      _ = ∑ _i ∈ B, v := Finset.sum_congr rfl hvol
      _ = _ := by simp
  have hsumA : ∑ i ∈ A, volume (Y i).carrier = (A.card : ENNReal) * v := by
    calc
      _ = ∑ _i ∈ A, v := Finset.sum_congr rfl hvolY
      _ = _ := by simp
  have hBpos : 0 < (B.card : ENNReal) := by exact_mod_cast hB.card_pos
  have hBvpos : 0 < (B.card : ENNReal) * v := ENNReal.mul_pos_iff.mpr ⟨hBpos, hv⟩
  have hBvfin : (B.card : ENNReal) * v ≠ ⊤ := ENNReal.mul_ne_top (by simp) hv_top.ne
  have hbase : lambda0 * ((B.card : ENNReal) * v) <= ∑ i ∈ B, volume (V i).shade := by
    rw [fullness', hsumB] at hfull
    exact (ENNReal.le_div_iff_mul_le (Or.inl hBvpos.ne') (Or.inl hBvfin)).mp hfull
  have hretained : (r * lambda0) * ((B.card : ENNReal) * v) <=
      ∑ i ∈ A, volume (Y i).shade := by
    calc
      _ <= r * (∑ i ∈ B, volume (V i).shade) := by
        simpa [mul_assoc] using mul_le_mul' (le_refl r) hbase
      _ <= _ := hmass
  have hshadevol : (∑ i ∈ A, volume (Y i).shade) <= (A.card : ENNReal) * v := by
    rw [← hsumA]
    exact Finset.sum_le_sum fun i _ => measure_mono (Y i).shade_subset
  have hcard : (r * lambda0) * (B.card : ENNReal) <= (A.card : ENNReal) := by
    apply (ENNReal.mul_le_mul_iff_left hv.ne' hv_top.ne).mp
    simpa [mul_assoc] using hretained.trans hshadevol
  have hkpos : 0 < r * lambda0 := ENNReal.mul_pos_iff.mpr ⟨hr, hlambda0⟩
  have hApos : 0 < (A.card : ENNReal) := (ENNReal.mul_pos_iff.mpr ⟨hkpos, hBpos⟩).trans_le hcard
  have hA : A.Nonempty := Finset.card_pos.mp (by exact_mod_cast hApos)
  have hAfull : r * lambda0 <= fullness' A Y := by
    rw [fullness', hsumA]
    apply (ENNReal.le_div_iff_mul_le (Or.inl (ENNReal.mul_pos_iff.mpr ⟨hApos, hv⟩).ne')
      (Or.inl (ENNReal.mul_ne_top (by simp) hv_top.ne))).mpr
    apply le_trans _ hretained
    exact mul_le_mul' le_rfl (mul_le_mul' (by exact_mod_cast Finset.card_le_card hAB) le_rfl)
  refine ⟨hA, hAfull, hcard, ?_⟩
  have hfrost : frostmanConstIn A (fun i => (V i).toConvexSpaceBody) K <=
      (r * lambda0)⁻¹ * F0 :=
    (frostmanConstIn_subfamily_le hB hvol hcontained hAB hkpos.ne' hcard).trans
      (mul_le_mul' le_rfl hF0)
  apply frostmanConstIn_le
  have hfrost' := (frostmanConstant_le_iff.mp hfrost)
  intro K' hK'
  rw [densityIn_congr hsame, densityIn_congr hsame]
  exact hfrost' K' hK'

/-- P0c: the lower bound belongs to the old complete cell; only the upper
bound belongs to its refined subfamily. -/
theorem maxDensity_drop_of_complete_cell_frostman_gap_w94
    {iota : Type uI} (A Aplus : Finset iota) (W : iota -> ConvexSpaceBody E)
    (K : ConvexSpaceBody E) (Lambda u : ENNReal)
    (hA : A.Nonempty) (hsub : Aplus ⊆ A)
    (hcontained : ∀ i ∈ A, W i <= K)
    (hK : 0 < volume K.carrier) (hK_top : volume K.carrier < ⊤)
    (hLambda : 0 < Lambda) (hLambda_top : Lambda < ⊤) (hu_top : u < ⊤)
    (hlower : Lambda <= frostmanConstIn A W K)
    (hupper : frostmanConstIn Aplus W K <= u) :
    maxDensity Aplus W <= (u / Lambda) * maxDensity A W := by
  have hnew := (frostmanConstant_le_iff.mp hupper).maxDensity_le_of_carrier_subset
    (fun i hi => hcontained i (hsub hi))
  have hmono := densityIn_mono W K hsub
  have hbound : maxDensity Aplus W <= u * densityIn A W K :=
    hnew.trans (mul_le_mul' le_rfl hmono)
  by_cases hz : densityIn A W K = 0
  · have hzero : maxDensity Aplus W <= 0 := by simpa [hz] using hbound
    exact hzero.trans zero_le
  have hdpos : 0 < densityIn A W K := pos_iff_ne_zero.mpr hz
  rw [frostmanConstIn_eq_frostmanConstant,
    frostmanConstant_eq_maxDensity_div hdpos hcontained] at hlower
  have hmul : Lambda * densityIn A W K <= maxDensity A W :=
    (ENNReal.le_div_iff_mul_le (Or.inl hz) (Or.inl (densityIn_ne_top A W K))).mp hlower
  calc
    maxDensity Aplus W <= u * densityIn A W K := hbound
    _ = (u / Lambda) * (Lambda * densityIn A W K) := by
      rw [div_eq_mul_inv, mul_assoc u, ← mul_assoc Lambda⁻¹,
        ENNReal.inv_mul_cancel hLambda.ne' hLambda_top.ne, one_mul]
    _ <= (u / Lambda) * maxDensity A W := mul_le_mul' le_rfl hmul

end

end Kakeya.ml1Boot.TrialRestartW94
