import MyLeanRepo.Kakeya.Cinematic.Section5.CenteredTaylorFiniteGraphTransportInputs
import MyLeanRepo.Kakeya.Cinematic.Section5.TaylorJetBounds
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

/-!
# Fixed geometry for centered Taylor globalization

This module fixes the controlled interval used after horizontally centering a
tiny physical interval. It also records the centered-sixteenth containment and
volume preservation needed to transfer a measurable level-set piece.
-/

noncomputable section

open MeasureTheory Set

namespace Kakeya.Cinematic

/-- The fixed controlled interval used after moving a tiny physical interval to `1/2`. -/
def centeredTaylorControlInterval (K : ℝ) (hK : 1 ≤ K) : ParameterInterval where
  left := 1 / 2 - 1 / (144 * K)
  right := 1 / 2 + 1 / (144 * K)
  left_mem := by
    have hdenom : (2 : ℝ) ≤ 144 * K := by linarith
    have hinv : 1 / (144 * K) ≤ 1 / 2 :=
      one_div_le_one_div_of_le (by norm_num) hdenom
    have hinv_nonneg : 0 ≤ 1 / (144 * K) := by positivity
    exact ⟨by linarith, by linarith⟩
  right_mem := by
    have hdenom : (2 : ℝ) ≤ 144 * K := by linarith
    have hinv : 1 / (144 * K) ≤ 1 / 2 :=
      one_div_le_one_div_of_le (by norm_num) hdenom
    have hinv_nonneg : 0 ≤ 1 / (144 * K) := by positivity
    exact ⟨by linarith, by linarith⟩
  left_le_right := by
    have hK_pos : 0 < K := by linarith
    have hinv : 0 ≤ 1 / (144 * K) := by positivity
    linarith

@[simp]
theorem centeredTaylorControlInterval_length (K : ℝ) (hK : 1 ≤ K) :
    (centeredTaylorControlInterval K hK).length = 1 / (72 * K) := by
  have hK_pos : 0 < K := by linarith
  unfold centeredTaylorControlInterval ParameterInterval.length
  dsimp
  field_simp [hK_pos.ne']
  ring

@[simp]
theorem centeredTaylorControlInterval_midpoint (K : ℝ) (hK : 1 ≤ K) :
    (centeredTaylorControlInterval K hK).midpoint = 1 / 2 := by
  unfold centeredTaylorControlInterval ParameterInterval.midpoint
  dsimp
  ring

theorem centeredTaylorControlInterval_isControlled (K : ℝ) (hK : 1 ≤ K) :
    (centeredTaylorControlInterval K hK).IsControlled (12 * K) := by
  have hK_pos : 0 < K := by linarith
  constructor
  · rw [centeredTaylorControlInterval_length]
    have hdenom : 72 * K ≤ 12 * (12 * K) := by nlinarith
    simpa [one_div] using
      (one_div_le_one_div_of_le (show 0 < 72 * K by positivity) hdenom)
  · rw [ParameterInterval.IsShort, centeredTaylorControlInterval_length]
    norm_num [one_div]
    ring_nf
    exact le_rfl

theorem centeredHorizontalPoint_mem_controlInterval
    {K : ℝ} (hK : 1 ≤ K) {I : ParameterInterval}
    (hI : I.IsShort (12 * K)) {p : ℝ × ℝ}
    (hp : p.1 ∈ I.realCenteredCarrier (1 / 16)) :
    (centeredHorizontalPoint I p).1 ∈
      (centeredTaylorControlInterval K hK).realCenteredCarrier (1 / 16) := by
  have hK_pos : 0 < K := by linarith
  have hp_bound : |p.1 - I.midpoint| ≤ I.length / 32 := by
    convert hp.2 using 1
    ring
  have hI_bound : I.length ≤ 1 / (72 * K) := by
    calc
      I.length ≤ (6 * (12 * K))⁻¹ := hI
      _ = 1 / (72 * K) := by
        field_simp [hK_pos.ne']
        ring
  have h72 : 1 / (72 * K) ≤ 1 / 72 :=
    one_div_le_one_div_of_le (by norm_num) (by nlinarith)
  have hI_small : I.length ≤ 1 / 72 := hI_bound.trans h72
  have hp_half : |p.1 - I.midpoint| ≤ 1 / 2 :=
    hp_bound.trans (by linarith [I.length_nonneg])
  have hshift :
      (centeredHorizontalPoint I p).1 - 1 / 2 = p.1 - I.midpoint := by
    simp [centeredHorizontalPoint, centeredHorizontalShift]
    ring
  have htarget_bound :
      |(centeredHorizontalPoint I p).1 - 1 / 2| ≤ 1 / (72 * K) / 32 := by
    rw [hshift]
    exact hp_bound.trans (by gcongr)
  have hcoord :
      (centeredHorizontalPoint I p).1 = 1 / 2 + (p.1 - I.midpoint) := by
    simp [centeredHorizontalPoint, centeredHorizontalShift]
    ring
  have hp_abs := abs_le.mp hp_half
  have hleft : 0 ≤ (centeredHorizontalPoint I p).1 := by
    rw [hcoord]
    linarith
  have hright : (centeredHorizontalPoint I p).1 ≤ 1 := by
    rw [hcoord]
    linarith
  refine ⟨⟨hleft, hright⟩, ?_⟩
  rw [centeredTaylorControlInterval_midpoint,
    centeredTaylorControlInterval_length]
  convert htarget_bound using 1
  ring

theorem centeredHorizontalPoint_mem_controlStrip
    {K : ℝ} (hK : 1 ≤ K) {I : ParameterInterval}
    (hI : I.IsShort (12 * K)) {c : ℝ} {p : ℝ × ℝ}
    (hp : p ∈
      I.realCenteredCarrier (1 / 16) ×ˢ Set.Icc c (c + 1)) :
    centeredHorizontalPoint I p ∈
      (centeredTaylorControlInterval K hK).realCenteredCarrier (1 / 16) ×ˢ
        Set.Icc c (c + 1) := by
  exact ⟨centeredHorizontalPoint_mem_controlInterval hK hI hp.1,
    by simpa [centeredHorizontalPoint] using hp.2⟩

theorem centeredHorizontalPoint_image_subset_controlStrip
    {K : ℝ} (hK : 1 ≤ K) {I : ParameterInterval}
    (hI : I.IsShort (12 * K)) {c : ℝ} {E : Set (ℝ × ℝ)}
    (hE : E ⊆
      I.realCenteredCarrier (1 / 16) ×ˢ Set.Icc c (c + 1)) :
    centeredHorizontalPoint I '' E ⊆
      (centeredTaylorControlInterval K hK).realCenteredCarrier (1 / 16) ×ˢ
        Set.Icc c (c + 1) := by
  rintro _ ⟨p, hp, rfl⟩
  exact centeredHorizontalPoint_mem_controlStrip hK hI (hE hp)

/-- Horizontal translation of the plane used by centered Taylor transport. -/
def centeredHorizontalEquiv (I : ParameterInterval) :
    ℝ × ℝ ≃ᵐ ℝ × ℝ where
  toFun := centeredHorizontalPoint I
  invFun := fun p => (p.1 - centeredHorizontalShift I, p.2)
  left_inv := by
    intro p
    ext <;> simp [centeredHorizontalPoint]
  right_inv := by
    intro p
    ext <;> simp [centeredHorizontalPoint]
  measurable_toFun :=
    Measurable.prodMk (measurable_fst.add measurable_const) measurable_snd
  measurable_invFun :=
    Measurable.prodMk (measurable_fst.sub measurable_const) measurable_snd

theorem centeredHorizontalEquiv_measurePreserving (I : ParameterInterval) :
    MeasurePreserving (centeredHorizontalEquiv I)
      MeasureTheory.volume MeasureTheory.volume := by
  have h_add : MeasurePreserving
      (fun x : ℝ => x + centeredHorizontalShift I) volume volume :=
    MeasureTheory.measurePreserving_add_right volume _
  have h_id : MeasurePreserving (id : ℝ → ℝ) volume volume :=
    MeasurePreserving.id volume
  change MeasurePreserving
    (Prod.map (fun x : ℝ => x + centeredHorizontalShift I) (id : ℝ → ℝ))
      (volume.prod volume) (volume.prod volume)
  exact h_add.prod h_id

theorem measurableSet_centeredHorizontalPoint_image
    (I : ParameterInterval) {E : Set (ℝ × ℝ)} (hE : MeasurableSet E) :
    MeasurableSet (centeredHorizontalPoint I '' E) := by
  exact ((centeredHorizontalEquiv I).measurableSet_image).2 hE

theorem volume_centeredHorizontalPoint_image
    (I : ParameterInterval) {E : Set (ℝ × ℝ)} (hE : MeasurableSet E) :
    volume (centeredHorizontalPoint I '' E) = volume E := by
  let e := centeredHorizontalEquiv I
  have hmp : MeasurePreserving e volume volume :=
    centeredHorizontalEquiv_measurePreserving I
  have himage : MeasurableSet (e '' E) :=
    measurableSet_centeredHorizontalPoint_image I hE
  have hpre := hmp.measure_preimage himage.nullMeasurableSet
  have hpreimage : e ⁻¹' (e '' E) = E := e.preimage_image E
  rw [hpreimage] at hpre
  simpa [e, centeredHorizontalEquiv] using hpre.symm

end Kakeya.Cinematic
