import MyLeanRepo.Kakeya.Streamlined.RandomTranslation.TranslatedCopies
import MyLeanRepo.Kakeya.Streamlined.GeometricLemmas.TubeVolume
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic

/-!
# Scratch: Intersection volume bounds for translated copies

Two deterministic pieces:
1. Same-copy intersection bound from essential distinctness of F
2. Convolution formula: ∫ volume(T ∩ (U+d)) dd = volume(T) * volume(U)
-/

noncomputable section

open MeasureTheory Kakeya.Streamlined Kakeya.Streamlined.RandomTranslation

namespace Kakeya.Streamlined.RandomTranslation

/-! ## 1. Same-copy intersection bound -/

/--
For two tubes in the same translated copy, their intersection volume is
at most V/2 when the original tubes are essentially distinct.
-/
lemma same_copy_pair_intersection
    {δ : ℝ} {F : TubeFamily δ} {J : ℕ} {shift : Fin J → Point3}
    (hF : F.IsEssentiallyDistinct)
    (j : Fin J) {i k : Fin F.card} (hne : i ≠ k)
    (V : ENNReal) (hV : ∀ l, (F.tube l).volume = V) :
    volume ((translateTube (F.tube i) (shift j)).carrier ∩
            (translateTube (F.tube k) (shift j)).carrier) ≤ V / 2 := by
  have h_ed : (F.tube i).EssentiallyDistinct (F.tube k) := hF i k hne
  have h_trans_ed : (translateTube (F.tube i) (shift j)).EssentiallyDistinct
      (translateTube (F.tube k) (shift j)) :=
    translate_essentiallyDistinct (F.tube i) (F.tube k) (shift j) h_ed
  have h_max : max (translateTube (F.tube i) (shift j)).volume
      (translateTube (F.tube k) (shift j)).volume = V := by
    have h1 : (translateTube (F.tube i) (shift j)).volume = V := by
      rw [translateTube_volume, hV i]
    have h2 : (translateTube (F.tube k) (shift j)).volume = V := by
      rw [translateTube_volume, hV k]
    rw [h1, h2]
    simp
  have h_eq : V / 2 = (2 : ENNReal)⁻¹ * V := by
    simp [div_eq_mul_inv]
    ring
  rw [h_eq]
  simpa [Kakeya.DeltaTube.EssentiallyDistinct, h_max] using h_trans_ed

/--
Sum of intersection volumes over all tubes in the same copy.
-/
lemma same_copy_intersection_sum
    {δ : ℝ} {F : TubeFamily δ} {J : ℕ} {shift : Fin J → Point3}
    (hF : F.IsEssentiallyDistinct)
    (j : Fin J) (k : Fin F.card)
    (V : ENNReal) (hV : ∀ l, (F.tube l).volume = V) :
    ∑ i : Fin F.card,
      volume ((translateTube (F.tube i) (shift j)).carrier ∩
              (translateTube (F.tube k) (shift j)).carrier) ≤
    V + ((F.card : ENNReal) - 1) * (V / 2) := by
  let T_k := translateTube (F.tube k) (shift j)
  let g : Fin F.card → ENNReal := fun i =>
    volume ((translateTube (F.tube i) (shift j)).carrier ∩ T_k.carrier)
  have h_pos : 0 < F.card := by
    have h : (k : ℕ) < F.card := k.is_lt
    omega
  have h_one_le : 1 ≤ F.card := by omega
  have h_vol_k : g k = V := by
    dsimp only [g]
    have h : T_k.carrier ∩ T_k.carrier = T_k.carrier := by simp
    rw [h]
    have h2 : T_k.volume = V := by rw [translateTube_volume, hV k]
    exact h2
  let s : Finset (Fin F.card) := Finset.univ.erase k
  have h_k_notin : k ∉ s := by simp [s]
  have h_insert : insert k s = (Finset.univ : Finset (Fin F.card)) := by
    rw [Finset.insert_erase (Finset.mem_univ k)]
  have h_split : ∑ i : Fin F.card, g i = g k + ∑ i ∈ s, g i := by
    have h : ∑ i ∈ insert k s, g i = g k + ∑ i ∈ s, g i :=
      Finset.sum_insert h_k_notin
    rw [h_insert] at h
    exact h
  rw [h_split, h_vol_k]
  have h_bound : ∑ i ∈ s, g i ≤ (s.card : ENNReal) * (V / 2) := by
    have h1 : ∀ i ∈ s, g i ≤ V / 2 := by
      intro i hi
      have hne : i ≠ k := by
        simpa [s, Finset.mem_erase] using (Finset.mem_erase.mp hi).1
      exact same_copy_pair_intersection hF j hne V hV
    calc
      ∑ i ∈ s, g i ≤ ∑ _ ∈ s, (V / 2) := Finset.sum_le_sum h1
      _ = (s.card : ENNReal) * (V / 2) := by
        rw [Finset.sum_const]; ring
  have h_card : s.card = F.card - 1 := by
    simp [s, Finset.card_erase_of_mem (Finset.mem_univ k)]
  have h1 : (1 : ENNReal) + ((F.card - 1 : ℕ) : ENNReal) = (F.card : ENNReal) := by
    norm_cast; omega
  have h_cast : (F.card : ENNReal) - 1 = ((F.card - 1 : ℕ) : ENNReal) := by
    rw [← h1]; simp
  rw [h_card] at h_bound
  have h_eq : ((F.card - 1 : ℕ) : ENNReal) = (F.card : ENNReal) - 1 := h_cast.symm
  have h_bound2 : ∑ i ∈ s, g i ≤ ((F.card : ENNReal) - 1) * (V / 2) := by
    simpa [h_eq] using h_bound
  exact add_le_add_right h_bound2 V

/-! ## 2. Convolution formula -/

/--
The full-space convolution identity:
`∫⁻ volume(T ∩ (U + d)) dd = volume(T) * volume(U)`

for measurable sets T, U with `volume U ≠ ⊤`.
-/
lemma convolution_intersection_volume
    {T U : Set Point3} (hT : MeasurableSet T) (hU : MeasurableSet U)
    (hU_ne_top : volume U ≠ ⊤) :
    ∫⁻ (d : Point3), volume (T ∩ translateSet U d) = volume T * volume U := by
  let one : Point3 → ENNReal := fun _ => 1
  let one2 : Point3 × Point3 → ENNReal := fun _ => 1
  -- Joint set S = {(d,x) | x ∈ T and x - d ∈ U}
  let g : Point3 × Point3 → Point3 := fun p => p.2 - p.1
  let S : Set (Point3 × Point3) := (Set.univ ×ˢ T) ∩ g ⁻¹' U
  have hS : MeasurableSet S :=
    (MeasurableSet.univ.prod hT).inter (hU.preimage (by fun_prop))
  let f : Point3 → Point3 → ENNReal := fun d x => Set.indicator S one2 (d, x)
  have h_meas : Measurable (Function.uncurry f) := by
    have h : Function.uncurry f = Set.indicator S one2 := by funext p; rfl
    rw [h]
    have h2 : Measurable one2 := by fun_prop
    exact h2.indicator hS
  have h_ae_meas : AEMeasurable (Function.uncurry f) (volume.prod volume) :=
    h_meas.aemeasurable
  -- Equivalence: x ∈ translateSet U d ↔ x - d ∈ U
  have h_mem_trans : ∀ (d x : Point3), x ∈ translateSet U d ↔ x - d ∈ U := by
    intro d x
    constructor
    · rintro ⟨y, hy, rfl⟩
      simpa using hy
    · intro h
      refine ⟨x - d, h, by abel⟩
  -- Key identity: f d x = indicator T x * indicator (translateSet U d) x
  have h_f_eq : ∀ (d x : Point3), f d x =
      Set.indicator T one x * Set.indicator (translateSet U d) one x := by
    intro d x
    have h1 : f d x = Set.indicator S one2 (d, x) := by rfl
    rw [h1]
    have h_iff : (d, x) ∈ S ↔ x ∈ T ∧ x ∈ translateSet U d := by
      simp [S, h_mem_trans]; tauto
    by_cases h : (d, x) ∈ S
    · have h' : x ∈ T ∧ x ∈ translateSet U d := h_iff.mp h
      simp [Set.indicator, h, h'.1, h'.2, one, one2]
    · have h' : ¬(x ∈ T ∧ x ∈ translateSet U d) := by
        intro h2; exact h (h_iff.mpr h2)
      simp [Set.indicator, h, one, one2]; tauto
  -- volume(T ∩ translateSet U d) = ∫⁻ x, f d x
  have h_main1 : ∀ (d : Point3),
      volume (T ∩ translateSet U d) = ∫⁻ (x : Point3), f d x := by
    intro d
    have h_meas_set : MeasurableSet (T ∩ translateSet U d) :=
      hT.inter (measurableSet_translateSet hU d)
    have h_ind : Set.indicator (T ∩ translateSet U d) one = fun x => f d x := by
      funext x
      have h_prod : Set.indicator (T ∩ translateSet U d) one x =
          Set.indicator T one x * Set.indicator (translateSet U d) one x := by
        by_cases h : x ∈ T ∩ translateSet U d
        · have hT' : x ∈ T := h.1
          have hU' : x ∈ translateSet U d := h.2
          simp [Set.indicator, h, hT', hU', one]
        · have h' : x ∉ T ∩ translateSet U d := h
          simp [Set.indicator, h', one] <;> tauto
      rw [h_prod, h_f_eq d x]
    have h : volume (T ∩ translateSet U d) =
        ∫⁻ (x : Point3), Set.indicator (T ∩ translateSet U d) one x :=
      (MeasureTheory.lintegral_indicator_one h_meas_set).symm
    rw [h, h_ind]
  -- Swap integrals
  have h_swap : ∫⁻ (d : Point3), ∫⁻ (x : Point3), f d x =
      ∫⁻ (x : Point3), ∫⁻ (d : Point3), f d x :=
    MeasureTheory.lintegral_lintegral_swap h_ae_meas
  -- Inner integral: ∫⁻ d, f d x = indicator T x * volume U
  have h_inner : ∀ (x : Point3),
      ∫⁻ (d : Point3), f d x = Set.indicator T one x * volume U := by
    intro x
    by_cases hx : x ∈ T
    · have hT1 : Set.indicator T one x = 1 := by
        simp [one, Set.indicator, hx]
      have h_eq1 : ∫⁻ (d : Point3), f d x =
          ∫⁻ (d : Point3), Set.indicator (translateSet U d) one x := by
        apply lintegral_congr
        intro d
        rw [h_f_eq d x, hT1] <;> ring
      rw [h_eq1, hT1]
      have h_set : {d : Point3 | x ∈ translateSet U d} =
          (fun d : Point3 => x - d) ⁻¹' U := by
        ext d
        simp [h_mem_trans, Set.mem_preimage]
      have h2 : ∫⁻ (d : Point3), Set.indicator (translateSet U d) one x =
          volume U := by
        have h3 : ∫⁻ (d : Point3), Set.indicator (translateSet U d) one x =
            volume {d : Point3 | x ∈ translateSet U d} := by
          exact MeasureTheory.lintegral_indicator_one
            (show MeasurableSet {d : Point3 | x ∈ translateSet U d} from by
              rw [h_set]
              exact hU.preimage (by fun_prop))
        rw [h3, h_set]
        have h_mp : MeasurePreserving (fun d : Point3 => x - d) :=
          Measure.measurePreserving_sub_left volume x
        exact h_mp.measure_preimage hU.nullMeasurableSet
      rw [h2] <;> ring
    · have hT1 : Set.indicator T one x = 0 := by
        simp [one, Set.indicator, hx]
      have h_zero : ∀ d, f d x = 0 := by
        intro d
        rw [h_f_eq d x, hT1] <;> ring
      have h_eq1 : ∫⁻ (d : Point3), f d x = 0 := by
        simpa using lintegral_congr h_zero
      rw [h_eq1, hT1] <;> simp
  -- Put it all together
  calc
    ∫⁻ (d : Point3), volume (T ∩ translateSet U d)
      = ∫⁻ (d : Point3), ∫⁻ (x : Point3), f d x := by
        apply lintegral_congr
        intro d
        exact h_main1 d
    _ = ∫⁻ (x : Point3), ∫⁻ (d : Point3), f d x := h_swap
    _ = ∫⁻ (x : Point3), Set.indicator T one x * volume U := by
        apply lintegral_congr
        intro x
        exact h_inner x
    _ = volume T * volume U := by
        have h_comm : ∫⁻ (x : Point3), Set.indicator T one x * volume U =
            ∫⁻ (x : Point3), volume U * Set.indicator T one x := by
          apply lintegral_congr
          intro x
          ring
        rw [h_comm]
        have h1 : ∫⁻ (x : Point3), volume U * Set.indicator T one x =
            volume U * ∫⁻ (x : Point3), Set.indicator T one x :=
          MeasureTheory.lintegral_const_mul' (volume U) (Set.indicator T one) hU_ne_top
        rw [h1]
        have h2 : ∫⁻ (x : Point3), Set.indicator T one x = volume T :=
          MeasureTheory.lintegral_indicator_one hT
        rw [h2] <;> ring

end Kakeya.Streamlined.RandomTranslation

end
