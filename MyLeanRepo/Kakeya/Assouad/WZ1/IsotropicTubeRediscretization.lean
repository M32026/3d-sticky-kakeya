import MyLeanRepo.Kakeya.Assouad.WZ1.MildRescalingRediscretizationStatements
import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Mathlib.Algebra.Order.Floor.Defs
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Analysis.Normed.Module.Ball.Pointwise

/-!
# WZ1 isotropic tube rediscretization

Cover the isotropically rescaled image of every source tube by exactly
`ceil scale` unit-length children on the same axis and construct the exact
childwise shading.
-/

noncomputable section

namespace Kakeya.Assouad

open Metric Set

variable {center : Point3} {scale : ℝ}

private lemma isotropicRescaling_injective (hscale_pos : 0 < scale) :
    Function.Injective (wz1IsotropicRescalingMap center scale) := by
  intro x y h
  have h2 : scale • (x - center) = scale • (y - center) := h
  have h3 : scale • (x - y) = 0 := by
    have h4 : scale • (x - center) - scale • (y - center) = 0 := by
      rw [h2]
      simp
    have h5 :
        scale • (x - center) - scale • (y - center) =
          scale • (x - y) := by
      have h_sub : (x - center) - (y - center) = x - y := by
        simp [sub_sub]
      calc
        scale • (x - center) - scale • (y - center)
            = scale • ((x - center) - (y - center)) := by rw [← smul_sub]
        _ = scale • (x - y) := by rw [h_sub]
    rw [h5] at h4
    exact h4
  have h7 : x - y = 0 := by
    rw [smul_eq_zero] at h3
    cases h3 with
    | inl h3 =>
        exfalso
        linarith
    | inr h3 => exact h3
  exact sub_eq_zero.mp h7

private lemma isotropicRescaling_surjective (hscale_pos : 0 < scale) :
    Function.Surjective (wz1IsotropicRescalingMap center scale) := by
  intro y
  let x : Point3 := center + scale⁻¹ • y
  have h : wz1IsotropicRescalingMap center scale x = y := by
    unfold x wz1IsotropicRescalingMap
    have h2 : center + scale⁻¹ • y - center = scale⁻¹ • y := by simp
    rw [h2]
    rw [smul_smul]
    have h4 : scale * scale⁻¹ = 1 := by
      field_simp [hscale_pos.ne']
    rw [h4, one_smul]
  exact ⟨x, h⟩

private lemma isotropicRescaling_infEDist (hscale_pos : 0 < scale)
    (x : Point3) (s : Set Point3) :
    infEDist (wz1IsotropicRescalingMap center scale x)
      (wz1IsotropicRescalingMap center scale '' s) =
    ENNReal.ofReal scale * infEDist x s := by
  let f := wz1IsotropicRescalingMap center scale
  let trans : Point3 → Point3 := fun y => y - center
  have htrans_isom : Isometry trans := by
    refine Isometry.of_dist_eq ?_
    intro a b
    have h : trans a - trans b = a - b := by simp [trans, sub_sub]
    rw [dist_eq_norm, dist_eq_norm, h]
  have h1 : infEDist (trans x) (trans '' s) = infEDist x s :=
    Metric.infEDist_image (hΦ := htrans_isom)
  have h_fx : f x = scale • trans x := by
    simp [f, trans, wz1IsotropicRescalingMap]
  have h_fs : f '' s = (fun y : Point3 => scale • y) '' (trans '' s) := by
    ext z
    simp [f, trans, wz1IsotropicRescalingMap, Set.mem_image]
    <;> constructor
    <;> rintro ⟨y, hy, rfl⟩
    <;> refine ⟨y, hy, by simp [trans]⟩
  have h_goal :
      infEDist (f x) (f '' s) =
        ENNReal.ofReal scale * infEDist x s := by
    rw [h_fx, h_fs]
    have h3 :
        infEDist (scale • trans x)
            ((fun y : Point3 => scale • y) '' (trans '' s)) =
          ‖(scale : ℝ)‖₊ • infEDist (trans x) (trans '' s) :=
      infEDist_smul₀ hscale_pos.ne' (trans '' s) (trans x)
    rw [h3, h1]
    have h5 : (‖(scale : ℝ)‖₊ : ℝ) = scale := by
      have h6 : (‖(scale : ℝ)‖₊ : ℝ) = |scale| :=
        Real.ext_cauchy rfl
      rw [h6, abs_of_pos hscale_pos]
    have h7 : (‖(scale : ℝ)‖₊ : ENNReal) = ENNReal.ofReal scale := by
      have h8 :
          (‖(scale : ℝ)‖₊ : ENNReal) =
            ENNReal.ofReal (‖(scale : ℝ)‖₊ : ℝ) :=
        ENNReal.coe_nnreal_eq ‖scale‖₊
      rw [h8, h5]
    have h9 :
        ‖(scale : ℝ)‖₊ • infEDist x s =
          (‖(scale : ℝ)‖₊ : ENNReal) * infEDist x s :=
      smul_eq_mul (↑‖scale‖₊) (infEDist x s)
    rw [h9, h7]
  simpa [f] using h_goal

private lemma isotropicRescaling_image_cthickening
    (hscale_pos : 0 < scale) (r : ℝ) (s : Set Point3) :
    wz1IsotropicRescalingMap center scale '' Metric.cthickening r s =
    Metric.cthickening (scale * r)
      (wz1IsotropicRescalingMap center scale '' s) := by
  let f := wz1IsotropicRescalingMap center scale
  have h_inj : Function.Injective f :=
    isotropicRescaling_injective hscale_pos
  have h_surj : Function.Surjective f :=
    isotropicRescaling_surjective hscale_pos
  ext p
  obtain ⟨x, rfl⟩ := h_surj p
  simp only [Set.mem_image, Metric.mem_cthickening_iff]
  have h_eq :
      infEDist (f x) (f '' s) =
        ENNReal.ofReal scale * infEDist x s :=
    isotropicRescaling_infEDist hscale_pos x s
  have h_mul :
      ENNReal.ofReal (scale * r) =
        ENNReal.ofReal scale * ENNReal.ofReal r := by
    rw [ENNReal.ofReal_mul] <;> linarith
  constructor
  · rintro ⟨y, hy, hfy⟩
    have h_yx : y = x := h_inj hfy
    rw [h_yx] at hy
    rw [h_eq, h_mul]
    gcongr
  · intro h
    refine ⟨x, ?_, rfl⟩
    rw [h_eq, h_mul] at h
    have hpos : ENNReal.ofReal scale ≠ 0 :=
      (ENNReal.ofReal_pos.mpr hscale_pos).ne'
    have htop : ENNReal.ofReal scale ≠ ⊤ := ENNReal.ofReal_ne_top
    exact (ENNReal.mul_le_mul_iff_right hpos htop).mp h

private lemma unitSegment_subset_isotropicRescaling
    (hscale_pos : 0 < scale) {b d : Point3}
    {a : ℝ} (ha : 0 ≤ a) (h : a + 1 ≤ scale) :
    unitSegment
        (wz1IsotropicRescalingMap center scale b + a • d) d ⊆
      wz1IsotropicRescalingMap center scale '' unitSegment b d := by
  let f := wz1IsotropicRescalingMap center scale
  intro p hp
  have hmem :
      ∃ t : ℝ, t ∈ Set.Icc (0 : ℝ) 1 ∧
        (f b + a • d) + t • d = p := by
    simpa [unitSegment, Set.mem_image] using hp
  rcases hmem with ⟨t, ht, hpt⟩
  set u : ℝ := (a + t) / scale with hu_def
  have hu0 : 0 ≤ u := by apply div_nonneg <;> linarith [ht.1]
  have hu1 : u ≤ 1 := by
    rw [div_le_one hscale_pos]
    linarith [ht.2]
  have h_main : f (b + u • d) = f b + (a + t) • d := by
    unfold f wz1IsotropicRescalingMap
    have h2 :
        scale • (b + u • d - center) =
          scale • (b - center) + (a + t) • d := by
      have h3 : b + u • d - center = (b - center) + u • d := by abel
      rw [h3, smul_add]
      have h4 : scale • (u • d) = (a + t) • d := by
        rw [smul_smul]
        have h5 : scale * u = a + t := by
          simp [u, hu_def]
          field_simp [hscale_pos.ne']
        rw [h5]
      rw [h4]
    exact h2
  have h_u_in : u ∈ Set.Icc (0 : ℝ) 1 := ⟨hu0, hu1⟩
  have h_eq :
      f b + (a + t) • d = (f b + a • d) + t • d := by
    rw [add_smul]
    abel
  have h6 : f (b + u • d) = p := by
    rw [h_main, h_eq, hpt]
  exact ⟨b + u • d, Set.mem_image_of_mem _ h_u_in, h6⟩

private lemma isotropicRescaling_axisLine
    (hscale_pos : 0 < scale)
    {δ : ℝ} {T : Kakeya.DeltaTube δ}
    {T' : Kakeya.DeltaTube (scale * δ)}
    (hbase : T'.base = wz1IsotropicRescalingMap center scale T.base)
    (hdirection : T'.direction = T.direction) :
    wz1IsotropicRescalingMap center scale '' tubeAxisLine T =
      tubeAxisLine T' := by
  let f := wz1IsotropicRescalingMap center scale
  ext p
  simp only [tubeAxisLine, Set.mem_image, Set.mem_setOf_eq]
  constructor
  · rintro ⟨q, ⟨t, rfl⟩, rfl⟩
    refine ⟨scale * t, ?_⟩
    unfold wz1IsotropicRescalingMap
    rw [hbase, hdirection]
    have h3 :
        T.base + t • T.direction - center =
          (T.base - center) + t • T.direction := by abel
    rw [h3, smul_add]
    rw [smul_smul]
    rfl
  · rintro ⟨s, rfl⟩
    let u : ℝ := s / scale
    refine ⟨T.base + u • T.direction, ⟨u, rfl⟩, ?_⟩
    unfold u wz1IsotropicRescalingMap
    rw [hbase, hdirection]
    have h3 :
        T.base + (s / scale) • T.direction - center =
          (T.base - center) + (s / scale) • T.direction := by abel
    rw [h3, smul_add]
    have h4 :
        scale • ((s / scale) • T.direction) =
          s • T.direction := by
      rw [smul_smul]
      have h5 : scale * (s / scale) = s := by
        field_simp [hscale_pos.ne']
      rw [h5]
    rw [h4]
    rfl

private lemma cthickening_finite_iUnion
    {α : Type*} [PseudoMetricSpace α] {r : ℝ}
    {ι : Type*} (t : Finset ι) (s : ι → Set α) :
    Metric.cthickening r (⋃ i ∈ t, s i) =
      ⋃ i ∈ t, Metric.cthickening r (s i) := by
  classical
  induction t using Finset.induction with
  | empty => simp
  | @insert a t ha ih =>
      have h1 :
          (⋃ i ∈ insert a t, s i) =
            s a ∪ (⋃ i ∈ t, s i) := by
        ext y
        simp [Finset.mem_insert, ha]
      have h2 :
          (⋃ i ∈ insert a t, Metric.cthickening r (s i)) =
            Metric.cthickening r (s a) ∪
              (⋃ i ∈ t, Metric.cthickening r (s i)) := by
        ext y
        simp [Finset.mem_insert, ha]
      rw [h1, h2, Metric.cthickening_union, ih]

private lemma deltaTube_carrier_measurable
    {δ : ℝ} (T : Kakeya.DeltaTube δ) :
    MeasurableSet T.carrier := by
  have h2 :
      IsClosed
        (Metric.cthickening δ
          (unitSegment T.base T.direction)) :=
    Metric.isClosed_cthickening
  exact h2.measurableSet

private lemma isotropicRescaling_unitSegment_image
    (hscale_pos : 0 < scale) {b d : Point3} :
    wz1IsotropicRescalingMap center scale '' unitSegment b d =
      {p | ∃ s : ℝ, 0 ≤ s ∧ s ≤ scale ∧
        p = wz1IsotropicRescalingMap center scale b + s • d} := by
  let f := wz1IsotropicRescalingMap center scale
  ext p
  simp only [unitSegment, Set.mem_image, Set.mem_setOf_eq]
  constructor
  · rintro ⟨q, ⟨t, ⟨ht0, ht1⟩, rfl⟩, rfl⟩
    refine ⟨scale * t, by positivity, ?_, ?_⟩
    · calc
        scale * t ≤ scale * 1 := by gcongr
        _ = scale := by ring
    · unfold wz1IsotropicRescalingMap
      have h2 :
          scale • (b + t • d - center) =
            scale • (b - center) + (scale * t) • d := by
        have h3 :
            b + t • d - center = (b - center) + t • d := by abel
        rw [h3, smul_add]
        rw [smul_smul]
      exact h2
  · rintro ⟨s, hs0, hs1, rfl⟩
    let t := s / scale
    have ht0 : 0 ≤ t := by positivity
    have ht1 : t ≤ 1 := by
      rw [div_le_one hscale_pos]
      exact hs1
    have h :
        f (b + t • d) = f b + s • d := by
      unfold f wz1IsotropicRescalingMap t
      have h2 :
          scale • (b + (s / scale) • d - center) =
            scale • (b - center) + s • d := by
        have h3 :
            b + (s / scale) • d - center =
              (b - center) + (s / scale) • d := by abel
        rw [h3, smul_add]
        have h4 : scale • ((s / scale) • d) = s • d := by
          rw [smul_smul]
          have h5 : scale * (s / scale) = s := by
            field_simp [hscale_pos.ne']
          rw [h5]
        rw [h4]
      exact h2
    exact ⟨b + t • d, ⟨t, ⟨ht0, ht1⟩, rfl⟩, h⟩

private lemma exists_nat_floor (x : ℝ) (hx : 0 ≤ x) :
    ∃ m : ℕ, (m : ℝ) ≤ x ∧ x < (m : ℝ) + 1 := by
  let m : ℤ := Int.floor x
  have hm1 : (m : ℝ) ≤ x := Int.floor_le x
  have hm2 : x < (m : ℝ) + 1 := Int.lt_floor_add_one x
  have hm0 : 0 ≤ m := Int.floor_nonneg.mpr hx
  let m' : ℕ := m.toNat
  have h_eq1 : (m' : ℤ) = m := by
    rw [Int.toNat_of_nonneg hm0]
  have h_eq : (m' : ℝ) = (m : ℝ) := by
    exact_mod_cast h_eq1
  refine ⟨m', ?_⟩
  constructor
  · rw [h_eq]
    exact hm1
  · rw [h_eq]
    exact hm2

private lemma isotropic_unitSegment_coverage
    (hscale : 1 ≤ scale) {b d : Point3}
    (n : ℕ) (hn : n = Nat.ceil scale) :
    wz1IsotropicRescalingMap center scale '' unitSegment b d ⊆
      ⋃ k : Fin n, unitSegment
        (wz1IsotropicRescalingMap center scale b +
          wz1IsotropicChildOffset n scale k • d) d := by
  let f := wz1IsotropicRescalingMap center scale
  have hscale_pos : 0 < scale := by linarith
  have hn1 : 1 ≤ n := by
    rw [hn]
    exact (Nat.one_le_ceil_iff (a := scale)).mpr hscale_pos
  have hscale_le_n : scale ≤ (n : ℝ) := by
    rw [hn]
    exact Nat.le_ceil scale
  have h_ceil_pos : 1 ≤ Nat.ceil scale :=
    (Nat.one_le_ceil_iff (a := scale)).mpr hscale_pos
  have h_lt : Nat.ceil scale - 1 < Nat.ceil scale := by omega
  have h' : ((Nat.ceil scale - 1 : ℕ) : ℝ) < scale :=
    (Nat.lt_ceil (a := scale)).mp h_lt
  have h_cast :
      ((Nat.ceil scale - 1 : ℕ) : ℝ) =
        (Nat.ceil scale : ℝ) - 1 := by
    rw [Nat.cast_sub h_ceil_pos]
    norm_num
  have hn_sub_one_lt_scale : (n : ℝ) - 1 < scale := by
    rw [hn]
    rw [h_cast] at h'
    exact h'
  intro p hp
  have hmem :
      ∃ s : ℝ, 0 ≤ s ∧ s ≤ scale ∧ p = f b + s • d := by
    rw [isotropicRescaling_unitSegment_image
      (center := center) hscale_pos] at hp
    exact hp
  rcases hmem with ⟨s, hs0, hs1, rfl⟩
  have h_main :
      ∃ k : Fin n,
        wz1IsotropicChildOffset n scale k ≤ s ∧
          s ≤ wz1IsotropicChildOffset n scale k + 1 := by
    by_cases h_case : s ≤ (n : ℝ) - 1
    · by_cases h_n1 : n = 1
      · have h_scale_eq_one : scale = 1 := by
          have h1 : n = Nat.ceil scale := hn
          rw [h_n1] at h1
          have h2 : Nat.ceil scale = 1 := h1.symm
          have h3 : scale ≤ (Nat.ceil scale : ℝ) :=
            Nat.le_ceil scale
          rw [h2] at h3
          have h4 : scale ≤ 1 := by exact_mod_cast h3
          linarith
        have hs0' : s = 0 := by
          rw [h_n1] at h_case
          norm_num at h_case ⊢
          linarith
        let k' : Fin n := ⟨0, by rw [h_n1]; omega⟩
        have hkoff :
            wz1IsotropicChildOffset n scale k' = scale - 1 := by
          simp [wz1IsotropicChildOffset, k', h_n1]
        refine ⟨k', ?_⟩
        rw [hkoff, hs0', h_scale_eq_one]
        norm_num
      · have hn2 : 2 ≤ n := by omega
        by_cases h_strict : s < (n : ℝ) - 1
        · rcases exists_nat_floor s hs0 with ⟨m, hm1, hm2⟩
          have hm3 : m < n - 1 := by
            have h4 : (m : ℝ) < (n : ℝ) - 1 := by linarith
            exact_mod_cast h4
          have hm4 : m + 1 < n := by omega
          let k : Fin n := ⟨m, by omega⟩
          have hkoff :
              wz1IsotropicChildOffset n scale k = (m : ℝ) := by
            simp [wz1IsotropicChildOffset, k, hm4]
          refine ⟨k, ?_⟩
          rw [hkoff]
          constructor <;> linarith
        · have h_eq : s = (n : ℝ) - 1 := by linarith
          let k : Fin n := ⟨n - 2, by omega⟩
          have h_k_lt : n - 2 + 1 < n := by omega
          have hkoff :
              wz1IsotropicChildOffset n scale k = (n : ℝ) - 2 := by
            rw [wz1IsotropicChildOffset, if_pos h_k_lt]
            have h2 : (k : ℕ) = n - 2 := by rfl
            rw [h2]
            rw [Nat.cast_sub (show 2 ≤ n from by omega)]
            norm_num
          refine ⟨k, ?_⟩
          rw [hkoff, h_eq]
          constructor <;> linarith
    · have h' : (n : ℝ) - 1 < s := by linarith
      let k : Fin n := ⟨n - 1, by omega⟩
      have hlast : ¬ (k : ℕ) + 1 < n := by
        dsimp [k]
        omega
      have hkoff :
          wz1IsotropicChildOffset n scale k = scale - 1 := by
        rw [wz1IsotropicChildOffset, if_neg hlast]
      refine ⟨k, ?_⟩
      rw [hkoff]
      constructor <;> linarith
  rcases h_main with ⟨k, hk1, hk2⟩
  let u : ℝ := s - wz1IsotropicChildOffset n scale k
  have hu0 : 0 ≤ u := by linarith
  have hu1 : u ≤ 1 := by linarith
  have h_point :
      f b + s • d ∈
        unitSegment
          (f b + wz1IsotropicChildOffset n scale k • d) d := by
    refine ⟨u, ⟨hu0, hu1⟩, ?_⟩
    have h_smul :
        wz1IsotropicChildOffset n scale k • d + u • d = s • d := by
      rw [← add_smul]
      have h_sum : wz1IsotropicChildOffset n scale k + u = s := by
        simp [u]
      rw [h_sum]
    have h_goal :
        (f b + wz1IsotropicChildOffset n scale k • d) + u • d =
          f b + s • d := by
      rw [add_assoc, h_smul]
    exact h_goal
  exact Set.mem_iUnion.mpr ⟨k, h_point⟩

theorem wz1_isotropic_tube_rediscretization :
    WZ1IsotropicTubeRediscretizationStatement := by
  intro sourceDelta scale hsourceDelta_pos hscale_one hscale_le_one
    F hF_nonempty Y center
  set n : ℕ := Nat.ceil scale with hn_def
  have hscale_pos : 0 < scale := by linarith
  have hn_pos : 0 < n := by
    rw [hn_def, Nat.ceil_pos]
    linarith
  let f : Point3 → Point3 :=
    wz1IsotropicRescalingMap center scale
  let fHomeo : Point3 ≃ₜ Point3 :=
    { toFun := f
      invFun := fun q => center + scale⁻¹ • q
      left_inv := by
        intro p
        dsimp only [f, wz1IsotropicRescalingMap]
        have h2 :
            scale⁻¹ • (scale • (p - center)) = p - center := by
          rw [smul_smul]
          have h3 : scale⁻¹ * scale = 1 := by
            field_simp [hscale_pos.ne']
          rw [h3, one_smul]
        rw [h2]
        exact add_sub_cancel center p
      right_inv := by
        intro q
        dsimp only [f, wz1IsotropicRescalingMap]
        have h2 :
            center + scale⁻¹ • q - center = scale⁻¹ • q := by simp
        rw [h2]
        rw [smul_smul]
        have h4 : scale * scale⁻¹ = 1 := by
          field_simp [hscale_pos.ne']
        rw [h4, one_smul]
      continuous_toFun := by
        exact continuous_const.smul
          (continuous_id.sub continuous_const)
      continuous_invFun := by
        exact continuous_const.add
          (continuous_const.smul continuous_id) }
  set targetCard : ℕ := F.card * n with htargetCard
  let sourceParent (j : Fin targetCard) : Fin F.card :=
    ⟨j.val / n, by
      have h' : j.val < targetCard := j.is_lt
      have h'' : j.val < F.card * n := by
        simpa [htargetCard] using h'
      by_contra h3
      have h4 : F.card ≤ j.val / n := by linarith
      have h5 : F.card * n ≤ j.val := by
        calc
          F.card * n ≤ (j.val / n) * n := by gcongr
          _ ≤ j.val := Nat.div_mul_le_self j.val n
      linarith⟩
  let childIndex (j : Fin targetCard) : Fin n :=
    ⟨j.val % n, Nat.mod_lt j.val hn_pos⟩
  let mkIndex (i : Fin F.card) (k : Fin n) : Fin targetCard :=
    ⟨i.val * n + k.val, by
      have h : i.val * n + k.val < F.card * n := by
        nlinarith [k.is_lt, i.is_lt]
      simpa [htargetCard] using h⟩
  have hmkIndex_parent :
      ∀ (i : Fin F.card) (k : Fin n),
        sourceParent (mkIndex i k) = i := by
    intro i k
    apply Fin.ext
    change (i.val * n + k.val) / n = i.val
    have h_comm : i.val * n + k.val = k.val + i.val * n := by ring
    rw [h_comm]
    rw [Nat.add_mul_div_right k.val i.val hn_pos]
    rw [Nat.div_eq_of_lt k.is_lt, zero_add]
  have hmkIndex_child :
      ∀ (i : Fin F.card) (k : Fin n),
        childIndex (mkIndex i k) = k := by
    intro i k
    apply Fin.ext
    change (i.val * n + k.val) % n = k.val
    have h_comm : i.val * n + k.val = k.val + i.val * n := by ring
    rw [h_comm]
    rw [Nat.add_mul_mod_self_right]
    rw [Nat.mod_eq_of_lt k.is_lt]
  have hmkIndex_surj :
      ∀ j : Fin targetCard,
        mkIndex (sourceParent j) (childIndex j) = j := by
    intro j
    apply Fin.ext
    have h' := Nat.div_add_mod j.val n
    have h'' : n * (j.val / n) + j.val % n = j.val := h'
    have h_comm3 :
        n * (j.val / n) = (j.val / n) * n := by ring
    rw [h_comm3] at h''
    simpa [sourceParent, childIndex, mkIndex] using h''
  let targetBase (i : Fin F.card) (k : Fin n) : Point3 :=
    f (F.tube i).base +
      wz1IsotropicChildOffset n scale k • (F.tube i).direction
  let targetTube (j : Fin targetCard) :
      DeltaTube (scale * sourceDelta) :=
    { base := targetBase (sourceParent j) (childIndex j)
      direction := (F.tube (sourceParent j)).direction
      direction_unit := (F.tube (sourceParent j)).direction_unit }
  let family : Kakeya.Streamlined.TubeFamily
      (scale * sourceDelta) :=
    { card := targetCard
      tube := targetTube }
  let shadingCarrier (j : Fin targetCard) : Set Point3 :=
    (family.tube j).carrier ∩
      f '' Y.carrier (sourceParent j)
  have h_measurable :
      ∀ j, MeasurableSet (shadingCarrier j) := by
    intro j
    have h1 : MeasurableSet (family.tube j).carrier :=
      deltaTube_carrier_measurable (family.tube j)
    have h2 :
        MeasurableSet (f '' Y.carrier (sourceParent j)) := by
      rcases Y.measurable_carrier (sourceParent j) with
        ⟨s', hs'meas, h_eq⟩
      have hYmeas :
          MeasurableSet (Y.carrier (sourceParent j)) := by
        rw [← h_eq]
        exact hs'meas.preimage (by fun_prop)
      have h_image_eq :
          f '' Y.carrier (sourceParent j) =
            fHomeo.invFun ⁻¹' Y.carrier (sourceParent j) := by
        ext z
        simp only [Set.mem_image, Set.mem_preimage]
        constructor
        · rintro ⟨y, hy, rfl⟩
          rw [fHomeo.left_inv]
          exact hy
        · intro hz
          exact ⟨fHomeo.invFun z, hz, fHomeo.right_inv z⟩
      rw [h_image_eq]
      exact hYmeas.preimage fHomeo.symm.measurable
    exact h1.inter h2
  have h_subset :
      ∀ j, shadingCarrier j ⊆ (family.tube j).carrier := by
    intro j
    exact inter_subset_left
  let shading : Kakeya.Streamlined.TubeShading family :=
    { carrier := shadingCarrier
      measurable_carrier := h_measurable
      subset_body := h_subset }
  have h_fiber_eq :
      ∀ i : Fin F.card,
        Finset.univ.filter
            (fun j : Fin targetCard => sourceParent j = i) =
          Finset.image (fun k : Fin n => mkIndex i k) Finset.univ := by
    intro i
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_image]
    constructor
    · intro h
      refine ⟨childIndex j, ?_⟩
      have h5 : mkIndex i (childIndex j) = j := by
        have h7 := hmkIndex_surj j
        rw [h] at h7
        exact h7
      exact h5
    · rintro ⟨k, hk⟩
      rw [← hk]
      exact hmkIndex_parent i k
  have h_image_thickening :
      ∀ i : Fin F.card,
        f '' (F.tube i).carrier =
          Metric.cthickening (scale * sourceDelta)
            (f '' unitSegment
              (F.tube i).base (F.tube i).direction) := by
    intro i
    have h :
        (F.tube i).carrier =
          Metric.cthickening sourceDelta
            (unitSegment
              (F.tube i).base (F.tube i).direction) := by
      simp [Kakeya.DeltaTube.carrier]
    rw [h]
    exact isotropicRescaling_image_cthickening
      (center := center) hscale_pos sourceDelta _
  have h_child_offset_bounds :
      ∀ (i : Fin F.card) (k : Fin n),
        0 ≤ wz1IsotropicChildOffset n scale k ∧
          wz1IsotropicChildOffset n scale k + 1 ≤ scale := by
    intro i k
    have h_ceil_pos2 : 1 ≤ Nat.ceil scale :=
      (Nat.one_le_ceil_iff (a := scale)).mpr hscale_pos
    have h_lt2 : Nat.ceil scale - 1 < Nat.ceil scale := by omega
    have h'2 : ((Nat.ceil scale - 1 : ℕ) : ℝ) < scale :=
      (Nat.lt_ceil (a := scale)).mp h_lt2
    have h_cast2 :
        ((Nat.ceil scale - 1 : ℕ) : ℝ) =
          (Nat.ceil scale : ℝ) - 1 := by
      rw [Nat.cast_sub h_ceil_pos2]
      norm_num
    have hn_sub_one_lt_scale : (n : ℝ) - 1 < scale := by
      rw [hn_def]
      rw [h_cast2] at h'2
      exact h'2
    by_cases h : (k : ℕ) + 1 < n
    · have ha :
          wz1IsotropicChildOffset n scale k = (k : ℝ) := by
        simp [wz1IsotropicChildOffset, h]
      constructor
      · rw [ha]
        exact Nat.cast_nonneg k
      · rw [ha]
        have h2 : (k : ℕ) + 1 ≤ n - 1 := by omega
        have h1 : (k : ℝ) + 1 ≤ (n : ℝ) - 1 := by
          exact_mod_cast h2
        linarith
    · have ha :
          wz1IsotropicChildOffset n scale k = scale - 1 := by
        simp [wz1IsotropicChildOffset, h]
      rw [ha]
      constructor <;> linarith
  have h_containment :
      ∀ (i : Fin F.card) (k : Fin n),
        unitSegment
            (targetBase i k) (F.tube i).direction ⊆
          f '' unitSegment
            (F.tube i).base (F.tube i).direction := by
    intro i k
    have h_bounds := h_child_offset_bounds i k
    exact unitSegment_subset_isotropicRescaling
      (center := center) hscale_pos h_bounds.1 h_bounds.2
  have h_coverage :
      ∀ i : Fin F.card,
        f '' unitSegment
            (F.tube i).base (F.tube i).direction ⊆
          ⋃ k : Fin n,
            unitSegment
              (targetBase i k) (F.tube i).direction := by
    intro i
    exact isotropic_unitSegment_coverage
      (center := center) hscale_one n hn_def
  have h_carrier_in_source_image :
      ∀ j : Fin targetCard,
        (family.tube j).carrier ⊆
          f '' (F.tube (sourceParent j)).carrier := by
    intro j
    let i := sourceParent j
    let k := childIndex j
    have h1 :
        (family.tube j).carrier =
          Metric.cthickening (scale * sourceDelta)
            (unitSegment
              (targetBase i k) (F.tube i).direction) := by
      dsimp only [family, targetTube, targetBase, i, k]
      simp [Kakeya.DeltaTube.carrier]
    rw [h1, h_image_thickening i]
    apply Metric.cthickening_subset_of_subset (scale * sourceDelta)
    exact h_containment i k
  have h_source_carrier_covered :
      ∀ i : Fin F.card,
        f '' (F.tube i).carrier ⊆
          ⋃ j ∈ Finset.univ.filter
              (fun j : Fin targetCard => sourceParent j = i),
            (family.tube j).carrier := by
    intro i
    rw [h_image_thickening i]
    have h1 :
        f '' unitSegment
            (F.tube i).base (F.tube i).direction ⊆
          ⋃ k : Fin n,
            unitSegment
              (targetBase i k) (F.tube i).direction :=
      h_coverage i
    have h2 :
        Metric.cthickening (scale * sourceDelta)
            (f '' unitSegment
              (F.tube i).base (F.tube i).direction) ⊆
          Metric.cthickening (scale * sourceDelta)
            (⋃ k : Fin n,
              unitSegment
                (targetBase i k) (F.tube i).direction) :=
      Metric.cthickening_subset_of_subset (scale * sourceDelta) h1
    have h3 :
        Metric.cthickening (scale * sourceDelta)
            (⋃ k : Fin n,
              unitSegment
                (targetBase i k) (F.tube i).direction) =
          ⋃ k : Fin n,
            Metric.cthickening (scale * sourceDelta)
              (unitSegment
                (targetBase i k) (F.tube i).direction) := by
      have h4 :=
        cthickening_finite_iUnion
          (r := scale * sourceDelta)
          (Finset.univ : Finset (Fin n))
          (fun k =>
            unitSegment
              (targetBase i k) (F.tube i).direction)
      have h_univ1 :
          (⋃ k : Fin n,
              unitSegment
                (targetBase i k) (F.tube i).direction) =
            ⋃ k ∈ (Finset.univ : Finset (Fin n)),
              unitSegment
                (targetBase i k) (F.tube i).direction := by
        ext x
        simp
      have h_univ2 :
          (⋃ k : Fin n,
              Metric.cthickening (scale * sourceDelta)
                (unitSegment
                  (targetBase i k) (F.tube i).direction)) =
            ⋃ k ∈ (Finset.univ : Finset (Fin n)),
              Metric.cthickening (scale * sourceDelta)
                (unitSegment
                  (targetBase i k) (F.tube i).direction) := by
        ext x
        simp
      rw [h_univ1, h4, h_univ2]
    rw [h3] at h2
    have h3' :
        (⋃ k : Fin n,
            Metric.cthickening (scale * sourceDelta)
              (unitSegment
                (targetBase i k) (F.tube i).direction)) =
          ⋃ k : Fin n,
            (family.tube (mkIndex i k)).carrier := by
      congr with k
      have h_par : sourceParent (mkIndex i k) = i :=
        hmkIndex_parent i k
      have h_child : childIndex (mkIndex i k) = k :=
        hmkIndex_child i k
      have h_base :
          targetBase
              (sourceParent (mkIndex i k))
              (childIndex (mkIndex i k)) =
            targetBase i k := by
        rw [h_par, h_child]
      have h_dir :
          (F.tube (sourceParent (mkIndex i k))).direction =
            (F.tube i).direction := by
        rw [h_par]
      dsimp only [family, targetTube, Kakeya.DeltaTube.carrier]
      rw [h_base, h_dir]
    rw [h3'] at h2
    have h4 :
        (⋃ k : Fin n,
            (family.tube (mkIndex i k)).carrier) =
          ⋃ j ∈ Finset.univ.filter
              (fun j : Fin targetCard => sourceParent j = i),
            (family.tube j).carrier := by
      ext x
      simp only [Set.mem_iUnion, Set.mem_iUnion₂]
      constructor
      · rintro ⟨k, hk⟩
        refine ⟨mkIndex i k, ?_, hk⟩
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        exact hmkIndex_parent i k
      · rintro ⟨j, hj, hxj⟩
        have h5 : sourceParent j = i := (Finset.mem_filter.mp hj).2
        refine ⟨childIndex j, ?_⟩
        have h6 : mkIndex i (childIndex j) = j := by
          rw [← h5]
          exact hmkIndex_surj j
        rw [h6]
        exact hxj
    rw [h4] at h2
    exact h2
  have h_axis_provenance :
      ∀ j : Fin targetCard,
        tubeAxisLine (family.tube j) =
          f '' tubeAxisLine (F.tube (sourceParent j)) := by
    intro j
    let i := sourceParent j
    let k := childIndex j
    let a := wz1IsotropicChildOffset n scale k
    have hbase :
        (family.tube j).base =
          f (F.tube i).base + a • (F.tube i).direction := by
      rfl
    have hdirection :
        (family.tube j).direction = (F.tube i).direction := by
      rfl
    let T' : DeltaTube (scale * sourceDelta) :=
      { base := f (F.tube i).base
        direction := (F.tube i).direction
        direction_unit := (F.tube i).direction_unit }
    have h_offset :
        tubeAxisLine (family.tube j) = tubeAxisLine T' := by
      ext p
      simp only [tubeAxisLine, Set.mem_setOf_eq]
      constructor
      · rintro ⟨t, ht⟩
        rw [hbase, hdirection] at ht
        refine ⟨a + t, ?_⟩
        dsimp only [T']
        have h_sum :
            a • (F.tube i).direction +
                t • (F.tube i).direction =
              (a + t) • (F.tube i).direction := by
          rw [← add_smul]
        have ht' :
            p =
              f (F.tube i).base +
                (a + t) • (F.tube i).direction := by
          have h_assoc :
              p =
                f (F.tube i).base +
                  (a • (F.tube i).direction +
                    t • (F.tube i).direction) := by
            simpa [add_assoc] using ht
          rw [h_sum] at h_assoc
          exact h_assoc
        exact ht'
      · rintro ⟨t, ht⟩
        refine ⟨t - a, ?_⟩
        have h_goal :
            (family.tube j).base +
                (t - a) • (family.tube j).direction =
              T'.base + t • T'.direction := by
          rw [hbase, hdirection]
          dsimp only [T']
          have h_assoc :
              f (F.tube i).base +
                  a • (F.tube i).direction +
                  (t - a) • (F.tube i).direction =
                f (F.tube i).base +
                  (a • (F.tube i).direction +
                    (t - a) • (F.tube i).direction) := by
            rw [add_assoc]
          rw [h_assoc]
          have h_sum :
              a • (F.tube i).direction +
                  (t - a) • (F.tube i).direction =
                (a + (t - a)) • (F.tube i).direction := by
            rw [← add_smul]
          rw [h_sum]
          have h2 : a + (t - a) = t := by abel
          rw [h2]
        rw [h_goal, ht]
    have h_main :
        f '' tubeAxisLine (F.tube i) = tubeAxisLine T' :=
      isotropicRescaling_axisLine
        (center := center) hscale_pos rfl rfl
    rw [h_offset]
    exact h_main.symm
  have h_source_shading_covered :
      ∀ i : Fin F.card,
        f '' Y.carrier i ⊆
          ⋃ j ∈ Finset.univ.filter
              (fun j : Fin targetCard => sourceParent j = i),
            shading.carrier j := by
    intro i x hx
    have h1 : x ∈ f '' (F.tube i).carrier := by
      rcases hx with ⟨y, hy, rfl⟩
      exact ⟨y, Y.subset_body i hy, rfl⟩
    have h3 :
        x ∈
          ⋃ j ∈ Finset.univ.filter
              (fun j : Fin targetCard => sourceParent j = i),
            (family.tube j).carrier :=
      h_source_carrier_covered i h1
    rcases Set.mem_iUnion₂.mp h3 with ⟨j, hj, hxj⟩
    have h4 : sourceParent j = i := (Finset.mem_filter.mp hj).2
    have h5 : x ∈ shading.carrier j := by
      have h6 : x ∈ f '' Y.carrier (sourceParent j) := by
        rw [h4]
        exact hx
      exact ⟨hxj, h6⟩
    exact Set.mem_iUnion₂.mpr ⟨j, hj, h5⟩
  have h_shading_union_eq :
      shading.union = f '' Y.union := by
    ext x
    simp only [Kakeya.Streamlined.Shading.union, Set.mem_setOf_eq]
    constructor
    · rintro ⟨j, hj⟩
      rcases hj.2 with ⟨y, hy, rfl⟩
      exact ⟨y, ⟨sourceParent j, hy⟩, rfl⟩
    · rintro ⟨y, ⟨i, hi⟩, rfl⟩
      have h3 : f y ∈ f '' Y.carrier i := ⟨y, hi, rfl⟩
      have h4 :
          f y ∈
            ⋃ j ∈ Finset.univ.filter
                (fun j : Fin targetCard => sourceParent j = i),
              shading.carrier j :=
        h_source_shading_covered i h3
      rcases Set.mem_iUnion₂.mp h4 with ⟨j, _, hj⟩
      exact ⟨j, hj⟩
  refine ⟨
    n, hn_pos, rfl, family, shading, sourceParent,
    childIndex, mkIndex,
    hmkIndex_parent, hmkIndex_child, hmkIndex_surj,
    ?_, ?_, ?_, ?_, h_axis_provenance,
    h_carrier_in_source_image, h_source_carrier_covered,
    ?_, h_source_shading_covered, h_shading_union_eq
  ⟩
  · intro i
    refine ⟨mkIndex i ⟨0, hn_pos⟩, ?_⟩
    exact hmkIndex_parent i _
  · intro i
    rw [h_fiber_eq i]
    rw [Finset.card_image_of_injective]
    · simp
    · intro k1 k2 h
      have h1 : childIndex (mkIndex i k1) = k1 :=
        hmkIndex_child i k1
      have h2 : childIndex (mkIndex i k2) = k2 :=
        hmkIndex_child i k2
      have h3 :
          childIndex (mkIndex i k1) =
            childIndex (mkIndex i k2) :=
        congr_arg childIndex h
      rw [h1, h2] at h3
      exact h3
  · intro j
    rfl
  · intro j
    rfl
  · intro j
    rfl

end Kakeya.Assouad
