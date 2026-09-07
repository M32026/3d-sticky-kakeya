import MyLeanRepo.Kakeya.Cinematic.Statements
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.ContDiff.Deriv

/-!
# Main assembly for RectanglePacking

This file assembles the proof of `incomparable_rectangles_packing_bound`
using the area computation and point packing bound components.

The proof is self-contained: it establishes the derivative separation,
pointwise overlap bound, and area comparison used in the paper.
-/

noncomputable section

open MeasureTheory Set

-- Enable subtype measure space (not global by default in Mathlib).
attribute [local instance] MeasureTheory.Measure.Subtype.measureSpace
attribute [local instance] Classical.propDecidable

namespace Kakeya.Cinematic

/-! ### Reused area computation lemmas -/

theorem mble_verticalNeighborhoodOn (f : C2Function) (δ : ℝ) (I : ParameterInterval) :
    MeasurableSet (verticalNeighborhoodOn f δ I) := by
  let g : UnitPoint × ℝ → ℝ := fun p => |p.2 - f p.1|
  have hg : Continuous g := by fun_prop
  have h1 : MeasurableSet {x : UnitPoint | I.left ≤ (x : ℝ)} :=
    isClosed_le continuous_const continuous_subtype_val |>.measurableSet
  have h2 : MeasurableSet {x : UnitPoint | (x : ℝ) ≤ I.right} :=
    isClosed_le continuous_subtype_val continuous_const |>.measurableSet
  have hI : MeasurableSet I.carrier := by
    have h4 : {x : UnitPoint | I.left ≤ (x : ℝ)} ∩ {x : UnitPoint | (x : ℝ) ≤ I.right} = I.carrier := by
      ext x; simp [ParameterInterval.carrier]
    exact h4 ▸ h1.inter h2
  have h5 : MeasurableSet {p : UnitPoint × ℝ | p.1 ∈ I.carrier} :=
    hI.preimage measurable_fst
  have h6 : MeasurableSet {p : UnitPoint × ℝ | g p ≤ δ} :=
    hg.measurable measurableSet_Iic
  have h7 : ({p : UnitPoint × ℝ | p.1 ∈ I.carrier} ∩ {p : UnitPoint × ℝ | g p ≤ δ}) =
      verticalNeighborhoodOn f δ I := by
    ext p; simp [verticalNeighborhoodOn, g]
  exact h7 ▸ h5.inter h6

theorem volume_verticalNeighborhoodOn (f : C2Function) (δ : ℝ)
    (I : ParameterInterval) (hδ : 0 ≤ δ) :
    volume (verticalNeighborhoodOn f δ I) = ENNReal.ofReal (2 * δ * I.length) := by
  have h_unit : MeasurableSet (unitInterval : Set ℝ) := isClosed_Icc.measurableSet
  have h_img : (Subtype.val '' I.carrier) = Set.Icc I.left I.right := by
    ext x
    simp only [Set.mem_image, ParameterInterval.carrier, Set.mem_setOf_eq]
    constructor
    · rintro ⟨y, hy, rfl⟩; exact ⟨hy.1, hy.2⟩
    · intro hx
      have h_x_in : x ∈ unitInterval :=
        ⟨I.left_mem.1.trans hx.1, hx.2.trans I.right_mem.2⟩
      exact ⟨⟨x, h_x_in⟩, ⟨hx.1, hx.2⟩, rfl⟩
  have h_vol_I : volume I.carrier = ENNReal.ofReal I.length := by
    have h_eq : volume (Subtype.val '' I.carrier) = volume I.carrier :=
      volume_image_subtype_coe h_unit I.carrier
    rw [←h_eq, h_img, Real.volume_Icc] <;> rfl
  have h_main : (volume : Measure (UnitPoint × ℝ)) =
      (volume : Measure UnitPoint).prod volume :=
    MeasureTheory.Measure.volume_eq_prod UnitPoint ℝ
  rw [h_main]
  let S := verticalNeighborhoodOn f δ I
  have hS : MeasurableSet S := mble_verticalNeighborhoodOn f δ I
  rw [MeasureTheory.Measure.prod_apply hS]
  have h_fiber : ∀ (x : UnitPoint),
      volume (Prod.mk x ⁻¹' S) =
        I.carrier.indicator (fun _ => ENNReal.ofReal (2 * δ)) x := by
    intro x
    have h_pre : (Prod.mk x ⁻¹' S) = {y : ℝ | (x, y) ∈ S} := by ext y; simp
    rw [h_pre]
    by_cases h : x ∈ I.carrier
    · rw [Set.indicator_of_mem h]
      have h_set : {y : ℝ | (x, y) ∈ S} = Set.Icc (f x - δ) (f x + δ) := by
        ext y
        simp only [S, verticalNeighborhoodOn, Set.mem_setOf_eq, Set.mem_Icc]
        constructor
        · intro hy
          have h5 : |y - f x| ≤ δ := hy.2
          have h6 : -δ ≤ y - f x := (abs_le.mp h5).1
          have h7 : y - f x ≤ δ := (abs_le.mp h5).2
          exact ⟨by linarith, by linarith⟩
        · intro hy
          have h_abs : |y - f x| ≤ δ := by
            apply abs_le.mpr
            constructor <;> linarith
          exact ⟨h, h_abs⟩
      rw [h_set, Real.volume_Icc]
      have h_eq : (f x + δ) - (f x - δ) = 2 * δ := by ring
      rw [h_eq]
    · rw [Set.indicator_apply, if_neg h]
      have h_set : {y : ℝ | (x, y) ∈ S} = ∅ := by
        ext y; simp [S, verticalNeighborhoodOn, h] <;> tauto
      rw [h_set] <;> simp
  have h_int : ∫⁻ (x : UnitPoint), volume (Prod.mk x ⁻¹' S) =
      ∫⁻ (x : UnitPoint), I.carrier.indicator (fun _ => ENNReal.ofReal (2 * δ)) x := by
    congr with x; exact h_fiber x
  rw [h_int, lintegral_indicator_const (by
    have h1 : MeasurableSet {x : UnitPoint | I.left ≤ (x : ℝ)} :=
      isClosed_le continuous_const continuous_subtype_val |>.measurableSet
    have h2 : MeasurableSet {x : UnitPoint | (x : ℝ) ≤ I.right} :=
      isClosed_le continuous_subtype_val continuous_const |>.measurableSet
    have h4 : {x : UnitPoint | I.left ≤ (x : ℝ)} ∩ {x : UnitPoint | (x : ℝ) ≤ I.right} = I.carrier := by
      ext x; simp [ParameterInterval.carrier]
    exact h4 ▸ h1.inter h2) (ENNReal.ofReal (2 * δ))]
  rw [h_vol_I]
  rw [←ENNReal.ofReal_mul (show 0 ≤ 2 * δ by linarith)]

/-! ### Half-interval and half-rectangles -/

/-- The middle half of a parameter interval: [left + length/4, right - length/4]. -/
def ParameterInterval.half (I : ParameterInterval) : ParameterInterval where
  left := I.left + I.length / 4
  right := I.right - I.length / 4
  left_mem := by
    have hlen : 0 ≤ I.length := I.length_nonneg
    constructor
    · linarith [I.left_mem.1]
    · have h : I.left + I.length / 4 ≤ I.right := by
        have h' : I.length = I.right - I.left := by simp [ParameterInterval.length]
        linarith
      linarith [I.right_mem.2]
  right_mem := by
    have hlen : 0 ≤ I.length := I.length_nonneg
    constructor
    · have h : I.left ≤ I.right - I.length / 4 := by
        have h' : I.length = I.right - I.left := by simp [ParameterInterval.length]
        linarith
      linarith [I.left_mem.1]
    · linarith [I.right_mem.2]
  left_le_right := by
    have hlen : 0 ≤ I.length := I.length_nonneg
    have h' : I.length = I.right - I.left := by simp [ParameterInterval.length]
    linarith

theorem ParameterInterval.half_length (I : ParameterInterval) :
    I.half.length = I.length / 2 := by
  simp [ParameterInterval.half, ParameterInterval.length]
  <;> ring

theorem ParameterInterval.half_carrier_subset (I : ParameterInterval) :
    I.half.carrier ⊆ I.carrier := by
  intro x hx
  have h1 : I.half.left ≤ (x : ℝ) := hx.1
  have h2 : (x : ℝ) ≤ I.half.right := hx.2
  have h3 : I.left ≤ (x : ℝ) := by
    have h4 : I.left ≤ I.half.left := by
      simp [ParameterInterval.half] <;> linarith [I.length_nonneg]
    linarith
  have h5 : (x : ℝ) ≤ I.right := by
    have h6 : I.half.right ≤ I.right := by
      simp [ParameterInterval.half] <;> linarith [I.length_nonneg]
    linarith
  exact ⟨h3, h5⟩

theorem ParameterInterval.abs_sub_half_le (I : ParameterInterval) {x y : UnitPoint}
    (hx : x ∈ I.half.carrier) (hy : y ∈ I.carrier) :
    |(x : ℝ) - (y : ℝ)| ≤ 3 * I.length / 4 := by
  have hLen : I.length = I.right - I.left := by simp [ParameterInterval.length]
  have hx1 : I.left + I.length / 4 ≤ (x : ℝ) := hx.1
  have hx2 : (x : ℝ) ≤ I.right - I.length / 4 := hx.2
  have hy1 : I.left ≤ (y : ℝ) := hy.1
  have hy2 : (y : ℝ) ≤ I.right := hy.2
  rw [abs_le]
  constructor
  · linarith [hLen]
  · linarith [hLen]

/-- The half-rectangle: vertical neighborhood over the middle half interval. -/
def CurvilinearRectangle.halfCarrier {δ t : ℝ} (R : CurvilinearRectangle δ t) :
    Set (UnitPoint × ℝ) :=
  verticalNeighborhoodOn R.function δ R.interval.half

theorem CurvilinearRectangle.volume_halfCarrier {δ t : ℝ}
    (R : CurvilinearRectangle δ t) (hδ : 0 ≤ δ) :
    volume R.halfCarrier = ENNReal.ofReal (δ * R.interval.length) := by
  rw [CurvilinearRectangle.halfCarrier]
  rw [volume_verticalNeighborhoodOn R.function δ R.interval.half hδ]
  rw [R.interval.half_length]
  have h_eq : 2 * δ * (R.interval.length / 2) = δ * R.interval.length := by ring
  rw [h_eq]

theorem CurvilinearRectangle.volume_containing {δ t lam : ℝ}
    (U : CurvilinearRectangle (lam * δ) t) (hδ : 0 ≤ δ) (hlam : 0 ≤ lam) :
    volume U.carrier = ENNReal.ofReal (2 * lam * δ * Real.sqrt (lam * δ / t)) := by
  have hlamδ : 0 ≤ lam * δ := mul_nonneg hlam hδ
  have h : volume U.carrier = ENNReal.ofReal (2 * (lam * δ) * Real.sqrt ((lam * δ) / t)) := by
    have h_carrier : U.carrier = verticalNeighborhoodOn U.function (lam * δ) U.interval := by rfl
    rw [h_carrier]
    rw [volume_verticalNeighborhoodOn U.function (lam * δ) U.interval hlamδ, U.interval_length]
  rw [h]
  have h_eq : 2 * (lam * δ) = 2 * lam * δ := by ring
  rw [h_eq]

theorem CurvilinearRectangle.halfCarrier_subset_carrier {δ t : ℝ}
    (R : CurvilinearRectangle δ t) :
    R.halfCarrier ⊆ R.carrier := by
  intro p hp
  have h1 : p.1 ∈ R.interval.half.carrier := hp.1
  have h2 : p.1 ∈ R.interval.carrier := R.interval.half_carrier_subset h1
  exact ⟨h2, hp.2⟩

/-! ### Bounded overlap with ENNReal multiplicity bound -/

private lemma sum_indicator_eq_card {α ι : Type*} [MeasurableSpace α]
    (s : Finset ι) (A : ι → Set α) (x : α) :
    ∑ i ∈ s, (A i).indicator (fun _ => (1 : ENNReal)) x =
      ↑((s.filter fun i => x ∈ A i).card) := by
  have h1 : ∀ i ∈ s, (A i).indicator (fun _ => (1 : ENNReal)) x =
      (if x ∈ A i then (1 : ENNReal) else (0 : ENNReal)) := by
    intro i _
    rw [Set.indicator_apply]
  have h2 : ∑ i ∈ s, (A i).indicator (fun _ => (1 : ENNReal)) x =
      ∑ i ∈ s, (if x ∈ A i then (1 : ENNReal) else (0 : ENNReal)) := by
    apply Finset.sum_congr rfl; exact h1
  rw [h2]
  have h3 : ∑ i ∈ s, (if x ∈ A i then (1 : ENNReal) else (0 : ENNReal)) =
      ∑ i ∈ s.filter (fun i => x ∈ A i), (1 : ENNReal) := by
    rw [←Finset.sum_filter]
  rw [h3]; simp

/-- Bounded-overlap inequality with an `ENNReal` multiplicity bound. -/
theorem bounded_overlap_ennreal {α : Type*} [MeasurableSpace α] {μ : Measure α} {ι : Type*}
    (s : Finset ι) (A : ι → Set α) (U : Set α)
    (hU : MeasurableSet U) (hA : ∀ i ∈ s, MeasurableSet (A i))
    (h_sub : ∀ i ∈ s, A i ⊆ U)
    (M : ENNReal) (h_mult : ∀ x ∈ U,
      (∑ i ∈ s, (A i).indicator (fun _ => (1 : ENNReal)) x) ≤ M) :
    ∑ i ∈ s, μ (A i) ≤ M * μ U := by
  let mult : α → ENNReal := fun x => ∑ i ∈ s, (A i).indicator (fun _ => (1 : ENNReal)) x
  have h1 : ∀ i ∈ s, ∫⁻ x, (A i).indicator (fun _ => (1 : ENNReal)) x ∂μ = μ (A i) := by
    intro i hi
    have h_ind : (A i).indicator (fun _ => (1 : ENNReal)) = (A i).indicator (1 : α → ENNReal) := by
      funext y; rfl
    rw [h_ind]; exact lintegral_indicator_one (hA i hi)
  have h_sum : ∫⁻ x, mult x ∂μ = ∑ i ∈ s, μ (A i) := by
    rw [lintegral_finsetSum s (fun i _ => measurable_const.indicator (hA i ‹_›))]
    apply Finset.sum_congr rfl; intro i hi; exact h1 i hi
  have h_bound : ∀ x, mult x ≤ M * U.indicator (fun _ => (1 : ENNReal)) x := by
    intro x
    by_cases hx : x ∈ U
    · have h : mult x ≤ M := h_mult x hx
      have h_ind : U.indicator (fun _ => (1 : ENNReal)) x = 1 := by
        rw [Set.indicator_of_mem hx]
      rw [h_ind]; rw [mul_one]; exact h
    · have h_notin : ∀ i ∈ s, x ∉ A i := by
        intro i hi; exact fun h => hx (h_sub i hi h)
      have h_each : ∀ i ∈ s, (A i).indicator (fun _ => (1 : ENNReal)) x = 0 := by
        intro i hi
        rw [Set.indicator_apply, if_neg (h_notin i hi)]
      have h_mult0 : mult x = 0 := by
        dsimp only [mult]
        rw [Finset.sum_congr rfl h_each]; simp
      rw [h_mult0]
      have h_ind : U.indicator (fun _ => (1 : ENNReal)) x = 0 := by
        rw [Set.indicator_apply, if_neg hx]
      rw [h_ind]; simp
  have h_int : ∫⁻ x, mult x ∂μ ≤ ∫⁻ x, M * U.indicator (fun _ => (1 : ENNReal)) x ∂μ :=
    lintegral_mono h_bound
  have h3 : ∫⁻ x, M * U.indicator (fun _ => (1 : ENNReal)) x ∂μ = M * μ U := by
    have h4 : (fun x : α => M * U.indicator (fun _ => (1 : ENNReal)) x) =
        U.indicator (fun _ => M) := by
      funext x
      by_cases hx : x ∈ U
      · rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx]; ring
      · rw [Set.indicator_apply, Set.indicator_apply]
        rw [if_neg hx, if_neg hx]; ring
    rw [h4]; exact lintegral_indicator_const hU M
  calc
    ∑ i ∈ s, μ (A i) = ∫⁻ x, mult x ∂μ := h_sum.symm
    _ ≤ ∫⁻ x, M * U.indicator (fun _ => (1 : ENNReal)) x ∂μ := h_int
    _ = M * μ U := h3

/-! ### Point packing bound -/

theorem point_packing_bound {d a b : ℝ} (hd : 0 < d) (hab : a ≤ b)
    (S : Finset ℝ) (h_sub : ∀ x ∈ S, x ∈ Set.Icc a b)
    (h_sep : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → |x - y| > d) :
    (S.card : ℝ) ≤ (b - a) / d + 1 := by
  classical
  have h_main : ∀ (n : ℕ),
      ∀ (T : Finset ℝ), T.card = n →
        ∀ (c e : ℝ), c ≤ e →
          (∀ x ∈ T, x ∈ Set.Icc c e) →
          (∀ x ∈ T, ∀ y ∈ T, x ≠ y → |x - y| > d) →
          (T.card : ℝ) ≤ (e - c) / d + 1 := by
    intro n
    induction n with
    | zero =>
      intro T hT c e hce _ _
      have h_empty : T = ∅ := Finset.card_eq_zero.mp hT
      rw [h_empty]
      have h_nonneg : 0 ≤ e - c := by linarith
      have h_div : 0 ≤ (e - c) / d := by positivity
      simp <;> linarith
    | succ n ih =>
      intro T hT c e hce hT_sub hT_sep
      have hne : T.Nonempty := by
        rw [Finset.nonempty_iff_ne_empty]
        by_contra h
        rw [h] at hT
        simp at hT
      let m := Finset.min' T hne
      have hm_in : m ∈ T := Finset.min'_mem T hne
      have hm_min : ∀ x ∈ T, m ≤ x := fun x hx => Finset.min'_le T x hx
      let T' := T.erase m
      have h_card' : T'.card = n := by
        rw [Finset.card_erase_of_mem hm_in, hT]
        simp
      by_cases hT'_empty : T' = ∅
      · have h2 : T ⊆ {m} := by
          intro x hx
          by_cases h3 : x = m
          · exact h3 ▸ Finset.mem_singleton_self m
          · have h4 : x ∈ T' := by
              dsimp only [T']; exact Finset.mem_erase.mpr ⟨h3, hx⟩
            rw [hT'_empty] at h4; simp at h4
        have h3 : {m} ⊆ T := by
          intro x hx; rw [Finset.mem_singleton.mp hx]; exact hm_in
        have hT_eq : T = {m} := Finset.Subset.antisymm h2 h3
        rw [hT_eq]
        have h_nonneg : 0 ≤ e - c := by linarith
        have h_div : 0 ≤ (e - c) / d := by positivity
        simp <;> linarith
      · have hne' : T'.Nonempty := Finset.nonempty_iff_ne_empty.mpr hT'_empty
        have h_above : ∀ x ∈ T', x > m + d := by
          intro x hx
          have h_xinT : x ∈ T := Finset.mem_of_mem_erase hx
          have h_xne_m : x ≠ m := (Finset.mem_erase.mp hx).1
          have h_sep' : |x - m| > d := hT_sep x h_xinT m hm_in h_xne_m
          have h_xge_m : m ≤ x := hm_min x h_xinT
          have h_xsub_m : 0 ≤ x - m := by linarith
          have h_abs : |x - m| = x - m := abs_of_nonneg h_xsub_m
          rw [h_abs] at h_sep'; linarith
        obtain ⟨x, hx⟩ := hne'
        have h_xinT : x ∈ T := Finset.mem_of_mem_erase hx
        have h_xle_e : x ≤ e := (hT_sub x h_xinT).2
        have h_md_le_e : m + d ≤ e := by have h : m + d < x := h_above x hx; linarith
        have hT'_sub : ∀ x ∈ T', x ∈ Set.Icc (m + d) e := by
          intro x hx
          have h_xinT : x ∈ T := Finset.mem_of_mem_erase hx
          have h_xle_e : x ≤ e := (hT_sub x h_xinT).2
          have h_xge : m + d < x := h_above x hx
          exact ⟨by linarith, h_xle_e⟩
        have hT'_sep : ∀ x ∈ T', ∀ y ∈ T', x ≠ y → |x - y| > d := by
          intro x hx y hy hxy
          exact hT_sep x (Finset.mem_of_mem_erase hx) y (Finset.mem_of_mem_erase hy) hxy
        have h_ih' : (T'.card : ℝ) ≤ (e - (m + d)) / d + 1 :=
          ih T' h_card' (m + d) e h_md_le_e hT'_sub hT'_sep
        have h1 : (T.card : ℝ) = (T'.card : ℝ) + 1 := by
          rw [h_card', hT]
          norm_cast
        rw [h1]
        have hmc : m ≥ c := (hT_sub m hm_in).1
        have h_alg : (e - (m + d)) / d + 1 + 1 ≤ (e - c) / d + 1 := by
          have h_step1 : (e - (m + d)) / d + 1 + 1 = (e - m) / d + 1 := by
            have h : (e - (m + d)) / d = (e - m) / d - 1 := by
              field_simp [hd.ne'] <;> ring
            rw [h]; ring
          rw [h_step1]
          have h5 : e - m ≤ e - c := by linarith
          have h6 : (e - m) / d ≤ (e - c) / d := by gcongr
          linarith
        linarith
  exact h_main S.card S rfl a b hab h_sub h_sep

/-! ### Extension interval for derivative lower bound -/

/-- Construct an interval of length 10*L containing the convex hull of two intervals. -/
def ParameterInterval.extensionInterval (I₁ I₂ : ParameterInterval) (L : ℝ)
    (hL : 0 ≤ L) (h10 : 10 * L ≤ 1 / 2)
    (_hull : max I₁.right I₂.right - min I₁.left I₂.left ≤ 2 * L) :
    ParameterInterval :=
  let a := min I₁.left I₂.left
  let jLeft := max 0 (min a (1 - 10 * L))
  {
    left := jLeft
    right := jLeft + 10 * L
    left_mem := by
      have h1 : 0 ≤ jLeft := by positivity
      have h2 : jLeft ≤ 1 := by
        have h3 : 0 ≤ 1 - 10 * L := by linarith
        have h4 : min a (1 - 10 * L) ≤ 1 - 10 * L := min_le_right _ _
        have h5 : jLeft ≤ 1 - 10 * L := by
          apply max_le <;> linarith
        linarith
      exact ⟨h1, h2⟩
    right_mem := by
      have h1 : 0 ≤ jLeft + 10 * L := by positivity
      have h2 : jLeft + 10 * L ≤ 1 := by
        have h3 : 0 ≤ 1 - 10 * L := by linarith
        have h4 : min a (1 - 10 * L) ≤ 1 - 10 * L := min_le_right _ _
        have h5 : jLeft ≤ 1 - 10 * L := by
          apply max_le <;> linarith
        linarith
      exact ⟨h1, h2⟩
    left_le_right := by
      have h : 0 ≤ 10 * L := by linarith
      linarith
  }

theorem ParameterInterval.extensionInterval_length (I₁ I₂ : ParameterInterval) (L : ℝ)
    (hL h10 _hull) :
    (I₁.extensionInterval I₂ L hL h10 _hull).length = 10 * L := by
  simp [ParameterInterval.extensionInterval, ParameterInterval.length]

theorem ParameterInterval.extensionInterval_contains (I₁ I₂ : ParameterInterval) (L : ℝ)
    (hL : 0 ≤ L) (h10 : 10 * L ≤ 1 / 2)
    (hull : max I₁.right I₂.right - min I₁.left I₂.left ≤ 2 * L) :
    (I₁.extensionInterval I₂ L hL h10 hull).left ≤ min I₁.left I₂.left ∧
    max I₁.right I₂.right ≤ (I₁.extensionInterval I₂ L hL h10 hull).right := by
  set a := min I₁.left I₂.left with ha_def
  set b := max I₁.right I₂.right with hb_def
  set J := I₁.extensionInterval I₂ L hL h10 hull with hJ_def
  have ha0 : 0 ≤ a := by
    have h1 : 0 ≤ I₁.left := I₁.left_mem.1
    have h2 : 0 ≤ I₂.left := I₂.left_mem.1
    exact le_min h1 h2
  have hb1 : b ≤ 1 := by
    have h1 : I₁.right ≤ 1 := I₁.right_mem.2
    have h2 : I₂.right ≤ 1 := I₂.right_mem.2
    exact max_le h1 h2
  have h_pos : 0 ≤ 1 - 10 * L := by linarith
  let jLeft := max 0 (min a (1 - 10 * L))
  have hJ_left : J.left = jLeft := by
    simp [J, ParameterInterval.extensionInterval, jLeft, ha_def]
  have hJ_right : J.right = jLeft + 10 * L := by
    simp [J, ParameterInterval.extensionInterval, jLeft, ha_def]
  by_cases h : a ≤ 1 - 10 * L
  · have hmin : min a (1 - 10 * L) = a := by
      rw [min_eq_left] <;> linarith
    have hjLeft : jLeft = a := by
      simp only [jLeft, hmin]
      rw [max_eq_right ha0]
    have hJleft : J.left = a := by rw [hJ_left, hjLeft]
    have hJright : J.right = a + 10 * L := by rw [hJ_right, hjLeft]
    constructor
    · rw [hJleft]
    · rw [hJright] <;> linarith
  · have h' : 1 - 10 * L < a := by linarith
    have hmin : min a (1 - 10 * L) = 1 - 10 * L := by
      rw [min_eq_right] <;> linarith
    have hjLeft : jLeft = 1 - 10 * L := by
      simp only [jLeft, hmin]
      rw [max_eq_right h_pos]
    have hJleft : J.left = 1 - 10 * L := by rw [hJ_left, hjLeft]
    have hJright : J.right = 1 := by rw [hJ_right, hjLeft] <;> linarith
    constructor
    · rw [hJleft] <;> linarith
    · rw [hJright] <;> exact hb1

/-! ### Derivative bound helpers -/

/-- If a rectangle is over the central quarter of I, its interval length ≤ I.length / 4. -/
lemma central_quarter_length_bound {δ t : ℝ} {R : CurvilinearRectangle δ t}
    {I : ParameterInterval} (h : R.IsOverCentralQuarterOf I) :
    R.interval.length ≤ I.length / 4 := by
  let l : UnitPoint := ⟨R.interval.left, R.interval.left_mem⟩
  let r : UnitPoint := ⟨R.interval.right, R.interval.right_mem⟩
  have hl : l ∈ R.interval.carrier := by
    have h1 : R.interval.left ≤ (l : ℝ) := by simp [l]
    have h2 : (l : ℝ) ≤ R.interval.right := by
      simp [l] <;> exact R.interval.left_le_right
    exact ⟨h1, h2⟩
  have hr : r ∈ R.interval.carrier := by
    have h1 : R.interval.left ≤ (r : ℝ) := by
      simp [r] <;> exact R.interval.left_le_right
    have h2 : (r : ℝ) ≤ R.interval.right := by simp [r]
    exact ⟨h1, h2⟩
  have hl' : l ∈ I.centeredCarrier (1 / 4) := h hl
  have hr' : r ∈ I.centeredCarrier (1 / 4) := h hr
  have h1 : |(l : ℝ) - I.midpoint| ≤ (1 / 4 : ℝ) * I.length / 2 := hl'
  have h2 : |(r : ℝ) - I.midpoint| ≤ (1 / 4 : ℝ) * I.length / 2 := hr'
  have h1' : |(l : ℝ) - I.midpoint| ≤ I.length / 8 := by
    have h_eq : (1 / 4 : ℝ) * I.length / 2 = I.length / 8 := by ring
    rw [h_eq] at h1; exact h1
  have h2' : |(r : ℝ) - I.midpoint| ≤ I.length / 8 := by
    have h_eq : (1 / 4 : ℝ) * I.length / 2 = I.length / 8 := by ring
    rw [h_eq] at h2; exact h2
  have h3 : (l : ℝ) ≥ I.midpoint - I.length / 8 := by
    have h4 := (abs_le.mp h1').1; linarith
  have h4 : (r : ℝ) ≤ I.midpoint + I.length / 8 := by
    have h5 := (abs_le.mp h2').2; linarith
  have h5 : R.interval.length = (r : ℝ) - (l : ℝ) := by
    simp [ParameterInterval.length] <;> ring
  rw [h5]; linarith

/-- For θ₀ in the half-interval of R, both endpoints are within 3L/4 of θ₀. -/
lemma half_interval_endpoint_bounds {δ t : ℝ} {R : CurvilinearRectangle δ t}
    {θ₀ : UnitPoint} (hθ₀ : θ₀ ∈ R.interval.half.carrier) :
    R.interval.right - (θ₀ : ℝ) ≤ 3 * R.interval.length / 4 ∧
    (θ₀ : ℝ) - R.interval.left ≤ 3 * R.interval.length / 4 := by
  have h1 : R.interval.half.left ≤ (θ₀ : ℝ) := hθ₀.1
  have h2 : (θ₀ : ℝ) ≤ R.interval.half.right := hθ₀.2
  have hL : R.interval.length = R.interval.right - R.interval.left := by
    simp [ParameterInterval.length]
  constructor
  · have h3 : (θ₀ : ℝ) ≥ R.interval.left + R.interval.length / 4 := by
      simpa [ParameterInterval.half] using h1
    linarith
  · have h4 : (θ₀ : ℝ) ≤ R.interval.right - R.interval.length / 4 := by
      simpa [ParameterInterval.half] using h2
    linarith

-- Helper: derivative of difference equals difference of derivatives on [0,1]
private lemma deriv_diff_eq {f g : C2Function} {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    deriv (f.extension - g.extension) x = f.firstDeriv ⟨x, hx⟩ - g.firstDeriv ⟨x, hx⟩ := by
  let x' : UnitPoint := ⟨x, hx⟩
  have h_df : DifferentiableAt ℝ f.extension x :=
    (f.extension_contDiff.differentiable (by norm_num)).differentiableAt
  have h_dg : DifferentiableAt ℝ g.extension x :=
    (g.extension_contDiff.differentiable (by norm_num)).differentiableAt
  have h_sub : HasDerivAt (f.extension - g.extension)
      (deriv f.extension x - deriv g.extension x) x :=
    h_df.hasDerivAt.sub h_dg.hasDerivAt
  have h1 : deriv (f.extension - g.extension) x = deriv f.extension x - deriv g.extension x :=
    h_sub.deriv
  rw [h1]
  have h3 : deriv f.extension x = f.firstDeriv x' := C2Function.deriv_extension_eq_firstDeriv f x'
  have h4 : deriv g.extension x = g.firstDeriv x' := C2Function.deriv_extension_eq_firstDeriv g x'
  rw [h3, h4]

-- Helper: second derivative of difference
private lemma second_deriv_diff_eq {f g : C2Function} {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    deriv (deriv (f.extension - g.extension)) x =
      f.secondDeriv ⟨x, hx⟩ - g.secondDeriv ⟨x, hx⟩ := by
  let x' : UnitPoint := ⟨x, hx⟩
  have h_eq1 : deriv (f.extension - g.extension) = deriv f.extension - deriv g.extension := by
    funext y
    have h_df : DifferentiableAt ℝ f.extension y :=
      (f.extension_contDiff.differentiable (by norm_num)).differentiableAt
    have h_dg : DifferentiableAt ℝ g.extension y :=
      (g.extension_contDiff.differentiable (by norm_num)).differentiableAt
    exact (h_df.hasDerivAt.sub h_dg.hasDerivAt).deriv
  rw [h_eq1]
  have h_f2 : ContDiff ℝ 1 (deriv f.extension) := by
    have h_tmp : ContDiff ℝ (1 + 1) f.extension := f.extension_contDiff
    exact ContDiff.deriv' h_tmp
  have h_g2 : ContDiff ℝ 1 (deriv g.extension) := by
    have h_tmp : ContDiff ℝ (1 + 1) g.extension := g.extension_contDiff
    exact ContDiff.deriv' h_tmp
  have h_df2 : DifferentiableAt ℝ (deriv f.extension) x :=
    (ContDiff.differentiable h_f2 (by norm_num)).differentiableAt
  have h_dg2 : DifferentiableAt ℝ (deriv g.extension) x :=
    (ContDiff.differentiable h_g2 (by norm_num)).differentiableAt
  have h_sub2 : HasDerivAt (deriv f.extension - deriv g.extension)
      (deriv (deriv f.extension) x - deriv (deriv g.extension) x) x :=
    h_df2.hasDerivAt.sub h_dg2.hasDerivAt
  have h1 : deriv (deriv f.extension - deriv g.extension) x =
      deriv (deriv f.extension) x - deriv (deriv g.extension) x := h_sub2.deriv
  rw [h1]
  have h3 : deriv (deriv f.extension) x = f.secondDeriv x' :=
    C2Function.secondDeriv_extension_eq_secondDeriv f x'
  have h4 : deriv (deriv g.extension) x = g.secondDeriv x' :=
    C2Function.secondDeriv_extension_eq_secondDeriv g x'
  rw [h3, h4]

/-- Bound on the first derivative difference at any point near θ₀. -/
lemma derivative_bound_at {δ t : ℝ} {f g : C2Function} {θ₀ : UnitPoint}
    (hδ : 0 < δ) (ht : 0 < t)
    (hdist : c2Distance f g ≤ 6 * t)
    (hderiv₀ : |f.firstDeriv θ₀ - g.firstDeriv θ₀| ≤ Real.sqrt (δ * t))
    {x : UnitPoint} (hx : |(x : ℝ) - (θ₀ : ℝ)| ≤ 3 / 4 * Real.sqrt (δ / t)) :
    |f.firstDeriv x - g.firstDeriv x| ≤ 11 / 2 * Real.sqrt (δ * t) := by
  set h : ℝ → ℝ := f.extension - g.extension with h_def
  have hC2 : ContDiff ℝ 2 h := by
    rw [h_def]; exact ContDiff.sub f.extension_contDiff g.extension_contDiff
  have h_diff2 : Differentiable ℝ (deriv h) := ContDiff.differentiable_deriv_two hC2
  have h_bound2 : ∀ y ∈ Set.Icc (0 : ℝ) 1, |deriv (deriv h) y| ≤ 6 * t := by
    intro y hy
    rw [second_deriv_diff_eq hy]
    exact (abs_secondDeriv_sub_le_c2Distance f g ⟨y, hy⟩).trans hdist
  have h_lip : ∀ (a b : ℝ), a ∈ Set.Icc (0 : ℝ) 1 → b ∈ Set.Icc (0 : ℝ) 1 →
      |deriv h a - deriv h b| ≤ (6 * t) * |a - b| := by
    intro a b ha hb
    have h_res := Convex.norm_image_sub_le_of_norm_deriv_le
      (fun y _ => h_diff2.differentiableAt)
      (fun y hy => by simpa [Real.norm_eq_abs] using h_bound2 y hy)
      (convex_Icc 0 1) hb ha
    simpa [Real.norm_eq_abs] using h_res
  have hθ0_in : (θ₀ : ℝ) ∈ Set.Icc (0 : ℝ) 1 := θ₀.prop
  have hx_in : (x : ℝ) ∈ Set.Icc (0 : ℝ) 1 := x.prop
  have h3 : |deriv h (x : ℝ) - deriv h (θ₀ : ℝ)| ≤ (6 * t) * |(x : ℝ) - (θ₀ : ℝ)| :=
    h_lip (x : ℝ) (θ₀ : ℝ) hx_in hθ0_in
  have h4 : |deriv h (θ₀ : ℝ)| ≤ Real.sqrt (δ * t) := by
    rw [deriv_diff_eq hθ0_in] <;> exact hderiv₀
  have h5 : |deriv h (x : ℝ)| ≤ |deriv h (θ₀ : ℝ)| + |deriv h (x : ℝ) - deriv h (θ₀ : ℝ)| := by
    set a := deriv h (θ₀ : ℝ) with ha_def
    set b := deriv h (x : ℝ) - deriv h (θ₀ : ℝ) with hb_def
    have h_eq : deriv h (x : ℝ) = a + b := by simp [ha_def, hb_def] <;> ring
    rw [h_eq]
    have h1 : -(|a| + |b|) ≤ a + b := by
      have h2 : -|a| ≤ a := neg_abs_le a
      have h3 : -|b| ≤ b := neg_abs_le b
      linarith
    have h4 : a + b ≤ |a| + |b| := by
      have h5 : a ≤ |a| := le_abs_self a
      have h6 : b ≤ |b| := le_abs_self b
      linarith
    exact abs_le.mpr ⟨h1, h4⟩
  have h_sqrt : t * Real.sqrt (δ / t) = Real.sqrt (δ * t) := by
    have h9 : 0 < t := ht
    have h10 : 0 ≤ δ / t := by positivity
    have h11 : t * Real.sqrt (δ / t) = Real.sqrt (t ^ 2) * Real.sqrt (δ / t) := by
      have h12 : Real.sqrt (t ^ 2) = t := by
        rw [Real.sqrt_sq_eq_abs, abs_of_pos h9]
      rw [h12]
    rw [h11]
    have h13 : Real.sqrt (t ^ 2) * Real.sqrt (δ / t) = Real.sqrt (t ^ 2 * (δ / t)) := by
      rw [← Real.sqrt_mul (by positivity)]
    rw [h13]
    have h14 : t ^ 2 * (δ / t) = δ * t := by
      field_simp [h9.ne'] <;> ring
    rw [h14]
  have h6 : (6 * t) * |(x : ℝ) - (θ₀ : ℝ)| ≤ (9 / 2 : ℝ) * Real.sqrt (δ * t) := by
    calc
      (6 * t) * |(x : ℝ) - (θ₀ : ℝ)|
        ≤ (6 * t) * (3 / 4 * Real.sqrt (δ / t)) := by gcongr
      _ = (9 / 2 : ℝ) * (t * Real.sqrt (δ / t)) := by ring
      _ = (9 / 2 : ℝ) * Real.sqrt (δ * t) := by rw [h_sqrt]
  have h7 : |deriv h (x : ℝ)| ≤ (11 / 2 : ℝ) * Real.sqrt (δ * t) := by
    calc
      |deriv h (x : ℝ)| ≤ |deriv h (θ₀ : ℝ)| + |deriv h (x : ℝ) - deriv h (θ₀ : ℝ)| := h5
      _ ≤ |deriv h (θ₀ : ℝ)| + (6 * t) * |(x : ℝ) - (θ₀ : ℝ)| := by gcongr
      _ ≤ Real.sqrt (δ * t) + (9 / 2 : ℝ) * Real.sqrt (δ * t) := by gcongr
      _ = (11 / 2 : ℝ) * Real.sqrt (δ * t) := by ring
  have h8 : deriv h (x : ℝ) = f.firstDeriv x - g.firstDeriv x := deriv_diff_eq hx_in
  rw [h8] at h7
  exact h7

/-- Bound on the function difference at any point near θ₀. -/
lemma function_bound_at {δ t : ℝ} {f g : C2Function} {θ₀ : UnitPoint}
    (hδ : 0 < δ) (ht : 0 < t)
    (hdist : c2Distance f g ≤ 6 * t)
    (hderiv₀ : |f.firstDeriv θ₀ - g.firstDeriv θ₀| ≤ Real.sqrt (δ * t))
    (hval₀ : |f θ₀ - g θ₀| ≤ 2 * δ)
    {x : UnitPoint} (hx : |(x : ℝ) - (θ₀ : ℝ)| ≤ 3 / 4 * Real.sqrt (δ / t)) :
    |f x - g x| ≤ 7 * δ := by
  set h : ℝ → ℝ := f.extension - g.extension with h_def
  have hC2 : ContDiff ℝ 2 h := by
    rw [h_def]; exact ContDiff.sub f.extension_contDiff g.extension_contDiff
  have h_diff1 : Differentiable ℝ h := hC2.differentiable (by norm_num)
  set a : ℝ := min (θ₀ : ℝ) (x : ℝ) with ha_def
  set b : ℝ := max (θ₀ : ℝ) (x : ℝ) with hb_def
  let s : Set ℝ := Set.Icc a b
  have hs : Convex ℝ s := convex_Icc a b
  have hθ0_s : (θ₀ : ℝ) ∈ s := by
    simp [s, ha_def, hb_def] <;> exact ⟨le_min_right (le_refl _), le_max_left (le_refl _)⟩
  have hx_s : (x : ℝ) ∈ s := by
    simp [s, ha_def, hb_def] <;> exact ⟨le_min_left (le_refl _), le_max_right (le_refl _)⟩
  have h_s_subset : s ⊆ Set.Icc (0 : ℝ) 1 := by
    intro y hy
    have h1 : a ≤ y := hy.1
    have h2 : y ≤ b := hy.2
    have h3 : 0 ≤ a := by
      simp [ha_def] <;> exact ⟨θ₀.prop.1, x.prop.1⟩
    have h4 : b ≤ 1 := by
      simp [hb_def] <;> exact ⟨θ₀.prop.2, x.prop.2⟩
    exact ⟨by linarith, by linarith⟩
  have h_bound1 : ∀ y ∈ s, |deriv h y| ≤ 11 / 2 * Real.sqrt (δ * t) := by
    intro y hy
    let y' : UnitPoint := ⟨y, h_s_subset hy⟩
    have h_dist : |y - (θ₀ : ℝ)| ≤ |(x : ℝ) - (θ₀ : ℝ)| := by
      have h1 : a ≤ y := hy.1
      have h2 : y ≤ b := hy.2
      by_cases h3 : (θ₀ : ℝ) ≤ (x : ℝ)
      · have ha : a = (θ₀ : ℝ) := by rw [ha_def, min_eq_left h3]
        have hb : b = (x : ℝ) := by rw [hb_def, max_eq_right h3]
        have h4 : (θ₀ : ℝ) ≤ y := by linarith [ha, h1]
        have h5 : y ≤ (x : ℝ) := by linarith [hb, h2]
        have h6 : 0 ≤ y - (θ₀ : ℝ) := by linarith
        have h7 : 0 ≤ (x : ℝ) - (θ₀ : ℝ) := by linarith
        rw [abs_of_nonneg h6, abs_of_nonneg h7] <;> linarith
      · have h4 : (x : ℝ) < (θ₀ : ℝ) := by linarith
        have ha : a = (x : ℝ) := by
          rw [ha_def, min_eq_right (show (x : ℝ) ≤ (θ₀ : ℝ) from by linarith)]
        have hb : b = (θ₀ : ℝ) := by
          rw [hb_def, max_eq_left (show (x : ℝ) ≤ (θ₀ : ℝ) from by linarith)]
        have h5 : (x : ℝ) ≤ y := by linarith [ha, h1]
        have h6 : y ≤ (θ₀ : ℝ) := by linarith [hb, h2]
        have h7 : y - (θ₀ : ℝ) ≤ 0 := by linarith
        have h8 : (x : ℝ) - (θ₀ : ℝ) ≤ 0 := by linarith
        rw [abs_of_nonpos h7, abs_of_nonpos h8] <;> linarith
    have h_dist2 : |y - (θ₀ : ℝ)| ≤ 3 / 4 * Real.sqrt (δ / t) := by
      calc
        |y - (θ₀ : ℝ)| ≤ |(x : ℝ) - (θ₀ : ℝ)| := h_dist
        _ ≤ 3 / 4 * Real.sqrt (δ / t) := hx
    have h_res : |f.firstDeriv y' - g.firstDeriv y'| ≤ 11 / 2 * Real.sqrt (δ * t) :=
      derivative_bound_at hδ ht hdist hderiv₀ (x := y') h_dist2
    have h_eq : deriv h y = f.firstDeriv y' - g.firstDeriv y' := deriv_diff_eq (h_s_subset hy)
    rw [h_eq]; exact h_res
  have h_lip : |h (x : ℝ) - h (θ₀ : ℝ)| ≤
      (11 / 2 * Real.sqrt (δ * t)) * |(x : ℝ) - (θ₀ : ℝ)| := by
    have h_res := Convex.norm_image_sub_le_of_norm_deriv_le
      (fun y _ => h_diff1.differentiableAt)
      (fun y hy => by simpa [Real.norm_eq_abs] using h_bound1 y hy)
      hs hθ0_s hx_s
    simpa [Real.norm_eq_abs] using h_res
  have h_sqrt2 : Real.sqrt (δ * t) * Real.sqrt (δ / t) = δ := by
    have h9 : 0 ≤ δ * t := by positivity
    rw [← Real.sqrt_mul h9]
    have h11 : (δ * t) * (δ / t) = δ ^ 2 := by
      field_simp [ht.ne'] <;> ring
    rw [h11, Real.sqrt_sq_eq_abs, abs_of_pos hδ]
  have h9 : (11 / 2 * Real.sqrt (δ * t)) * |(x : ℝ) - (θ₀ : ℝ)| ≤ (33 / 8 : ℝ) * δ := by
    calc
      (11 / 2 * Real.sqrt (δ * t)) * |(x : ℝ) - (θ₀ : ℝ)|
        ≤ (11 / 2 * Real.sqrt (δ * t)) * (3 / 4 * Real.sqrt (δ / t)) := by gcongr
      _ = (33 / 8 : ℝ) * (Real.sqrt (δ * t) * Real.sqrt (δ / t)) := by ring
      _ = (33 / 8 : ℝ) * δ := by rw [h_sqrt2]
  have h10 : |h (x : ℝ) - h (θ₀ : ℝ)| ≤ (33 / 8 : ℝ) * δ := by
    calc
      |h (x : ℝ) - h (θ₀ : ℝ)|
        ≤ (11 / 2 * Real.sqrt (δ * t)) * |(x : ℝ) - (θ₀ : ℝ)| := h_lip
      _ ≤ (33 / 8 : ℝ) * δ := h9
  have h11 : |h (x : ℝ)| ≤ |h (θ₀ : ℝ)| + (33 / 8 : ℝ) * δ := by
    calc
      |h (x : ℝ)|
        = |h (θ₀ : ℝ) + (h (x : ℝ) - h (θ₀ : ℝ))| := by ring_nf
      _ ≤ |h (θ₀ : ℝ)| + |h (x : ℝ) - h (θ₀ : ℝ)| := by
        exact abs_add_le (h ↑θ₀) (h ↑x - h ↑θ₀)
      _ ≤ |h (θ₀ : ℝ)| + (33 / 8 : ℝ) * δ := by gcongr
  have h12 : h (θ₀ : ℝ) = f θ₀ - g θ₀ := by
    simp [h, C2Function.extension_eq_value] <;> rfl
  have h13 : |h (θ₀ : ℝ)| ≤ 2 * δ := by
    rw [h12] <;> exact hval₀
  have h14 : |h (x : ℝ)| ≤ 7 * δ := by
    calc
      |h (x : ℝ)| ≤ |h (θ₀ : ℝ)| + (33 / 8 : ℝ) * δ := h11
      _ ≤ 2 * δ + (33 / 8 : ℝ) * δ := by gcongr
      _ = (49 / 8 : ℝ) * δ := by ring
      _ ≤ 7 * δ := by
        have h15 : 0 ≤ δ := by linarith
        nlinarith
  have h15 : h (x : ℝ) = f x - g x := by
    simp [h, C2Function.extension_eq_value] <;> rfl
  rw [h15] at h14
  exact h14

/-! ### Derivative lower bound theorem -/

/-- Two rectangles satisfying the derivative lower bound are 100-comparable. -/
theorem derivative_lower_bound
    {δ t K : ℝ} (hδ : 0 < δ) (ht : 0 < t) (hK : 1 ≤ K)
    {family : Set C2Function}
    {I : ParameterInterval} (hI_short : I.IsShort K)
    {R_i R_j : CurvilinearRectangle δ t}
    (h_i_quarter : R_i.IsOverCentralQuarterOf I)
    (h_j_quarter : R_j.IsOverCentralQuarterOf I)
    {θ₀ : UnitPoint}
    (hθ₀_i : θ₀ ∈ R_i.interval.half.carrier)
    (hθ₀_j : θ₀ ∈ R_j.interval.half.carrier)
    (hfi : R_i.function ∈ family)
    (hdist : c2Distance R_i.function R_j.function ≤ 6 * t)
    (hval₀ : |R_i.function θ₀ - R_j.function θ₀| ≤ 2 * δ)
    (hderiv₀ : |R_i.function.firstDeriv θ₀ - R_j.function.firstDeriv θ₀| ≤
        Real.sqrt (δ * t)) :
    R_i.AreLambdaComparable R_j family 100 := by
  set L : ℝ := Real.sqrt (δ / t) with hL_def
  have hL_pos : 0 ≤ L := Real.sqrt_nonneg _
  have h_i_len : R_i.interval.length = L := by
    rw [hL_def] <;> exact R_i.interval_length
  have h_j_len : R_j.interval.length = L := by
    rw [hL_def] <;> exact R_j.interval_length
  have h_i_L_le : L ≤ I.length / 4 := by
    rw [← h_i_len] <;> exact central_quarter_length_bound h_i_quarter
  have h_short : I.length ≤ (6 * K)⁻¹ := hI_short
  have h10L : 10 * L ≤ 1 / 2 := by
    have h1 : L ≤ I.length / 4 := h_i_L_le
    have h2 : I.length ≤ 1 / (6 * K) := by
      simpa [ParameterInterval.IsShort] using h_short
    have h4 : L ≤ 1 / (6 * K) / 4 := by linarith
    have h5 : 1 / (6 * K) / 4 = 1 / (24 * K) := by ring
    rw [h5] at h4
    have h6 : 1 / (24 * K) ≤ 1 / 24 := by
      have h7 : 0 < K := by linarith
      apply one_div_le_one_div_of_le <;> linarith
    have h7 : L ≤ 1 / 24 := by linarith
    linarith
  have h_i_bounds := half_interval_endpoint_bounds hθ₀_i
  have h_j_bounds := half_interval_endpoint_bounds hθ₀_j
  have h_i_right : R_i.interval.right ≤ (θ₀ : ℝ) + 3 * L / 4 := by
    rw [h_i_len] at h_i_bounds <;> linarith
  have h_i_left : R_i.interval.left ≥ (θ₀ : ℝ) - 3 * L / 4 := by
    rw [h_i_len] at h_i_bounds <;> linarith
  have h_j_right : R_j.interval.right ≤ (θ₀ : ℝ) + 3 * L / 4 := by
    rw [h_j_len] at h_j_bounds <;> linarith
  have h_j_left : R_j.interval.left ≥ (θ₀ : ℝ) - 3 * L / 4 := by
    rw [h_j_len] at h_j_bounds <;> linarith
  set a : ℝ := min R_i.interval.left R_j.interval.left with ha_def
  set b : ℝ := max R_i.interval.right R_j.interval.right with hb_def
  have ha_ge : a ≥ (θ₀ : ℝ) - 3 * L / 4 := by
    simp [ha_def] <;> constructor <;> linarith
  have hb_le : b ≤ (θ₀ : ℝ) + 3 * L / 4 := by
    simp [hb_def] <;> constructor <;> linarith
  have h_hull : b - a ≤ 2 * L := by linarith
  let J : ParameterInterval := R_i.interval.extensionInterval
    R_j.interval L hL_pos h10L h_hull
  have hJ_len : J.length = 10 * L :=
    ParameterInterval.extensionInterval_length R_i.interval R_j.interval L hL_pos h10L h_hull
  have hJ_contains : J.left ≤ a ∧ b ≤ J.right :=
    ParameterInterval.extensionInterval_contains R_i.interval R_j.interval L hL_pos h10L h_hull
  have hJ_len' : J.length = Real.sqrt ((100 * δ) / t) := by
    rw [hJ_len, hL_def]
    have h1 : (100 * δ) / t = 100 * (δ / t) := by ring
    rw [h1]
    have h2 : Real.sqrt (100 * (δ / t)) = Real.sqrt 100 * Real.sqrt (δ / t) := by
      rw [Real.sqrt_mul (by norm_num)]
    rw [h2]
    have h3 : Real.sqrt 100 = 10 := by
      rw [Real.sqrt_eq_cases] <;> norm_num
    rw [h3] <;> ring
  let U : CurvilinearRectangle (100 * δ) t :=
    { function := R_i.function
      interval := J
      interval_length := hJ_len' }
  have hU_family : U.function ∈ family := hfi
  have h_i_sub : R_i.carrier ⊆ U.carrier := by
    intro p hp
    have h1 : p.1 ∈ R_i.interval.carrier := hp.1
    have h2 : |p.2 - R_i.function p.1| ≤ δ := hp.2
    have h3 : p.1 ∈ J.carrier := by
      have h4 : R_i.interval.left ≤ (p.1 : ℝ) := h1.1
      have h5 : (p.1 : ℝ) ≤ R_i.interval.right := h1.2
      have h6 : J.left ≤ R_i.interval.left := by
        have h7 : J.left ≤ a := hJ_contains.1
        simpa [ha_def] using le_trans h7 (min_le_left _ _)
      have h8 : R_i.interval.right ≤ J.right := by
        have h9 : b ≤ J.right := hJ_contains.2
        simpa [hb_def] using le_trans (le_max_left _ _) h9
      exact ⟨by linarith, by linarith⟩
    have h10 : |p.2 - U.function p.1| ≤ 100 * δ := by
      have h11 : U.function p.1 = R_i.function p.1 := by rfl
      rw [h11]
      have h12 : δ ≤ 100 * δ := by linarith [hδ]
      exact h2.trans h12
    exact ⟨h3, h10⟩
  have h_j_sub : R_j.carrier ⊆ U.carrier := by
    intro p hp
    have h1 : p.1 ∈ R_j.interval.carrier := hp.1
    have h2 : |p.2 - R_j.function p.1| ≤ δ := hp.2
    have h3 : p.1 ∈ J.carrier := by
      have h4 : R_j.interval.left ≤ (p.1 : ℝ) := h1.1
      have h5 : (p.1 : ℝ) ≤ R_j.interval.right := h1.2
      have h6 : J.left ≤ R_j.interval.left := by
        have h7 : J.left ≤ a := hJ_contains.1
        simpa [ha_def] using le_trans h7 (min_le_right _ _)
      have h8 : R_j.interval.right ≤ J.right := by
        have h9 : b ≤ J.right := hJ_contains.2
        simpa [hb_def] using le_trans (le_max_right _ _) h9
      exact ⟨by linarith, by linarith⟩
    have hθ_dist : |(p.1 : ℝ) - (θ₀ : ℝ)| ≤ 3 / 4 * L := by
      have h : |(θ₀ : ℝ) - (p.1 : ℝ)| ≤ 3 * R_j.interval.length / 4 :=
        ParameterInterval.abs_sub_half_le R_j.interval (x := θ₀) (y := p.1) hθ₀_j h1
      have h_abs : |(p.1 : ℝ) - (θ₀ : ℝ)| = |(θ₀ : ℝ) - (p.1 : ℝ)| := by rw [abs_sub_comm]
      rw [h_abs]
      have h' : R_j.interval.length = L := h_j_len
      rw [h'] at h
      have h_eq : 3 * L / 4 = 3 / 4 * L := by ring
      rw [h_eq] at h
      exact h
    have hθ_dist' : |(p.1 : ℝ) - (θ₀ : ℝ)| ≤ 3 / 4 * Real.sqrt (δ / t) := by
      simpa [hL_def] using hθ_dist
    have h4 : |R_i.function p.1 - R_j.function p.1| ≤ 7 * δ :=
      function_bound_at hδ ht hdist hderiv₀ hval₀ (x := p.1) hθ_dist'
    have h5 : |R_j.function p.1 - R_i.function p.1| ≤ 7 * δ := by
      have h6 : |R_j.function p.1 - R_i.function p.1| = |R_i.function p.1 - R_j.function p.1| := by
        rw [show R_j.function p.1 - R_i.function p.1 = -(R_i.function p.1 - R_j.function p.1) from by ring]
        rw [abs_neg]
      rw [h6]; exact h4
    have h7 : |p.2 - R_i.function p.1| ≤ 100 * δ := by
      calc
        |p.2 - R_i.function p.1|
          ≤ |p.2 - R_j.function p.1| + |R_j.function p.1 - R_i.function p.1| := by
            exact abs_sub_le p.2 (R_j.function p.1) (R_i.function p.1)
        _ ≤ δ + 7 * δ := by gcongr
        _ = 8 * δ := by ring
        _ ≤ 100 * δ := by linarith [hδ]
    have h10 : |p.2 - U.function p.1| ≤ 100 * δ := by
      have h11 : U.function p.1 = R_i.function p.1 := by rfl
      rw [h11] <;> exact h7
    exact ⟨h3, h10⟩
  exact ⟨U, hU_family, by simp [h_i_sub, h_j_sub]⟩

/-! ### Derivative upper bound lemma -/

/-- If function difference is bounded by 2λδ on [θ₀, θ₀+L], then derivative
difference at θ₀ is bounded by 10λ√(δt). -/
lemma derivative_upper_bound
    (f g : C2Function)
    (θ₀ : UnitPoint)
    (δ t lambda : ℝ)
    (hδ : 0 < δ)
    (ht : 0 < t)
    (hlambda : 100 ≤ lambda)
    (hdist : c2Distance f g ≤ 6 * t)
    (hval : |f θ₀ - g θ₀| ≤ 2 * δ)
    (L : ℝ)
    (hL : L = Real.sqrt (δ / t) / 4)
    (hθ₁_in : (θ₀ : ℝ) + L ≤ 1)
    (hbound : ∀ (x : UnitPoint), (θ₀ : ℝ) ≤ (x : ℝ) → (x : ℝ) ≤ (θ₀ : ℝ) + L →
        |f x - g x| ≤ 2 * lambda * δ) :
    |f.firstDeriv θ₀ - g.firstDeriv θ₀| ≤ 10 * lambda * Real.sqrt (δ * t) := by
  set h_ext : ℝ → ℝ := f.extension - g.extension with h_ext_def
  set h_ext' : ℝ → ℝ := deriv h_ext with h_ext'_def
  have hcd_f : ContDiff ℝ 2 f.extension := C2Function.extension_contDiff f
  have hcd_g : ContDiff ℝ 2 g.extension := C2Function.extension_contDiff g
  have hcd : ContDiff ℝ 2 h_ext := ContDiff.sub hcd_f hcd_g
  have h_diff1 : Differentiable ℝ h_ext := hcd.differentiable (by norm_num)
  have h_diff2 : Differentiable ℝ h_ext' := hcd.differentiable_deriv_two
  let θ₁ : ℝ := (θ₀ : ℝ) + L
  have hL_pos : 0 < L := by rw [hL] <;> positivity
  have hθ₀_lt_θ₁ : (θ₀ : ℝ) < θ₁ := by dsimp only [θ₁]; linarith [hL_pos]
  have hθ₁_in_interval : θ₁ ∈ Set.Icc (0 : ℝ) 1 := by
    dsimp only [θ₁]; constructor
    · linarith [θ₀.prop.1]
    · exact hθ₁_in
  have h_deriv1 : ∀ (x : ℝ), h_ext' x = deriv f.extension x - deriv g.extension x := by
    intro x
    have hdf : DifferentiableAt ℝ f.extension x := hcd_f.differentiable (by norm_num) x
    have hdg : DifferentiableAt ℝ g.extension x := hcd_g.differentiable (by norm_num) x
    have h : deriv h_ext x = deriv f.extension x - deriv g.extension x := by
      rw [h_ext_def, deriv_sub hdf hdg]
    exact h
  have h_deriv2 : ∀ (x : ℝ), deriv h_ext' x = deriv (deriv f.extension) x - deriv (deriv g.extension) x := by
    intro x
    have hdf' : DifferentiableAt ℝ (deriv f.extension) x := hcd_f.differentiable_deriv_two x
    have hdg' : DifferentiableAt ℝ (deriv g.extension) x := hcd_g.differentiable_deriv_two x
    have h_eq1 : h_ext' = deriv f.extension - deriv g.extension := by funext y; exact h_deriv1 y
    rw [h_eq1, deriv_sub hdf' hdg']
  have h_secondDeriv_bound : ∀ (x : ℝ), x ∈ Set.Icc (0 : ℝ) 1 →
      |deriv h_ext' x| ≤ 6 * t := by
    intro x hx
    have h_x_val : x ∈ Kakeya.Cinematic.unitInterval := hx
    rw [h_deriv2 x]
    have h2 : deriv (deriv f.extension) x = f.secondDeriv ⟨x, h_x_val⟩ :=
      C2Function.secondDeriv_extension_eq_secondDeriv f ⟨x, h_x_val⟩
    have h3 : deriv (deriv g.extension) x = g.secondDeriv ⟨x, h_x_val⟩ :=
      C2Function.secondDeriv_extension_eq_secondDeriv g ⟨x, h_x_val⟩
    rw [h2, h3]
    have h4 : |f.secondDeriv ⟨x, h_x_val⟩ - g.secondDeriv ⟨x, h_x_val⟩| ≤ c2Distance f g :=
      abs_secondDeriv_sub_le_c2Distance f g ⟨x, h_x_val⟩
    linarith [hdist]
  have h_lipschitz : ∀ (x y : ℝ), x ∈ Set.Icc (0 : ℝ) 1 → y ∈ Set.Icc (0 : ℝ) 1 →
      |h_ext' x - h_ext' y| ≤ 6 * t * |x - y| := by
    intro x y hx hy
    have h_main : ‖h_ext' x - h_ext' y‖ ≤ 6 * t * ‖x - y‖ :=
      Convex.norm_image_sub_le_of_norm_deriv_le
        (s := Set.Icc (0 : ℝ) 1) (f := h_ext') (C := 6 * t) (x := y) (y := x)
        (fun z _ => h_diff2 z)
        (fun z hz => by simpa [Real.norm_eq_abs] using h_secondDeriv_bound z hz)
        (convex_Icc 0 1) hy hx
    simpa [Real.norm_eq_abs] using h_main
  have h_deriv_at_θ₀ : h_ext' (θ₀ : ℝ) = f.firstDeriv θ₀ - g.firstDeriv θ₀ := by
    rw [h_deriv1 (θ₀ : ℝ)]
    have h1 : deriv f.extension (θ₀ : ℝ) = f.firstDeriv θ₀ :=
      C2Function.deriv_extension_eq_firstDeriv f θ₀
    have h2 : deriv g.extension (θ₀ : ℝ) = g.firstDeriv θ₀ :=
      C2Function.deriv_extension_eq_firstDeriv g θ₀
    rw [h1, h2]
  have h_val_at_θ₀ : h_ext (θ₀ : ℝ) = f θ₀ - g θ₀ := by
    have h1 : h_ext (θ₀ : ℝ) = f.extension (θ₀ : ℝ) - g.extension (θ₀ : ℝ) := by
      simp [h_ext_def]
    rw [h1]
    have h2 : f.extension (θ₀ : ℝ) = f θ₀ := C2Function.extension_eq_value f θ₀
    have h3 : g.extension (θ₀ : ℝ) = g θ₀ := C2Function.extension_eq_value g θ₀
    rw [h2, h3] <;> rfl
  by_contra h
  have h_deriv_large : |h_ext' (θ₀ : ℝ)| > 10 * lambda * Real.sqrt (δ * t) := by
    have h' : |f.firstDeriv θ₀ - g.firstDeriv θ₀| > 10 * lambda * Real.sqrt (δ * t) :=
      lt_of_not_ge h
    rw [h_deriv_at_θ₀] at * <;> exact h'
  have h_sqrt_pos : 0 < Real.sqrt (δ * t) := Real.sqrt_pos.mpr (mul_pos hδ ht)
  have h_tsqrt : t * Real.sqrt (δ / t) = Real.sqrt (δ * t) := by
    have h1 : 0 ≤ t := by linarith
    have h2 : 0 ≤ t * Real.sqrt (δ / t) := by positivity
    have h3 : (t * Real.sqrt (δ / t)) ^ 2 = (Real.sqrt (δ * t)) ^ 2 := by
      calc
        (t * Real.sqrt (δ / t)) ^ 2
          = t ^ 2 * (δ / t) := by ring_nf; rw [Real.sq_sqrt (by positivity)] <;> field_simp [ht.ne'] <;> ring
        _ = δ * t := by field_simp [ht.ne'] <;> ring
        _ = (Real.sqrt (δ * t)) ^ 2 := by rw [Real.sq_sqrt (by positivity)]
    nlinarith [h2]
  have h_sqrt_mul : Real.sqrt (δ * t) * Real.sqrt (δ / t) = δ := by
    have h_pos1 : 0 ≤ δ * t := by positivity
    have h_pos2 : 0 ≤ δ / t := by positivity
    have h : Real.sqrt (δ * t) * Real.sqrt (δ / t) = Real.sqrt ((δ * t) * (δ / t)) := by
      rw [← Real.sqrt_mul h_pos1] <;> rfl
    rw [h]
    have h2 : (δ * t) * (δ / t) = δ ^ 2 := by
      field_simp [ht.ne'] <;> ring
    rw [h2, Real.sqrt_sq_eq_abs, abs_of_pos hδ]
  have h_deriv_lower_bound : ∀ (x : ℝ), x ∈ Set.Icc (θ₀ : ℝ) θ₁ →
      |h_ext' x| > 9 * lambda * Real.sqrt (δ * t) := by
    intro x hx
    have h_x_in : x ∈ Set.Icc (0 : ℝ) 1 := by
      constructor <;> linarith [θ₀.prop.1, hθ₁_in, hx.1, hx.2]
    have h_θ₀_in : (θ₀ : ℝ) ∈ Set.Icc (0 : ℝ) 1 := ⟨θ₀.prop.1, θ₀.prop.2⟩
    have h5 : |h_ext' x - h_ext' (θ₀ : ℝ)| ≤ 6 * t * |x - (θ₀ : ℝ)| :=
      h_lipschitz x (θ₀ : ℝ) h_x_in h_θ₀_in
    have h6 : |x - (θ₀ : ℝ)| ≤ L := by
      have h7 : (θ₀ : ℝ) ≤ x := hx.1
      have h8 : x ≤ θ₁ := hx.2
      have h9 : 0 ≤ x - (θ₀ : ℝ) := by linarith
      rw [abs_of_nonneg h9]
      dsimp only [θ₁] at h8 <;> linarith
    have h10 : 6 * t * |x - (θ₀ : ℝ)| ≤ 6 * t * L := by gcongr <;> linarith
    have h_rev : |h_ext' (θ₀ : ℝ)| ≤ |h_ext' x| + |h_ext' x - h_ext' (θ₀ : ℝ)| := by
      calc
        |h_ext' (θ₀ : ℝ)|
          = |h_ext' x + (h_ext' (θ₀ : ℝ) - h_ext' x)| := by ring_nf
        _ ≤ |h_ext' x| + |h_ext' (θ₀ : ℝ) - h_ext' x| := by
          exact abs_add_le (h_ext' x) (h_ext' (θ₀ : ℝ) - h_ext' x)
        _ = |h_ext' x| + |h_ext' x - h_ext' (θ₀ : ℝ)| := by rw [abs_sub_comm]
    have h11 : |h_ext' (θ₀ : ℝ)| ≤ |h_ext' x| + 6 * t * L := by
      calc
        |h_ext' (θ₀ : ℝ)| ≤ |h_ext' x| + |h_ext' x - h_ext' (θ₀ : ℝ)| := h_rev
        _ ≤ |h_ext' x| + 6 * t * L := by gcongr <;> linarith
    have h12 : |h_ext' x| ≥ |h_ext' (θ₀ : ℝ)| - 6 * t * L := by linarith
    have h13 : 6 * t * L = (3 / 2 : ℝ) * Real.sqrt (δ * t) := by
      rw [hL]
      have h14 : 6 * t * (Real.sqrt (δ / t) / 4) = (3 / 2 : ℝ) * (t * Real.sqrt (δ / t)) := by ring
      rw [h14, h_tsqrt] <;> ring
    rw [h13] at h12
    have h15 : |h_ext' (θ₀ : ℝ)| - (3 / 2 : ℝ) * Real.sqrt (δ * t) >
        9 * lambda * Real.sqrt (δ * t) := by
      have h16 : 0 < Real.sqrt (δ * t) := h_sqrt_pos
      nlinarith
    linarith
  have h_cont : ContinuousOn h_ext (Set.Icc (θ₀ : ℝ) θ₁) :=
    h_diff1.continuous.continuousOn
  have h_deriv_at : ∀ x ∈ Set.Ioo (θ₀ : ℝ) θ₁, HasDerivAt h_ext (h_ext' x) x := by
    intro x _
    exact (h_diff1 x).hasDerivAt
  rcases exists_hasDerivAt_eq_slope (hab := hθ₀_lt_θ₁) (hfc := h_cont) (hff' := h_deriv_at)
    with ⟨c, hc, h_eq⟩
  have hc_in_Icc : c ∈ Set.Icc (θ₀ : ℝ) θ₁ := ⟨hc.1.le, hc.2.le⟩
  have h_deriv_c_large : |h_ext' c| > 9 * lambda * Real.sqrt (δ * t) :=
    h_deriv_lower_bound c hc_in_Icc
  have h_eq2 : h_ext θ₁ - h_ext (θ₀ : ℝ) = h_ext' c * (θ₁ - (θ₀ : ℝ)) := by
    have hne : (θ₁ - (θ₀ : ℝ)) ≠ 0 := by linarith
    have h : h_ext' c = (h_ext θ₁ - h_ext (θ₀ : ℝ)) / (θ₁ - (θ₀ : ℝ)) := h_eq
    field_simp [hne] at h ⊢ <;> linarith
  have h_diff_large : |h_ext θ₁ - h_ext (θ₀ : ℝ)| > (9 / 4 : ℝ) * lambda * δ := by
    have h17 : |h_ext θ₁ - h_ext (θ₀ : ℝ)| = |h_ext' c| * (θ₁ - (θ₀ : ℝ)) := by
      rw [h_eq2]
      have h18 : 0 < θ₁ - (θ₀ : ℝ) := by linarith
      rw [abs_mul, abs_of_pos h18] <;> ring
    rw [h17]
    have h19 : θ₁ - (θ₀ : ℝ) = L := by dsimp only [θ₁] <;> ring
    rw [h19]
    have h20 : Real.sqrt (δ * t) * L = δ / 4 := by
      rw [hL] <;> linarith [h_sqrt_mul]
    nlinarith [h_deriv_c_large, hL_pos, h20]
  have h24 : |h_ext θ₁ - h_ext (θ₀ : ℝ)| ≤ |h_ext θ₁| + |h_ext (θ₀ : ℝ)| :=
    abs_sub _ _
  have h25 : |h_ext (θ₀ : ℝ)| ≤ 2 * δ := by
    rw [h_val_at_θ₀] <;> exact hval
  have h_val_θ₁_large : |h_ext θ₁| > 2 * lambda * δ := by
    nlinarith [h_diff_large, h24, h25, hδ, hlambda]
  let x₁ : UnitPoint := ⟨θ₁, hθ₁_in_interval⟩
  have h_x₁_val : h_ext θ₁ = f x₁ - g x₁ := by
    have h26 : h_ext θ₁ = f.extension θ₁ - g.extension θ₁ := by simp [h_ext_def]
    rw [h26]
    have h27 : f.extension θ₁ = f x₁ := C2Function.extension_eq_value f x₁
    have h28 : g.extension θ₁ = g x₁ := C2Function.extension_eq_value g x₁
    rw [h27, h28] <;> rfl
  rw [h_x₁_val] at h_val_θ₁_large
  have h_contra : |f x₁ - g x₁| ≤ 2 * lambda * δ :=
    hbound x₁ (by simp [x₁, θ₁] <;> linarith) (by simp [x₁, θ₁] <;> linarith)
  linarith

/-! ### Main theorem assembly -/

theorem incomparable_rectangles_packing_bound :
    RectanglePackingStatement := by
  intro K hK
  use 42
  constructor
  · norm_num
  · intro family _hCurv I hI delta t lambda hdelta hdt ht hlam center R hCenters hOver hIncomp hdist U hUcont
    let half : Fin R.card → Set (UnitPoint × ℝ) :=
      fun i => (R.rectangle i).halfCarrier
    have h_half_mble : ∀ i : Fin R.card, MeasurableSet (half i) := by
      intro i; exact mble_verticalNeighborhoodOn _ _ _
    have h_half_sub : ∀ i : Fin R.card, half i ⊆ U.carrier := by
      intro i
      have h1 : half i ⊆ (R.rectangle i).carrier :=
        (R.rectangle i).halfCarrier_subset_carrier
      exact h1.trans (hUcont i)
    have h_area_half : ∀ i : Fin R.card,
        volume (half i) = ENNReal.ofReal (delta * Real.sqrt (delta / t)) := by
      intro i
      rw [(R.rectangle i).volume_halfCarrier hdelta.le, (R.rectangle i).interval_length]
      <;> ring
    have h_area_U : volume U.carrier =
        ENNReal.ofReal (2 * lambda * delta * Real.sqrt (lambda * delta / t)) :=
      U.volume_containing hdelta.le (show 0 ≤ lambda by linarith)
    /- KEY BOUNDED-OVERLAP STATEMENT -/
    have h_mult : ∀ (p : UnitPoint × ℝ), p ∈ U.carrier →
        (∑ i ∈ Finset.univ, (half i).indicator (fun _ => (1 : ENNReal)) p) ≤
          ENNReal.ofReal (21 * lambda) := by
      intro p hp
      let θ₀ : UnitPoint := p.1
      let y₀ : ℝ := p.2
      let S : Finset (Fin R.card) := Finset.univ.filter (fun i => p ∈ half i)
      have h_sum_eq : ∑ i ∈ Finset.univ, (half i).indicator (fun _ => (1 : ENNReal)) p =
          (S.card : ENNReal) := by
        rw [sum_indicator_eq_card]
        <;> rfl
      rw [h_sum_eq]
      by_cases hS_empty : S = ∅
      · rw [hS_empty]
        simp
        <;> positivity
      have hS_nonempty : S.Nonempty := Finset.nonempty_iff_ne_empty.mpr hS_empty
      let i₀ := Finset.min' S hS_nonempty
      have hi₀_in : i₀ ∈ S := Finset.min'_mem S hS_nonempty
      let f : Fin R.card → C2Function := fun i => (R.rectangle i).function
      let D : Fin R.card → ℝ := fun i => (f i).firstDeriv θ₀
      let d : ℝ := Real.sqrt (delta * t)
      have ht_pos : 0 < t := by linarith [hdelta, hdt]
      have hd_pos : 0 < d := Real.sqrt_pos.mpr (mul_pos hdelta ht_pos)
      have hθ₀_half : ∀ i ∈ S, θ₀ ∈ (R.rectangle i).interval.half.carrier := by
        intro i hi
        have h : p ∈ half i := (Finset.mem_filter.mp hi).2
        exact h.1
      have hy₀ : ∀ i ∈ S, |y₀ - f i θ₀| ≤ delta := by
        intro i hi
        have h : p ∈ half i := (Finset.mem_filter.mp hi).2
        exact h.2
      have hdist6 : ∀ i j, c2Distance (f i) (f j) ≤ 6 * t := by
        intro i j
        have h1 : c2Distance (f i) center ≤ 3 * t := by
          have h1a : c2Distance center (f i) ≤ 3 * t := hdist i
          have h_sym : c2Distance (f i) center = c2Distance center (f i) := by
            rw [c2Distance_eq_dist, c2Distance_eq_dist, dist_comm]
          rw [h_sym]; exact h1a
        have h2 : c2Distance center (f j) ≤ 3 * t := hdist j
        have h3 : c2Distance (f i) (f j) ≤ c2Distance (f i) center + c2Distance center (f j) := by
          have h4 : c2Distance (f i) (f j) = dist (f i) (f j) := c2Distance_eq_dist (f i) (f j)
          have h5 : c2Distance (f i) center = dist (f i) center := c2Distance_eq_dist (f i) center
          have h6 : c2Distance center (f j) = dist center (f j) := c2Distance_eq_dist center (f j)
          rw [h4, h5, h6]
          exact dist_triangle (f i) center (f j)
        linarith
      have hval2 : ∀ i ∈ S, ∀ j ∈ S, |f i θ₀ - f j θ₀| ≤ 2 * delta := by
        intro i hi j hj
        have hi' : |f i θ₀ - y₀| ≤ delta := by
          have h : |y₀ - f i θ₀| ≤ delta := hy₀ i hi
          have h' : |f i θ₀ - y₀| = |y₀ - f i θ₀| := by rw [abs_sub_comm]
          rw [h']; exact h
        have hj' : |y₀ - f j θ₀| ≤ delta := hy₀ j hj
        calc
          |f i θ₀ - f j θ₀| ≤ |f i θ₀ - y₀| + |y₀ - f j θ₀| := by
            exact abs_sub_le (f i θ₀) y₀ (f j θ₀)
          _ ≤ delta + delta := by gcongr
          _ = 2 * delta := by ring
      let L : ℝ := Real.sqrt (delta / t) / 4
      have hθ₁_in : (θ₀ : ℝ) + L ≤ 1 := by
        have h1 : θ₀ ∈ (R.rectangle i₀).interval.half.carrier := hθ₀_half i₀ hi₀_in
        have h2 : (θ₀ : ℝ) ≤ (R.rectangle i₀).interval.half.right := h1.2
        have h_right_up : (R.rectangle i₀).interval.right ≤ 1 := (R.rectangle i₀).interval.right_mem.2
        have h_len : (R.rectangle i₀).interval.length = Real.sqrt (delta / t) :=
          (R.rectangle i₀).interval_length
        have h3 : (R.rectangle i₀).interval.half.right =
            (R.rectangle i₀).interval.right - (R.rectangle i₀).interval.length / 4 := by
          rfl
        rw [h3, h_len] at h2
        have h4 : (θ₀ : ℝ) + Real.sqrt (delta / t) / 4 ≤ (R.rectangle i₀).interval.right := by linarith
        have h5 : (θ₀ : ℝ) + L ≤ (R.rectangle i₀).interval.right := by
          have hL_eq : L = Real.sqrt (delta / t) / 4 := by rfl
          rw [hL_eq]; exact h4
        linarith [h_right_up, h5]
      have h_x_in_interval : ∀ i ∈ S, ∀ (x : UnitPoint),
          (θ₀ : ℝ) ≤ (x : ℝ) → (x : ℝ) ≤ (θ₀ : ℝ) + L →
          x ∈ (R.rectangle i).interval.carrier := by
        intro i hi x hx1 hx2
        have h1 : θ₀ ∈ (R.rectangle i).interval.half.carrier := hθ₀_half i hi
        have h_left : (R.rectangle i).interval.left ≤ (x : ℝ) := by
          have h2 : (R.rectangle i).interval.half.left ≤ (θ₀ : ℝ) := h1.1
          have h3 : (R.rectangle i).interval.left ≤ (R.rectangle i).interval.half.left := by
            simp [ParameterInterval.half] <;> linarith [(R.rectangle i).interval.length_nonneg]
          linarith
        have h_right : (x : ℝ) ≤ (R.rectangle i).interval.right := by
          have h2 : (θ₀ : ℝ) ≤ (R.rectangle i).interval.half.right := h1.2
          have h4 : (R.rectangle i).interval.half.right =
              (R.rectangle i).interval.right - (R.rectangle i).interval.length / 4 := by rfl
          have h5 : (R.rectangle i).interval.length = Real.sqrt (delta / t) :=
            (R.rectangle i).interval_length
          rw [h4, h5] at h2
          have h6 : (x : ℝ) ≤ (θ₀ : ℝ) + Real.sqrt (delta / t) / 4 := hx2
          linarith
        exact ⟨h_left, h_right⟩
      have hbound : ∀ i ∈ S, ∀ j ∈ S, ∀ (x : UnitPoint),
          (θ₀ : ℝ) ≤ (x : ℝ) → (x : ℝ) ≤ (θ₀ : ℝ) + L →
          |f i x - f j x| ≤ 2 * lambda * delta := by
        intro i hi j hj x hx1 hx2
        have hxi : x ∈ (R.rectangle i).interval.carrier := h_x_in_interval i hi x hx1 hx2
        have hxj : x ∈ (R.rectangle j).interval.carrier := h_x_in_interval j hj x hx1 hx2
        have h_i_car : (x, f i x) ∈ (R.rectangle i).carrier := by
          have h_zero : |f i x - f i x| = 0 := by simp
          exact ⟨hxi, by rw [h_zero] <;> linarith [hdelta]⟩
        have h_j_car : (x, f j x) ∈ (R.rectangle j).carrier := by
          have h_zero : |f j x - f j x| = 0 := by simp
          exact ⟨hxj, by rw [h_zero] <;> linarith [hdelta]⟩
        have h_i_U : (x, f i x) ∈ U.carrier := hUcont i h_i_car
        have h_j_U : (x, f j x) ∈ U.carrier := hUcont j h_j_car
        have h_i_bound : |f i x - U.function x| ≤ lambda * delta := h_i_U.2
        have h_j_bound : |f j x - U.function x| ≤ lambda * delta := h_j_U.2
        have h_j_bound' : |U.function x - f j x| ≤ lambda * delta := by
          have h : |U.function x - f j x| = |f j x - U.function x| := by rw [abs_sub_comm]
          rw [h]; exact h_j_bound
        have h_tri : |f i x - f j x| ≤ |f i x - U.function x| + |U.function x - f j x| := by
          calc
            |f i x - f j x| = |(f i x - U.function x) + (U.function x - f j x)| := by ring_nf
            _ ≤ |f i x - U.function x| + |U.function x - f j x| := by
              exact abs_add_le (f i x - U.function x) (U.function x - f j x)
        linarith [h_i_bound, h_j_bound', h_tri]
      have h_upper : ∀ i ∈ S, ∀ j ∈ S, |D i - D j| ≤ 10 * lambda * d := by
        intro i hi j hj
        exact derivative_upper_bound (f i) (f j) θ₀ delta t lambda hdelta ht_pos hlam
          (hdist6 i j) (hval2 i hi j hj) L rfl hθ₁_in (hbound i hi j hj)
      have h_lower : ∀ i ∈ S, ∀ j ∈ S, i ≠ j → |D i - D j| > d := by
        intro i hi j hj hne
        by_contra h
        have h' : |D i - D j| ≤ d := by linarith
        have h_comp : (R.rectangle i).AreLambdaComparable (R.rectangle j) family 100 :=
          derivative_lower_bound hdelta ht_pos hK hI
            (hOver i) (hOver j)
            (hθ₀_half i hi) (hθ₀_half j hj)
            (hCenters i) (hdist6 i j) (hval2 i hi j hj) h'
        have h_incomp : (R.rectangle i).AreLambdaIncomparable (R.rectangle j) family 100 :=
          hIncomp i j hne
        exact h_incomp h_comp
      let a : ℝ := D i₀ - 10 * lambda * d
      let b : ℝ := D i₀ + 10 * lambda * d
      have hab : a ≤ b := by
        dsimp only [a, b]
        have h : 0 ≤ 20 * lambda * d := by positivity
        linarith
      let S' : Finset ℝ := Finset.image D S
      have hS'_sub : ∀ x ∈ S', x ∈ Set.Icc a b := by
        intro x hx
        obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
        have h : |D i - D i₀| ≤ 10 * lambda * d := h_upper i hi i₀ hi₀_in
        have h5 : a ≤ D i := by
          have h6 := (abs_le.mp h).1
          dsimp only [a] at * <;> linarith
        have h7 : D i ≤ b := by
          have h8 := (abs_le.mp h).2
          dsimp only [b] at * <;> linarith
        exact ⟨h5, h7⟩
      have hS'_sep : ∀ x ∈ S', ∀ y ∈ S', x ≠ y → |x - y| > d := by
        intro x hx y hy hxy
        obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
        obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hy
        have hne : i ≠ j := by
          intro h
          rw [h] at hxy
          simp at hxy
        exact h_lower i hi j hj hne
      have h_inj : Set.InjOn D S := by
        intro i hi j hj h
        by_contra hne
        have h_sep : |D i - D j| > d := h_lower i hi j hj hne
        have h_eq : |D i - D j| = 0 := by
          have h' : D i = D j := h
          rw [h'] <;> simp
        linarith [hd_pos, h_sep, h_eq]
      have h_card : S'.card = S.card :=
        Finset.card_image_of_injOn h_inj
      have h_pack2 : (S'.card : ℝ) ≤ (b - a) / d + 1 :=
        point_packing_bound hd_pos hab S' hS'_sub hS'_sep
      have h_ba : b - a = 20 * lambda * d := by
        dsimp only [a, b] <;> ring
      rw [h_card] at h_pack2
      rw [h_ba] at h_pack2
      have h_final : (S.card : ℝ) ≤ 21 * lambda := by
        have h9 : (S.card : ℝ) ≤ 20 * lambda + 1 := by
          have h10 : (20 * lambda * d) / d = 20 * lambda := by
            field_simp [hd_pos.ne'] <;> ring
          rw [h10] at h_pack2
          exact h_pack2
        have h11 : 20 * lambda + 1 ≤ 21 * lambda := by
          have h12 : 1 ≤ lambda := by linarith
          linarith
        linarith
      have h_ennreal : (S.card : ENNReal) ≤ ENNReal.ofReal (21 * lambda) := by
        have h13 : (S.card : ENNReal) = ENNReal.ofReal (S.card : ℝ) := by
          norm_cast
        rw [h13]
        have h14 : 0 ≤ (S.card : ℝ) := by positivity
        exact ENNReal.ofReal_le_ofReal h_final
      exact h_ennreal
    /- Apply bounded overlap -/
    have hU_mble : MeasurableSet U.carrier :=
      mble_verticalNeighborhoodOn U.function (lambda * delta) U.interval
    have h_half_mble' : ∀ i ∈ Finset.univ, MeasurableSet (half i) := by
      intro i _; exact h_half_mble i
    have h_half_sub' : ∀ i ∈ Finset.univ, half i ⊆ U.carrier := by
      intro i _; exact h_half_sub i
    have h_pack : ∑ i ∈ Finset.univ, volume (half i) ≤
        ENNReal.ofReal (21 * lambda) * volume U.carrier :=
      bounded_overlap_ennreal
        (s := Finset.univ) (A := half) (U := U.carrier)
        hU_mble h_half_mble' h_half_sub'
        (ENNReal.ofReal (21 * lambda)) h_mult
    /- Compute left side -/
    have h_sum : ∑ i ∈ Finset.univ, volume (half i) =
        (R.card : ENNReal) * ENNReal.ofReal (delta * Real.sqrt (delta / t)) := by
      have h4 : ∀ i ∈ Finset.univ, volume (half i) =
          ENNReal.ofReal (delta * Real.sqrt (delta / t)) := by
        intro i _; exact h_area_half i
      rw [Finset.sum_congr rfl h4]
      simp [Finset.sum_const]
    rw [h_sum] at h_pack
    /- Compute right side -/
    have ht_pos : 0 < t := by linarith
    have h_rpow2 : lambda^2 * Real.sqrt lambda = Real.rpow lambda (5 / 2 : ℝ) := by
      have h1 : 0 < lambda := by linarith
      have h2 : Real.sqrt lambda = Real.rpow lambda (1 / 2 : ℝ) :=
        Real.sqrt_eq_rpow lambda
      have h3 : lambda^2 = Real.rpow lambda (2 : ℝ) := by
        simp [Real.rpow_two]
      rw [h3, h2]
      have h4 : Real.rpow lambda (2 : ℝ) * Real.rpow lambda (1 / 2 : ℝ) =
          Real.rpow lambda ((2 : ℝ) + (1 / 2 : ℝ)) := by
        exact (Real.rpow_add h1 (2 : ℝ) (1 / 2 : ℝ)).symm
      rw [h4]
      <;> norm_num
    have h_sqrt_mul : Real.sqrt (lambda * delta / t) =
        Real.sqrt lambda * Real.sqrt (delta / t) := by
      have h1 : 0 ≤ lambda := by linarith
      have h2 : lambda * delta / t = lambda * (delta / t) := by ring
      rw [h2]
      have h3 : Real.sqrt (lambda * (delta / t)) = Real.sqrt lambda * Real.sqrt (delta / t) := by
        exact Real.sqrt_mul h1 (delta / t)
      exact h3
    rw [h_area_U] at h_pack
    rw [h_sqrt_mul] at h_pack
    have h_rhs : ENNReal.ofReal (21 * lambda) *
        ENNReal.ofReal (2 * lambda * delta * (Real.sqrt lambda * Real.sqrt (delta / t))) =
        ENNReal.ofReal (42 * Real.rpow lambda (5 / 2 : ℝ) * delta * Real.sqrt (delta / t)) := by
      have h_nonneg1 : 0 ≤ 21 * lambda := by linarith
      have h_nonneg2 : 0 ≤ 2 * lambda * delta * (Real.sqrt lambda * Real.sqrt (delta / t)) := by positivity
      have h_mul : ENNReal.ofReal (21 * lambda) * ENNReal.ofReal (2 * lambda * delta * (Real.sqrt lambda * Real.sqrt (delta / t))) =
          ENNReal.ofReal ((21 * lambda) * (2 * lambda * delta * (Real.sqrt lambda * Real.sqrt (delta / t)))) := by
        exact Eq.symm (ENNReal.ofReal_mul h_nonneg1)
      rw [h_mul]
      congr 1
      have h5 : (21 * lambda) * (2 * lambda * delta * (Real.sqrt lambda * Real.sqrt (delta / t))) =
          42 * (lambda^2 * Real.sqrt lambda) * delta * Real.sqrt (delta / t) := by ring
      rw [h5, h_rpow2] <;> ring
    rw [h_rhs] at h_pack
    /- Cancel positive factor and conclude -/
    have h_pos : 0 < delta * Real.sqrt (delta / t) := by positivity
    have h_cast : (R.card : ENNReal) = ENNReal.ofReal (R.card : ℝ) := by norm_cast
    have h_combine1 : (R.card : ENNReal) * ENNReal.ofReal (delta * Real.sqrt (delta / t)) =
        ENNReal.ofReal ((R.card : ℝ) * (delta * Real.sqrt (delta / t))) := by
      rw [h_cast]
      rw [←ENNReal.ofReal_mul (by positivity)]
    rw [h_combine1] at h_pack
    have h_rhs_eq : (42 * Real.rpow lambda (5 / 2 : ℝ) * delta * Real.sqrt (delta / t)) =
        (42 * Real.rpow lambda (5 / 2 : ℝ)) * (delta * Real.sqrt (delta / t)) := by ring
    rw [h_rhs_eq] at h_pack
    have h_pack_real : (R.card : ℝ) * (delta * Real.sqrt (delta / t)) ≤
        (42 * Real.rpow lambda (5 / 2 : ℝ)) * (delta * Real.sqrt (delta / t)) := by
      have h_nonneg1 : 0 ≤ (R.card : ℝ) * (delta * Real.sqrt (delta / t)) := by positivity
      have h_nonneg2 : 0 ≤ (42 * Real.rpow lambda (5 / 2 : ℝ)) * (delta * Real.sqrt (delta / t)) := by
        have h1 : 0 ≤ lambda := by linarith
        have h2 : 0 ≤ Real.rpow lambda (5 / 2 : ℝ) := Real.rpow_nonneg h1 _
        positivity
      have h_iff : ENNReal.ofReal ((R.card : ℝ) * (delta * Real.sqrt (delta / t))) ≤
          ENNReal.ofReal ((42 * Real.rpow lambda (5 / 2 : ℝ)) * (delta * Real.sqrt (delta / t))) ↔
          (R.card : ℝ) * (delta * Real.sqrt (delta / t)) ≤
          (42 * Real.rpow lambda (5 / 2 : ℝ)) * (delta * Real.sqrt (delta / t)) := by
        exact ENNReal.ofReal_le_ofReal_iff h_nonneg2
      exact h_iff.mp h_pack
    have h_final_real : (R.card : ℝ) ≤ 42 * Real.rpow lambda (5 / 2 : ℝ) := by
      nlinarith [h_pos]
    exact_mod_cast h_final_real

end Kakeya.Cinematic
