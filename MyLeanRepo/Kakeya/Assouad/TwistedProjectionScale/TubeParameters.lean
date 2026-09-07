import MyLeanRepo.Kakeya.Assouad.Definitions
import MyLeanRepo.Kakeya.Streamlined.Families

/-!
# Tube parameter extraction and c-window pigeonholing

Extracts vertical-chart parameters `(a,b,c,d)` from each tube, where the axis is
`(a + c*z, b + d*z, z)`. Provides coordinate bounds and a pigeonholing lemma for
selecting a narrow `c`-window containing a fixed fraction of tubes.

Whiteprint node: `tube_parameters`.
-/

noncomputable section

open Set Finset

namespace Kakeya.Assouad

/-- Parameters of a tube axis in the vertical chart: axis is `(a + c*z, b + d*z, z)`. -/
structure TubeParams where
  a : ℝ
  b : ℝ
  c : ℝ
  d : ℝ

@[ext]
lemma TubeParams.ext {p q : TubeParams}
    (ha : p.a = q.a) (hb : p.b = q.b)
    (hc : p.c = q.c) (hd : p.d = q.d) :
    p = q := by
  cases p
  cases q
  simp_all

/-- Extract vertical-chart parameters directly from one tube. -/
def tubeParamsOfTube {δ : ℝ} (T : Kakeya.DeltaTube δ) : TubeParams :=
  let base := T.base
  let dir := T.direction
  let dz := dir (2 : Fin 3)
  {
    a := base 0 - base 2 * dir 0 / dz
    b := base 1 - base 2 * dir 1 / dz
    c := dir 0 / dz
    d := dir 1 / dz
  }

/-- Extract vertical-chart parameters from a tube. -/
def tubeParams {δ : ℝ} {F : Kakeya.Streamlined.TubeFamily δ}
    (i : Fin F.card) : TubeParams :=
  tubeParamsOfTube (F.tube i)

/--
The indexed four-parameter Frostman count used in Section 7.

The coordinate box is quantitatively equivalent to a ball in `ℝ⁴`.  Keeping
the index filter explicit preserves tube multiplicity when different modeled
unit segments have the same supporting-line parameters.
-/
def TubeParameterFrostmanBound {δ : ℝ}
    (F : Kakeya.Streamlined.TubeFamily δ) (C : ENNReal) : Prop :=
  ∀ r : ℝ, δ ≤ r → r ≤ 1 →
    ∀ reference : Fin F.card,
      ((Finset.univ.filter fun i : Fin F.card =>
        |(tubeParams i).a - (tubeParams reference).a| ≤ r ∧
        |(tubeParams i).b - (tubeParams reference).b| ≤ r ∧
        |(tubeParams i).c - (tubeParams reference).c| ≤ r ∧
        |(tubeParams i).d - (tubeParams reference).d| ≤ r).card : ENNReal) ≤
          C * Kakeya.realRpowENN r 2 * F.enncard

/-- Each coordinate of a Euclidean vector is bounded by its norm. -/
private lemma coord_le_norm {n : ℕ} (x : EuclideanSpace ℝ (Fin n)) (k : Fin n) :
    |x k| ≤ ‖x‖ := by
  have h2 : ∀ i ∈ Finset.univ, 0 ≤ (x i) ^ 2 := by intro i _; positivity
  have h1 : (x k) ^ 2 ≤ ∑ i : Fin n, (x i) ^ 2 :=
    Finset.single_le_sum h2 (Finset.mem_univ k)
  have h_sum_nonneg : 0 ≤ ∑ i : Fin n, (x i) ^ 2 := by positivity
  have h3 : ‖x‖ ^ 2 = ∑ i : Fin n, (x i) ^ 2 := by
    have h4 : ‖x‖ = Real.sqrt (∑ i : Fin n, (x i) ^ 2) := by
      simp [EuclideanSpace.norm_eq]
    rw [h4, Real.sq_sqrt h_sum_nonneg]
  have h4 : (x k) ^ 2 ≤ ‖x‖ ^ 2 := by
    rw [h3]; exact h1
  have h5 : |x k| ^ 2 = (x k) ^ 2 := by rw [sq_abs]
  have h6 : |x k| ^ 2 ≤ ‖x‖ ^ 2 := by
    rw [h5]; exact h4
  have h7 : |(|x k|)| ≤ |(‖x‖)| := sq_le_sq.mp h6
  have h8 : |(|x k|)| = |x k| := by simp
  have h9 : |(‖x‖)| = ‖x‖ := by simp [abs_of_nonneg (show 0 ≤ ‖x‖ from by positivity)]
  rw [h8, h9] at h7
  exact h7

/-- Bounds on `c` and `d` from the vertical chart condition. -/
lemma tubeParams_cd_bounds {δ : ℝ} {F : Kakeya.Streamlined.TubeFamily δ}
    (hvert : IsInVerticalChart F) (i : Fin F.card) :
    |(tubeParams i).c| ≤ 2 ∧ |(tubeParams i).d| ≤ 2 := by
  let T := F.tube i
  let dir := T.direction
  have hdir_unit : ‖dir‖ = 1 := T.direction_unit
  have hdz : (1 / 2 : ℝ) ≤ |dir (2 : Fin 3)| := hvert i
  have hdir_coord : ∀ k : Fin 3, |dir k| ≤ 1 := by
    intro k
    have h : |dir k| ≤ ‖dir‖ := coord_le_norm dir k
    rw [hdir_unit] at h; exact h
  have h_c : |(tubeParams i).c| ≤ 2 := by
    dsimp only [tubeParams, tubeParamsOfTube]
    have hdiv : |dir 0 / dir (2 : Fin 3)| = |dir 0| / |dir (2 : Fin 3)| := by
      rw [abs_div]
    rw [hdiv]
    have h1 : |dir 0| ≤ 1 := hdir_coord 0
    have h2 : 0 < |dir (2 : Fin 3)| := by linarith
    calc
      |dir 0| / |dir (2 : Fin 3)| ≤ 1 / |dir (2 : Fin 3)| := by
        gcongr
      _ ≤ 1 / (1 / 2 : ℝ) := by gcongr
      _ = 2 := by norm_num
  have h_d : |(tubeParams i).d| ≤ 2 := by
    dsimp only [tubeParams, tubeParamsOfTube]
    have hdiv : |dir 1 / dir (2 : Fin 3)| = |dir 1| / |dir (2 : Fin 3)| := by
      rw [abs_div]
    rw [hdiv]
    have h1 : |dir 1| ≤ 1 := hdir_coord 1
    have h2 : 0 < |dir (2 : Fin 3)| := by linarith
    calc
      |dir 1| / |dir (2 : Fin 3)| ≤ 1 / |dir (2 : Fin 3)| := by gcongr
      _ ≤ 1 / (1 / 2 : ℝ) := by gcongr
      _ = 2 := by norm_num
  exact ⟨h_c, h_d⟩

/-- Bounds on `a` and `b` from bounded base and vertical chart. -/
lemma tubeParams_ab_bounds {δ : ℝ} {F : Kakeya.Streamlined.TubeFamily δ}
    (hbase : HasBoundedBase F 4) (hvert : IsInVerticalChart F)
    (i : Fin F.card) :
    |(tubeParams i).a| ≤ 12 ∧ |(tubeParams i).b| ≤ 12 := by
  let T := F.tube i
  let base := T.base
  let dir := T.direction
  have hdir_unit : ‖dir‖ = 1 := T.direction_unit
  have hdz : (1 / 2 : ℝ) ≤ |dir (2 : Fin 3)| := hvert i
  have hbase_norm : ‖base‖ ≤ 4 := hbase i
  have hbase_coord : ∀ k : Fin 3, |base k| ≤ 4 := by
    intro k
    have h : |base k| ≤ ‖base‖ := coord_le_norm base k
    linarith
  have hdir_coord : ∀ k : Fin 3, |dir k| ≤ 1 := by
    intro k
    have h : |dir k| ≤ ‖dir‖ := coord_le_norm dir k
    rw [hdir_unit] at h; exact h
  have h_a : |(tubeParams i).a| ≤ 12 := by
    dsimp only [tubeParams, tubeParamsOfTube]
    have h_b0 : |base 0| ≤ 4 := hbase_coord 0
    have h_b2 : |base 2| ≤ 4 := hbase_coord 2
    have h_d0 : |dir 0| ≤ 1 := hdir_coord 0
    have h_pos : 0 < |dir (2 : Fin 3)| := by linarith
    have h1 : |base 2 * dir 0 / dir (2 : Fin 3)| =
        |base 2| * |dir 0| / |dir (2 : Fin 3)| := by
      rw [abs_div, abs_mul]
    have h2 : |base 2| * |dir 0| ≤ 4 := by
      have h21 : |base 2| * |dir 0| ≤ 4 * |dir 0| :=
        mul_le_mul_of_nonneg_right h_b2 (abs_nonneg _)
      have h22 : 4 * |dir 0| ≤ 4 := by
        have h23 : |dir 0| ≤ 1 := h_d0
        nlinarith
      linarith
    have h3 : |base 2| * |dir 0| / |dir (2 : Fin 3)| ≤ 4 / |dir (2 : Fin 3)| :=
      div_le_div_of_nonneg_right h2 h_pos.le
    have h4 : |base 0 - base 2 * dir 0 / dir (2 : Fin 3)| ≤
        |base 0| + |base 2 * dir 0 / dir (2 : Fin 3)| := abs_sub _ _
    rw [h1] at h4
    have h5 : |base 0| + |base 2| * |dir 0| / |dir (2 : Fin 3)| ≤
        4 + 4 / |dir (2 : Fin 3)| := by linarith
    have h6 : 4 / |dir (2 : Fin 3)| ≤ 8 := by
      have h7 : |dir (2 : Fin 3)| ≥ 1 / 2 := hdz
      calc 4 / |dir (2 : Fin 3)| ≤ 4 / (1 / 2 : ℝ) := by gcongr
        _ = 8 := by norm_num
    linarith
  have h_b : |(tubeParams i).b| ≤ 12 := by
    dsimp only [tubeParams, tubeParamsOfTube]
    have h_b1 : |base 1| ≤ 4 := hbase_coord 1
    have h_b2 : |base 2| ≤ 4 := hbase_coord 2
    have h_d1 : |dir 1| ≤ 1 := hdir_coord 1
    have h_pos : 0 < |dir (2 : Fin 3)| := by linarith
    have h1 : |base 2 * dir 1 / dir (2 : Fin 3)| =
        |base 2| * |dir 1| / |dir (2 : Fin 3)| := by
      rw [abs_div, abs_mul]
    have h2 : |base 2| * |dir 1| ≤ 4 := by
      have h21 : |base 2| * |dir 1| ≤ 4 * |dir 1| :=
        mul_le_mul_of_nonneg_right h_b2 (abs_nonneg _)
      have h22 : 4 * |dir 1| ≤ 4 := by
        have h23 : |dir 1| ≤ 1 := h_d1
        nlinarith
      linarith
    have h3 : |base 2| * |dir 1| / |dir (2 : Fin 3)| ≤ 4 / |dir (2 : Fin 3)| :=
      div_le_div_of_nonneg_right h2 h_pos.le
    have h4 : |base 1 - base 2 * dir 1 / dir (2 : Fin 3)| ≤
        |base 1| + |base 2 * dir 1 / dir (2 : Fin 3)| := abs_sub _ _
    rw [h1] at h4
    have h5 : |base 1| + |base 2| * |dir 1| / |dir (2 : Fin 3)| ≤
        4 + 4 / |dir (2 : Fin 3)| := by linarith
    have h6 : 4 / |dir (2 : Fin 3)| ≤ 8 := by
      have h7 : |dir (2 : Fin 3)| ≥ 1 / 2 := hdz
      calc 4 / |dir (2 : Fin 3)| ≤ 4 / (1 / 2 : ℝ) := by gcongr
        _ = 8 := by norm_num
    linarith
  exact ⟨h_a, h_b⟩

/-- Full bounds on all tube parameters. -/
lemma tubeParams_bounds {δ : ℝ} {F : Kakeya.Streamlined.TubeFamily δ}
    (hbase : HasBoundedBase F 4) (hvert : IsInVerticalChart F)
    (i : Fin F.card) :
    |(tubeParams i).a| ≤ 12 ∧ |(tubeParams i).b| ≤ 12 ∧
    |(tubeParams i).c| ≤ 2 ∧ |(tubeParams i).d| ≤ 2 :=
  let ⟨ha, hb⟩ := tubeParams_ab_bounds hbase hvert i
  let ⟨hc, hd⟩ := tubeParams_cd_bounds hvert i
  ⟨ha, hb, hc, hd⟩

/--
The twisted projection of the tube axis at height `z` has horizontal coordinate
`cinematicEval f a b d z + c * z`.
-/
lemma twistedProjection_axis {δ : ℝ} {F : Kakeya.Streamlined.TubeFamily δ}
    (i : Fin F.card) (f : SlopeFunction) (z : ℝ) :
    twistedProjection f
      (point3 ((tubeParams i).a + (tubeParams i).c * z)
        ((tubeParams i).b + (tubeParams i).d * z) z) =
      (cinematicEval f (tubeParams i).a (tubeParams i).b (tubeParams i).d z +
        (tubeParams i).c * z) •
          EuclideanSpace.single (0 : Fin 2) 1 +
        z • EuclideanSpace.single (1 : Fin 2) 1 := by
  simp [twistedProjection, cinematicEval, point3]
  ; ring

/--
Pigeonhole a `c`-window: there exists a center `c0` such that at least
`F.card * w / 8` tubes satisfy `|c_i - c0| ≤ w / 2`.

Requires `0 < w ≤ 4`.
-/
lemma exists_c_window {δ : ℝ} {F : Kakeya.Streamlined.TubeFamily δ}
    (hvert : IsInVerticalChart F) (w : ℝ) (hw : 0 < w) (hw4 : w ≤ 4) :
    ∃ c0 : ℝ,
      ((Finset.univ.filter fun i : Fin F.card =>
        |(tubeParams i).c - c0| ≤ w / 2).card : ℝ) ≥
      (F.card : ℝ) * w / 8 := by
  by_cases h_empty : F.card = 0
  · refine ⟨0, ?_⟩
    simp [h_empty] <;> norm_num
  · have hN_pos : 0 < F.card := Nat.pos_of_ne_zero h_empty
    classical
    let n : ℕ := Nat.ceil (4 / w)
    have h_pos4 : 0 < 4 / w := by positivity
    have hn_pos : 0 < n := Nat.ceil_pos.mpr h_pos4
    have hn1 : (n : ℝ) ≥ 4 / w := Nat.le_ceil (4 / w)
    have hn2 : (n : ℝ) ≤ 8 / w := by
      have h1 : (n : ℝ) ≤ 4 / w + 1 := (Nat.ceil_lt_add_one (show 0 ≤ 4 / w from by positivity)).le
      have h2 : 4 / w + 1 ≤ 8 / w := by
        have h3 : 0 < w := hw
        field_simp [h3.ne'] <;> linarith
      linarith
    let binOf (c : ℝ) : ℕ :=
      if c = 2 then n - 1 else Nat.floor ((c + 2) / w)
    let binCenter (k : ℕ) : ℝ := -2 + ((k : ℝ) + 1 / 2) * w
    let fiber (k : ℕ) : Finset (Fin F.card) :=
      Finset.univ.filter (fun i : Fin F.card => binOf (tubeParams i).c = k)
    have h_binOf_lt_n : ∀ c ∈ Set.Icc (-2 : ℝ) 2, binOf c < n := by
      intro c hc
      by_cases hc2 : c = 2
      · have h_k : binOf c = n - 1 := by
          simp [binOf, hc2]
        rw [h_k] <;> omega
      · have h_k : binOf c = Nat.floor ((c + 2) / w) := by
          simp [binOf, hc2]
        rw [h_k]
        have h_lt : c < 2 := by
          have h_ne : c ≠ 2 := hc2
          have h_le : c ≤ 2 := hc.2
          exact lt_of_le_of_ne h_le h_ne
        have h5 : (c + 2) / w < 4 / w := by gcongr <;> linarith
        have h_pos4w : 0 < (4 / w : ℝ) := by positivity
        have h6 : Nat.floor ((c + 2) / w) < n := by
          simpa [n] using Nat.floor_lt_ceil_of_lt_of_pos h5 h_pos4w
        exact h6
    have h_center_bound : ∀ (c : ℝ), c ∈ Set.Icc (-2 : ℝ) 2 →
        |c - binCenter (binOf c)| ≤ w / 2 := by
      intro c hc
      set k := binOf c with hk_def
      have hk_lt_n : k < n := h_binOf_lt_n c hc
      by_cases hc2 : c = 2
      · -- c = 2 case
        have h_k_eq : k = n - 1 := by
          simp [k, binOf, hc2]
        rw [h_k_eq, hc2]
        dsimp only [binCenter]
        have h_cast : (↑(n - 1) : ℝ) = (n : ℝ) - 1 := by
          rw [Nat.cast_sub (by omega)] <;> norm_num
        rw [h_cast]
        have h_nw1 : (n : ℝ) - 1 < 4 / w := by
          have h : (n : ℝ) < 4 / w + 1 := Nat.ceil_lt_add_one (by positivity)
          linarith
        have h_nw2 : (n : ℝ) ≥ 4 / w := hn1
        have h9 : |(4 : ℝ) - ((n : ℝ) - 1 / 2) * w| ≤ w / 2 := by
          have h10 : 4 - w / 2 ≤ ((n : ℝ) - 1 / 2) * w := by
            have h11 : (n : ℝ) * w ≥ 4 := by
              calc (n : ℝ) * w ≥ (4 / w) * w := by gcongr
                _ = 4 := by field_simp [hw.ne'] <;> ring
            linarith
          have h12 : ((n : ℝ) - 1 / 2) * w < 4 + w / 2 := by
            have h13 : ((n : ℝ) - 1) * w < 4 := by
              calc ((n : ℝ) - 1) * w < (4 / w) * w := by gcongr
                _ = 4 := by field_simp [hw.ne'] <;> ring
            linarith
          have h14 : -(w / 2) ≤ 4 - ((n : ℝ) - 1 / 2) * w := by linarith
          have h15 : 4 - ((n : ℝ) - 1 / 2) * w ≤ w / 2 := by linarith
          exact abs_le.mpr ⟨h14, h15⟩
        have h10 : (2 : ℝ) - (-2 + (((n : ℝ) - 1 + 1 / 2) * w)) =
            4 - ((n : ℝ) - 1 / 2) * w := by ring
        have h_goal : |(2 : ℝ) - (-2 + (((n : ℝ) - 1 + 1 / 2) * w))| ≤ w / 2 := by
          rw [h10]; exact h9
        simpa [binCenter, Nat.cast_sub hn_pos] using h_goal
      · -- c < 2 case
        have h_k_eq : k = Nat.floor ((c + 2) / w) := by
          simp [k, binOf, hc2]
        have h_nonneg : 0 ≤ (c + 2) / w := by
          have h_c2 : -2 ≤ c := hc.1
          have h : 0 ≤ c + 2 := by linarith
          positivity
        have h1 : (k : ℝ) ≤ (c + 2) / w := by
          rw [h_k_eq]; exact Nat.floor_le h_nonneg
        have h2 : (c + 2) / w < (k : ℝ) + 1 := by
          rw [h_k_eq]
          have h_floor : (Nat.floor ((c + 2) / w) : ℝ) + 1 > (c + 2) / w := by
            exact Nat.lt_floor_add_one ((c + 2) / w)
          exact h_floor
        have h3 : -2 + (k : ℝ) * w ≤ c := by
          calc
            -2 + (k : ℝ) * w ≤ -2 + (((c + 2) / w) * w) := by gcongr
            _ = c := by
              have h4 : ((c + 2) / w) * w = c + 2 := by
                field_simp [hw.ne'] <;> ring
              linarith
        have h4 : c < -2 + ((k : ℝ) + 1) * w := by
          calc
            c = -2 + (((c + 2) / w) * w) := by
              have h5 : ((c + 2) / w) * w = c + 2 := by
                field_simp [hw.ne'] <;> ring
              linarith
            _ < -2 + (((k : ℝ) + 1) * w) := by gcongr
        dsimp only [binCenter]
        have h5 : -(w / 2) ≤ c - (-2 + ((k : ℝ) + 1 / 2) * w) := by linarith
        have h6 : c - (-2 + ((k : ℝ) + 1 / 2) * w) ≤ w / 2 := by linarith
        exact abs_le.mpr ⟨h5, h6⟩
    let counts : ℕ → ℕ := fun k =>
      (Finset.univ.filter fun i : Fin F.card => binOf (tubeParams i).c = k).card
    have h_sum : ∑ k ∈ Finset.range n, counts k = F.card := by
      have h1 : ∀ (i : Fin F.card), binOf (tubeParams i).c ∈ Finset.range n := by
        intro i
        have hc : (tubeParams i).c ∈ Set.Icc (-2 : ℝ) 2 := by
          have h_bounds := tubeParams_cd_bounds hvert i
          have h_abs : |(tubeParams i).c| ≤ 2 := h_bounds.1
          have h11 : -2 ≤ (tubeParams i).c := (abs_le.mp h_abs).1
          have h12 : (tubeParams i).c ≤ 2 := (abs_le.mp h_abs).2
          exact ⟨h11, h12⟩
        exact Finset.mem_range.mpr (h_binOf_lt_n (tubeParams i).c hc)
      have h2 : ∑ k ∈ Finset.range n, (Finset.univ.filter (fun i : Fin F.card => binOf (tubeParams i).c = k)).card =
          (Finset.univ : Finset (Fin F.card)).card := by
        have h_disj : Set.PairwiseDisjoint (Finset.range n : Set ℕ)
            (fun k => Finset.univ.filter (fun i : Fin F.card => binOf (tubeParams i).c = k)) := by
          intro k _ l _ hkl
          simp only [Finset.disjoint_left]
          intro i hi1 hi2
          have h4 : binOf (tubeParams i).c = k := (Finset.mem_filter.mp hi1).2
          have h5 : binOf (tubeParams i).c = l := (Finset.mem_filter.mp hi2).2
          have h6 : k = l := by rw [←h4, h5]
          exact hkl h6
        have h_bunion : (Finset.range n).biUnion (fun k => Finset.univ.filter (fun i : Fin F.card => binOf (tubeParams i).c = k)) = (Finset.univ : Finset (Fin F.card)) := by
          apply Finset.ext
          intro i
          simp only [Finset.mem_biUnion, Finset.mem_filter, Finset.mem_univ, true_and]
          constructor
          · intro ⟨k, _, _⟩; trivial
          · intro _
            have h4 : binOf (tubeParams i).c ∈ Finset.range n := h1 i
            exact ⟨binOf (tubeParams i).c, h4, rfl⟩
        have h_card : ∑ k ∈ Finset.range n, (Finset.univ.filter (fun i : Fin F.card => binOf (tubeParams i).c = k)).card =
            ((Finset.range n).biUnion (fun k => Finset.univ.filter (fun i : Fin F.card => binOf (tubeParams i).c = k))).card := by
          rw [Finset.card_biUnion h_disj]
        rw [h_card, h_bunion]
        <;> rfl
      have h_counts_unfold : ∀ k, counts k = (Finset.univ.filter (fun i : Fin F.card => binOf (tubeParams i).c = k)).card := by
        intro k; rfl
      rw [Finset.sum_congr rfl (fun k _ => h_counts_unfold k)]
      rw [h2]
      simp
    have h_pigeonhole : ∃ k ∈ Finset.range n,
        (counts k : ℝ) ≥ (F.card : ℝ) / (n : ℝ) := by
      by_contra h
      push Not at h
      have h_sum_lt : ∑ k ∈ Finset.range n, (counts k : ℝ) <
          ∑ k ∈ Finset.range n, ((F.card : ℝ) / (n : ℝ)) := by
        apply Finset.sum_lt_sum_of_nonempty
        · exact Finset.nonempty_of_ne_empty (by simp [hn_pos.ne'])
        · intro k hk
          exact h k hk
      have h_rhs : ∑ k ∈ Finset.range n, ((F.card : ℝ) / (n : ℝ)) =
          (F.card : ℝ) := by
        simp [Finset.sum_const] <;> field_simp <;> ring
      rw [h_rhs] at h_sum_lt
      have h_sum' : (∑ k ∈ Finset.range n, (counts k : ℝ)) = (F.card : ℝ) := by
        exact_mod_cast h_sum
      rw [h_sum'] at h_sum_lt
      <;> linarith
    rcases h_pigeonhole with ⟨k, hk_in, hcount_ge⟩
    let c0 := binCenter k
    have h_subset : (Finset.univ.filter fun i : Fin F.card =>
        binOf (tubeParams i).c = k) ⊆
      (Finset.univ.filter fun i : Fin F.card =>
        |(tubeParams i).c - c0| ≤ w / 2) := by
      intro i hi
      have h9 : binOf (tubeParams i).c = k := (Finset.mem_filter.mp hi).2
      have h10 : (tubeParams i).c ∈ Set.Icc (-2 : ℝ) 2 := by
        have h_bounds := tubeParams_cd_bounds hvert i
        have h_abs : |(tubeParams i).c| ≤ 2 := h_bounds.1
        have h11 : -2 ≤ (tubeParams i).c := (abs_le.mp h_abs).1
        have h12 : (tubeParams i).c ≤ 2 := (abs_le.mp h_abs).2
        exact ⟨h11, h12⟩
      have h11 : |(tubeParams i).c - c0| ≤ w / 2 := by
        have h_eq : c0 = binCenter (binOf (tubeParams i).c) := by
          dsimp only [c0]
          rw [h9]
        rw [h_eq]
        exact h_center_bound (tubeParams i).c h10
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ i, h11⟩
    have h_card_ge : ((Finset.univ.filter fun i : Fin F.card =>
        |(tubeParams i).c - c0| ≤ w / 2).card : ℝ) ≥
        (counts k : ℝ) := by
      exact_mod_cast Finset.card_le_card h_subset
    have h_final : (counts k : ℝ) ≥ (F.card : ℝ) * w / 8 := by
      calc
        (counts k : ℝ) ≥ (F.card : ℝ) / (n : ℝ) := hcount_ge
        _ ≥ (F.card : ℝ) / (8 / w) := by gcongr
        _ = (F.card : ℝ) * w / 8 := by
          field_simp [hw.ne'] <;> ring
    exact ⟨c0, le_trans h_final h_card_ge⟩

end Kakeya.Assouad
