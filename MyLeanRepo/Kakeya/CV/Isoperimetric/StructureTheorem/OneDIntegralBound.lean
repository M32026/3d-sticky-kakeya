import MyLeanRepo.Kakeya.CV.Isoperimetric.InnerMinkowski.Basic
import MyLeanRepo.Kakeya.CV.Isoperimetric.Measure.EilenbergD0
import Mathlib.MeasureTheory.Integral.IntervalIntegral.ContDiff
import Mathlib.Tactic


/-!
# 1D Integral Bound

For `F ⊆ ℝ` measurable and `g ∈ C_c^1(ℝ)` with `|g| ≤ C`:
  `ENNReal.ofReal |∫_F g'| ≤ ENNReal.ofReal C * μH[0](frontier F)`

Proof route: finite frontier → sort points → telescoping integral →
summation by parts on lists → bound by C * |frontier|.
-/

open MeasureTheory Metric Set ENNReal Classical
open scoped MeasureTheory

namespace Geometry

/-- On an open interval disjoint from `frontier F`, either `F` contains the
whole interval or is disjoint from it. -/
lemma interval_constant {F : Set ℝ} {a b : ℝ} (hab : a < b)
    (h_disj : Disjoint (Ioo a b) (frontier F)) :
    (Ioo a b ⊆ F) ∨ (Ioo a b ∩ F = ∅) := by
  let s := Ioo a b
  have h1 : IsConnected s := isConnected_Ioo hab
  have h2 : s ⊆ interior F ∪ interior Fᶜ := by
    intro x hx
    have h_nf : x ∉ frontier F := Set.disjoint_left.mp h_disj hx
    by_cases h : x ∈ closure F
    · left
      have h' : x ∈ interior F := by
        by_contra h''
        have h9 : x ∈ closure Fᶜ := by simpa [interior_compl] using h''
        have h_front : x ∈ frontier F := by
          have h10 : frontier F = closure F ∩ closure Fᶜ := by
            exact frontier_eq_closure_inter_closure
          rw [h10]; exact ⟨h, h9⟩
        exact h_nf h_front
      exact h'
    · right
      have h' : x ∈ interior Fᶜ := by simpa [interior_compl] using h
      exact h'
  have h3 : IsOpen (interior F) := isOpen_interior
  have h4 : IsOpen (interior Fᶜ) := isOpen_interior
  have h5 : Disjoint (interior F) (interior Fᶜ) := by
    rw [Set.disjoint_left]; intro x hx1 hx2
    have h6 : x ∉ closure F := by simpa [interior_compl] using hx2
    have h7 : x ∈ closure F := subset_closure (interior_subset hx1)
    exact h6 h7
  have h7 := h1.isPreconnected.subset_or_subset h3 h4 h5 h2
  rcases h7 with (h7 | h7)
  · exact Or.inl (fun x hx => interior_subset (h7 hx))
  · have h8 : s ∩ F = ∅ := by
      ext x
      simp only [Set.mem_inter_iff, Set.mem_empty_iff_false, iff_false]
      intro hx
      have h9 : x ∈ interior Fᶜ := h7 hx.1
      have h10 : x ∉ F := interior_subset h9
      exact h10 hx.2
    exact Or.inr h8

/-- Indicator of `Ioo a b ⊆ F` as `0` or `1`. -/
noncomputable def eps (F : Set ℝ) (a b : ℝ) : ℝ :=
  if Ioo a b ⊆ F then 1 else 0

/-- `eps F x y` is always 0 or 1. -/
lemma eps_binary (F : Set ℝ) (x y : ℝ) : eps F x y = 0 ∨ eps F x y = 1 := by
  by_cases h : Ioo x y ⊆ F
  · have h' : eps F x y = 1 := by simp [eps, h]
    exact Or.inr h'
  · have h' : eps F x y = 0 := by simp [eps, h]
    exact Or.inl h'

/-- Telescoping sum over consecutive pairs. -/
noncomputable def telSum (g : ℝ → ℝ) (F : Set ℝ) : List ℝ → ℝ
  | [] => 0
  | [_] => 0
  | a :: b :: t => eps F a b * (g b - g a) + telSum g F (b :: t)

/-- Summation by parts form of `telSum`. -/
noncomputable def byPartsSum (g : ℝ → ℝ) (F : Set ℝ)
    (prev_eps : ℝ) : List ℝ → ℝ
  | [] => 0
  | [last] => prev_eps * g last
  | b :: c :: t =>
    let next_eps := eps F b c
    (prev_eps - next_eps) * g b + byPartsSum g F next_eps (c :: t)

/-- `telSum` equals its summation-by-parts expansion. -/
lemma telSum_eq_byParts (g : ℝ → ℝ) (F : Set ℝ) {a b : ℝ} {t : List ℝ} :
    telSum g F (a :: b :: t) =
      -eps F a b * g a + byPartsSum g F (eps F a b) (b :: t) := by
  have h_main : ∀ (l : List ℝ), ∀ (x y : ℝ),
      telSum g F (x :: y :: l) = -eps F x y * g x + byPartsSum g F (eps F x y) (y :: l) := by
    intro l
    induction l with
    | nil =>
      intro x y
      simp [telSum, byPartsSum] <;> ring
    | cons z t' ih =>
      intro x y
      have h1 : telSum g F (x :: y :: z :: t') =
          eps F x y * (g y - g x) + telSum g F (y :: z :: t') := by
        simp [telSum] <;> rfl
      have h_ih' : telSum g F (y :: z :: t') =
          -eps F y z * g y + byPartsSum g F (eps F y z) (z :: t') := ih y z
      rw [h1, h_ih']
      have h2 : byPartsSum g F (eps F x y) (y :: z :: t') =
          (eps F x y - eps F y z) * g y + byPartsSum g F (eps F y z) (z :: t') := by
        simp [byPartsSum] <;> rfl
      rw [h2] <;> ring
  exact h_main t a b

/-- Bound on `byPartsSum` when the last value is zero. -/
lemma byPartsSum_bound_last_zero (g : ℝ → ℝ) (F : Set ℝ) {C : ℝ}
    (hC : ∀ x, |g x| ≤ C) {L : List ℝ} (hne : L ≠ [])
    (h_last : g L.reverse.headI = 0) (prev_eps : ℝ)
    (h_eps : prev_eps = 0 ∨ prev_eps = 1) :
    |byPartsSum g F prev_eps L| ≤ C * ((L.length : ℝ) - 1) := by
  have hC0 : 0 ≤ C := by
    have h := hC 0
    linarith [abs_nonneg (g 0)]
  have h_abs_add : ∀ (a b : ℝ), |a + b| ≤ |a| + |b| := by
    intro a b
    exact abs_add_le a b
  have h_main : ∀ (L : List ℝ), L ≠ [] → g L.reverse.headI = 0 →
      ∀ (pe : ℝ), pe = 0 ∨ pe = 1 →
      |byPartsSum g F pe L| ≤ C * ((L.length : ℝ) - 1) := by
    intro L
    induction L with
    | nil =>
      intro hne _ _ _
      exfalso; exact hne rfl
    | cons b t ih =>
      intro hne h_last pe h_eps
      cases t with
      | nil =>
        have h_eq : byPartsSum g F pe [b] = pe * g b := by
          simp [byPartsSum]
        rw [h_eq]
        have h_glast : g b = 0 := by simpa using h_last
        rw [h_glast] <;> simp <;> exact hC0
      | cons c t' =>
        set next_eps : ℝ := eps F b c with hnext_def
        have h_next_bin : next_eps = 0 ∨ next_eps = 1 := eps_binary F b c
        have h_last_tail : g (c :: t').reverse.headI = 0 := by
          have h2 : (c :: t').reverse ≠ [] := by simp
          have h3 : ∀ (l : List ℝ), l ≠ [] → (l ++ [b]).headI = l.headI := by
            intro l hl
            cases' l with d ds
            · exfalso; exact hl rfl
            · have h4 : ((d :: ds) ++ [b]).headI = d := by
                have h_append : (d :: ds) ++ [b] = d :: (ds ++ [b]) := by rfl
                rw [h_append, List.headI_cons]
              have h5 : (d :: ds).headI = d := by rw [List.headI_cons]
              rw [h4, h5]
          have h_eq : (c :: t').reverse.headI = (b :: c :: t').reverse.headI := by
            have h1 : (b :: c :: t').reverse = (c :: t').reverse ++ [b] := by
              simp [List.reverse_cons] <;> rfl
            rw [h1]
            exact (h3 (c :: t').reverse h2).symm
          rw [h_eq]
          exact h_last
        have h_diff : |pe - next_eps| ≤ 1 := by
          rcases h_eps with (hpe | hpe)
          · rw [hpe]; rcases h_next_bin with (hne | hne) <;> rw [hne] <;> norm_num
          · rw [hpe]; rcases h_next_bin with (hne | hne) <;> rw [hne] <;> norm_num
        have h1 : |(pe - next_eps) * g b| ≤ C := by
          calc
            |(pe - next_eps) * g b|
              = |pe - next_eps| * |g b| := by rw [abs_mul]
            _ ≤ 1 * C := by
              have h2 : |pe - next_eps| ≤ 1 := h_diff
              have h3 : |g b| ≤ C := hC b
              calc
                |pe - next_eps| * |g b| ≤ 1 * |g b| := by gcongr
                _ ≤ 1 * C := by gcongr
            _ = C := by ring
        have h2 : |byPartsSum g F next_eps (c :: t')| ≤
            C * (((c :: t').length : ℝ) - 1) :=
          ih (by simp) h_last_tail next_eps h_next_bin
        have h3 : (c :: t').length ≥ 1 := by simp
        have h4 : C + C * (((c :: t').length : ℝ) - 1) = C * ((c :: t').length : ℝ) := by
          have h5 : ((c :: t').length : ℝ) ≥ 1 := by exact_mod_cast h3
          have h6 : C * (1 : ℝ) + C * (((c :: t').length : ℝ) - 1) = C * ((c :: t').length : ℝ) := by
            rw [← mul_add]
            have h7 : (1 : ℝ) + (((c :: t').length : ℝ) - 1) = ((c :: t').length : ℝ) := by linarith
            rw [h7]
          simpa using h6
        simp only [byPartsSum]
        have h_abs : |(pe - next_eps) * g b + byPartsSum g F next_eps (c :: t')| ≤
            |(pe - next_eps) * g b| + |byPartsSum g F next_eps (c :: t')| :=
          h_abs_add _ _
        calc
          |(pe - next_eps) * g b + byPartsSum g F next_eps (c :: t')|
            ≤ |(pe - next_eps) * g b| + |byPartsSum g F next_eps (c :: t')| := h_abs
          _ ≤ C + C * (((c :: t').length : ℝ) - 1) := by gcongr
          _ = C * ((c :: t').length : ℝ) := h4
          _ = C * (((b :: c :: t').length : ℝ) - 1) := by
            simp [Nat.cast_add] <;> ring
  exact h_main L hne h_last prev_eps h_eps

/-- `headI` of a non-empty list is a member. -/
lemma headI_mem_self {l : List ℝ} (hne : l ≠ []) : l.headI ∈ l := by
  match l with
  | [] => contradiction
  | x :: xs =>
    have h1 : (x :: xs).headI = x := by simp [List.headI_cons]
    rw [h1]
    <;> simp

/-- A non-empty list equals `headI :: tail`. -/
lemma cons_headI_tail {l : List ℝ} (hne : l ≠ []) : l = l.headI :: l.tail := by
  match l with
  | [] => contradiction
  | x :: xs =>
    have h1 : (x :: xs).headI = x := by simp [List.headI_cons]
    have h2 : (x :: xs).tail = xs := by simp [List.tail_cons]
    rw [h1, h2]

/-- For a non-empty list with `≤`-pairwise ordering, the first element is ≤ the last. -/
lemma sorted_first_le_last {l : List ℝ} (hne : l ≠ [])
    (hsorted : List.Pairwise (· ≤ ·) l) : l.headI ≤ l.reverse.headI := by
  have h_main : ∀ (l : List ℝ), l ≠ [] → List.Pairwise (· ≤ ·) l → l.headI ≤ l.reverse.headI := by
    intro l
    induction l with
    | nil =>
      intro hne _
      exfalso; exact hne rfl
    | cons x t ih =>
      intro hne hpair
      by_cases h_t : t = []
      · rw [h_t]
        simp [List.headI_cons]
        <;> exact le_refl x
      · have h_t_ne : t ≠ [] := h_t
        have h_t_sorted : List.Pairwise (· ≤ ·) t := (List.pairwise_cons.mp hpair).2
        have h_ih : t.headI ≤ t.reverse.headI := ih h_t_ne h_t_sorted
        have h_x_le_head : x ≤ t.headI := (List.pairwise_cons.mp hpair).1 t.headI (headI_mem_self h_t_ne)
        have h_last_eq : (x :: t).reverse.headI = t.reverse.headI := by
          have h1 : (x :: t).reverse = t.reverse ++ [x] := by
            simp [List.reverse_cons] <;> rfl
          rw [h1]
          have h2 : t.reverse ≠ [] := by
            intro h3
            have h4 : t.length = 0 := by
              simpa [List.length_reverse] using congr_arg List.length h3
            exact h_t_ne (by simpa using h4)
          have h3 : ∀ (l : List ℝ), l ≠ [] → (l ++ [x]).headI = l.headI := by
            intro l hl
            have h_eq : l = l.headI :: l.tail := cons_headI_tail hl
            rw [h_eq]
            have h4 : ((l.headI :: l.tail) ++ [x]).headI = l.headI := by
              have h_append : (l.headI :: l.tail) ++ [x] = l.headI :: (l.tail ++ [x]) := by rfl
              rw [h_append, List.headI_cons]
            have h5 : (l.headI :: l.tail).headI = l.headI := by
              rw [List.headI_cons]
            rw [h4, h5]
          exact h3 t.reverse h2
        rw [h_last_eq]
        exact le_trans h_x_le_head h_ih
  exact h_main l hne hsorted

/-- FTC on open interval. -/
lemma FTC_Ioo {g : ℝ → ℝ} (hg : ContDiff ℝ 1 g) {a b : ℝ} (hab : a < b) :
    ∫ x in Ioo a b, deriv g x = g b - g a := by
  have h_diff : Differentiable ℝ g := hg.differentiable (by norm_num)
  have h_deriv_cont : Continuous (deriv g) := hg.continuous_deriv_one
  have hint : IntervalIntegrable (deriv g) volume a b :=
    h_deriv_cont.intervalIntegrable a b
  have h1 : ∫ x in a..b, deriv g x = g b - g a :=
    intervalIntegral.integral_deriv_eq_sub (fun x _ => h_diff.differentiableAt) hint
  have h2 : ∫ x in a..b, deriv g x = ∫ x in Ioc a b, deriv g x := by
    rw [intervalIntegral.integral_of_le hab.le]
  have h4 : Ioo a b =ᵐ[volume] Ioc a b := by
    have ha : volume ({a} : Set ℝ) = 0 := by simp
    have hb : volume ({b} : Set ℝ) = 0 := by simp
    have h6a : ∀ᵐ x ∂volume, x ≠ a := by simpa [ae_iff] using ha
    have h6b : ∀ᵐ x ∂volume, x ≠ b := by simpa [ae_iff] using hb
    filter_upwards [h6a, h6b] with x hxa hxb
    have h7 : x ∈ Ioo a b ↔ x ∈ Ioc a b := by
      simp only [mem_Ioo, mem_Ioc]
      constructor
      · rintro ⟨h1, h2⟩; exact ⟨by linarith, by linarith⟩
      · rintro ⟨h1, h2⟩
        have h2' : x < b := lt_of_le_of_ne h2 hxb
        exact ⟨h1, h2'⟩
    exact propext h7
  have h5 : ∫ x in Ioo a b, deriv g x = ∫ x in Ioc a b, deriv g x := by
    rw [Measure.restrict_congr_set h4]
  rw [h5, ← h2, h1]

/-- Integral equals telescoping sum — proved by list recursion. -/
lemma integral_eq_telSum {F : Set ℝ} (hF : MeasurableSet F)
    {g : ℝ → ℝ} (hg : ContDiff ℝ 1 g)
    {L : List ℝ} (hne : L ≠ []) (hsorted : List.Pairwise (· < ·) L)
    (h_const : ∀ {x y : ℝ}, x ∈ L → y ∈ L → x < y →
      (∀ z, x < z → z < y → z ∉ L) → Ioo x y ⊆ F ∨ Ioo x y ∩ F = ∅) :
    ∫ x in F ∩ Ioo L.headI L.reverse.headI, deriv g x = telSum g F L := by
  induction' L with a t ih
  · contradiction
  · cases t with
    | nil =>
      have h_head : ([a] : List ℝ).headI = a := by simp
      have h_last : ([a] : List ℝ).reverse.headI = a := by simp
      rw [h_head, h_last]
      have h_empty : F ∩ Ioo a a = (∅ : Set ℝ) := by
        ext z; simp [mem_Ioo] <;> tauto
      rw [h_empty]
      simp [telSum]
    | cons b t' =>
      set rest : List ℝ := b :: t' with hrest
      have h_rest_ne : rest ≠ [] := by simp [rest]
      have h_rest_sorted : List.Pairwise (· < ·) rest :=
        (List.pairwise_cons.mp hsorted).2
      have h_pair : ∀ (x : ℝ), x ∈ rest → a < x := (List.pairwise_cons.mp hsorted).1
      have hb_in_rest : b ∈ rest := by simp [rest]
      have hab : a < b := h_pair b hb_in_rest
      have h_const' : ∀ {x y : ℝ}, x ∈ rest → y ∈ rest → x < y →
          (∀ z, x < z → z < y → z ∉ rest) → Ioo x y ⊆ F ∨ Ioo x y ∩ F = ∅ := by
        intro x y hx hy hxy h_between
        have hx' : x ∈ (a :: rest) := by simp [hx]
        have hy' : y ∈ (a :: rest) := by simp [hy]
        have h_between' : ∀ z, x < z → z < y → z ∉ (a :: rest) := by
          intro z hz1 hz2
          have hz' : z ∉ rest := h_between z hz1 hz2
          by_contra hzL
          have hz_x : z ≠ a := by
            intro h_eq
            have h_contra : a < x := h_pair x hx
            rw [h_eq] at hz1
            linarith
          have : z ∈ rest := by
            simp only [List.mem_cons] at hzL
            rcases hzL with (rfl | h)
            · exfalso; exact hz_x rfl
            · exact h
          exact hz' this
        exact h_const hx' hy' hxy h_between'
      have h_ih := ih h_rest_ne h_rest_sorted h_const'
      let c : ℝ := rest.reverse.headI
      let s_ab : Set ℝ := F ∩ Ioo a b
      let s_bc : Set ℝ := F ∩ Ioo b c
      let s_ac : Set ℝ := F ∩ Ioo a c
      have h_disj : Disjoint s_ab s_bc := by
        rw [Set.disjoint_left]
        intro z hz1 hz2
        have h1 : z < b := hz1.2.2
        have h2 : b < z := hz2.2.1
        linarith
      have h_meas1 : MeasurableSet s_ab := hF.inter isOpen_Ioo.measurableSet
      have h_meas2 : MeasurableSet s_bc := hF.inter isOpen_Ioo.measurableSet
      have h_b_null : volume ({b} : Set ℝ) = 0 := by simp
      have h_b_le_c : b ≤ c := by
        dsimp only [c]
        have h_le_sorted : List.Pairwise (· ≤ ·) rest :=
          h_rest_sorted.imp (fun {x y} hxy => le_of_lt hxy)
        have h : rest.headI ≤ rest.reverse.headI := sorted_first_le_last h_rest_ne h_le_sorted
        have h_head : rest.headI = b := by simp [rest]
        rw [h_head] at h
        exact h
      have h_union_ae : s_ac =ᵐ[volume] Set.union s_ab s_bc := by
        have h : ∀ᵐ (x : ℝ) ∂volume, x ∈ s_ac ↔ x ∈ Set.union s_ab s_bc := by
          filter_upwards [show ∀ᵐ x ∂volume, x ≠ b from by simpa [ae_iff] using h_b_null] with z hzb
          simp only [s_ac, s_ab, s_bc, Set.mem_inter_iff, Set.mem_union, mem_Ioo]
          constructor
          · rintro ⟨hFz, h1, h2⟩
            by_cases h : z < b
            · exact Or.inl ⟨hFz, h1, h⟩
            · have h' : b < z := by
                by_contra h_eq
                have : z = b := by linarith
                exact hzb this
              exact Or.inr ⟨hFz, h', h2⟩
          · rintro (⟨hFz, h1, h2⟩ | ⟨hFz, h1, h2⟩)
            · exact ⟨hFz, h1, by linarith [h2, h_b_le_c]⟩
            · exact ⟨hFz, by linarith [h1], h2⟩
        exact Filter.eventuallyEq_set.mpr h
      have h_restrict : volume.restrict s_ac = volume.restrict (Set.union s_ab s_bc) :=
        Measure.restrict_congr_set h_union_ae
      have h_deriv_cont : Continuous (deriv g) := hg.continuous_deriv_one
      have h_int_ab : IntegrableOn (deriv g) s_ab := by
        have h1 : s_ab ⊆ Icc a b := by
          intro z hz; exact ⟨by linarith [hz.2.1], by linarith [hz.2.2]⟩
        have h2 : IntegrableOn (deriv g) (Icc a b) := h_deriv_cont.integrableOn_Icc
        exact h2.mono_set h1
      have h_int_bc : IntegrableOn (deriv g) s_bc := by
        have h1 : s_bc ⊆ Icc b c := by
          intro z hz; exact ⟨by linarith [hz.2.1], by linarith [hz.2.2]⟩
        have h2 : IntegrableOn (deriv g) (Icc b c) := h_deriv_cont.integrableOn_Icc
        exact h2.mono_set h1
      have h_ae_disj : AEDisjoint volume s_ab s_bc := h_disj.aedisjoint
      have h_null2 : NullMeasurableSet s_bc volume := h_meas2.nullMeasurableSet
      have h_main : (∫ x in s_ac, deriv g x) =
          (∫ x in s_ab, deriv g x) + (∫ x in s_bc, deriv g x) := by
        rw [h_restrict]
        have h_result := MeasureTheory.setIntegral_union₀ h_ae_disj h_null2 h_int_ab h_int_bc
        have h_union : Set.union s_ab s_bc = s_ab ∪ s_bc := by rfl
        rw [h_union]
        exact h_result
      have hxa : a ∈ (a :: rest) := by simp
      have hxb : b ∈ (a :: rest) := by simp [rest] <;> tauto
      have h_between_ab : ∀ z, a < z → z < b → z ∉ (a :: rest) := by
        intro z h1 h2
        intro hz
        simp only [List.mem_cons] at hz
        rcases hz with (rfl | hz')
        · linarith
        · have hz'' : z = b ∨ z ∈ t' := by
            simpa [rest, List.mem_cons] using hz'
          rcases hz'' with (rfl | hz'')
          · linarith
          · have h_b_lt_z : b < z := (List.pairwise_cons.mp h_rest_sorted).1 z hz''
            linarith
      have h_ab_const : Ioo a b ⊆ F ∨ Ioo a b ∩ F = ∅ :=
        h_const hxa hxb hab h_between_ab
      have h_first : ∫ x in s_ab, deriv g x = eps F a b * (g b - g a) := by
        rcases h_ab_const with (h_in | h_disj2)
        · have h_int : ∫ x in s_ab, deriv g x = ∫ x in Ioo a b, deriv g x := by
            have h_set : s_ab = Ioo a b := by
              ext z; simp [s_ab, h_in] <;> tauto
            rw [h_set]
          rw [h_int, FTC_Ioo hg hab]
          have h_eps : eps F a b = 1 := by simp [eps, h_in]
          rw [h_eps] <;> ring
        · have h_not_sub : ¬(Ioo a b ⊆ F) := by
            intro h_sub
            have h9 : Ioo a b ∩ F = Ioo a b := by
              ext z; simp [h_sub] <;> tauto
            rw [h9] at h_disj2
            have h10 : (Ioo a b).Nonempty := nonempty_Ioo.mpr hab
            exact h10.ne_empty h_disj2
          have h_empty : s_ab = ∅ := by
            have h_comm : s_ab = Ioo a b ∩ F := by
              ext z; simp [s_ab] <;> tauto
            rw [h_comm, h_disj2]
          have h_eps : eps F a b = 0 := by simp [eps, h_not_sub]
          rw [h_empty, h_eps] <;> simp
      have h_rest_head : rest.headI = b := by simp [rest]
      have h_ih' : ∫ x in s_bc, deriv g x = telSum g F rest := by
        have h_eq : (F ∩ Ioo rest.headI rest.reverse.headI) = s_bc := by
          rw [h_rest_head]
          <;> rfl
        rw [h_eq] at h_ih
        exact h_ih
      have h_head : (a :: rest).headI = a := by simp
      have h_last : (a :: rest).reverse.headI = c := by
        have h1 : (a :: rest).reverse = rest.reverse ++ [a] := by
          simp [List.reverse_cons] <;> rfl
        rw [h1]
        have h2 : rest.reverse ≠ [] := by
          intro h3
          have h4 : rest.length = 0 := by
            simpa [List.length_reverse] using congr_arg List.length h3
          have h5 : rest = [] := by
            simpa using h4
          exact h_rest_ne h5
        have h3 : ∀ (l : List ℝ), l ≠ [] → (l ++ [a]).headI = l.headI := by
          intro l hl
          cases' l with d ds
          · exfalso; exact hl rfl
          · simp
        exact h3 rest.reverse h2
      have h_goal : ∫ x in F ∩ Ioo (a :: rest).headI (a :: rest).reverse.headI, deriv g x =
          telSum g F (a :: rest) := by
        rw [h_head, h_last]
        have h_step1 : (∫ x in s_ac, deriv g x) =
            (∫ x in s_ab, deriv g x) + (∫ x in s_bc, deriv g x) := h_main
        have h_step2 : (∫ x in s_ab, deriv g x) + (∫ x in s_bc, deriv g x) =
            eps F a b * (g b - g a) + telSum g F rest := by
          have h1' : (∫ x in s_ab, deriv g x) = eps F a b * (g b - g a) := h_first
          have h2' : (∫ x in s_bc, deriv g x) = telSum g F rest := h_ih'
          rw [h1', h2'] <;> ring
        have h_step3 : eps F a b * (g b - g a) + telSum g F rest = telSum g F (a :: rest) := by
          have h : telSum g F (a :: rest) = eps F a b * (g b - g a) + telSum g F rest := by
            simp [telSum, rest] <;> rfl
          exact h.symm
        rw [h_step1, h_step2, h_step3]
      exact h_goal

/-- **1D integral bound** (sharp constant). -/
theorem oneD_integral_bound' {F : Set ℝ} (hF : MeasurableSet F)
    {g : ℝ → ℝ} (hg : ContDiff ℝ 1 g) (hgcs : HasCompactSupport g)
    {C : ℝ} (hC : ∀ x, |g x| ≤ C) :
    ENNReal.ofReal |∫ x in F, deriv g x| ≤
      ENNReal.ofReal C * μH[0] (frontier F) := by
  by_cases hC_neg : C < 0
  · exfalso
    have h := hC 0
    linarith [abs_nonneg (g 0)]
  have hC0 : 0 ≤ C := by linarith
  by_cases hinf : μH[0] (frontier F) = ⊤
  · rw [hinf]
    by_cases hC0' : C = 0
    · have hg0 : ∀ x, g x = 0 := by
        intro x
        have h1 : |g x| ≤ C := hC x
        rw [hC0'] at h1
        have h2 : |g x| ≤ 0 := h1
        have h3 : 0 ≤ |g x| := abs_nonneg (g x)
        have h4 : |g x| = 0 := by linarith
        simpa [abs_eq_zero] using h4
      have hderiv0 : deriv g = 0 := by
        funext x
        have h1 : g = 0 := by funext y; exact hg0 y
        rw [h1]; simp
      simp [hderiv0, hC0']
    · have h_pos : 0 < C := by
        exact lt_of_le_of_ne hC0 (Ne.symm hC0')
      have h_ne : ENNReal.ofReal C ≠ 0 := (ENNReal.ofReal_pos.mpr h_pos).ne'
      rw [ENNReal.mul_top h_ne] <;> exact le_top
  · have hfin : (frontier F).Finite := by
      by_contra h_inf'
      have h_inf'' : (frontier F).Infinite := h_inf'
      have h_forall : ∀ (n : ℕ), (n : ENNReal) ≤ μH[0] (frontier F) := by
        intro n
        rcases h_inf''.exists_subset_card_eq n with ⟨F0, hF_sub, hF_card⟩
        have h1 : μH[0] (F0 : Set ℝ) ≤ μH[0] (frontier F) := measure_mono hF_sub
        have h2 : μH[0] (F0 : Set ℝ) = (F0.card : ENNReal) :=
          EilenbergInequality.hausdorff0_finset F0
        rw [h2, hF_card] at h1
        exact h1
      have h_top : μH[0] (frontier F) = ⊤ := by
        by_contra h
        have h_lt : μH[0] (frontier F) < ⊤ := by simpa [lt_top_iff_ne_top] using h
        let r : ℝ := (μH[0] (frontier F)).toReal
        have hR : μH[0] (frontier F) = ENNReal.ofReal r := (ENNReal.ofReal_toReal h).symm
        have h_arch : ∃ (n : ℕ), r < (n : ℝ) := exists_nat_gt r
        rcases h_arch with ⟨n, hn⟩
        have h_r_nonneg : 0 ≤ r := by positivity
        have h6 : μH[0] (frontier F) < (n : ENNReal) := by
          rw [hR]
          have h7 : ENNReal.ofReal r < ENNReal.ofReal (n : ℝ) :=
            (ENNReal.ofReal_lt_ofReal_iff_of_nonneg h_r_nonneg).mpr hn
          have h8 : (ENNReal.ofReal (n : ℝ)) = (n : ENNReal) := by simp
          rw [h8] at h7; exact h7
        have h9 : (n : ENNReal) ≤ μH[0] (frontier F) := h_forall n
        exact not_le.mpr h6 h9
      exact hinf h_top
    let S : Finset ℝ := hfin.toFinset
    have hS : (S : Set ℝ) = frontier F := hfin.coe_toFinset
    have hS_bdd : Bornology.IsBounded (S : Set ℝ) :=
      Set.Finite.isBounded (Finset.finite_toSet S)
    rcases hS_bdd.subset_ball 0 with ⟨K, hK⟩
    have hgcs' : IsCompact (tsupport g) := hgcs
    have hgcs_bdd : Bornology.IsBounded (tsupport g) := IsCompact.isBounded hgcs'
    rcases hgcs_bdd.subset_ball (0 : ℝ) with ⟨R, hR⟩
    let M : ℝ := max (max K R) 0 + 1
    let a : ℝ := -M
    let b : ℝ := M
    have hM_K : K < M := by
      have h : K ≤ max K R := le_max_left K R
      have h2 : max K R ≤ max (max K R) 0 := le_max_left (max K R) 0
      linarith
    have hM_R : R < M := by
      have h : R ≤ max K R := le_max_right K R
      have h2 : max K R ≤ max (max K R) 0 := le_max_left (max K R) 0
      linarith
    have hM_pos : 0 < M := by
      have h : 0 ≤ max (max K R) 0 := le_max_right (max K R) 0
      linarith
    have hab : a < b := by
      simp [a, b, hM_pos] <;> linarith
    have hga : ∀ x ≤ a, g x = 0 := by
      intro x hx
      have h2 : |x| ≥ M := by
        have h3 : x ≤ -M := by simpa [a] using hx
        have h4 : -x ≥ M := by linarith
        have h5 : -x ≤ |x| := by
          have h6 : -x ≤ |-x| := le_abs_self (-x)
          have h7 : |-x| = |x| := abs_neg x
          rw [h7] at h6
          exact h6
        linarith
      have h1 : R < |x| := by linarith
      have h2' : dist x 0 > R := by
        simpa [dist_eq_norm] using h1
      have h3 : x ∉ tsupport g := by
        intro h4
        have h5 : x ∈ ball (0 : ℝ) R := hR h4
        have h6 : dist x 0 < R := by simpa [Metric.mem_ball] using h5
        linarith
      have h4 : x ∉ Function.support g := fun h5 => h3 (subset_closure h5)
      simpa [Function.mem_support] using h4
    have hgb : ∀ x ≥ b, g x = 0 := by
      intro x hx
      have h2 : |x| ≥ M := by
        have h3 : x ≥ M := by simpa [b] using hx
        have h4 : x ≤ |x| := le_abs_self x
        linarith
      have h1 : R < |x| := by linarith
      have h2' : dist x 0 > R := by
        simpa [dist_eq_norm] using h1
      have h3 : x ∉ tsupport g := by
        intro h4
        have h5 : x ∈ ball (0 : ℝ) R := hR h4
        have h6 : dist x 0 < R := by simpa [Metric.mem_ball] using h5
        linarith
      have h4 : x ∉ Function.support g := fun h5 => h3 (subset_closure h5)
      simpa [Function.mem_support] using h4
    have ha_not_S : a ∉ S := by
      intro h2
      have h3 : a ∈ ball (0 : ℝ) K := hK h2
      have h4 : dist a 0 < K := by simpa [Metric.mem_ball] using h3
      have h5 : dist a 0 > K := by
        have h6 : |a| = M := by simp [a, abs_neg] <;> linarith
        simpa [dist_eq_norm] using h6 ▸ hM_K
      linarith
    have hb_not_S : b ∉ S := by
      intro h2
      have h3 : b ∈ ball (0 : ℝ) K := hK h2
      have h4 : dist b 0 < K := by simpa [Metric.mem_ball] using h3
      have h5 : dist b 0 > K := by
        have h6 : |b| = M := by simp [b] <;> linarith
        simpa [dist_eq_norm] using h6 ▸ hM_K
      linarith
    let T : Finset ℝ := S ∪ {a, b}
    have hT_disj : Disjoint S ({a, b} : Finset ℝ) := by
      simp [S, ha_not_S, hb_not_S] <;> tauto
    have h_ab_ne : a ≠ b := by linarith
    have hT_card : T.card = S.card + 2 := by
      rw [Finset.card_union_of_disjoint hT_disj]
      have h : ({a, b} : Finset ℝ).card = 2 := by
        simp [Finset.mem_insert, Finset.mem_singleton, h_ab_ne] <;> tauto
      rw [h] <;> ring
    have h_a_min : ∀ x ∈ (T : Set ℝ), a ≤ x := by
      intro x hx
      have h_xin : x ∈ S ∨ x = a ∨ x = b := by
        have h : x ∈ S ∪ ({a, b} : Finset ℝ) := by simpa [T] using hx
        simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton] at h
        tauto
      rcases h_xin with (h | rfl | rfl)
      · have h2 : dist x 0 < K := hK h
        have h3 : |x| < K := by simpa [dist_eq_norm] using h2
        have h4 : -K < x := by linarith [abs_lt.mp h3]
        simp [a, M] <;> linarith
      · simp [a, M] <;> linarith
      · simp [a, b, M] <;> linarith
    have h_b_max : ∀ x ∈ (T : Set ℝ), x ≤ b := by
      intro x hx
      have h_xin : x ∈ S ∨ x = a ∨ x = b := by
        have h : x ∈ S ∪ ({a, b} : Finset ℝ) := by simpa [T] using hx
        simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton] at h
        tauto
      rcases h_xin with (h | rfl | rfl)
      · have h2 : dist x 0 < K := hK h
        have h3 : |x| < K := by simpa [dist_eq_norm] using h2
        have h4 : x < K := by linarith [abs_lt.mp h3]
        simp [b, M] <;> linarith
      · simp [a, b, M] <;> linarith
      · simp [b, M] <;> linarith
    let pts : List ℝ := T.sort (· ≤ ·)
    have hpts_len : pts.length = T.card := by
      simpa [pts] using Finset.length_sort _ _
    have hpts_nodup : pts.Nodup := by
      simpa [pts] using Finset.sort_nodup _ _
    have hpts_sorted : List.Pairwise (· ≤ ·) pts := by
      simpa [pts] using Finset.sort_sorted _ _
    have hpts_strict : List.Pairwise (· < ·) pts := by
      have h_main : ∀ (l : List ℝ), List.Pairwise (· ≤ ·) l → l.Nodup → List.Pairwise (· < ·) l := by
        intro l
        induction l with
        | nil => intro _ _; constructor
        | cons a t ih =>
          intro hpair hnd
          have h1 : ∀ (x : ℝ), x ∈ t → a ≤ x := (List.pairwise_cons.mp hpair).1
          have h2 : List.Pairwise (· ≤ ·) t := (List.pairwise_cons.mp hpair).2
          have hnd' : a ∉ t ∧ t.Nodup := List.nodup_cons.mp hnd
          have hnd_t : t.Nodup := hnd'.2
          constructor
          · intro x hx
            have hle : a ≤ x := h1 x hx
            have hne : a ≠ x := by
              intro h_eq
              have h5 : a ∈ t := by
                exact h_eq ▸ hx
              exact hnd'.1 h5
            exact lt_of_le_of_ne hle hne
          · exact ih h2 hnd_t
      exact h_main pts hpts_sorted hpts_nodup
    have hpts_nonempty : pts ≠ [] := by
      have h1 : pts.length = T.card := hpts_len
      have h2 : T.card > 0 := by rw [hT_card] <;> omega
      have h3 : pts.length > 0 := by rw [h1] <;> omega
      exact List.ne_nil_of_length_pos h3
    have h_const : ∀ {x y : ℝ}, x ∈ pts → y ∈ pts → x < y →
        (∀ z, x < z → z < y → z ∉ pts) → Ioo x y ⊆ F ∨ Ioo x y ∩ F = ∅ := by
      intro x y hx hy hxy h_between
      have h_disj : Disjoint (Ioo x y) (frontier F) := by
        rw [Set.disjoint_left]
        intro z hz hfz
        have hzS : z ∈ (S : Set ℝ) := by
          exact hS ▸ hfz
        have hzT : z ∈ (T : Set ℝ) := by
          simp [T, hzS] <;> tauto
        have hz_pts : z ∈ pts := by
          have h : z ∈ T.sort (· ≤ ·) := by
            exact (Finset.mem_sort (r := (· ≤ ·))).mpr hzT
          exact h
        exact h_between z hz.1 hz.2 hz_pts
      exact interval_constant hxy h_disj
    have h_first_pts : pts.headI = a := by
      have h2 : a ∈ pts := by
        exact (Finset.mem_sort (r := (· ≤ ·))).mpr (by simp [T])
      have h1 : pts.headI ∈ (T : Set ℝ) := by
        have h : pts.headI ∈ pts := headI_mem_self hpts_nonempty
        exact (Finset.mem_sort (r := (· ≤ ·))).mp h
      have h3 : a ≤ pts.headI := h_a_min pts.headI h1
      have h4 : pts.headI ≤ a := by
        have h5 : List.Pairwise (· ≤ ·) pts := hpts_sorted
        have h6 : pts.head! ≤ a := h5.head!_le h2
        have h7 : pts.headI = pts.head! := by
          cases pts <;> simp [hpts_nonempty] <;> tauto
        rw [h7] <;> exact h6
      exact le_antisymm h4 h3
    have h_last_pts : pts.reverse.headI = b := by
      have h2 : b ∈ pts := by
        exact (Finset.mem_sort (r := (· ≤ ·))).mpr (by simp [T])
      have h1 : pts.reverse.headI ∈ (T : Set ℝ) := by
        have h_rev_ne : pts.reverse ≠ [] := by
          intro h_eq
          have h2 : pts = [] := by
            simpa [List.length_reverse] using congr_arg List.length h_eq
          exact hpts_nonempty h2
        have h : pts.reverse.headI ∈ pts.reverse := headI_mem_self h_rev_ne
        have h' : pts.reverse.headI ∈ pts := by
          simpa [List.mem_reverse] using h
        exact (Finset.mem_sort (r := (· ≤ ·))).mp h'
      have h3 : pts.reverse.headI ≤ b := h_b_max pts.reverse.headI h1
      have h4 : b ≤ pts.reverse.headI := by
        have h_last_ge : ∀ (l : List ℝ), l ≠ [] → List.Pairwise (· ≤ ·) l →
            ∀ (x : ℝ), x ∈ l → x ≤ l.reverse.headI := by
          intro l
          induction l with
          | nil =>
            intro hne _ _ _
            exfalso; exact hne rfl
          | cons a t ih =>
            intro hne hpair x hx
            cases t with
            | nil =>
              have h_x_eq_a : x = a := by simpa [List.mem_singleton] using hx
              rw [h_x_eq_a] <;> simp
            | cons b t' =>
              have h_rest_sorted : List.Pairwise (· ≤ ·) (b :: t') :=
                (List.pairwise_cons.mp hpair).2
              have h2 : (b :: t').reverse ≠ [] := by
                intro h3
                have h4 : (b :: t').length = 0 := by
                  simpa [List.length_reverse] using congr_arg List.length h3
                have h5 : (b :: t') = [] := by
                  simpa using h4
                simp at h5
              have h3 : ∀ (l : List ℝ), l ≠ [] → (l ++ [a]).headI = l.headI := by
                intro l hl
                cases' l with d ds
                · exfalso; exact hl rfl
                · simp
              have h_last_eq : (a :: b :: t').reverse.headI = (b :: t').reverse.headI := by
                have h1 : (a :: b :: t').reverse = (b :: t').reverse ++ [a] := by
                  simp [List.reverse_cons] <;> rfl
                rw [h1]
                exact h3 (b :: t').reverse h2
              rw [h_last_eq]
              by_cases h : x = a
              · rw [h]
                have h_a_le_b : a ≤ b := (List.pairwise_cons.mp hpair).1 b (by simp)
                have h_b_le_last : b ≤ (b :: t').reverse.headI :=
                  ih (by simp) h_rest_sorted b (by simp)
                exact le_trans h_a_le_b h_b_le_last
              · have h4 : x = a ∨ x ∈ (b :: t') := by simpa [List.mem_cons] using hx
                have h_x_in_rest : x ∈ (b :: t') := by
                  rcases h4 with (rfl | h5)
                  · exfalso; exact h rfl
                  · exact h5
                exact ih (by simp) h_rest_sorted x h_x_in_rest
        exact h_last_ge pts hpts_nonempty hpts_sorted b h2
      exact le_antisymm h3 h4
    have h_support : ∀ x, x ∉ Ioo a b → deriv g x = 0 := by
      intro x hx
      by_cases h : x ∈ tsupport g
      · have h2 : dist x 0 < R := by
          have h3 : x ∈ ball (0 : ℝ) R := hR h
          simpa [Metric.mem_ball] using h3
        have h3 : dist x 0 ≤ R := by linarith
        have h4 : |x| ≤ R := by simpa [dist_eq_norm] using h3
        have h5 : -R ≤ x := by
          have h6 : |x| ≤ R := h4
          cases' abs_cases x with h7 h7 <;> linarith
        have h6 : x ≤ R := by
          have h7 : |x| ≤ R := h4
          cases' abs_cases x with h8 h8 <;> linarith
        have h7 : a < x := by simp [a] <;> linarith
        have h8 : x < b := by simp [b] <;> linarith
        have h9 : x ∈ Ioo a b := ⟨h7, h8⟩
        exact False.elim (hx h9)
      · have h6 : x ∉ Function.support g := fun h7 => h (subset_closure h7)
        have h9 : IsOpen (tsupport g)ᶜ := isOpen_compl_iff.mpr isClosed_closure
        have h10 : x ∈ (tsupport g)ᶜ := h
        have h11 : ∀ᶠ (y : ℝ) in nhds x, y ∉ tsupport g := h9.mem_nhds h10
        have h7 : ∀ᶠ (y : ℝ) in nhds x, g y = 0 := by
          filter_upwards [h11] with y hy
          have h12 : y ∉ Function.support g := fun h13 => hy (subset_closure h13)
          simpa [Function.mem_support] using h12
        have h7' : g =ᶠ[nhds x] (0 : ℝ → ℝ) := h7
        have h8 : HasDerivAt g 0 x :=
          (hasDerivAt_const x (0 : ℝ)).congr_of_eventuallyEq h7'
        exact h8.deriv
    have h_main_eq : ∫ x in F, deriv g x = ∫ x in F ∩ Ioo a b, deriv g x := by
      have h1 : ∫ x in F, deriv g x = ∫ x in F, Set.indicator (Ioo a b) (deriv g) x := by
        apply integral_congr_ae
        filter_upwards with x
        by_cases h : x ∈ Ioo a b
        · simp [h, Set.indicator_of_mem]
        · have h4 : deriv g x = 0 := h_support x h
          have h5 : Set.indicator (Ioo a b) (deriv g) x = 0 := by
            simp [Set.indicator_apply, h]
          rw [h4, h5]
      rw [h1]
      have h2 : ∫ x in F, Set.indicator (Ioo a b) (deriv g) x =
               ∫ x in F ∩ Ioo a b, deriv g x := by
        have h3 : ∫ x in F, Set.indicator (Ioo a b) (deriv g) x =
                  ∫ x in Ioo a b, (deriv g) x ∂(volume.restrict F) :=
          integral_indicator (μ := volume.restrict F) isOpen_Ioo.measurableSet
        rw [h3]
        have h4 : ∫ x in Ioo a b, (deriv g) x ∂(volume.restrict F) =
                  ∫ x in F ∩ Ioo a b, deriv g x := by
          rw [Measure.restrict_restrict isOpen_Ioo.measurableSet]
          have h_comm : Ioo a b ∩ F = F ∩ Ioo a b := by ext z; simp [and_comm]
          rw [h_comm]
        exact h4
      exact h2
    rw [h_main_eq]
    have h_intsum : ∫ x in F ∩ Ioo a b, deriv g x = telSum g F pts := by
      have h1 : Ioo a b = Ioo pts.headI pts.reverse.headI := by
        rw [h_first_pts, h_last_pts]
      rw [h1]
      exact integral_eq_telSum hF hg hpts_nonempty hpts_strict h_const
    rw [h_intsum]
    have h_len2 : 2 ≤ pts.length := by
      have h1 : pts.length = T.card := hpts_len
      rw [h1, hT_card] <;> omega
    set x0 : ℝ := pts.headI with hx0_def
    set t : List ℝ := pts.tail with ht_def
    have h_eq1 : pts = x0 :: t := by
      have h : pts = pts.headI :: pts.tail := cons_headI_tail hpts_nonempty
      simpa [hx0_def, ht_def] using h
    set x1 : ℝ := t.headI with hx1_def
    set t' : List ℝ := t.tail with ht'_def
    have h_t_ne : t ≠ [] := by
      have h : pts.length ≥ 2 := h_len2
      rw [h_eq1] at h
      have h' : t.length ≥ 1 := by simpa using h
      intro h_eq
      rw [h_eq] at h'
      simp at h'
    have h_eq2 : t = x1 :: t' := by
      have h : t = t.headI :: t.tail := cons_headI_tail h_t_ne
      simpa [hx1_def, ht'_def] using h
    have h_pts_eq : pts = x0 :: x1 :: t' := by
      rw [h_eq1, h_eq2]
    have h_x0 : x0 = a := by
      have h_head : pts.headI = x0 := by
        rw [h_pts_eq] <;> simp
      exact h_head.trans h_first_pts
    have h_eps_bin : eps F x0 x1 = 0 ∨ eps F x0 x1 = 1 := eps_binary F x0 x1
    have h_tel : telSum g F pts =
        -eps F x0 x1 * g x0 + byPartsSum g F (eps F x0 x1) (x1 :: t') := by
      rw [h_pts_eq]
      exact telSum_eq_byParts g F
    have h_gx0 : g x0 = 0 := by
      rw [h_x0]
      exact hga a (by simp [a, b] <;> linarith)
    have h_main2 : telSum g F pts = byPartsSum g F (eps F x0 x1) (x1 :: t') := by
      rw [h_tel, h_gx0] <;> ring
    have h_last_tail : g (x1 :: t').reverse.headI = 0 := by
      have h2 : (x1 :: t').reverse ≠ [] := by
        intro h3
        have h4 : (x1 :: t').length = 0 := by
          simpa [List.length_reverse] using congr_arg List.length h3
        have h5 : (x1 :: t') = [] := by
          simpa using h4
        simp at h5
      have h3 : ∀ (l : List ℝ), l ≠ [] → (l ++ [x0]).headI = l.headI := by
        intro l hl
        cases' l with d ds
        · exfalso; exact hl rfl
        · simp
      have h1 : (x1 :: t').reverse.headI = b := by
        have h4 : pts.reverse = (x1 :: t').reverse ++ [x0] := by
          rw [h_pts_eq] <;> simp [List.reverse_cons] <;> rfl
        have h5 : pts.reverse.headI = b := h_last_pts
        rw [h4] at h5
        rw [h3 (x1 :: t').reverse h2] at h5
        exact h5
      rw [h1]
      exact hgb b (by simp [a, b] <;> linarith)
    have h_bound : |byPartsSum g F (eps F x0 x1) (x1 :: t')| ≤
        C * (((x1 :: t').length : ℝ) - 1) :=
      byPartsSum_bound_last_zero g F hC (by simp) h_last_tail (eps F x0 x1) h_eps_bin
    have h_len_eq : ((x1 :: t').length : ℝ) - 1 = (S.card : ℝ) := by
      have h2 : (x1 :: t').length = pts.length - 1 := by
        rw [h_pts_eq] <;> simp
      rw [h2, hpts_len, hT_card] <;> simp [Nat.cast_add] <;> ring
    have h_abs_bound : |telSum g F pts| ≤ C * (S.card : ℝ) := by
      calc
        |telSum g F pts|
          = |byPartsSum g F (eps F x0 x1) (x1 :: t')| := by rw [h_main2]
        _ ≤ C * (((x1 :: t').length : ℝ) - 1) := h_bound
        _ = C * (S.card : ℝ) := by rw [h_len_eq]
    have h_haus : μH[0] (frontier F) = (S.card : ENNReal) := by
      rw [← hS]
      exact EilenbergInequality.hausdorff0_finset S
    rw [h_haus]
    have h_final : ENNReal.ofReal (C * (S.card : ℝ)) = ENNReal.ofReal C * (S.card : ENNReal) := by
      simp [ENNReal.ofReal_mul hC0, Nat.cast_nonneg] <;> ring
    have h_goal : ENNReal.ofReal |telSum g F pts| ≤ ENNReal.ofReal (C * (S.card : ℝ)) :=
      ENNReal.ofReal_le_ofReal h_abs_bound
    rw [h_final] at h_goal
    exact h_goal

end Geometry
