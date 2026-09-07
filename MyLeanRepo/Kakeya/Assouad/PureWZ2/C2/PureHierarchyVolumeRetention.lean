import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.GenericHierarchyAlgorithms
import MyLeanRepo.Kakeya.Assouad.WZ1.AnchoredHierarchyIteration
import MyLeanRepo.Kakeya.Assouad.WZ1.Corollary26IntervalPacking
import MyLeanRepo.Kakeya.Assouad.WZ1.Corollary26PopularityRefinement
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperRelativeMultiplicityHelpers
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Tactic

/-!
# Volume retention for multi-level popularity refinement

Given raw trapezoids with separation, select popular ones at each level using
a threshold `C * L_j`, thin using RAW popular cores (no shrinking), and prove
that each popular core retains volume `> A_max * L_j` after all finer-level
thinning.

The key bound: removed volume from t.core at level k is at most
`(√ρ_j / √ρ_k + 3) * A_max * C * L_k`. Summing the geometric series over k > j
and choosing `C` and `delta` small enough gives retention `> A_max * L_j`.
-/

noncomputable section

open MeasureTheory Set Metric Finset ENNReal

namespace Kakeya.Assouad.PureHierarchyGeneric

/-- If a height thinning preserves a factor-two multiplicity band and at
least two thirds of the original union volume, then it retains one third of
the indexed shaded mass.  This is the body-family generic form needed by the
paper-carrier hierarchy. -/
lemma mass_retention_from_volume_generic
    {BF : Kakeya.Streamlined.BodyFamily}
    {Z Z_out : Kakeya.Streamlined.Shading BF}
    {m : ℕ}
    (hZ_mult : Z.HasConstantMultiplicity m (2 * m))
    (hZ_out_mult : Z_out.HasConstantMultiplicity m (2 * m))
    (hV_ne_top : volume Z.union ≠ ⊤)
    (hvolume : ENNReal.ofReal (2 / 3) * volume Z.union ≤
      volume Z_out.union) :
    ENNReal.ofReal (1 / 3) * Z.mass ≤ Z_out.mass := by
  have hZmass := (constant_multiplicity_mass_volume_generic hZ_mult).2
  have hOutMass :=
    (constant_multiplicity_mass_volume_generic hZ_out_mult).1
  let V : ENNReal := volume Z.union
  let Vout : ENNReal := volume Z_out.union
  have hmassEq : ENNReal.ofReal (1 / 3) * ((2 * m : ENNReal) * V) =
      (m : ENNReal) * (ENNReal.ofReal (2 / 3) * V) := by
    have hleftTop : ENNReal.ofReal (1 / 3) *
        ((2 * m : ENNReal) * V) ≠ ⊤ :=
      ENNReal.mul_ne_top (by simp) <|
        ENNReal.mul_ne_top
          (ENNReal.mul_ne_top (by norm_num) (ENNReal.natCast_ne_top m))
          (by simpa [V] using hV_ne_top)
    have hrightTop : (m : ENNReal) *
        (ENNReal.ofReal (2 / 3) * V) ≠ ⊤ :=
      ENNReal.mul_ne_top (ENNReal.natCast_ne_top m) <|
        ENNReal.mul_ne_top (by simp) (by simpa [V] using hV_ne_top)
    apply (ENNReal.toReal_eq_toReal_iff' hleftTop hrightTop).mp
    simp only [ENNReal.toReal_mul, ENNReal.toReal_ofReal,
      ENNReal.toReal_natCast]
    norm_num
    ring
  calc
    ENNReal.ofReal (1 / 3) * Z.mass ≤
        ENNReal.ofReal (1 / 3) * ((2 * m : ENNReal) * V) := by
          exact mul_le_mul_left' hZmass _
    _ = (m : ENNReal) * (ENNReal.ofReal (2 / 3) * V) := hmassEq
    _ ≤ (m : ENNReal) * Vout := by
          exact mul_le_mul_left' hvolume _
    _ ≤ Z_out.mass := hOutMass

/-! ## 1. Single-level thinning with raw cores -/

/--
Select popular trapezoids by volume threshold and thin the shading by keeping
only heights in the RAW popular cores (no shrinking).

Outputs the thinned shading `Z'`, the popular set, and coverage with raw cores.
-/
lemma single_level_thin_only
    {F : Kakeya.Streamlined.BodyFamily}
    {Z : Kakeya.Streamlined.Shading F}
    {T : Finset WZ1VerticalTrapezoid}
    {A_max : ENNReal} {threshold : ℝ}
    (h_thresh_pos : 0 ≤ threshold)
    (h_slab_bound : ∀ (a b : ℝ), a ≤ b →
      volume (Z.union ∩ horizontalSlab a b) ≤ A_max * ENNReal.ofReal (b - a)) :
    ∃ (Z' : Kakeya.Streamlined.Shading F)
      (popular : Finset WZ1VerticalTrapezoid),
      IsSubshadingGeneric Z' Z ∧
      (∀ t, t ∈ popular ↔ t ∈ T ∧ volumeInCoreGeneric Z t > A_max * ENNReal.ofReal threshold) ∧
      (∀ (z : ℝ), horizontalSlice Z'.union z ≠ ∅ → ∃ t ∈ popular, z ∈ t.core) ∧
      (Z'.union = Z.union \ {p : Point3 | p 2 ∉ (⋃ s ∈ popular, s.core)}) ∧
      (∀ p ∈ Z'.union, Z'.pointMultiplicity p = Z.pointMultiplicity p) := by
  classical
  let popular : Finset WZ1VerticalTrapezoid :=
    T.filter (fun t => volumeInCoreGeneric Z t > A_max * ENNReal.ofReal threshold)
  have h_popular_iff : ∀ t, t ∈ popular ↔
      t ∈ T ∧ volumeInCoreGeneric Z t > A_max * ENNReal.ofReal threshold := by
    intro t; simp [popular] <;> tauto
  let popularCores : Set ℝ := ⋃ t ∈ popular, t.core
  have h_meas : MeasurableSet popularCores := by
    have h : (popular : Set WZ1VerticalTrapezoid).Countable := Set.to_countable _
    exact MeasurableSet.biUnion h (fun t _ => measurableSet_Icc)
  let H : Set ℝ := popularCoresᶜ
  have hH_meas : MeasurableSet H := h_meas.compl
  let Z' : Kakeya.Streamlined.Shading F := thinShadingGeneric Z H hH_meas
  have hZ'_sub : IsSubshadingGeneric Z' Z := thinShadingGeneric_subshading
  have hZ'_union : Z'.union = Z.union \ {p : Point3 | p 2 ∈ H} := thinShadingGeneric_union
  have h_coverage : ∀ (z : ℝ), horizontalSlice Z'.union z ≠ ∅ → ∃ t ∈ popular, z ∈ t.core := by
    intro z hz
    have h_z_in : z ∈ popularCores := by
      by_contra h
      have hz' : z ∈ H := h
      have h_empty : horizontalSlice Z'.union z = ∅ := by
        ext p
        simp only [Set.mem_empty_iff_false, iff_false]
        intro hp
        have hpe : p ∈ Z'.union ∧ p 2 = z := by
          simp only [horizontalSlice, Set.mem_setOf_eq] at hp <;> exact hp
        rw [hZ'_union] at hpe
        have h2 : p 2 ∉ H := hpe.1.2
        rw [hpe.2] at h2
        exact h2 hz'
      rw [h_empty] at hz <;> simp at hz
    simp only [popularCores, Set.mem_iUnion] at h_z_in
    rcases h_z_in with ⟨t, ht, hzcore⟩
    exact ⟨t, ht, hzcore⟩
  have h_union_eq : Z'.union = Z.union \ {p : Point3 | p 2 ∉ (⋃ s ∈ popular, s.core)} := by
    have hH_eq : {p : Point3 | p 2 ∈ H} = {p : Point3 | p 2 ∉ (⋃ s ∈ popular, s.core)} := by
      ext p; simp [H, popularCores] <;> tauto
    rw [hZ'_union, hH_eq]
  have h_same_mult : ∀ p ∈ Z'.union, Z'.pointMultiplicity p = Z.pointMultiplicity p :=
    fun p hp => thinShadingGeneric_same_multiplicity (hp := hp)
  exact ⟨Z', popular, hZ'_sub, h_popular_iff, h_coverage, h_union_eq, h_same_mult⟩

/-! ## 2. Packing bound for separated points -/

/--
If a finset of real numbers lies in `[a, b]` and distinct elements are at least
`d` apart, then its cardinality is at most `(b - a) / d + 1`.
-/
lemma real_packing_bound {d : ℝ} (hd : 0 < d) {S : Finset ℝ} {a b : ℝ}
    (hab : a ≤ b)
    (hS_sub : ∀ x ∈ S, a ≤ x ∧ x ≤ b)
    (hS_sep : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → d ≤ |x - y|) :
    (S.card : ℝ) ≤ (b - a) / d + 1 := by
  classical
  have h_main : ∀ (n : ℕ), ∀ (S : Finset ℝ), S.card = n →
      ∀ (a b : ℝ), a ≤ b →
        (∀ x ∈ S, a ≤ x ∧ x ≤ b) →
        (∀ x ∈ S, ∀ y ∈ S, x ≠ y → d ≤ |x - y|) →
        (S.card : ℝ) ≤ (b - a) / d + 1 := by
    intro n
    induction n with
    | zero =>
      intro S hcard a b hab hS_sub hS_sep
      have h_empty : S = ∅ := by
        simpa [Finset.card_eq_zero] using hcard
      have h_goal : (S.card : ℝ) = 0 := by
        rw [h_empty]; simp
      rw [h_goal]
      have h1 : 0 ≤ (b - a) / d := by positivity
      exact add_nonneg h1 (by norm_num)
    | succ n ih =>
      intro S hcard a b hab hS_sub hS_sep
      have hS_nonempty : S.Nonempty := by
        rw [Finset.nonempty_iff_ne_empty]
        intro h
        rw [h] at hcard
        simp at hcard <;> omega
      let m := Finset.min' S hS_nonempty
      have hm_in : m ∈ S := Finset.min'_mem S hS_nonempty
      have hm_ge_a : a ≤ m := (hS_sub m hm_in).1
      let S' := S.erase m
      have hS'_card : S'.card = n := by
        rw [Finset.card_erase_of_mem hm_in, hcard] <;> omega
      have hS'_sub : S' ⊆ S := Finset.erase_subset _ _
      have hS'_props : ∀ x ∈ S', a + d ≤ x ∧ x ≤ b := by
        intro x hx
        have hx_in_S : x ∈ S := hS'_sub hx
        have hx_ne_m : x ≠ m := Finset.ne_of_mem_erase hx
        have h_sep1 : d ≤ |x - m| := hS_sep x hx_in_S m hm_in hx_ne_m
        have h_m_le_x : m ≤ x := Finset.min'_le S x hx_in_S
        have h_pos : 0 ≤ x - m := by linarith
        have h_sep2 : d ≤ x - m := by
          rw [abs_of_nonneg h_pos] at h_sep1; exact h_sep1
        have h_ineq : a + d ≤ x := by linarith
        exact ⟨h_ineq, (hS_sub x hx_in_S).2⟩
      have hS'_sep : ∀ x ∈ S', ∀ y ∈ S', x ≠ y → d ≤ |x - y| := by
        intro x hx y hy hne
        exact hS_sep x (hS'_sub hx) y (hS'_sub hy) hne
      by_cases hS'_empty : S' = ∅
      · have h_card1 : (S.card : ℝ) = 1 := by
          have h3 : S'.card = 0 := by rw [hS'_empty]; simp
          rw [hS'_card] at h3
          norm_cast at h3 ⊢ <;> omega
        rw [h_card1]
        have h4 : 0 ≤ (b - a) / d := by positivity
        linarith
      · have hS'_ne : S'.Nonempty := Finset.nonempty_iff_ne_empty.mpr hS'_empty
        rcases hS'_ne with ⟨x, hx⟩
        have h_ad_le_b : a + d ≤ b := by
          have h5 : a + d ≤ x := (hS'_props x hx).1
          have h6 : x ≤ b := (hS'_props x hx).2
          linarith
        have h_ih' := ih S' hS'_card (a + d) b h_ad_le_b
          (fun x hx => ⟨(hS'_props x hx).1, (hS'_props x hx).2⟩) hS'_sep
        have h_card_cast : (S'.card : ℝ) = (S.card : ℝ) - 1 := by
          have h1 : (S'.card : ℝ) = ↑n := by exact_mod_cast hS'_card
          have h2 : (S.card : ℝ) = ↑(n + 1) := by exact_mod_cast hcard
          rw [h1, h2] <;> simp <;> ring
        rw [h_card_cast] at h_ih'
        have h_final : (b - (a + d)) / d + 1 = (b - a) / d := by
          have h3 : b - (a + d) = b - a - d := by ring
          rw [h3]
          field_simp [hd.ne'] <;> ring
        rw [h_final] at h_ih'
        linarith
  exact h_main S.card S rfl a b hab hS_sub hS_sep

/--
Number of pairwise-separated trapezoid cores (length ≤ √ρ_k, separation ≥ √ρ_k)
that intersect an interval of length ≤ √ρ_j is at most √ρ_j / √ρ_k + 2.

We pack the left endpoints: distinct left endpoints are ≥ √ρ_k apart, and all
lie in an interval of length ≤ √ρ_j + √ρ_k.
-/
lemma count_intersecting_cores
    {N : ℕ} {delta : ℝ}
    {rawTrapezoids : Fin N → Finset WZ1VerticalTrapezoid}
    {j k : Fin N}
    (hdelta_pos : 0 < delta)
    (h_length : ∀ i, ∀ t ∈ rawTrapezoids i, t.length ≤ Real.sqrt (wz1Corollary26Scale delta N i))
    (h_sep : ∀ i, ∀ t ∈ rawTrapezoids i, ∀ s ∈ rawTrapezoids i, t ≠ s →
      ∀ z ∈ t.core, ∀ w ∈ s.core, Real.sqrt (wz1Corollary26Scale delta N i) ≤ |z - w|)
    (t : WZ1VerticalTrapezoid)
    (ht_len : t.length ≤ Real.sqrt (wz1Corollary26Scale delta N j))
    (S : Finset WZ1VerticalTrapezoid)
    (hS_sub : S ⊆ rawTrapezoids k)
    (hS_sep : ∀ t ∈ S, ∀ s ∈ S, t ≠ s →
      ∀ z ∈ t.core, ∀ w ∈ s.core, Real.sqrt (wz1Corollary26Scale delta N k) ≤ |z - w|)
    (h_intersect : ∀ s ∈ S, (s.core ∩ t.core).Nonempty) :
    (S.card : ℝ) ≤ Real.sqrt (wz1Corollary26Scale delta N j) / Real.sqrt (wz1Corollary26Scale delta N k) + 2 := by
  let rho_j := wz1Corollary26Scale delta N j
  let rho_k := wz1Corollary26Scale delta N k
  have h_rho_j_pos : 0 < rho_j := Real.rpow_pos_of_pos hdelta_pos _
  have h_rho_k_pos : 0 < rho_k := Real.rpow_pos_of_pos hdelta_pos _
  have h_sqrt_k_pos : 0 < Real.sqrt rho_k := Real.sqrt_pos.mpr h_rho_k_pos
  let leftEndpoints : Finset ℝ := S.image (fun s => s.left)
  have h_inj : Set.InjOn (fun (s : WZ1VerticalTrapezoid) => s.left) S := by
    intro s hs s' hs' h_eq
    by_contra hne
    have h1 : s.left ∈ s.core := Set.left_mem_Icc.mpr s.left_lt_right.le
    have h2 : s'.left ∈ s'.core := Set.left_mem_Icc.mpr s'.left_lt_right.le
    have h3 : s.left = s'.left := h_eq
    have h4 : Real.sqrt rho_k ≤ |s.left - s'.left| := hS_sep s hs s' hs' hne s.left h1 s'.left h2
    have h5 : Real.sqrt rho_k ≤ 0 := by
      simpa [h3, abs_lt] using h4
    linarith [h_sqrt_k_pos]
  have h_card : leftEndpoints.card = S.card := by
    rw [Finset.card_image_of_injOn h_inj]
  let a : ℝ := t.left - Real.sqrt rho_k
  let b : ℝ := t.right
  have hab : a ≤ b := by
    simp only [a, b]
    have h_len_def : t.length = t.right - t.left := by rfl
    have h_pos : 0 < t.length := by
      have h : t.left < t.right := t.left_lt_right
      dsimp only [WZ1VerticalTrapezoid.length] at *
      <;> linarith
    have h_nonneg : 0 ≤ Real.sqrt rho_k := Real.sqrt_nonneg _
    have h1 : -Real.sqrt rho_k ≤ t.length := by linarith
    rw [h_len_def] at h1
    linarith
  have h_bounds : ∀ x ∈ leftEndpoints, a ≤ x ∧ x ≤ b := by
    intro x hx
    rcases Finset.mem_image.mp hx with ⟨s, hs, rfl⟩
    have h_int : (s.core ∩ t.core).Nonempty := h_intersect s hs
    rcases h_int with ⟨z, hz1, hz2⟩
    have h_s_len : s.length ≤ Real.sqrt rho_k := h_length k s (hS_sub hs)
    have h1 : s.left ≤ z := hz1.1
    have h2 : z ≤ t.right := hz2.2
    have h3 : t.left ≤ z := hz2.1
    have h4 : z ≤ s.right := hz1.2
    have h5 : s.left ≤ t.right := by linarith
    have h6 : s.left ≥ t.left - Real.sqrt rho_k := by
      have h7 : s.right - s.left ≤ Real.sqrt rho_k := h_s_len
      linarith
    exact ⟨by simpa [a] using h6, by simpa [b] using h5⟩
  have h_sep' : ∀ x ∈ leftEndpoints, ∀ y ∈ leftEndpoints, x ≠ y → Real.sqrt rho_k ≤ |x - y| := by
    intro x hx y hy hne
    rcases Finset.mem_image.mp hx with ⟨s, hs, rfl⟩
    rcases Finset.mem_image.mp hy with ⟨s', hs', rfl⟩
    have h_s_ne : s ≠ s' := by
      intro h; rw [h] at hne; exact hne rfl
    have h_disjoint : Disjoint s.core s'.core := by
      rw [Set.disjoint_left]
      intro z hz1 hz2
      have h := hS_sep s hs s' hs' h_s_ne z hz1 z hz2
      have h0 : |z - z| = 0 := by simp
      rw [h0] at h
      linarith [h_sqrt_k_pos]
    by_cases h_order : s.left < s'.left
    · have h_no_overlap : s.right < s'.left := by
        by_contra h
        have h' : s'.left ≤ s.right := by linarith
        have h1 : s'.left ∈ s.core := ⟨by linarith, h'⟩
        have h2 : s'.left ∈ s'.core := Set.left_mem_Icc.mpr s'.left_lt_right.le
        have h_in : s'.left ∈ s.core ⊓ s'.core := ⟨h1, h2⟩
        have h_bot : s'.left ∈ (∅ : Set ℝ) := h_disjoint.le_bot h_in
        simpa using h_bot
      have h3 : Real.sqrt rho_k ≤ s'.left - s.right := by
        have h4 : s.right ∈ s.core := Set.right_mem_Icc.mpr s.left_lt_right.le
        have h5 : s'.left ∈ s'.core := Set.left_mem_Icc.mpr s'.left_lt_right.le
        have h6 : Real.sqrt rho_k ≤ |s'.left - s.right| := by
          have h6_raw : Real.sqrt rho_k ≤ |s.right - s'.left| := hS_sep s hs s' hs' h_s_ne s.right h4 s'.left h5
          have h_eq : |s'.left - s.right| = |s.right - s'.left| := by
            rw [show s'.left - s.right = -(s.right - s'.left) by ring, abs_neg]
          rw [h_eq]
          exact h6_raw
        have h7 : 0 < s'.left - s.right := by linarith
        rw [abs_of_pos h7] at h6
        exact h6
      have h8 : Real.sqrt rho_k ≤ s'.left - s.left := by
        have h9 : 0 ≤ s.right - s.left := by linarith [s.left_lt_right]
        linarith
      have h10 : |s.left - s'.left| = s'.left - s.left := by
        have h_neg : s.left - s'.left < 0 := by linarith
        rw [abs_of_neg h_neg] <;> linarith
      rw [h10]; exact h8
    · have h_order' : s'.left < s.left := by
        have h_le : s'.left ≤ s.left := by linarith
        have h_ne : s'.left ≠ s.left := Ne.symm hne
        exact lt_of_le_of_ne h_le h_ne
      have h_no_overlap : s'.right < s.left := by
        by_contra h
        have h' : s.left ≤ s'.right := by linarith
        have h1 : s.left ∈ s'.core := ⟨by linarith, h'⟩
        have h2 : s.left ∈ s.core := Set.left_mem_Icc.mpr s.left_lt_right.le
        have h_in : s.left ∈ s.core ⊓ s'.core := ⟨h2, h1⟩
        have h_bot : s.left ∈ (∅ : Set ℝ) := h_disjoint.le_bot h_in
        simpa using h_bot
      have h3 : Real.sqrt rho_k ≤ s.left - s'.right := by
        have h4 : s'.right ∈ s'.core := Set.right_mem_Icc.mpr s'.left_lt_right.le
        have h5 : s.left ∈ s.core := Set.left_mem_Icc.mpr s.left_lt_right.le
        have h6 : Real.sqrt rho_k ≤ |s'.right - s.left| := hS_sep s' hs' s hs h_s_ne.symm s'.right h4 s.left h5
        have h6' : Real.sqrt rho_k ≤ |s.left - s'.right| := by
          have h_eq : |s.left - s'.right| = |s'.right - s.left| := by
            rw [show s.left - s'.right = -(s'.right - s.left) by ring, abs_neg]
          rw [h_eq]
          exact h6
        have h7 : 0 < s.left - s'.right := by linarith
        rw [abs_of_pos h7] at h6'
        exact h6'
      have h8 : Real.sqrt rho_k ≤ s.left - s'.left := by
        have h9 : 0 ≤ s'.right - s'.left := by linarith [s'.left_lt_right]
        linarith
      have h10 : |s.left - s'.left| = s.left - s'.left := by
        rw [abs_of_pos] <;> linarith
      rw [h10]; exact h8
  have h_main := real_packing_bound (S := leftEndpoints) (a := a) (b := b) h_sqrt_k_pos hab h_bounds h_sep'
  rw [h_card] at h_main
  have h_final : (b - a) / Real.sqrt rho_k + 1 ≤ Real.sqrt rho_j / Real.sqrt rho_k + 2 := by
    have h17 : b - a = t.length + Real.sqrt rho_k := by
      simp [a, b, WZ1VerticalTrapezoid.length] <;> ring
    rw [h17]
    have h18 : (t.length + Real.sqrt rho_k) / Real.sqrt rho_k + 1 =
        t.length / Real.sqrt rho_k + 2 := by
      field_simp [h_sqrt_k_pos.ne'] <;> ring
    rw [h18]
    gcongr <;> linarith [ht_len]
  exact h_main.trans h_final

/-! ## 3. Multi-level thinning with raw cores -/

/--
Process levels 0..j coarsest to finest using `single_level_thin_only`.
Outputs Z_out and popular sets P_i with raw cores + coverage.
-/
lemma multi_level_thin_only_up_to
    {N : ℕ} {F : Kakeya.Streamlined.BodyFamily}
    {Z : Kakeya.Streamlined.Shading F}
    {rawTrapezoids : Fin N → Finset WZ1VerticalTrapezoid}
    {A_max : ENNReal}
    {L : Fin N → ℝ}
    (C : ℝ)
    (hC_nonneg : 0 ≤ C)
    (hL_pos : ∀ j, 0 ≤ L j)
    (h_slab_bound : ∀ (a b : ℝ), a ≤ b →
      volume (Z.union ∩ horizontalSlab a b) ≤ A_max * ENNReal.ofReal (b - a)) :
    ∀ (j : ℕ), j < N →
      ∀ (Z_j : Kakeya.Streamlined.Shading F),
        IsSubshadingGeneric Z_j Z →
    ∃ (Z_out : Kakeya.Streamlined.Shading F)
      (P : Fin N → Finset WZ1VerticalTrapezoid),
      IsSubshadingGeneric Z_out Z_j ∧
      (∀ (i : Fin N), (i : ℕ) ≤ j → P i ⊆ rawTrapezoids i) ∧
      (∀ (i : Fin N), (i : ℕ) ≤ j →
        ∀ (z : ℝ), horizontalSlice Z_out.union z ≠ ∅ → ∃ t ∈ P i, z ∈ t.core) := by
  intro j
  induction j with
  | zero =>
    intro hj Z_j hZ_j_sub
    let j_fin : Fin N := ⟨0, hj⟩
    have h_slab_bound_j : ∀ (a b : ℝ), a ≤ b →
        volume (Z_j.union ∩ horizontalSlab a b) ≤ A_max * ENNReal.ofReal (b - a) := by
      intro a b hab
      have h1 : Z_j.union ∩ horizontalSlab a b ⊆ Z.union ∩ horizontalSlab a b :=
        Set.inter_subset_inter_left _ hZ_j_sub.union_subset
      exact (measure_mono h1).trans (h_slab_bound a b hab)
    have h_thresh_pos : 0 ≤ C * L j_fin := mul_nonneg hC_nonneg (hL_pos j_fin)
    rcases single_level_thin_only h_thresh_pos h_slab_bound_j with
      ⟨Z_out, P_0, hZ_out_sub, h_spec_0, h_cov_0, _⟩
    let P : Fin N → Finset WZ1VerticalTrapezoid :=
      fun i => if (i : ℕ) = 0 then P_0 else ∅
    refine ⟨Z_out, P, hZ_out_sub, ?_⟩
    constructor
    · intro i hi
      have h_i_zero : (i : ℕ) = 0 := by omega
      have hP : P i = P_0 := by dsimp only [P]; rw [if_pos h_i_zero]
      have h_i_eq : i = j_fin := by apply Fin.ext; exact h_i_zero
      rw [hP, h_i_eq]
      intro t ht
      exact ((h_spec_0 t).mp ht).1
    · intro i hi z hz
      have h_i_zero : (i : ℕ) = 0 := by omega
      have hP : P i = P_0 := by dsimp only [P]; rw [if_pos h_i_zero]
      rw [hP]; exact h_cov_0 z hz
  | succ j' ih =>
    intro hj Z_j hZ_j_sub
    have h_j'_lt_N : j' < N := by omega
    rcases ih h_j'_lt_N Z_j hZ_j_sub with
      ⟨Z_prev, P_prev, hZ_prev_sub, h_sub_prev, h_cov_prev⟩
    let j_fin : Fin N := ⟨j'.succ, hj⟩
    have h_slab_bound_prev : ∀ (a b : ℝ), a ≤ b →
        volume (Z_prev.union ∩ horizontalSlab a b) ≤ A_max * ENNReal.ofReal (b - a) := by
      intro a b hab
      let h_trans : IsSubshadingGeneric Z_prev Z := fun i => Set.Subset.trans (hZ_prev_sub i) (hZ_j_sub i)
      have h1 : Z_prev.union ∩ horizontalSlab a b ⊆ Z.union ∩ horizontalSlab a b :=
        Set.inter_subset_inter_left _ h_trans.union_subset
      exact (measure_mono h1).trans (h_slab_bound a b hab)
    have h_thresh_pos : 0 ≤ C * L j_fin := mul_nonneg hC_nonneg (hL_pos j_fin)
    rcases single_level_thin_only h_thresh_pos h_slab_bound_prev with
      ⟨Z_out, P_j, hZ_out_sub, h_spec_j, h_cov_j, _⟩
    let P : Fin N → Finset WZ1VerticalTrapezoid :=
      fun i => if (i : ℕ) = j'.succ then P_j else P_prev i
    refine ⟨Z_out, P, fun i => Set.Subset.trans (hZ_out_sub i) (hZ_prev_sub i), ?_⟩
    constructor
    · intro i hi
      by_cases h_i_j : (i : ℕ) = j'.succ
      · have hP : P i = P_j := by dsimp only [P]; rw [if_pos h_i_j]
        have h_i_eq : i = j_fin := by apply Fin.ext; exact h_i_j
        rw [hP, h_i_eq]
        intro t ht; exact ((h_spec_j t).mp ht).1
      · have h_i_le : (i : ℕ) ≤ j' := by omega
        have h_ne : (i : ℕ) ≠ j'.succ := h_i_j
        have hP : P i = P_prev i := by dsimp only [P]; rw [if_neg h_ne]
        rw [hP]; exact h_sub_prev i h_i_le
    · intro i hi z hz
      by_cases h_i_j : (i : ℕ) = j'.succ
      · have hP : P i = P_j := by dsimp only [P]; rw [if_pos h_i_j]
        rw [hP]; exact h_cov_j z hz
      · have h_i_le : (i : ℕ) ≤ j' := by omega
        have h_ne : (i : ℕ) ≠ j'.succ := h_i_j
        have hP : P i = P_prev i := by dsimp only [P]; rw [if_neg h_ne]
        rw [hP]
        have h_z_prev : horizontalSlice Z_prev.union z ≠ ∅ := by
          have h2 : Z_out.union ⊆ Z_prev.union := hZ_out_sub.union_subset
          have h3 : horizontalSlice Z_out.union z ⊆ horizontalSlice Z_prev.union z :=
            fun p hp => ⟨h2 hp.1, hp.2⟩
          exact Set.Nonempty.mono h3 (Set.nonempty_iff_ne_empty.mpr hz) |>.ne_empty
        exact h_cov_prev i h_i_le z h_z_prev

/--
Top-level multi-level thinning with raw popular cores.
Processes all N levels coarsest to finest.
-/
lemma multi_level_thin_only
    {N : ℕ} {F : Kakeya.Streamlined.BodyFamily}
    {Z : Kakeya.Streamlined.Shading F}
    {rawTrapezoids : Fin N → Finset WZ1VerticalTrapezoid}
    {A_max : ENNReal}
    {L : Fin N → ℝ}
    (C : ℝ)
    (hC_nonneg : 0 ≤ C)
    (hN_pos : 0 < N)
    (hL_pos : ∀ j, 0 ≤ L j)
    (h_slab_bound : ∀ (a b : ℝ), a ≤ b →
      volume (Z.union ∩ horizontalSlab a b) ≤ A_max * ENNReal.ofReal (b - a)) :
    ∃ (Z1 : Kakeya.Streamlined.Shading F)
      (P : Fin N → Finset WZ1VerticalTrapezoid),
      IsSubshadingGeneric Z1 Z ∧
      (∀ j, P j ⊆ rawTrapezoids j) ∧
      (∀ j, ∀ z, horizontalSlice Z1.union z ≠ ∅ → ∃ t ∈ P j, z ∈ t.core) := by
  have h_last_lt : N - 1 < N := by omega
  have h_id : IsSubshadingGeneric Z Z := fun i => Set.Subset.refl (Z.carrier i)
  rcases multi_level_thin_only_up_to C hC_nonneg hL_pos h_slab_bound (N - 1) h_last_lt Z h_id with
    ⟨Z1, P, hZ1_sub, h_sub, h_cov⟩
  refine ⟨Z1, P, hZ1_sub, ?_⟩
  constructor
  · intro j
    have hj_le : (j : ℕ) ≤ N - 1 := by omega
    exact h_sub j hj_le
  · intro j z hz
    have hj_le : (j : ℕ) ≤ N - 1 := by omega
    exact h_cov j hj_le z hz


/-! ## 4. Geometric series bound for volume retention -/

/--
Geometric series bound: the total volume removal from a level-`i` core over all
finer levels is less than `2/3 * L i`, provided `delta^(hierarchyLoss/N) ≤ 1/10`.

TODO: prove this pure real-analysis lemma.
-/
lemma geometric_series_volume_bound
    {N : ℕ} {delta hierarchyLoss : ℝ} {L : Fin N → ℝ}
    (hN_pos : 0 < N)
    (hdelta_pos : 0 < delta)
    (hdelta_lt_one : delta < 1)
    (hh_pos : 0 < hierarchyLoss)
    (hL_eq : ∀ j, L j = Real.rpow (wz1Corollary26Scale delta N j) (1 / 2 + hierarchyLoss))
    (h_cond : Real.rpow delta (hierarchyLoss / (N : ℝ)) < 1 / 9)
    (i : Fin N) :
    ∑ k ∈ Finset.univ.filter (fun k : Fin N => i < k),
      (Real.sqrt (wz1Corollary26Scale delta N i) / Real.sqrt (wz1Corollary26Scale delta N k) + 2) * L k
    < (2 / 3 : ℝ) * L i := by
  let N' : ℝ := (N : ℝ)
  let h : ℝ := hierarchyLoss
  let e : ℝ := 1 / 2 + h
  let r : ℝ := Real.rpow delta (1 / N')
  let q : ℝ := Real.rpow delta (h / N')
  let rho (j : Fin N) : ℝ := wz1Corollary26Scale delta N j

  have hN'_pos : 0 < N' := by positivity
  have hdelta_nonneg : 0 ≤ delta := hdelta_pos.le
  have hr_pos : 0 < r := Real.rpow_pos_of_pos hdelta_pos _
  have hr_nonneg : 0 ≤ r := hr_pos.le
  have hr_lt_one : r < 1 := Real.rpow_lt_one hdelta_nonneg hdelta_lt_one (by positivity)
  have hq_pos : 0 < q := Real.rpow_pos_of_pos hdelta_pos _
  have hq_nonneg : 0 ≤ q := hq_pos.le
  have hq_lt_one : q < 1 := by linarith
  have hrho_pos : ∀ j, 0 < rho j := fun j => Real.rpow_pos_of_pos hdelta_pos _
  have hL_i_pos : 0 < L i := by
    rw [hL_eq i]; exact Real.rpow_pos_of_pos (hrho_pos i) _
  have he_pos : 0 < e := by positivity

  -- rho j = r ^ (j+1)
  have h_rho : ∀ (j : Fin N), rho j = Real.rpow r ((j : ℕ) + 1 : ℝ) := by
    intro j
    have h1 : rho j = Real.rpow delta (((j : ℕ) + 1 : ℝ) / N') := by
      simp [rho, wz1Corollary26Scale] <;> rfl
    have h2 : ((j : ℕ) + 1 : ℝ) / N' = (1 / N') * ((j : ℕ) + 1 : ℝ) := by ring
    calc rho j
      = Real.rpow delta (((j : ℕ) + 1 : ℝ) / N') := h1
    _ = Real.rpow delta ((1 / N') * ((j : ℕ) + 1 : ℝ)) := by rw [h2]
    _ = (Real.rpow delta (1 / N')) ^ ((j : ℕ) + 1 : ℝ) := Real.rpow_mul hdelta_nonneg (1 / N') ((j : ℕ) + 1 : ℝ)
    _ = Real.rpow r ((j : ℕ) + 1 : ℝ) := by rfl

  -- L j = r ^ ((j+1) * e)
  have h_L : ∀ (j : Fin N), L j = Real.rpow r (((j : ℕ) + 1 : ℝ) * e) := by
    intro j
    calc L j
      = Real.rpow (rho j) e := by rw [hL_eq j] <;> rfl
    _ = Real.rpow (Real.rpow r ((j : ℕ) + 1 : ℝ)) e := by rw [h_rho j]
    _ = Real.rpow r (((j : ℕ) + 1 : ℝ) * e) := (Real.rpow_mul hr_nonneg (((j : ℕ) + 1 : ℝ)) e).symm

  -- q = r ^ h
  have h_q : q = Real.rpow r h := by
    have h2 : h / N' = (1 / N') * h := by ring
    calc q
      = Real.rpow delta (h / N') := by rfl
    _ = Real.rpow delta ((1 / N') * h) := by rw [h2]
    _ = (Real.rpow delta (1 / N')) ^ h := Real.rpow_mul hdelta_nonneg (1 / N') h
    _ = Real.rpow r h := by rfl

  -- q^m = r^(m*h)
  have h_q_pow : ∀ (m : ℕ), q ^ m = Real.rpow r ((m : ℝ) * h) := by
    intro m
    have h1 : (q ^ m : ℝ) = q ^ (m : ℝ) := (Real.rpow_natCast q m).symm
    calc (q ^ m : ℝ)
      = q ^ (m : ℝ) := h1
    _ = (Real.rpow r h) ^ (m : ℝ) := by rw [h_q]
    _ = Real.rpow r (h * (m : ℝ)) := (Real.rpow_mul hr_nonneg h (m : ℝ)).symm
    _ = Real.rpow r ((m : ℝ) * h) := by ring_nf

  -- Term bound
  have h_term : ∀ (k : Fin N), i < k →
      (Real.sqrt (rho i) / Real.sqrt (rho k) + 2) * L k <
      3 * L i * q ^ ((k : ℕ) - (i : ℕ)) := by
    intro k hk
    let m : ℕ := (k : ℕ) - (i : ℕ)
    have hm_pos : 0 < m := by omega
    have hk_eq : (k : ℕ) = (i : ℕ) + m := by omega
    set ii : ℝ := ((i : ℕ) + 1 : ℝ) with hii
    set kk : ℝ := ((k : ℕ) + 1 : ℝ) with hkk
    have hkk_eq : kk = ii + (m : ℝ) := by
      simp [ii, kk, hk_eq] <;> ring

    have h_sqrt_i : Real.sqrt (rho i) = Real.rpow r (ii / 2) := by
      calc Real.sqrt (rho i)
        = Real.sqrt (Real.rpow r ii) := by rw [h_rho i]
      _ = (Real.rpow r ii) ^ (1 / 2 : ℝ) := Real.sqrt_eq_rpow (Real.rpow r ii)
      _ = Real.rpow r (ii * (1 / 2 : ℝ)) := (Real.rpow_mul hr_nonneg ii (1 / 2 : ℝ)).symm
      _ = Real.rpow r (ii / 2) := by ring_nf

    have h_sqrt_k : Real.sqrt (rho k) = Real.rpow r (kk / 2) := by
      calc Real.sqrt (rho k)
        = Real.sqrt (Real.rpow r kk) := by rw [h_rho k]
      _ = (Real.rpow r kk) ^ (1 / 2 : ℝ) := Real.sqrt_eq_rpow (Real.rpow r kk)
      _ = Real.rpow r (kk * (1 / 2 : ℝ)) := (Real.rpow_mul hr_nonneg kk (1 / 2 : ℝ)).symm
      _ = Real.rpow r (kk / 2) := by ring_nf

    have h_sub : ii / 2 - kk / 2 = -(m : ℝ) / 2 := by
      simp [ii, kk, hkk_eq] <;> ring

    have h_ratio : Real.sqrt (rho i) / Real.sqrt (rho k) = Real.rpow r (-(m : ℝ) / 2) := by
      calc Real.sqrt (rho i) / Real.sqrt (rho k)
        = Real.rpow r (ii / 2) / Real.rpow r (kk / 2) := by rw [h_sqrt_i, h_sqrt_k]
      _ = Real.rpow r (ii / 2 - kk / 2) := (Real.rpow_sub hr_pos (ii / 2) (kk / 2)).symm
      _ = Real.rpow r (-(m : ℝ) / 2) := by rw [h_sub]

    have h_expand : kk * e = ii * e + (m : ℝ) * e := by
      simp [ii, kk, hkk_eq] <;> ring

    have h_Lk : L k = L i * Real.rpow r ((m : ℝ) * e) := by
      calc L k
        = Real.rpow r (kk * e) := h_L k
      _ = Real.rpow r (ii * e + (m : ℝ) * e) := by rw [h_expand]
      _ = Real.rpow r (ii * e) * Real.rpow r ((m : ℝ) * e) := Real.rpow_add hr_pos (ii * e) ((m : ℝ) * e)
      _ = L i * Real.rpow r ((m : ℝ) * e) := by rw [←h_L i] <;> ring

    have h_me : (m : ℝ) * e = (m : ℝ) / 2 + (m : ℝ) * h := by
      simp [e] <;> ring

    have h_Lk2 : L k = L i * Real.rpow r ((m : ℝ) / 2) * q ^ m := by
      calc L k
        = L i * Real.rpow r ((m : ℝ) * e) := h_Lk
      _ = L i * Real.rpow r ((m : ℝ) / 2 + (m : ℝ) * h) := by rw [h_me]
      _ = L i * (Real.rpow r ((m : ℝ) / 2) * Real.rpow r ((m : ℝ) * h)) := by
        have h_add : Real.rpow r ((m : ℝ) / 2 + (m : ℝ) * h) =
            Real.rpow r ((m : ℝ) / 2) * Real.rpow r ((m : ℝ) * h) :=
          Real.rpow_add hr_pos ((m : ℝ) / 2) ((m : ℝ) * h)
        rw [h_add]
      _ = L i * Real.rpow r ((m : ℝ) / 2) * q ^ m := by rw [h_q_pow m] <;> ring

    have h_rm2_lt_one : Real.rpow r ((m : ℝ) / 2) < 1 :=
      Real.rpow_lt_one hr_nonneg hr_lt_one (by positivity)

    have h_Lk_lt : L k < L i * q ^ m := by
      rw [h_Lk2]
      have h10 : L i * Real.rpow r ((m : ℝ) / 2) < L i * 1 :=
        mul_lt_mul_of_pos_left h_rm2_lt_one hL_i_pos
      have h10' : L i * Real.rpow r ((m : ℝ) / 2) < L i := by
        rwa [mul_one] at h10
      have h11 : (L i * Real.rpow r ((m : ℝ) / 2)) * q ^ m < L i * q ^ m :=
        mul_lt_mul_of_pos_right h10' (by positivity)
      exact h11

    have h_inv_mul : Real.rpow r (-(m : ℝ) / 2) * Real.rpow r ((m : ℝ) / 2) = 1 := by
      have h3 := Real.rpow_add hr_pos (-(m : ℝ) / 2) ((m : ℝ) / 2)
      have h4 : -(m : ℝ) / 2 + (m : ℝ) / 2 = 0 := by ring
      rw [h4] at h3
      simpa using h3.symm

    have h_ratio_mul : (Real.sqrt (rho i) / Real.sqrt (rho k)) * L k = L i * q ^ m := by
      calc (Real.sqrt (rho i) / Real.sqrt (rho k)) * L k
        = Real.rpow r (-(m : ℝ) / 2) * L k := by rw [h_ratio]
      _ = Real.rpow r (-(m : ℝ) / 2) * (L i * Real.rpow r ((m : ℝ) / 2) * q ^ m) := by rw [h_Lk2]
      _ = L i * (Real.rpow r (-(m : ℝ) / 2) * Real.rpow r ((m : ℝ) / 2)) * q ^ m := by ring
      _ = L i * 1 * q ^ m := by rw [h_inv_mul] <;> ring
      _ = L i * q ^ m := by ring

    calc
      (Real.sqrt (rho i) / Real.sqrt (rho k) + 2) * L k
        = (Real.sqrt (rho i) / Real.sqrt (rho k)) * L k + 2 * L k := by ring
      _ = L i * q ^ m + 2 * L k := by rw [h_ratio_mul]
      _ < L i * q ^ m + 2 * (L i * q ^ m) := by gcongr
      _ = 3 * L i * q ^ m := by ring

  -- Reindex
  let M : ℕ := N - (i : ℕ)
  let g : ℕ → Fin N := fun m =>
    if h : (i : ℕ) + m < N then ⟨(i : ℕ) + m, h⟩ else ⟨0, hN_pos⟩
  have h_g_val : ∀ m ∈ Finset.Ico 1 M, (g m).val = (i : ℕ) + m := by
    intro m hm
    have h1 : (i : ℕ) + m < N := by
      have h2 : m < M := (Finset.mem_Ico.mp hm).2
      omega
    have h3 : g m = ⟨(i : ℕ) + m, h1⟩ := by
      simp [g, h1]
      <;> aesop
    rw [h3] <;> rfl

  have h_filter_eq : Finset.univ.filter (fun k : Fin N => i < k) =
      Finset.image g (Finset.Ico 1 M) := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image, Finset.mem_Ico]
    constructor
    · intro hk
      have hki : i < k := hk
      let m : ℕ := (k : ℕ) - (i : ℕ)
      have hm1 : 1 ≤ m := by omega
      have hm2 : m < M := by omega
      refine ⟨m, ⟨hm1, hm2⟩, ?_⟩
      apply Fin.ext
      have h4 : (g m).val = (i : ℕ) + m := h_g_val m (Finset.mem_Ico.mpr ⟨hm1, hm2⟩)
      omega
    · intro h
      rcases h with ⟨m, hm, h_eq⟩
      have h2 : (g m).val = (i : ℕ) + m := h_g_val m (Finset.mem_Ico.mpr hm)
      have h3 : i < g m := by
        apply Fin.lt_iff_val_lt_val.mpr
        rw [h2]
        <;> omega
      simpa [h_eq] using h3

  have h_inj : Set.InjOn g (Finset.Ico 1 M) := by
    intro m1 hm1 m2 hm2 h
    have h_eq1 : (g m1).val = (i : ℕ) + m1 := h_g_val m1 hm1
    have h_eq2 : (g m2).val = (i : ℕ) + m2 := h_g_val m2 hm2
    have h_val_eq : (g m1).val = (g m2).val := by
      rw [h]
    rw [h_eq1, h_eq2] at h_val_eq
    omega

  have h_sum_reindex : ∑ k ∈ Finset.univ.filter (fun k : Fin N => i < k),
      (Real.sqrt (rho i) / Real.sqrt (rho k) + 2) * L k =
      ∑ m ∈ Finset.Ico 1 M,
        (Real.sqrt (rho i) / Real.sqrt (rho (g m)) + 2) * L (g m) := by
    rw [h_filter_eq, Finset.sum_image h_inj] <;> rfl

  rw [h_sum_reindex]

  -- Geometric series bound
  have h_geom : ∑ m ∈ Finset.Ico 1 M, q ^ m ≤ q / (1 - q) := by
    by_cases hM : M ≤ 1
    · have h_empty : Finset.Ico 1 M = ∅ := by
        ext x; simp [hM] <;> omega
      rw [h_empty]
      exact div_nonneg hq_nonneg (by linarith)
    · have hM' : 1 < M := by omega
      have h_sum_formula : ∑ m ∈ Finset.Ico 1 M, q ^ m = (q - q ^ M) / (1 - q) := by
        rw [geom_sum_Ico' hq_lt_one.ne (by omega)] <;> ring
      rw [h_sum_formula]
      have h_pos : 0 < q ^ M := by positivity
      have h_denom_pos : 0 < 1 - q := by linarith
      have h : (q - q ^ M) / (1 - q) ≤ q / (1 - q) := by
        apply div_le_div_of_nonneg_right
        · linarith
        · linarith
      exact h

  have h_q_div_lt : q / (1 - q) < 1 / 8 := by
    have h4 : 0 < 1 - q := by linarith
    have h5 : q / (1 - q) < (1 / 9 : ℝ) / (1 - 1 / 9 : ℝ) := by gcongr <;> linarith
    norm_num at h5 ⊢ <;> linarith

  have h_main_bound : ∑ m ∈ Finset.Ico 1 M, 3 * L i * q ^ m < (2 / 3 : ℝ) * L i := by
    have h1 : ∑ m ∈ Finset.Ico 1 M, 3 * L i * q ^ m =
        3 * L i * ∑ m ∈ Finset.Ico 1 M, q ^ m := by
      rw [Finset.mul_sum] <;> ring
    rw [h1]
    have h2 : 3 * L i * ∑ m ∈ Finset.Ico 1 M, q ^ m ≤ 3 * L i * (q / (1 - q)) := by gcongr
    have h3 : 3 * L i * (q / (1 - q)) < 3 * L i * (1 / 8 : ℝ) := by gcongr
    have h4 : 3 * L i * (1 / 8 : ℝ) < (2 / 3 : ℝ) * L i := by
      have h5 : 0 < L i := hL_i_pos
      nlinarith
    linarith

  by_cases h_nonempty : (Finset.Ico 1 M).Nonempty
  · have h_sum_lt2 : ∑ m ∈ Finset.Ico 1 M,
        (Real.sqrt (rho i) / Real.sqrt (rho (g m)) + 2) * L (g m) <
        ∑ m ∈ Finset.Ico 1 M, 3 * L i * q ^ m := by
      have h_strict : ∀ m ∈ Finset.Ico 1 M,
          (Real.sqrt (rho i) / Real.sqrt (rho (g m)) + 2) * L (g m) <
          3 * L i * q ^ m := by
        intro m hm
        have h2 : (g m).val = (i : ℕ) + m := h_g_val m hm
        have hgm : i < g m := by
          apply Fin.lt_iff_val_lt_val.mpr
          rw [h2]
          have h3 : (i : ℕ) < (i : ℕ) + m := by
            have h4 : 1 ≤ m := (Finset.mem_Ico.mp hm).1
            omega
          exact h3
        have h_exp_eq : (g m).val - (i : ℕ) = m := by
          rw [h2] <;> omega
        have h_res := h_term (g m) hgm
        rw [h_exp_eq] at h_res
        exact h_res
      exact Finset.sum_lt_sum_of_nonempty h_nonempty h_strict
    exact h_sum_lt2.trans h_main_bound
  · have h_empty : Finset.Ico 1 M = ∅ := by simpa using h_nonempty
    rw [h_empty]
    exact mul_pos (by norm_num) hL_i_pos

/--
Total volume removal geometric series bound:
`∑_{k=0}^{N-1} ρ_k^h < (9/8) * δ^{h/N}`.

Since `ρ_k = δ^{(k+1)/N}`, we have `ρ_k^h = q^{k+1}` where `q = δ^{h/N}`.
The sum is `q + q^2 + ... + q^N < q/(1-q) < (9/8)q` when `q < 1/9`.
-/
lemma geometric_series_total_volume_bound
    {N : ℕ} {delta hierarchyLoss : ℝ}
    (hN_pos : 0 < N)
    (hdelta_pos : 0 < delta)
    (hdelta_lt_one : delta < 1)
    (hh_pos : 0 < hierarchyLoss)
    (h_cond : Real.rpow delta (hierarchyLoss / (N : ℝ)) < 1 / 9) :
    ∑ k ∈ (Finset.univ : Finset (Fin N)),
      Real.rpow (wz1Corollary26Scale delta N k) hierarchyLoss <
      (9 / 8 : ℝ) * Real.rpow delta (hierarchyLoss / (N : ℝ)) := by
  let N' : ℝ := (N : ℝ)
  let q : ℝ := Real.rpow delta (hierarchyLoss / N')
  have hq_pos : 0 < q := Real.rpow_pos_of_pos hdelta_pos _
  have hq_nonneg : 0 ≤ q := hq_pos.le
  have hq_lt_one : q < 1 := by linarith
  have hq_lt_ninth : q < 1 / 9 := h_cond
  have h1 : ∀ (k : Fin N), Real.rpow (wz1Corollary26Scale delta N k) hierarchyLoss =
      q ^ ((k : ℕ) + 1) := by
    intro k
    set x : ℝ := Real.rpow delta (hierarchyLoss / N') with hx_def
    have hx_nonneg : 0 ≤ x := by positivity
    have h_rho : wz1Corollary26Scale delta N k = Real.rpow delta (((k : ℕ) + 1 : ℝ) / N') := by
      simp [wz1Corollary26Scale] <;> rfl
    have h_pos : 0 ≤ delta := by positivity
    let y : ℝ := ((k : ℕ) + 1 : ℝ) / N'
    have h_rho : wz1Corollary26Scale delta N k = Real.rpow delta y := by
      simp [wz1Corollary26Scale, y] <;> rfl
    have h_step1 : Real.rpow (wz1Corollary26Scale delta N k) hierarchyLoss =
        Real.rpow delta (y * hierarchyLoss) := by
      rw [h_rho]
      exact (Real.rpow_mul h_pos y hierarchyLoss).symm
    have h_mul : y * hierarchyLoss = (hierarchyLoss / N') * ((k : ℕ) + 1 : ℝ) := by
      dsimp only [y] <;> ring
    have h_step2 : Real.rpow delta (y * hierarchyLoss) =
        Real.rpow delta ((hierarchyLoss / N') * ((k : ℕ) + 1 : ℝ)) := by
      rw [h_mul]
    have h_rpow_mul2 : Real.rpow delta ((hierarchyLoss / N') * ((k : ℕ) + 1 : ℝ)) =
        Real.rpow (Real.rpow delta (hierarchyLoss / N')) ((k : ℕ) + 1 : ℝ) := by
      exact Real.rpow_mul h_pos (hierarchyLoss / N') ((k : ℕ) + 1 : ℝ)
    have h_nat : Real.rpow (Real.rpow delta (hierarchyLoss / N')) ((k : ℕ) + 1 : ℝ) =
        (Real.rpow delta (hierarchyLoss / N')) ^ ((k : ℕ) + 1) := by
      let x := Real.rpow delta (hierarchyLoss / N')
      let n : ℕ := (k : ℕ) + 1
      have h_eq1 : ((k : ℕ) + 1 : ℝ) = (n : ℝ) := by norm_cast
      have h_eq2 : x ^ ((k : ℕ) + 1) = x ^ n := by norm_cast
      rw [h_eq1, h_eq2]
      exact Real.rpow_natCast x n
    rw [h_step1, h_step2, h_rpow_mul2, h_nat] <;> rfl
  have h_sum_eq : ∑ k ∈ (Finset.univ : Finset (Fin N)), Real.rpow (wz1Corollary26Scale delta N k) hierarchyLoss =
      ∑ k ∈ (Finset.univ : Finset (Fin N)), q ^ ((k : ℕ) + 1) := by
    apply Finset.sum_congr rfl
    intro k _
    exact h1 k
  rw [h_sum_eq]
  have h_sum_geom : ∑ k ∈ (Finset.univ : Finset (Fin N)), q ^ ((k : ℕ) + 1) =
      q * ∑ m ∈ Finset.range N, q ^ m := by
    have h_eq : ∑ k ∈ (Finset.univ : Finset (Fin N)), q ^ ((k : ℕ) + 1) =
        ∑ m ∈ Finset.range N, q ^ (m + 1) := by
      apply Finset.sum_bij' (fun (k : Fin N) _ => (k : ℕ)) (fun m hm => ⟨m, Finset.mem_range.mp hm⟩)
      <;> simp [Fin.ext_iff] <;> omega
    rw [h_eq]
    have h2 : ∑ m ∈ Finset.range N, q ^ (m + 1) = q * ∑ m ∈ Finset.range N, q ^ m := by
      have h3 : ∀ m ∈ Finset.range N, q ^ (m + 1) = q * q ^ m := by
        intro m _; ring
      rw [Finset.sum_congr rfl h3, Finset.mul_sum]
    exact h2
  rw [h_sum_geom]
  have h_geom_sum : ∑ m ∈ Finset.range N, q ^ m < 1 / (1 - q) := by
    have hq_ne_one : q ≠ 1 := hq_lt_one.ne
    have h_formula : ∑ m ∈ Finset.range N, q ^ m = (1 - q ^ N) / (1 - q) := by
      rw [geom_sum_eq hq_ne_one N]
      have h : (q ^ N - 1) / (q - 1) = (1 - q ^ N) / (1 - q) := by
        have h1 : q - 1 ≠ 0 := by linarith
        field_simp [h1] <;> ring
      exact h
    rw [h_formula]
    have h_pos : 0 < 1 - q := by linarith
    have hqN_pos : 0 < q ^ N := pow_pos hq_pos N
    have h : (1 - q ^ N) / (1 - q) < 1 / (1 - q) := by
      apply div_lt_div_of_pos_right _ h_pos
      linarith
    exact h
  have h9 : 1 / (1 - q) < 9 / 8 := by
    have h10 : 0 < 1 - q := by linarith
    have h11 : q < 1 / 9 := hq_lt_ninth
    have h12 : 1 / (1 - q) < 9 / 8 := by
      calc 1 / (1 - q)
        < 1 / (1 - 1 / 9) := by gcongr
      _ = 9 / 8 := by norm_num
    exact h12
  have h13 : q * ∑ m ∈ Finset.range N, q ^ m < q * (1 / (1 - q)) := by
    exact mul_lt_mul_of_pos_left h_geom_sum hq_pos
  have h14 : q * (1 / (1 - q)) ≤ (9 / 8 : ℝ) * q := by
    have h15 : 1 / (1 - q) ≤ 9 / 8 := h9.le
    nlinarith
  exact h13.trans_le h14

/-! ## 5. Volume retention through multi-level thinning -/

/--
Volume removed from `t.core` at one level by thinning to popular cores.
TODO: prove this lemma.
-/
lemma single_level_removal_bound
    {N : ℕ} {delta : ℝ} {F : Kakeya.Streamlined.BodyFamily}
    {Z : Kakeya.Streamlined.Shading F}
    {rawTrapezoids : Fin N → Finset WZ1VerticalTrapezoid}
    {A_max : ENNReal} {L : Fin N → ℝ} {C : ℝ}
    {j k : Fin N}
    (hdelta_pos : 0 < delta)
    (h_length : ∀ i, ∀ t ∈ rawTrapezoids i, t.length ≤ Real.sqrt (wz1Corollary26Scale delta N i))
    (h_sep : ∀ i, ∀ t ∈ rawTrapezoids i, ∀ s ∈ rawTrapezoids i, t ≠ s →
      ∀ z ∈ t.core, ∀ w ∈ s.core, Real.sqrt (wz1Corollary26Scale delta N i) ≤ |z - w|)
    (h_coverage : ∀ i, ∀ z ∈ Set.Icc (-1 : ℝ) 1,
      horizontalSlice Z.union z ≠ ∅ → ∃ t ∈ rawTrapezoids i, z ∈ t.core)
    (hZ_height : ∀ point ∈ Z.union, point 2 ∈ Set.Icc (-1 : ℝ) 1)
    (Z_k : Kakeya.Streamlined.Shading F)
    (hZ_k_sub : IsSubshadingGeneric Z_k Z)
    (popular : Finset WZ1VerticalTrapezoid)
    (h_popular_def : ∀ s, s ∈ popular ↔ s ∈ rawTrapezoids k ∧ volumeInCoreGeneric Z_k s > A_max * ENNReal.ofReal (C * L k))
    (t : WZ1VerticalTrapezoid)
    (ht_len : t.length ≤ Real.sqrt (wz1Corollary26Scale delta N j))
    (hC_nonneg : 0 ≤ C) (hL_k_nonneg : 0 ≤ L k) :
    volume (Z_k.union ∩ {p : Point3 | p 2 ∈ t.core \ (⋃ s ∈ popular, s.core)}) ≤
    A_max * ENNReal.ofReal ((Real.sqrt (wz1Corollary26Scale delta N j) / Real.sqrt (wz1Corollary26Scale delta N k) + 2) * C * L k) := by
  classical
  let unpopular := (rawTrapezoids k).filter (fun s => s ∉ popular)
  let S := unpopular.filter (fun s => (s.core ∩ t.core).Nonempty)
  have hS_sub : S ⊆ rawTrapezoids k := by
    intro s hs
    have h1 : s ∈ unpopular := (Finset.mem_filter.mp hs).1
    exact (Finset.mem_filter.mp h1).1
  have hS_sep : ∀ (t1 : WZ1VerticalTrapezoid), t1 ∈ S → ∀ (s1 : WZ1VerticalTrapezoid), s1 ∈ S → t1 ≠ s1 →
      ∀ z ∈ t1.core, ∀ w ∈ s1.core, Real.sqrt (wz1Corollary26Scale delta N k) ≤ |z - w| := by
    intro t1 ht1 s1 hs1 hne z hz w hw
    have h1 : t1 ∈ rawTrapezoids k := by exact hS_sub ht1
    have h2 : s1 ∈ rawTrapezoids k := by exact hS_sub hs1
    exact h_sep k t1 h1 s1 h2 hne z hz w hw
  have h_intersect : ∀ s1 ∈ S, (s1.core ∩ t.core).Nonempty := by
    intro s1 hs1; exact (Finset.mem_filter.mp hs1).2
  have h_card : (S.card : ℝ) ≤ Real.sqrt (wz1Corollary26Scale delta N j) / Real.sqrt (wz1Corollary26Scale delta N k) + 2 :=
    count_intersecting_cores hdelta_pos h_length h_sep t ht_len S hS_sub hS_sep h_intersect
  have h_unpopular_vol : ∀ s1 ∈ S, volumeInCoreGeneric Z_k s1 ≤ A_max * ENNReal.ofReal (C * L k) := by
    intro s1 hs1
    have h1 : s1 ∈ unpopular := (Finset.mem_filter.mp hs1).1
    have h2 : s1 ∈ rawTrapezoids k := (Finset.mem_filter.mp h1).1
    have h3 : s1 ∉ popular := (Finset.mem_filter.mp h1).2
    have h4 : ¬(volumeInCoreGeneric Z_k s1 > A_max * ENNReal.ofReal (C * L k)) := by
      intro h5; exact h3 ((h_popular_def s1).mpr ⟨h2, h5⟩)
    exact le_of_not_gt h4
  let removedSet := Z_k.union ∩ {p : Point3 | p 2 ∈ t.core \ (⋃ s ∈ popular, s.core)}
  have h_cover : removedSet ⊆ ⋃ s1 ∈ S, (Z_k.union ∩ {p : Point3 | p 2 ∈ s1.core}) := by
    intro p hp
    have h_p_in_Zk : p ∈ Z_k.union := hp.1
    have h_p2_tcore : p 2 ∈ t.core := hp.2.1
    have h_p2_not_pop : p 2 ∉ (⋃ s ∈ popular, s.core) := hp.2.2
    have h_p2_in_Icc : p 2 ∈ Set.Icc (-1 : ℝ) 1 :=
      hZ_height p (hZ_k_sub.union_subset h_p_in_Zk)
    have h_slice_nonempty : horizontalSlice Z.union (p 2) ≠ ∅ := by
      have h6 : p ∈ horizontalSlice Z.union (p 2) := ⟨hZ_k_sub.union_subset h_p_in_Zk, rfl⟩
      have h7 : (horizontalSlice Z.union (p 2)).Nonempty := ⟨p, h6⟩
      exact h7.ne_empty
    rcases h_coverage k (p 2) h_p2_in_Icc h_slice_nonempty with ⟨s1, hs_raw, hs_core⟩
    have hs_not_pop : s1 ∉ popular := by
      intro hs_pop
      have h_in_pop : p 2 ∈ (⋃ s ∈ popular, s.core) := by
        simpa [Finset.mem_biUnion] using ⟨s1, hs_pop, hs_core⟩
      exact h_p2_not_pop h_in_pop
    have hs_in_S : s1 ∈ S := by
      have hs_in_unpopular : s1 ∈ unpopular := by
        rw [Finset.mem_filter] <;> exact ⟨hs_raw, hs_not_pop⟩
      rw [Finset.mem_filter] <;> exact ⟨hs_in_unpopular, ⟨p 2, hs_core, h_p2_tcore⟩⟩
    have h_in_union : p ∈ (⋃ s1 ∈ S, (Z_k.union ∩ {p : Point3 | p 2 ∈ s1.core})) := by
      have h2 : p ∈ (Z_k.union ∩ {p : Point3 | p 2 ∈ s1.core}) := ⟨h_p_in_Zk, hs_core⟩
      exact Set.mem_iUnion₂.mpr ⟨s1, hs_in_S, h2⟩
    exact h_in_union
  let A (s1 : WZ1VerticalTrapezoid) : Set Point3 := Z_k.union ∩ {p : Point3 | p 2 ∈ s1.core}
  have h_union_bound : ∀ (T : Finset WZ1VerticalTrapezoid),
      volume (⋃ s1 ∈ T, A s1) ≤ ∑ s1 ∈ T, volume (A s1) := by
    intro T
    induction T using Finset.induction with
    | empty => simp
    | @insert s T' hs ih =>
      have h1 : (⋃ s1 ∈ (insert s T'), A s1) = A s ∪ (⋃ s1 ∈ T', A s1) := by
        ext x
        simp [Finset.mem_insert, Set.mem_iUnion₂] <;> tauto
      rw [h1]
      have h2 : volume (A s ∪ (⋃ s1 ∈ T', A s1)) ≤ volume (A s) + volume (⋃ s1 ∈ T', A s1) := by
        apply MeasureTheory.measure_union_le (μ := volume)
      calc volume (A s ∪ (⋃ s1 ∈ T', A s1))
        ≤ volume (A s) + volume (⋃ s1 ∈ T', A s1) := h2
      _ ≤ volume (A s) + ∑ s1 ∈ T', volume (A s1) := by gcongr
      _ = ∑ s1 ∈ (insert s T'), volume (A s1) := by
        rw [Finset.sum_insert hs] <;> ring
  have h_vol1 : volume removedSet ≤ ∑ s1 ∈ S, volumeInCoreGeneric Z_k s1 := by
    calc volume removedSet
      ≤ volume (⋃ s1 ∈ S, A s1) := measure_mono h_cover
    _ ≤ ∑ s1 ∈ S, volume (A s1) := h_union_bound S
    _ = ∑ s1 ∈ S, volumeInCoreGeneric Z_k s1 := by rfl
  have h_vol2 : ∑ s1 ∈ S, volumeInCoreGeneric Z_k s1 ≤ ∑ s1 ∈ S, A_max * ENNReal.ofReal (C * L k) := by
    apply Finset.sum_le_sum; intro s1 hs1; exact h_unpopular_vol s1 hs1
  have h_vol3 : ∑ s1 ∈ S, A_max * ENNReal.ofReal (C * L k) = (S.card : ENNReal) * A_max * ENNReal.ofReal (C * L k) := by
    simp [Finset.sum_const] <;> ring
  let c : ℝ := Real.sqrt (wz1Corollary26Scale delta N j) / Real.sqrt (wz1Corollary26Scale delta N k) + 2
  have hc_nonneg : 0 ≤ c := by positivity
  have h_card' : (S.card : ENNReal) ≤ ENNReal.ofReal c := by
    have h : (S.card : ℝ) ≤ c := h_card
    have h' : ENNReal.ofReal (S.card : ℝ) ≤ ENNReal.ofReal c :=
      ENNReal.ofReal_le_ofReal h
    have h'' : (S.card : ENNReal) = ENNReal.ofReal (S.card : ℝ) := by
      simp
    rw [h'']
    exact h'
  have h_nonneg2 : 0 ≤ C * L k := mul_nonneg hC_nonneg hL_k_nonneg
  have h_main1 : volume removedSet ≤ (S.card : ENNReal) * A_max * ENNReal.ofReal (C * L k) := by
    calc volume removedSet
      ≤ ∑ s1 ∈ S, volumeInCoreGeneric Z_k s1 := h_vol1
    _ ≤ ∑ s1 ∈ S, A_max * ENNReal.ofReal (C * L k) := h_vol2
    _ = (S.card : ENNReal) * A_max * ENNReal.ofReal (C * L k) := h_vol3
  have h_mul : ENNReal.ofReal c * A_max * ENNReal.ofReal (C * L k) =
      A_max * ENNReal.ofReal (c * (C * L k)) := by
    have h1 : ENNReal.ofReal c * ENNReal.ofReal (C * L k) = ENNReal.ofReal (c * (C * L k)) := by
      have h : ENNReal.ofReal (c * (C * L k)) = ENNReal.ofReal c * ENNReal.ofReal (C * L k) :=
        ENNReal.ofReal_mul (hp := hc_nonneg)
      exact h.symm
    have h2 : ENNReal.ofReal c * A_max * ENNReal.ofReal (C * L k) =
        A_max * (ENNReal.ofReal c * ENNReal.ofReal (C * L k)) := by
      rw [mul_comm (ENNReal.ofReal c) A_max, mul_assoc]
    rw [h2, h1]
  calc volume removedSet
    ≤ (S.card : ENNReal) * A_max * ENNReal.ofReal (C * L k) := h_main1
  _ ≤ ENNReal.ofReal c * A_max * ENNReal.ofReal (C * L k) := by gcongr
  _ = A_max * ENNReal.ofReal (c * (C * L k)) := h_mul
  _ = A_max * ENNReal.ofReal ((Real.sqrt (wz1Corollary26Scale delta N j) / Real.sqrt (wz1Corollary26Scale delta N k) + 2) * C * L k) := by
    congr 1
    <;> simp [c] <;> ring_nf

/-! ## 6. Multi-level thinning with volume retention -/

/-- If t is popular, thinning by popular cores preserves volumeInCoreGeneric. -/
lemma popular_core_volume_preserved
    {F : Kakeya.Streamlined.BodyFamily}
    {Z Z_out : Kakeya.Streamlined.Shading F}
    {popular : Finset WZ1VerticalTrapezoid} {t : WZ1VerticalTrapezoid}
    (ht : t ∈ popular)
    (h_union : Z_out.union = Z.union \ {p : Point3 | p 2 ∉ (⋃ s ∈ popular, s.core)}) :
    volumeInCoreGeneric Z_out t = volumeInCoreGeneric Z t := by
  have h_sub : Z_out.union ⊆ Z.union := by
    rw [h_union]
    intro x hx
    exact hx.1
  have h1 : Z_out.union ∩ horizontalSlab t.left t.right =
      Z.union ∩ horizontalSlab t.left t.right := by
    apply Set.Subset.antisymm
    · exact Set.inter_subset_inter_left _ h_sub
    · intro p hp
      have h_p_in_Z : p ∈ Z.union := hp.1
      have h_p_in_slab : p ∈ horizontalSlab t.left t.right := hp.2
      have h_p2_in_core : p 2 ∈ t.core := by
        simpa [horizontalSlab, WZ1VerticalTrapezoid.core] using h_p_in_slab
      have h_p2_in_pop : p 2 ∈ (⋃ s ∈ popular, s.core) := Set.mem_iUnion₂.mpr ⟨t, ht, h_p2_in_core⟩
      have h61 : p ∉ {p : Point3 | p 2 ∉ (⋃ s ∈ popular, s.core)} := by simpa using h_p2_in_pop
      have h_p_in_Zout : p ∈ Z_out.union := by
        rw [h_union]; exact ⟨h_p_in_Z, h61⟩
      exact ⟨h_p_in_Zout, h_p_in_slab⟩
  have h2 : volumeInCoreGeneric Z_out t = volume (Z_out.union ∩ horizontalSlab t.left t.right) := by rfl
  have h3 : volumeInCoreGeneric Z t = volume (Z.union ∩ horizontalSlab t.left t.right) := by rfl
  rw [h2, h3, h1]

/-- Decompose volume before thinning into after-thinning plus removed set. -/
lemma thinning_volume_decomp
    {F : Kakeya.Streamlined.BodyFamily}
    {Z_prev Z_out : Kakeya.Streamlined.Shading F}
    {popular : Finset WZ1VerticalTrapezoid} {t : WZ1VerticalTrapezoid} {B : ENNReal}
    (h_union : Z_out.union = Z_prev.union \ {p : Point3 | p 2 ∉ (⋃ s ∈ popular, s.core)})
    (h_rem : volume (Z_prev.union ∩ {p : Point3 | p 2 ∈ t.core \ (⋃ s ∈ popular, s.core)}) ≤ B) :
    volumeInCoreGeneric Z_prev t ≤ volumeInCoreGeneric Z_out t + B := by
  let removedSet := Z_prev.union ∩ {p : Point3 | p 2 ∈ t.core \ (⋃ s ∈ popular, s.core)}
  have h1 : Z_prev.union ∩ horizontalSlab t.left t.right ⊆
      (Z_out.union ∩ horizontalSlab t.left t.right) ∪ removedSet := by
    intro p hp
    by_cases h5 : p 2 ∈ (⋃ s ∈ popular, s.core)
    · have h6 : p ∈ Z_out.union := by
        rw [h_union]
        have h61 : p ∉ {p : Point3 | p 2 ∉ (⋃ s ∈ popular, s.core)} := by
          simpa using h5
        exact ⟨hp.1, h61⟩
      exact Or.inl ⟨h6, hp.2⟩
    · have h7 : p 2 ∈ t.core := by simpa [horizontalSlab, WZ1VerticalTrapezoid.core] using hp.2
      exact Or.inr ⟨hp.1, ⟨h7, h5⟩⟩
  have h2 : volume ((Z_out.union ∩ horizontalSlab t.left t.right) ∪ removedSet) ≤
      volume (Z_out.union ∩ horizontalSlab t.left t.right) + volume removedSet := by
    exact MeasureTheory.measure_union_le (μ := volume) (s := (Z_out.union ∩ horizontalSlab t.left t.right)) (t := removedSet)
  calc volumeInCoreGeneric Z_prev t
    = volume (Z_prev.union ∩ horizontalSlab t.left t.right) := by rfl
  _ ≤ volume ((Z_out.union ∩ horizontalSlab t.left t.right) ∪ removedSet) := measure_mono h1
  _ ≤ volume (Z_out.union ∩ horizontalSlab t.left t.right) + volume removedSet := h2
  _ = volumeInCoreGeneric Z_out t + volume removedSet := by rfl
  _ ≤ volumeInCoreGeneric Z_out t + B := by gcongr

/--
Number of trapezoids at level `j` whose core intersects `[-1,1]` is at most
`4 / sqrt(rho_j)`, using separation and length bounds.
-/
lemma level_intersecting_count_bound
    {N : ℕ} {delta : ℝ}
    {rawTrapezoids : Fin N → Finset WZ1VerticalTrapezoid}
    {j : Fin N}
    (hdelta_pos : 0 < delta)
    (hdelta_lt_one : delta < 1)
    (h_length : ∀ t ∈ rawTrapezoids j, t.length ≤ Real.sqrt (wz1Corollary26Scale delta N j))
    (h_sep : ∀ t ∈ rawTrapezoids j, ∀ s ∈ rawTrapezoids j, t ≠ s →
      ∀ z ∈ t.core, ∀ w ∈ s.core, Real.sqrt (wz1Corollary26Scale delta N j) ≤ |z - w|) :
    ((rawTrapezoids j).filter (fun t => t.left ≤ 1 ∧ -1 ≤ t.right)).card ≤
      4 / Real.sqrt (wz1Corollary26Scale delta N j) := by
  let rho : ℝ := wz1Corollary26Scale delta N j
  let S : Finset WZ1VerticalTrapezoid :=
    (rawTrapezoids j).filter (fun t => t.left ≤ 1 ∧ -1 ≤ t.right)
  have h_rho_pos : 0 < rho := Real.rpow_pos_of_pos hdelta_pos _
  have h_sqrt_pos : 0 < Real.sqrt rho := Real.sqrt_pos.mpr h_rho_pos
  have hdelta_one : delta ≤ 1 := le_of_lt hdelta_lt_one
  have h_sqrt_le_one : Real.sqrt rho ≤ 1 := by
    have h1 : rho ≤ 1 := Real.rpow_le_one hdelta_pos.le hdelta_one (by positivity)
    exact Real.sqrt_le_one.mpr h1
  let leftEndpoints : Finset ℝ := S.image (fun t => t.left)
  have hS_sub : S ⊆ rawTrapezoids j := by
    intro t ht; exact (Finset.mem_filter.mp ht).1
  have h_inj : Set.InjOn (fun t : WZ1VerticalTrapezoid => t.left) S := by
    intro t ht s hs h_eq
    by_contra hne
    have h1 : t.left ∈ t.core := Set.left_mem_Icc.mpr t.left_lt_right.le
    have h2 : s.left ∈ s.core := Set.left_mem_Icc.mpr s.left_lt_right.le
    have h3 : Real.sqrt rho ≤ |t.left - s.left| :=
      h_sep t (hS_sub ht) s (hS_sub hs) hne t.left h1 s.left h2
    have h_eq' : t.left = s.left := by simpa using h_eq
    have h4 : t.left - s.left = 0 := by linarith
    have h5 : |t.left - s.left| = 0 := by
      rw [h4]
      simp
    have h6 : Real.sqrt rho ≤ 0 := by
      rw [h5] at h3
      exact h3
    exact not_le.mpr h_sqrt_pos h6
  have h_bounds : ∀ x ∈ leftEndpoints, -1 - Real.sqrt rho ≤ x ∧ x ≤ 1 := by
    intro x hx
    rcases Finset.mem_image.mp hx with ⟨t, ht, rfl⟩
    have h_filter : t.left ≤ 1 ∧ -1 ≤ t.right := (Finset.mem_filter.mp ht).2
    let z : ℝ := max t.left (-1)
    have hz_core : z ∈ t.core := by
      have h1 : t.left ≤ z := le_max_left _ _
      have h2 : z ≤ t.right := by
        have h3 : t.left ≤ t.right := t.left_lt_right.le
        have h4 : -1 ≤ t.right := h_filter.2
        exact max_le h3 h4
      exact ⟨h1, h2⟩
    have hz_Icc : z ∈ Set.Icc (-1 : ℝ) 1 := by
      have h1 : -1 ≤ z := le_max_right _ _
      have h2 : z ≤ 1 := by
        have h3 : t.left ≤ 1 := h_filter.1
        have h4 : (-1 : ℝ) ≤ 1 := by norm_num
        exact max_le h3 h4
      exact ⟨h1, h2⟩
    have h4 : t.left ≤ z := hz_core.1
    have h5 : z ≤ 1 := hz_Icc.2
    have h6 : t.length ≤ Real.sqrt rho := h_length t (hS_sub ht)
    have h7 : z - t.length ≤ t.left := by
      dsimp only [WZ1VerticalTrapezoid.length]
      have h8 : z ≤ t.right := hz_core.2
      linarith
    have h9 : z - Real.sqrt rho ≤ t.left := by linarith [h6, h7]
    have h10 : -1 - Real.sqrt rho ≤ t.left := by linarith [hz_Icc.1, h9]
    exact ⟨h10, by linarith⟩
  have h_sep' : ∀ x ∈ leftEndpoints, ∀ y ∈ leftEndpoints, x ≠ y → Real.sqrt rho ≤ |x - y| := by
    intro x hx y hy hne
    rcases Finset.mem_image.mp hx with ⟨t, ht, rfl⟩
    rcases Finset.mem_image.mp hy with ⟨s, hs, rfl⟩
    have h_ts : t ≠ s := by intro h; rw [h] at hne; exact hne rfl
    have h1 : t.left ∈ t.core := Set.left_mem_Icc.mpr t.left_lt_right.le
    have h2 : s.left ∈ s.core := Set.left_mem_Icc.mpr s.left_lt_right.le
    exact h_sep t (hS_sub ht) s (hS_sub hs) h_ts t.left h1 s.left h2
  have h_card_left : leftEndpoints.card = S.card := by
    rw [Finset.card_image_of_injOn h_inj]
  have h_main := real_packing_bound h_sqrt_pos (by linarith) h_bounds h_sep'
  rw [h_card_left] at h_main
  have h9 : (1 - (-1 - Real.sqrt rho)) = 2 + Real.sqrt rho := by ring
  rw [h9] at h_main
  have h10 : (2 + Real.sqrt rho) / Real.sqrt rho + 1 ≤ 4 / Real.sqrt rho := by
    have h11 : 0 < Real.sqrt rho := h_sqrt_pos
    have h12 : Real.sqrt rho ≤ 1 := h_sqrt_le_one
    field_simp [h11.ne'] <;> nlinarith
  exact le_trans h_main h10

/--
Total volume removed in one popularity-thinning step, bounded by packing.

The removed set is covered by unpopular cores intersecting `[-1,1]`.
By separation, there are at most `4/√ρ_j` such cores, each with volume
at most `A_max * 3*L(j)`. Thus the removed volume is at most
`12 * A_max * ρ_j^hierarchyLoss`.
-/
lemma single_level_thin_removed_volume
    {N : ℕ} {delta hierarchyLoss C : ℝ} {F : Kakeya.Streamlined.BodyFamily}
    {Z Z_prev Z_out : Kakeya.Streamlined.Shading F}
    {rawTrapezoids : Fin N → Finset WZ1VerticalTrapezoid}
    {A_max : ENNReal} {L : Fin N → ℝ}
    {j : Fin N}
    (hC_nonneg : 0 ≤ C)
    (hL_pos : 0 ≤ L j)
    (hL_eq : L j = Real.rpow (wz1Corollary26Scale delta N j) (1 / 2 + hierarchyLoss))
    (h_slab_bound : ∀ (a b : ℝ), a ≤ b →
      volume (Z_prev.union ∩ horizontalSlab a b) ≤ A_max * ENNReal.ofReal (b - a))
    (h_length : ∀ t ∈ rawTrapezoids j, t.length ≤ Real.sqrt (wz1Corollary26Scale delta N j))
    (h_sep : ∀ t ∈ rawTrapezoids j, ∀ s ∈ rawTrapezoids j, t ≠ s →
      ∀ z ∈ t.core, ∀ w ∈ s.core, Real.sqrt (wz1Corollary26Scale delta N j) ≤ |z - w|)
    (h_coverage : ∀ z ∈ Set.Icc (-1 : ℝ) 1,
      horizontalSlice Z.union z ≠ ∅ → ∃ t ∈ rawTrapezoids j, z ∈ t.core)
    (hZ_prev_sub : IsSubshadingGeneric Z_prev Z)
    (hZ_prev_height : ∀ point ∈ Z_prev.union,
      point 2 ∈ Set.Icc (-1 : ℝ) 1)
    (hdelta_pos : 0 < delta)
    (hdelta_lt_one : delta < 1)
    (hhierarchyLoss_pos : 0 < hierarchyLoss)
    (popular : Finset WZ1VerticalTrapezoid)
    (h_popular_def : ∀ s, s ∈ popular ↔ s ∈ rawTrapezoids j ∧ volumeInCoreGeneric Z_prev s > A_max * ENNReal.ofReal (C * L j))
    (h_union : Z_out.union = Z_prev.union \ {p : Point3 | p 2 ∉ (⋃ s ∈ popular, s.core)}) :
    volume Z_prev.union ≤ volume Z_out.union +
      A_max * ENNReal.ofReal (4 * C * Real.rpow (wz1Corollary26Scale delta N j) hierarchyLoss) := by
  classical
  let rho : ℝ := wz1Corollary26Scale delta N j
  let S_all : Finset WZ1VerticalTrapezoid :=
    (rawTrapezoids j).filter (fun t => t.left ≤ 1 ∧ -1 ≤ t.right)
  let unpopular := S_all.filter (fun s => s ∉ popular)
  have hS_sub : S_all ⊆ rawTrapezoids j := by
    intro t ht; exact (Finset.mem_filter.mp ht).1
  have h_unpopular_sub : unpopular ⊆ S_all := by
    intro s hs; exact (Finset.mem_filter.mp hs).1
  let removedSet := Z_prev.union \ Z_out.union
  have h_removed_eq : removedSet = Z_prev.union ∩ {p : Point3 | p 2 ∉ (⋃ s ∈ popular, s.core)} := by
    ext p
    simp only [removedSet, Set.mem_sdiff, Set.mem_inter_iff, Set.mem_setOf_eq]
    constructor
    · rintro ⟨h4, h5⟩
      have h6 : p 2 ∉ (⋃ s ∈ popular, s.core) := by
        by_contra h7
        have h7' : p 2 ∈ (⋃ s ∈ popular, s.core) := by simpa using h7
        have h8 : p ∈ Z_out.union := by
          have h9 : p ∈ Z_prev.union ∩ {p : Point3 | p 2 ∈ (⋃ s ∈ popular, s.core)} := ⟨h4, h7'⟩
          rw [h_union]
          simpa [Set.mem_sdiff, Set.mem_setOf_eq] using h9
        exact h5 h8
      exact ⟨h4, h6⟩
    · rintro ⟨h4, h6⟩
      have h5 : p ∉ Z_out.union := by
        intro h5
        have h5' : p ∈ Z_prev.union \ {p : Point3 | p 2 ∉ (⋃ s ∈ popular, s.core)} := by
          rwa [h_union] at h5
        have h7 : p 2 ∈ (⋃ s ∈ popular, s.core) := by
          simpa [Set.mem_sdiff, Set.mem_setOf_eq] using h5'.2
        exact h6 h7
      exact ⟨h4, h5⟩
  have h_cover : removedSet ⊆ ⋃ t ∈ unpopular, (Z_prev.union ∩ horizontalSlab t.left t.right) := by
    intro p hp
    have h_p_in : p ∈ Z_prev.union := hp.1
    have h_p2_not_pop : p 2 ∉ (⋃ s ∈ popular, s.core) := by
      rw [h_removed_eq] at hp; exact hp.2
    have h_p2_in_Icc : p 2 ∈ Set.Icc (-1 : ℝ) 1 :=
      hZ_prev_height p h_p_in
    have h_p_in_Z : p ∈ Z.union := hZ_prev_sub.union_subset h_p_in
    have h_slice_nonempty : horizontalSlice Z.union (p 2) ≠ ∅ := by
      have h6 : p ∈ horizontalSlice Z.union (p 2) := ⟨h_p_in_Z, rfl⟩
      exact Set.nonempty_iff_ne_empty.mp ⟨p, h6⟩
    rcases h_coverage (p 2) h_p2_in_Icc h_slice_nonempty with ⟨t, ht_raw, ht_core⟩
    have ht_in_Sall : t ∈ S_all := by
      rw [Finset.mem_filter]
      have h1 : t.left ≤ p 2 := ht_core.1
      have h2 : p 2 ≤ t.right := ht_core.2
      have h3 : t.left ≤ 1 := by linarith [h_p2_in_Icc.2]
      have h4 : -1 ≤ t.right := by linarith [h_p2_in_Icc.1]
      exact ⟨ht_raw, ⟨h3, h4⟩⟩
    have ht_not_pop : t ∉ popular := by
      intro ht_pop
      have h_in : p 2 ∈ (⋃ s ∈ popular, s.core) := by
        simpa [Finset.mem_biUnion] using ⟨t, ht_pop, ht_core⟩
      exact h_p2_not_pop h_in
    have ht_in_unpopular : t ∈ unpopular := by
      rw [Finset.mem_filter] <;> exact ⟨ht_in_Sall, ht_not_pop⟩
    have h_in_slab : p ∈ Z_prev.union ∩ horizontalSlab t.left t.right := by
      have h9 : t.left ≤ p 2 := ht_core.1
      have h10 : p 2 ≤ t.right := ht_core.2
      exact ⟨h_p_in, ⟨h9, h10⟩⟩
    exact Set.mem_iUnion₂.mpr ⟨t, ht_in_unpopular, h_in_slab⟩
  have h_unpopular_vol : ∀ t ∈ unpopular, volumeInCoreGeneric Z_prev t ≤ A_max * ENNReal.ofReal (C * L j) := by
    intro t ht
    have h1 : t ∈ S_all := h_unpopular_sub ht
    have h2 : t ∈ rawTrapezoids j := hS_sub h1
    have h3 : t ∉ popular := (Finset.mem_filter.mp ht).2
    have h4 : ¬(volumeInCoreGeneric Z_prev t > A_max * ENNReal.ofReal (C * L j)) := by
      intro h5; exact h3 ((h_popular_def t).mpr ⟨h2, h5⟩)
    exact le_of_not_gt h4
  have h_card_le : (S_all.card : ℝ) ≤ 4 / Real.sqrt rho := by
    have h := level_intersecting_count_bound hdelta_pos hdelta_lt_one h_length h_sep
    simpa [S_all, rho] using h
  have h_rho_pos : 0 < rho := Real.rpow_pos_of_pos hdelta_pos _
  have h_sqrt_pos : 0 < Real.sqrt rho := Real.sqrt_pos.mpr h_rho_pos
  have hL_decomp : L j = Real.sqrt rho * rho ^ hierarchyLoss := by
    rw [hL_eq]
    have h2 : Real.rpow rho (1 / 2 + hierarchyLoss) =
        Real.rpow rho (1 / 2 : ℝ) * Real.rpow rho hierarchyLoss :=
      Real.rpow_add h_rho_pos (1 / 2 : ℝ) hierarchyLoss
    rw [h2]
    have h3 : Real.rpow rho (1 / 2 : ℝ) = Real.sqrt rho := by
      simp [Real.sqrt_eq_rpow]
    have h4 : Real.rpow rho hierarchyLoss = rho ^ hierarchyLoss := by
      simp
    rw [h3, h4] <;> ring
  have h_real_id : (4 / Real.sqrt rho) * (C * L j) = 4 * C * rho ^ hierarchyLoss := by
    rw [hL_decomp]
    have h_sqrt_ne_zero : Real.sqrt rho ≠ 0 := h_sqrt_pos.ne'
    field_simp [h_sqrt_ne_zero] <;> ring
  have h_vol_removed : volume removedSet ≤ ∑ t ∈ unpopular, volumeInCoreGeneric Z_prev t := by
    calc volume removedSet
      ≤ volume (⋃ t ∈ unpopular, (Z_prev.union ∩ horizontalSlab t.left t.right)) := measure_mono h_cover
    _ ≤ ∑ t ∈ unpopular, volume (Z_prev.union ∩ horizontalSlab t.left t.right) :=
        MeasureTheory.measure_biUnion_finset_le unpopular _
    _ = ∑ t ∈ unpopular, volumeInCoreGeneric Z_prev t := by rfl
  have h_sum_bound : ∑ t ∈ unpopular, volumeInCoreGeneric Z_prev t ≤
      (unpopular.card : ENNReal) * A_max * ENNReal.ofReal (C * L j) := by
    calc ∑ t ∈ unpopular, volumeInCoreGeneric Z_prev t
      ≤ ∑ t ∈ unpopular, A_max * ENNReal.ofReal (C * L j) :=
        Finset.sum_le_sum h_unpopular_vol
    _ = (unpopular.card : ENNReal) * A_max * ENNReal.ofReal (C * L j) := by
      simp [Finset.sum_const] <;> ring
  have h_card_le' : (unpopular.card : ENNReal) ≤ (S_all.card : ENNReal) := by
    exact_mod_cast Finset.card_le_card h_unpopular_sub
  have h_final : volume removedSet ≤ A_max * ENNReal.ofReal (4 * C * Real.rpow rho hierarchyLoss) := by
    calc volume removedSet
      ≤ ∑ t ∈ unpopular, volumeInCoreGeneric Z_prev t := h_vol_removed
    _ ≤ (unpopular.card : ENNReal) * A_max * ENNReal.ofReal (C * L j) := h_sum_bound
    _ ≤ (S_all.card : ENNReal) * A_max * ENNReal.ofReal (C * L j) := by gcongr
    _ ≤ ENNReal.ofReal (4 / Real.sqrt rho) * A_max * ENNReal.ofReal (C * L j) := by
      have h5 : (S_all.card : ENNReal) ≤ ENNReal.ofReal (4 / Real.sqrt rho) := by
        have h51 : (S_all.card : ENNReal) = ENNReal.ofReal (S_all.card : ℝ) := by simp
        rw [h51]
        exact ENNReal.ofReal_le_ofReal h_card_le
      gcongr
    _ = A_max * ENNReal.ofReal ((4 / Real.sqrt rho) * (C * L j)) := by
      have h_nonneg1 : 0 ≤ 4 / Real.sqrt rho := by positivity
      have h_nonneg2 : 0 ≤ C * L j := by positivity
      have h_mul : ENNReal.ofReal (4 / Real.sqrt rho) * ENNReal.ofReal (C * L j) =
          ENNReal.ofReal ((4 / Real.sqrt rho) * (C * L j)) := by
        rw [ENNReal.ofReal_mul h_nonneg1]
      have h_comm : ENNReal.ofReal (4 / Real.sqrt rho) * A_max * ENNReal.ofReal (C * L j) =
          A_max * (ENNReal.ofReal (4 / Real.sqrt rho) * ENNReal.ofReal (C * L j)) := by ring
      rw [h_comm, h_mul] <;> ring
    _ = A_max * ENNReal.ofReal (4 * C * rho ^ hierarchyLoss) := by rw [h_real_id]
  have h_sub : Z_out.union ⊆ Z_prev.union := by
    rw [h_union]
    exact Set.sdiff_subset
  have h1 : Z_prev.union = Z_out.union ∪ removedSet := by
    ext x
    simp only [removedSet, Set.mem_union, Set.mem_sdiff]
    constructor
    · intro hx
      by_cases h : x ∈ Z_out.union
      · exact Or.inl h
      · exact Or.inr ⟨hx, h⟩
    · rintro (h | h)
      · exact h_sub h
      · exact h.1
  have h_meas_out : MeasurableSet Z_out.union := by
    have h : Z_out.union = ⋃ i : Fin F.card, Z_out.carrier i := by
      ext x; simp [Kakeya.Streamlined.Shading.union] <;> rfl
    rw [h]
    exact MeasurableSet.iUnion (fun i => Z_out.measurable_carrier i)
  have h_meas_removed : MeasurableSet removedSet := by
    have h : removedSet = Z_prev.union \ Z_out.union := by rfl
    rw [h]
    have h1 : MeasurableSet Z_prev.union := by
      have h2 : Z_prev.union = ⋃ i : Fin F.card, Z_prev.carrier i := by
        ext x; simp [Kakeya.Streamlined.Shading.union] <;> rfl
      rw [h2]
      exact MeasurableSet.iUnion (fun i => Z_prev.measurable_carrier i)
    exact h1.diff h_meas_out
  have h_disj : Disjoint Z_out.union removedSet := by
    rw [Set.disjoint_left]; intro x hx1 hx2; exact hx2.2 hx1
  have h_decomp : volume Z_prev.union = volume Z_out.union + volume removedSet := by
    rw [h1]
    exact MeasureTheory.measure_union h_disj h_meas_removed
  rw [h_decomp]
  gcongr

/-- Helper to combine two ENNReal volume bounds transitively. -/
lemma combine_volume_bounds_helper {α : Type*} [MeasureTheory.MeasureSpace α] {s t u : Set α} {μ : MeasureTheory.Measure α} {a b : ENNReal}
    (h1 : μ s ≤ μ t + a) (h2 : μ t ≤ μ u + b) : μ s ≤ μ u + (a + b) := by
  calc μ s ≤ μ t + a := h1
       _ ≤ (μ u + b) + a := by gcongr
       _ = μ u + (a + b) := by abel

/-- Helper: `A_max * ofReal(a+b) = A_max * ofReal(a) + A_max * ofReal(b)` for nonneg a,b. -/
lemma ennreal_mul_add_helper {A_max : ENNReal} {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    A_max * ENNReal.ofReal (a + b) = A_max * ENNReal.ofReal a + A_max * ENNReal.ofReal b := by
  rw [ENNReal.ofReal_add ha hb, mul_add]

/-- Combine two volume bounds with real arithmetic done outside the induction. -/
lemma combine_volume_bounds_real {α : Type*} [MeasureTheory.MeasureSpace α] {s t u : Set α}
    {μ : MeasureTheory.Measure α} {A_max : ENNReal} {a b c : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (habc : a + b = c)
    (h1 : μ s ≤ μ t + A_max * ENNReal.ofReal a)
    (h2 : μ t ≤ μ u + A_max * ENNReal.ofReal b) :
    μ s ≤ μ u + A_max * ENNReal.ofReal c := by
  have h3 : A_max * ENNReal.ofReal c = A_max * ENNReal.ofReal a + A_max * ENNReal.ofReal b := by
    have h4 : c = a + b := habc.symm
    rw [h4, ennreal_mul_add_helper ha hb]
  have h5 : μ s ≤ μ u + (A_max * ENNReal.ofReal a + A_max * ENNReal.ofReal b) :=
    combine_volume_bounds_helper h1 h2
  rw [← h3] at h5
  exact h5

/--
Multi-level thinning with cumulative volume-retention invariant.
Processes levels 0..j. For each popular t at level i ≤ j,
`volumeInCoreGeneric Z_out t + ofReal(∑_{i<k≤j} term(i,k)) > ofReal(C * L_i)`.
-/
lemma multi_level_thin_with_retention_up_to
    {N : ℕ} {delta : ℝ} {F : Kakeya.Streamlined.BodyFamily}
    {Z : Kakeya.Streamlined.Shading F}
    {rawTrapezoids : Fin N → Finset WZ1VerticalTrapezoid}
    {A_max : ENNReal} {L : Fin N → ℝ} {C : ℝ}
    (hC_nonneg : 0 ≤ C)
    (hL_pos : ∀ j, 0 ≤ L j)
    (h_slab_bound : ∀ (a b : ℝ), a ≤ b →
      volume (Z.union ∩ horizontalSlab a b) ≤ A_max * ENNReal.ofReal (b - a))
    (h_length : ∀ i, ∀ t ∈ rawTrapezoids i, t.length ≤ Real.sqrt (wz1Corollary26Scale delta N i))
    (h_sep : ∀ i, ∀ t ∈ rawTrapezoids i, ∀ s ∈ rawTrapezoids i, t ≠ s →
      ∀ z ∈ t.core, ∀ w ∈ s.core, Real.sqrt (wz1Corollary26Scale delta N i) ≤ |z - w|)
    (h_coverage : ∀ i, ∀ z ∈ Set.Icc (-1 : ℝ) 1,
      horizontalSlice Z.union z ≠ ∅ → ∃ t ∈ rawTrapezoids i, z ∈ t.core)
    (hZ_height : ∀ point ∈ Z.union, point 2 ∈ Set.Icc (-1 : ℝ) 1)
    (hdelta_pos : 0 < delta)
    (hdelta_lt_one : delta < 1)
    (hierarchyLoss : ℝ)
    (hhierarchyLoss_pos : 0 < hierarchyLoss)
    (hL_eq : ∀ j, L j = Real.rpow (wz1Corollary26Scale delta N j) (1 / 2 + hierarchyLoss))
    (hN_pos : 0 < N)
    (h_level0_popular : ∃ t ∈ rawTrapezoids (⟨0, hN_pos⟩),
        volumeInCoreGeneric Z t > A_max * ENNReal.ofReal (C * L (⟨0, hN_pos⟩))) :
    ∀ (j : ℕ), j < N → ∀ (Z_j : Kakeya.Streamlined.Shading F), IsSubshadingGeneric Z_j Z →
      (hZ_j_eq_Z : Z_j = Z) →
    ∃ (Z_out : Kakeya.Streamlined.Shading F)
      (P : Fin N → Finset WZ1VerticalTrapezoid),
      IsSubshadingGeneric Z_out Z_j ∧
      (∀ (i : Fin N), (i : ℕ) ≤ j → P i ⊆ rawTrapezoids i) ∧
      (∀ (i : Fin N), (i : ℕ) ≤ j → ∀ z, horizontalSlice Z_out.union z ≠ ∅ → ∃ t ∈ P i, z ∈ t.core) ∧
      (∀ (i : Fin N), (i : ℕ) ≤ j → ∀ t ∈ P i,
        volumeInCoreGeneric Z_out t +
        A_max * ENNReal.ofReal (∑ k ∈ (Finset.univ.filter (fun k : Fin N => i < k ∧ (k : ℕ) ≤ j)),
          (Real.sqrt (wz1Corollary26Scale delta N i) / Real.sqrt (wz1Corollary26Scale delta N k) + 2) * C * L k)
        > A_max * ENNReal.ofReal (C * L i)) ∧
      (P ⟨0, hN_pos⟩).Nonempty ∧
      (volume Z.union ≤ volume Z_out.union +
        A_max * ENNReal.ofReal (4 * C * ∑ k ∈ Finset.univ.filter (fun k : Fin N => (k : ℕ) ≤ j),
          Real.rpow (wz1Corollary26Scale delta N k) hierarchyLoss)) ∧
      (∀ p ∈ Z_out.union, Z_out.pointMultiplicity p = Z.pointMultiplicity p) := by
  let term (i k : Fin N) : ℝ :=
    (Real.sqrt (wz1Corollary26Scale delta N i) / Real.sqrt (wz1Corollary26Scale delta N k) + 2) * C * L k
  let sum_up_to (i : Fin N) (m : ℕ) : Finset (Fin N) :=
    Finset.univ.filter (fun k => i < k ∧ (k : ℕ) ≤ m)
  intro j
  induction j with
  | zero =>
    intro hj Z_j hZ_j_sub hZ_j_eq_Z
    let j_fin : Fin N := ⟨0, hj⟩
    have h_slab_bound_j : ∀ (a b : ℝ), a ≤ b →
        volume (Z_j.union ∩ horizontalSlab a b) ≤ A_max * ENNReal.ofReal (b - a) := by
      intro a b hab
      have h1 : Z_j.union ∩ horizontalSlab a b ⊆ Z.union ∩ horizontalSlab a b :=
        Set.inter_subset_inter_left _ hZ_j_sub.union_subset
      exact (measure_mono h1).trans (h_slab_bound a b hab)
    have h_thresh_pos : 0 ≤ C * L j_fin := mul_nonneg hC_nonneg (hL_pos j_fin)
    rcases single_level_thin_only h_thresh_pos h_slab_bound_j with
      ⟨Z_out, P_0, hZ_out_sub, h_spec_0, h_cov_0, h_union_0, h_same_mult_0⟩
    let P : Fin N → Finset WZ1VerticalTrapezoid := fun i => if (i : ℕ) = 0 then P_0 else ∅
    have h_retention : ∀ (i : Fin N), (i : ℕ) ≤ 0 → ∀ t ∈ P i,
        volumeInCoreGeneric Z_out t + A_max * ENNReal.ofReal (∑ k ∈ sum_up_to i 0, term i k)
        > A_max * ENNReal.ofReal (C * L i) := by
      intro i hi t ht
      have h_i_zero : (i : ℕ) = 0 := by omega
      have hP : P i = P_0 := by dsimp only [P]; rw [if_pos h_i_zero]
      rw [hP] at ht
      have h_vol : volumeInCoreGeneric Z_j t > A_max * ENNReal.ofReal (C * L i) := by
        have h_i_eq : i = j_fin := by
          apply Fin.ext
          simpa [j_fin] using h_i_zero
        rw [h_i_eq]; exact ((h_spec_0 t).mp ht).2
      have h_eq : volumeInCoreGeneric Z_out t = volumeInCoreGeneric Z_j t :=
        popular_core_volume_preserved ht h_union_0
      have h_sum_empty : sum_up_to i 0 = ∅ := by ext k; simp [sum_up_to]; omega
      rw [h_eq, h_sum_empty]
      simpa using h_vol
    have hP0_nonempty : (P ⟨0, hN_pos⟩).Nonempty := by
      rcases h_level0_popular with ⟨t, ht_raw, ht_vol⟩
      have h_j0 : j_fin = (⟨0, hN_pos⟩ : Fin N) := by apply Fin.ext; simp [j_fin]
      have ht_vol_j : volumeInCoreGeneric Z_j t > A_max * ENNReal.ofReal (C * L j_fin) := by
        rw [h_j0, hZ_j_eq_Z]; exact ht_vol
      have h_t_in_P0 : t ∈ P_0 := (h_spec_0 t).mpr ⟨ht_raw, ht_vol_j⟩
      have hP : P ⟨0, hN_pos⟩ = P_0 := by dsimp only [P]; rw [if_pos rfl]
      rw [hP]; exact ⟨t, h_t_in_P0⟩
    have hZ_j_height : ∀ point ∈ Z_j.union,
        point 2 ∈ Set.Icc (-1 : ℝ) 1 := by
      rw [hZ_j_eq_Z]
      exact hZ_height
    have h_vol_bound0 : volume Z_j.union ≤ volume Z_out.union +
        A_max * ENNReal.ofReal (4 * C * Real.rpow (wz1Corollary26Scale delta N j_fin) hierarchyLoss) :=
      single_level_thin_removed_volume
        (C := C) hC_nonneg (hL_pos j_fin) (hL_eq j_fin) h_slab_bound_j
        (h_length j_fin) (h_sep j_fin) (h_coverage j_fin)
        hZ_j_sub hZ_j_height hdelta_pos hdelta_lt_one hhierarchyLoss_pos
        P_0 h_spec_0 h_union_0
    have h_vol_sum0 : (Finset.univ.filter (fun k : Fin N => (k : ℕ) ≤ 0)) = {j_fin} := by
      ext k
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
      have h_j0 : (j_fin : ℕ) = 0 := by simp [j_fin]
      have h_iff : (k : ℕ) ≤ 0 ↔ k = j_fin := by
        constructor
        · intro hle
          have h3 : (k : ℕ) = 0 := by omega
          apply Fin.ext
          rw [h3, h_j0]
        · intro heq
          have h : (k : ℕ) ≤ 0 := by
            rw [heq, h_j0] <;> norm_num
          exact h
      exact h_iff
    have h_vol_bound : volume Z.union ≤ volume Z_out.union +
        A_max * ENNReal.ofReal (4 * C * ∑ k ∈ Finset.univ.filter (fun k : Fin N => (k : ℕ) ≤ 0),
          Real.rpow (wz1Corollary26Scale delta N k) hierarchyLoss) := by
      have hZ_eq : Z_j = Z := hZ_j_eq_Z
      rw [h_vol_sum0, Finset.sum_singleton]
      rw [hZ_eq] at h_vol_bound0
      exact h_vol_bound0
    have h_same_mult : ∀ p ∈ Z_out.union, Z_out.pointMultiplicity p = Z.pointMultiplicity p := by
      intro p hp
      have h1 : Z_out.pointMultiplicity p = Z_j.pointMultiplicity p := h_same_mult_0 p hp
      rw [h1, hZ_j_eq_Z]
    refine ⟨Z_out, P, hZ_out_sub, ?_⟩
    constructor
    · intro i hi
      have h_i_zero : (i : ℕ) = 0 := by omega
      have hP : P i = P_0 := by dsimp only [P]; rw [if_pos h_i_zero]
      have h_i_eq : i = j_fin := by
        apply Fin.ext
        simpa [j_fin] using h_i_zero
      rw [hP, h_i_eq]; intro t ht; exact ((h_spec_0 t).mp ht).1
    · constructor
      · intro i hi z hz
        have h_i_zero : (i : ℕ) = 0 := by omega
        have hP : P i = P_0 := by dsimp only [P]; rw [if_pos h_i_zero]
        rw [hP]; exact h_cov_0 z hz
      · constructor
        · exact h_retention
        · constructor
          · exact hP0_nonempty
          · constructor
            · exact h_vol_bound
            · exact h_same_mult
  | succ j' ih =>
    intro hj Z_j hZ_j_sub hZ_j_eq_Z
    have h_j'_lt_N : j' < N := by omega
    rcases ih h_j'_lt_N Z_j hZ_j_sub hZ_j_eq_Z with
      ⟨Z_prev, P_prev, hZ_prev_sub, h_sub_prev, h_cov_prev, h_ret_prev, hP0_nonempty_prev, h_vol_prev, h_same_mult_prev⟩
    let j_fin : Fin N := ⟨j'.succ, hj⟩
    have h_prev_sub_Z : IsSubshadingGeneric Z_prev Z := fun i =>
      Set.Subset.trans (hZ_prev_sub i) (hZ_j_sub i)
    have h_slab_bound_prev : ∀ (a b : ℝ), a ≤ b →
        volume (Z_prev.union ∩ horizontalSlab a b) ≤ A_max * ENNReal.ofReal (b - a) := by
      intro a b hab
      have h1 : Z_prev.union ∩ horizontalSlab a b ⊆ Z.union ∩ horizontalSlab a b :=
        Set.inter_subset_inter_left _ h_prev_sub_Z.union_subset
      exact (measure_mono h1).trans (h_slab_bound a b hab)
    have h_thresh_pos : 0 ≤ C * L j_fin := mul_nonneg hC_nonneg (hL_pos j_fin)
    rcases single_level_thin_only h_thresh_pos h_slab_bound_prev with
      ⟨Z_out, P_j, hZ_out_sub, h_spec_j, h_cov_j, h_union_j, h_same_mult_step⟩
    let P : Fin N → Finset WZ1VerticalTrapezoid :=
      fun i => if (i : ℕ) = j'.succ then P_j else P_prev i
    have h_retention : ∀ (i : Fin N), (i : ℕ) ≤ j'.succ → ∀ t ∈ P i,
        volumeInCoreGeneric Z_out t + A_max * ENNReal.ofReal (∑ k ∈ sum_up_to i j'.succ, term i k)
        > A_max * ENNReal.ofReal (C * L i) := by
      intro i hi t ht
      by_cases h_i_j : (i : ℕ) = j'.succ
      · -- Case i = j'+1: newly popular, volume preserved
        have hP : P i = P_j := by dsimp only [P]; rw [if_pos h_i_j]
        rw [hP] at ht
        have h_vol : volumeInCoreGeneric Z_prev t > A_max * ENNReal.ofReal (C * L i) := by
          have h_i_eq : i = j_fin := by
            apply Fin.ext
            simpa [j_fin] using h_i_j
          rw [h_i_eq]; exact ((h_spec_j t).mp ht).2
        have h_eq : volumeInCoreGeneric Z_out t = volumeInCoreGeneric Z_prev t :=
          popular_core_volume_preserved ht h_union_j
        have h_sum_empty : sum_up_to i j'.succ = ∅ := by ext k; simp [sum_up_to, h_i_j]; omega
        rw [h_eq, h_sum_empty]; simpa using h_vol
      · -- Case i ≤ j': apply removal bound
        have h_i_le : (i : ℕ) ≤ j' := by omega
        have h_ne : (i : ℕ) ≠ j'.succ := h_i_j
        have hP : P i = P_prev i := by dsimp only [P]; rw [if_neg h_ne]
        rw [hP] at ht
        have h_t_raw : t ∈ rawTrapezoids i := h_sub_prev i h_i_le ht
        have h_t_len : t.length ≤ Real.sqrt (wz1Corollary26Scale delta N i) :=
          h_length i t h_t_raw
        have h_i_lt_jfin : i < j_fin := by
          apply Fin.lt_def.mpr
          have h1 : i.val ≤ j' := h_i_le
          have h2 : i.val < j'.succ := Nat.lt_succ_of_le h1
          simpa [j_fin] using h2
        have h_removal_bound : volume (Z_prev.union ∩ {p : Point3 | p 2 ∈ t.core \ (⋃ s ∈ P_j, s.core)}) ≤
            A_max * ENNReal.ofReal (term i j_fin) :=
          single_level_removal_bound hdelta_pos h_length h_sep h_coverage hZ_height
            Z_prev h_prev_sub_Z P_j h_spec_j t h_t_len hC_nonneg (hL_pos j_fin)
        have h_decomp : volumeInCoreGeneric Z_prev t ≤ volumeInCoreGeneric Z_out t + A_max * ENNReal.ofReal (term i j_fin) :=
          thinning_volume_decomp h_union_j h_removal_bound
        have h_sum_ext : sum_up_to i j'.succ = insert j_fin (sum_up_to i j') := by
          ext k
          simp only [sum_up_to, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
          constructor
          · rintro ⟨h_k_gt_i, h_k_le⟩
            by_cases h_k_eq : (k : ℕ) = j'.succ
            · have h_k_eq_jfin : k = j_fin := by
                apply Fin.ext
                simpa [j_fin] using h_k_eq
              exact Or.inl h_k_eq_jfin
            · have h_k_le_j : (k : ℕ) ≤ j' := by omega
              exact Or.inr ⟨h_k_gt_i, h_k_le_j⟩
          · rintro (rfl | ⟨h_k_gt_i, h_k_le⟩)
            · have h_i_lt_jfin : i < j_fin := by
                apply Fin.lt_def.mpr
                have h1 : i.val ≤ j' := h_i_le
                have h2 : i.val < j'.succ := Nat.lt_succ_of_le h1
                simpa [j_fin] using h2
              exact ⟨h_i_lt_jfin, by simp [j_fin]⟩
            · exact ⟨h_k_gt_i, by omega⟩
        have h_jfin_notin : j_fin ∉ sum_up_to i j' := by
          intro h
          simp only [sum_up_to, Finset.mem_filter, Finset.mem_univ, true_and] at h
          have h3 : (j_fin : ℕ) ≤ j' := h.2
          simp [j_fin] at h3 <;> omega
        have h_sum_eq : ∑ k ∈ sum_up_to i j'.succ, term i k =
            (∑ k ∈ sum_up_to i j', term i k) + term i j_fin := by
          rw [h_sum_ext, Finset.sum_insert h_jfin_notin] <;> ring
        have h_term_nonneg_all : ∀ (k : Fin N), 0 ≤ term i k := by
          intro k
          dsimp only [term]
          have h1 : 0 ≤ Real.sqrt (wz1Corollary26Scale delta N i) := Real.sqrt_nonneg _
          have h2 : 0 ≤ Real.sqrt (wz1Corollary26Scale delta N k) := Real.sqrt_nonneg _
          have h3 : 0 ≤ Real.sqrt (wz1Corollary26Scale delta N i) / Real.sqrt (wz1Corollary26Scale delta N k) := by positivity
          have h4 : 0 ≤ (Real.sqrt (wz1Corollary26Scale delta N i) / Real.sqrt (wz1Corollary26Scale delta N k) + 2) := by linarith
          exact mul_nonneg (mul_nonneg h4 hC_nonneg) (hL_pos k)
        have h_sum_prev_nonneg : 0 ≤ ∑ k ∈ sum_up_to i j', term i k := by
          apply Finset.sum_nonneg
          intro k _
          exact h_term_nonneg_all k
        have h_term_nonneg : 0 ≤ term i j_fin := h_term_nonneg_all j_fin
        set S := A_max * ENNReal.ofReal (∑ k ∈ sum_up_to i j', term i k) with hS
        set T := A_max * ENNReal.ofReal (term i j_fin) with hT
        have h1 : ENNReal.ofReal (∑ k ∈ sum_up_to i j'.succ, term i k) =
            ENNReal.ofReal (∑ k ∈ sum_up_to i j', term i k) + ENNReal.ofReal (term i j_fin) := by
          rw [h_sum_eq, ENNReal.ofReal_add h_sum_prev_nonneg h_term_nonneg]
        have h_ofReal_sum : A_max * ENNReal.ofReal (∑ k ∈ sum_up_to i j'.succ, term i k) = S + T := by
          rw [h1, mul_add] <;> simp [hS, hT] <;> rfl
        have h_ih' := h_ret_prev i h_i_le t ht
        have h_ih'' : volumeInCoreGeneric Z_prev t + S > A_max * ENNReal.ofReal (C * L i) := by
          simpa [hS] using h_ih'
        have h_decomp' : volumeInCoreGeneric Z_prev t ≤ volumeInCoreGeneric Z_out t + T := by
          simpa [hT] using h_decomp
        have h_shuffle : volumeInCoreGeneric Z_out t + (S + T) = (volumeInCoreGeneric Z_out t + T) + S := by
          have h_ST : S + T = T + S := add_comm S T
          rw [h_ST, add_assoc]
        have h_main : volumeInCoreGeneric Z_prev t + S ≤ volumeInCoreGeneric Z_out t + (S + T) := by
          rw [h_shuffle]
          gcongr
        have h_final : A_max * ENNReal.ofReal (C * L i) < volumeInCoreGeneric Z_out t + (S + T) :=
          lt_of_lt_of_le h_ih'' h_main
        simpa [h_ofReal_sum] using h_final
    have hP0_nonempty : (P ⟨0, hN_pos⟩).Nonempty := by
      have h_ne : (0 : ℕ) ≠ j'.succ := by omega
      have hP : P ⟨0, hN_pos⟩ = P_prev ⟨0, hN_pos⟩ := by dsimp only [P]; rw [if_neg h_ne]
      rw [hP]; exact hP0_nonempty_prev
    have hZ_prev_height : ∀ point ∈ Z_prev.union,
        point 2 ∈ Set.Icc (-1 : ℝ) 1 := by
      intro point hpoint
      exact hZ_height point (h_prev_sub_Z.union_subset hpoint)
    have h_vol_step : volume Z_prev.union ≤ volume Z_out.union +
        A_max * ENNReal.ofReal (4 * C * Real.rpow (wz1Corollary26Scale delta N j_fin) hierarchyLoss) :=
      single_level_thin_removed_volume
        (C := C) hC_nonneg (hL_pos j_fin) (hL_eq j_fin) h_slab_bound_prev
        (h_length j_fin) (h_sep j_fin) (h_coverage j_fin)
        h_prev_sub_Z hZ_prev_height hdelta_pos hdelta_lt_one hhierarchyLoss_pos
        P_j h_spec_j h_union_j
    let vol_sum_prev := Finset.univ.filter (fun k : Fin N => (k : ℕ) ≤ j')
    let vol_sum_succ := Finset.univ.filter (fun k : Fin N => (k : ℕ) ≤ j'.succ)
    have h_sum_ext : vol_sum_succ = insert j_fin vol_sum_prev := by
      ext k
      simp only [vol_sum_succ, vol_sum_prev, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
      constructor
      · intro h_k_le
        by_cases h_k_eq : (k : ℕ) = j'.succ
        · have h_k_eq_jfin : k = j_fin := by
            apply Fin.ext; simpa [j_fin] using h_k_eq
          exact Or.inl h_k_eq_jfin
        · have h_k_le_j' : (k : ℕ) ≤ j' := by omega
          exact Or.inr h_k_le_j'
      · rintro (rfl | h_k_le_j')
        · simp [j_fin]
        · omega
    have h_jfin_notin : j_fin ∉ vol_sum_prev := by
      simp only [vol_sum_prev, Finset.mem_filter, Finset.mem_univ, true_and]
      simp [j_fin] <;> omega
    let rho_pow (k : Fin N) := Real.rpow (wz1Corollary26Scale delta N k) hierarchyLoss
    have h_sum_eq : ∑ k ∈ vol_sum_succ, rho_pow k = (∑ k ∈ vol_sum_prev, rho_pow k) + rho_pow j_fin := by
      rw [h_sum_ext, Finset.sum_insert h_jfin_notin] <;> ring
    have h_scale_nonneg : ∀ (k : Fin N), 0 ≤ wz1Corollary26Scale delta N k := by
      intro k
      simpa [wz1Corollary26Scale] using Real.rpow_nonneg hdelta_pos.le (((k : ℕ) + 1 : ℝ) / (N : ℝ))
    have h_sum_nonneg1 : 0 ≤ ∑ k ∈ vol_sum_prev, rho_pow k := by
      apply Finset.sum_nonneg; intro k _; exact Real.rpow_nonneg (h_scale_nonneg k) hierarchyLoss
    have h_sum_nonneg2 : 0 ≤ rho_pow j_fin := Real.rpow_nonneg (h_scale_nonneg j_fin) hierarchyLoss
    have h_a_nonneg : 0 ≤ 4 * C * ∑ k ∈ vol_sum_prev, rho_pow k :=
      mul_nonneg (mul_nonneg (by norm_num) hC_nonneg) h_sum_nonneg1
    have h_b_nonneg : 0 ≤ 4 * C * rho_pow j_fin :=
      mul_nonneg (mul_nonneg (by norm_num) hC_nonneg) h_sum_nonneg2
    have h_sum_real : (4 * C * ∑ k ∈ vol_sum_prev, rho_pow k) + (4 * C * rho_pow j_fin) =
        4 * C * ∑ k ∈ vol_sum_succ, rho_pow k := by
      rw [h_sum_eq, mul_add]
    have h_vol_bound : volume Z.union ≤ volume Z_out.union +
        A_max * ENNReal.ofReal (4 * C * ∑ k ∈ vol_sum_succ, rho_pow k) :=
      combine_volume_bounds_real h_a_nonneg h_b_nonneg h_sum_real h_vol_prev h_vol_step
    have h_same_mult : ∀ p ∈ Z_out.union, Z_out.pointMultiplicity p = Z.pointMultiplicity p := by
      intro p hp
      have h1 : Z_out.pointMultiplicity p = Z_prev.pointMultiplicity p := h_same_mult_step p hp
      have h2 : p ∈ Z_prev.union := hZ_out_sub.union_subset hp
      have h3 : Z_prev.pointMultiplicity p = Z.pointMultiplicity p := h_same_mult_prev p h2
      rw [h1, h3]
    refine ⟨Z_out, P, fun i => Set.Subset.trans (hZ_out_sub i) (hZ_prev_sub i), ?_⟩
    constructor
    · intro i hi
      by_cases h_i_j : (i : ℕ) = j'.succ
      · have hP : P i = P_j := by dsimp only [P]; rw [if_pos h_i_j]
        have h_i_eq : i = j_fin := by
          apply Fin.ext
          simpa [j_fin] using h_i_j
        rw [hP, h_i_eq]; intro t ht; exact ((h_spec_j t).mp ht).1
      · have h_i_le : (i : ℕ) ≤ j' := by omega
        have h_ne : (i : ℕ) ≠ j'.succ := h_i_j
        have hP : P i = P_prev i := by dsimp only [P]; rw [if_neg h_ne]
        rw [hP]; exact h_sub_prev i h_i_le
    · constructor
      · intro i hi z hz
        by_cases h_i_j : (i : ℕ) = j'.succ
        · have hP : P i = P_j := by dsimp only [P]; rw [if_pos h_i_j]
          rw [hP]; exact h_cov_j z hz
        · have h_i_le : (i : ℕ) ≤ j' := by omega
          have h_ne : (i : ℕ) ≠ j'.succ := h_i_j
          have hP : P i = P_prev i := by dsimp only [P]; rw [if_neg h_ne]
          rw [hP]
          have h_z_prev : horizontalSlice Z_prev.union z ≠ ∅ := by
            have h2 : Z_out.union ⊆ Z_prev.union := hZ_out_sub.union_subset
            have h3 : horizontalSlice Z_out.union z ⊆ horizontalSlice Z_prev.union z :=
              fun p hp => ⟨h2 hp.1, hp.2⟩
            exact Set.Nonempty.mono h3 (Set.nonempty_iff_ne_empty.mpr hz) |>.ne_empty
          exact h_cov_prev i h_i_le z h_z_prev
      · constructor
        · exact h_retention
        · constructor
          · exact hP0_nonempty
          · constructor
            · exact h_vol_bound
            · exact h_same_mult

/--
Top-level multi-level thinning with simplified per-core volume retention.

Processes all N levels and proves that every popular trapezoid at level i retains
volume strictly greater than `A_max * ofReal (L i)`, using the geometric series
bound to discharge the cumulative removal sum.

Requires `C = 3` and `delta^(hierarchyLoss/N) < 1/9`.
-/
lemma multi_level_thin_with_retention
    {N : ℕ} {delta hierarchyLoss : ℝ} {F : Kakeya.Streamlined.BodyFamily}
    {Z : Kakeya.Streamlined.Shading F}
    {rawTrapezoids : Fin N → Finset WZ1VerticalTrapezoid}
    {A_max : ENNReal} {L : Fin N → ℝ}
    (hC_nonneg : 0 ≤ (3 : ℝ))
    (hL_pos : ∀ j, 0 ≤ L j)
    (hL_eq : ∀ j, L j = Real.rpow (wz1Corollary26Scale delta N j) (1 / 2 + hierarchyLoss))
    (h_slab_bound : ∀ (a b : ℝ), a ≤ b →
      volume (Z.union ∩ horizontalSlab a b) ≤ A_max * ENNReal.ofReal (b - a))
    (h_length : ∀ i, ∀ t ∈ rawTrapezoids i, t.length ≤ Real.sqrt (wz1Corollary26Scale delta N i))
    (h_sep : ∀ i, ∀ t ∈ rawTrapezoids i, ∀ s ∈ rawTrapezoids i, t ≠ s →
      ∀ z ∈ t.core, ∀ w ∈ s.core, Real.sqrt (wz1Corollary26Scale delta N i) ≤ |z - w|)
    (h_coverage : ∀ i, ∀ z ∈ Set.Icc (-1 : ℝ) 1,
      horizontalSlice Z.union z ≠ ∅ → ∃ t ∈ rawTrapezoids i, z ∈ t.core)
    (hZ_height : ∀ point ∈ Z.union, point 2 ∈ Set.Icc (-1 : ℝ) 1)
    (hdelta_pos : 0 < delta)
    (hdelta_lt_one : delta < 1)
    (hh_pos : 0 < hierarchyLoss)
    (hN_pos : 0 < N)
    (h_cond : Real.rpow delta (hierarchyLoss / (N : ℝ)) < 1 / 9)
    (h_level0_popular : ∃ t ∈ rawTrapezoids (⟨0, hN_pos⟩),
        volumeInCoreGeneric Z t > A_max * ENNReal.ofReal ((3 : ℝ) * L (⟨0, hN_pos⟩))) :
    ∃ (Z_out : Kakeya.Streamlined.Shading F)
      (P : Fin N → Finset WZ1VerticalTrapezoid),
      IsSubshadingGeneric Z_out Z ∧
      (∀ i, P i ⊆ rawTrapezoids i) ∧
      (∀ i, ∀ z, horizontalSlice Z_out.union z ≠ ∅ → ∃ t ∈ P i, z ∈ t.core) ∧
      (∀ i, ∀ t ∈ P i, volumeInCoreGeneric Z_out t > A_max * ENNReal.ofReal (L i)) ∧
      (∀ i, (P i).Nonempty) ∧
      (volume Z.union ≤ volume Z_out.union +
        A_max * ENNReal.ofReal (12 * ∑ k ∈ Finset.univ, Real.rpow (wz1Corollary26Scale delta N k) hierarchyLoss)) ∧
      (∀ p ∈ Z_out.union, Z_out.pointMultiplicity p = Z.pointMultiplicity p) := by
  let C : ℝ := 3
  let term (i k : Fin N) : ℝ :=
    (Real.sqrt (wz1Corollary26Scale delta N i) / Real.sqrt (wz1Corollary26Scale delta N k) + 2) * C * L k
  have h_last_lt : N - 1 < N := by omega
  have h_id : IsSubshadingGeneric Z Z := fun i => Set.Subset.refl (Z.carrier i)
  rcases multi_level_thin_with_retention_up_to (C := C) (show 0 ≤ C from by norm_num) hL_pos h_slab_bound
      h_length h_sep h_coverage hZ_height hdelta_pos hdelta_lt_one hierarchyLoss hh_pos hL_eq hN_pos h_level0_popular
      (N - 1) h_last_lt Z h_id rfl with
    ⟨Z_out, P, hZ_out_sub, h_sub, h_cov, h_ret, hP0_nonempty, h_vol, h_same_mult⟩
  have h_geo : ∀ (i : Fin N), ∑ k ∈ Finset.univ.filter (fun k : Fin N => i < k),
      (Real.sqrt (wz1Corollary26Scale delta N i) / Real.sqrt (wz1Corollary26Scale delta N k) + 2) * L k
      < (2 / 3 : ℝ) * L i :=
    geometric_series_volume_bound hN_pos hdelta_pos hdelta_lt_one hh_pos hL_eq h_cond
  have h_ret_simple : ∀ (i : Fin N), ∀ t ∈ P i,
      volumeInCoreGeneric Z_out t > A_max * ENNReal.ofReal (L i) := by
    intro i t ht
    have hi_le : (i : ℕ) ≤ N - 1 := by omega
    have h1 := h_ret i hi_le t ht
    have h_sum_eq : (Finset.univ.filter (fun k : Fin N => i < k ∧ (k : ℕ) ≤ N - 1)) =
        Finset.univ.filter (fun k : Fin N => i < k) := by
      ext k
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · intro h
        exact h.1
      · intro h
        have h2 : (k : ℕ) ≤ N - 1 := by omega
        exact ⟨h, h2⟩
    rw [h_sum_eq] at h1
    let S : ℝ := ∑ k ∈ Finset.univ.filter (fun k : Fin N => i < k), term i k
    have hS_nonneg : 0 ≤ S := by
      dsimp only [S, term]
      apply Finset.sum_nonneg
      intro k _
      have h1 : 0 ≤ Real.sqrt (wz1Corollary26Scale delta N i) := Real.sqrt_nonneg _
      have h2 : 0 ≤ Real.sqrt (wz1Corollary26Scale delta N k) := Real.sqrt_nonneg _
      have h3 : 0 ≤ Real.sqrt (wz1Corollary26Scale delta N i) / Real.sqrt (wz1Corollary26Scale delta N k) := by positivity
      have h4 : 0 ≤ (Real.sqrt (wz1Corollary26Scale delta N i) / Real.sqrt (wz1Corollary26Scale delta N k) + 2) := by linarith
      exact mul_nonneg (mul_nonneg h4 (by norm_num)) (hL_pos k)
    have hS_lt : S < 2 * L i := by
      dsimp only [S, term]
      have h2 : ∑ k ∈ Finset.univ.filter (fun k : Fin N => i < k), term i k =
          C * ∑ k ∈ Finset.univ.filter (fun k : Fin N => i < k),
            (Real.sqrt (wz1Corollary26Scale delta N i) / Real.sqrt (wz1Corollary26Scale delta N k) + 2) * L k := by
        have h21 : ∀ k, term i k = C * ((Real.sqrt (wz1Corollary26Scale delta N i) / Real.sqrt (wz1Corollary26Scale delta N k) + 2) * L k) := by
          intro k
          dsimp only [term]
          ring
        have h22 : ∑ k ∈ Finset.univ.filter (fun k : Fin N => i < k), term i k =
            ∑ k ∈ Finset.univ.filter (fun k : Fin N => i < k), C * ((Real.sqrt (wz1Corollary26Scale delta N i) / Real.sqrt (wz1Corollary26Scale delta N k) + 2) * L k) :=
          Finset.sum_congr rfl (fun k _ => h21 k)
        rw [h22, Finset.mul_sum]
      rw [h2]
      have h3 := h_geo i
      have h4 : (0 : ℝ) ≤ L i := hL_pos i
      linarith
    have hL_i_nonneg : 0 ≤ L i := hL_pos i
    by_contra h_contra
    have h5 : volumeInCoreGeneric Z_out t ≤ A_max * ENNReal.ofReal (L i) := by simpa using h_contra
    have h6 : volumeInCoreGeneric Z_out t + A_max * ENNReal.ofReal S ≤
        A_max * ENNReal.ofReal (L i + S) := by
      calc volumeInCoreGeneric Z_out t + A_max * ENNReal.ofReal S
        ≤ A_max * ENNReal.ofReal (L i) + A_max * ENNReal.ofReal S := by gcongr
      _ = A_max * (ENNReal.ofReal (L i) + ENNReal.ofReal S) := by ring
      _ = A_max * ENNReal.ofReal (L i + S) := by
        rw [ENNReal.ofReal_add hL_i_nonneg hS_nonneg] <;> ring
    have h7 : L i + S < C * L i := by
      dsimp only [C]
      linarith
    have h8 : ENNReal.ofReal (L i + S) ≤ ENNReal.ofReal (C * L i) :=
      ENNReal.ofReal_le_ofReal h7.le
    have h9 : volumeInCoreGeneric Z_out t + A_max * ENNReal.ofReal S ≤
        A_max * ENNReal.ofReal (C * L i) := by
      calc volumeInCoreGeneric Z_out t + A_max * ENNReal.ofReal S
        ≤ A_max * ENNReal.ofReal (L i + S) := h6
      _ ≤ A_max * ENNReal.ofReal (C * L i) := by gcongr
    have h10 : volumeInCoreGeneric Z_out t + A_max * ENNReal.ofReal S <
        volumeInCoreGeneric Z_out t + A_max * ENNReal.ofReal S := lt_of_le_of_lt h9 h1
    exact lt_irrefl _ h10
  have h_sum_all : (Finset.univ.filter (fun k : Fin N => (k : ℕ) ≤ N - 1)) = (Finset.univ : Finset (Fin N)) := by
    ext k; simp; omega
  have hC3 : C = 3 := by simp [C]
  have h_vol_bound : volume Z.union ≤ volume Z_out.union +
      A_max * ENNReal.ofReal (4 * C * ∑ k ∈ Finset.univ.filter (fun k : Fin N => (k : ℕ) ≤ N - 1),
        Real.rpow (wz1Corollary26Scale delta N k) hierarchyLoss) := h_vol
  have h_vol' : volume Z.union ≤ volume Z_out.union +
      A_max * ENNReal.ofReal (12 * ∑ k ∈ (Finset.univ : Finset (Fin N)), Real.rpow (wz1Corollary26Scale delta N k) hierarchyLoss) := by
    rw [h_sum_all] at h_vol_bound
    have h12 : 4 * C = (12 : ℝ) := by rw [hC3] <;> norm_num
    rw [h12] at h_vol_bound
    exact h_vol_bound
  refine ⟨Z_out, P, hZ_out_sub, ?_⟩
  constructor
  · intro i
    have hi_le : (i : ℕ) ≤ N - 1 := by omega
    exact h_sub i hi_le
  · constructor
    · intro i z hz
      have hi_le : (i : ℕ) ≤ N - 1 := by omega
      exact h_cov i hi_le z hz
    · constructor
      · exact h_ret_simple
      · constructor
        · intro i
          by_cases h_i0 : (i : ℕ) = 0
          · have h_i_eq : i = (⟨0, hN_pos⟩ : Fin N) := by apply Fin.ext; omega
            rw [h_i_eq]; exact hP0_nonempty
          · have hZout_nonempty : Z_out.union.Nonempty := by
              rcases hP0_nonempty with ⟨t, ht⟩
              have h_vol_pos : 0 < volumeInCoreGeneric Z_out t := by
                have h4 : (0 : ENNReal) ≤ A_max * ENNReal.ofReal (L ⟨0, hN_pos⟩) := by positivity
                exact lt_of_le_of_lt h4 (h_ret_simple ⟨0, hN_pos⟩ t ht)
              have h3 : volumeInCoreGeneric Z_out t ≤ volume Z_out.union := by
                apply measure_mono; intro p hp; exact hp.1
              have h4 : 0 < volume Z_out.union := lt_of_lt_of_le h_vol_pos h3
              by_contra h5
              have h6 : Z_out.union = ∅ := by simpa [Set.not_nonempty_iff_eq_empty] using h5
              rw [h6] at h4
              simp at h4
            rcases hZout_nonempty with ⟨p, hp⟩
            have h_slice_nonempty : horizontalSlice Z_out.union (p 2) ≠ ∅ := by
              have h5 : p ∈ horizontalSlice Z_out.union (p 2) := ⟨hp, rfl⟩
              exact Set.nonempty_iff_ne_empty.mp ⟨p, h5⟩
            have hi_le : (i : ℕ) ≤ N - 1 := by omega
            rcases h_cov i hi_le (p 2) h_slice_nonempty with ⟨t, ht, _⟩
            exact ⟨t, ht⟩
        · constructor
          · exact h_vol'
          · exact h_same_mult


/-! ## 8. BodyFamily compactification -/

/-- BodyFamily-generic inner regularization with simultaneous retention of
per-core volume, total union volume, and total shaded mass. -/
lemma compact_subshading_main_generic
    {BF : Kakeya.Streamlined.BodyFamily}
    {Z : Kakeya.Streamlined.Shading BF}
    {T : Finset WZ1VerticalTrapezoid}
    {core_bound : WZ1VerticalTrapezoid → ENNReal} {vol_bound mass_bound : ENNReal}
    (hBF_card_pos : 0 < BF.card)
    (hZ_vol_lt_top : volume Z.union ≠ ⊤)
    (hZ_mass_lt_top : Z.mass ≠ ⊤)
    (min_gap vol_gap mass_gap : ℝ)
    (hmin_gap_pos : 0 < min_gap)
    (h_min_gap_le_vol : min_gap ≤ vol_gap)
    (h_min_gap_le_mass : min_gap ≤ mass_gap)
    (hvol_gap_works : volume Z.union > vol_bound + ENNReal.ofReal vol_gap)
    (hmass_gap_works : Z.mass > mass_bound + ENNReal.ofReal mass_gap)
    (h_core_data : ∀ t ∈ T, ∃ (g : ℝ), 0 < g ∧
      volumeInCoreGeneric Z t > core_bound t + ENNReal.ofReal g ∧ min_gap ≤ g) :
    ∃ (Z_comp : Kakeya.Streamlined.Shading BF),
      IsSubshadingGeneric Z_comp Z ∧
      IsCompact Z_comp.union ∧
      (∀ t ∈ T, volumeInCoreGeneric Z_comp t > core_bound t) ∧
      volume Z_comp.union ≥ vol_bound ∧
      Z_comp.mass ≥ mass_bound := by
  classical
  let n : ℕ := BF.card
  have hn_pos : 0 < n := by
    dsimp only [n]
    exact hBF_card_pos
  let eps_real : ℝ := min_gap / (n : ℝ)
  have heps_real_pos : 0 < eps_real := by
    dsimp only [eps_real]; apply div_pos hmin_gap_pos; exact_mod_cast hn_pos
  let eps : ENNReal := ENNReal.ofReal eps_real
  have heps_pos : 0 < eps := ENNReal.ofReal_pos.mpr heps_real_pos
  have heps_ne_zero : eps ≠ 0 := heps_pos.ne'
  have heps_lt_top : eps ≠ ⊤ := by simp [eps]
  have h_total : (n : ENNReal) * eps = ENNReal.ofReal min_gap := by
    have h1 : (n : ENNReal) * eps = ENNReal.ofReal ((n : ℝ) * eps_real) := by
      have h2 : ENNReal.ofReal ((n : ℝ) * eps_real) =
          ENNReal.ofReal (n : ℝ) * ENNReal.ofReal eps_real := by
        rw [ENNReal.ofReal_mul] <;> positivity
      rw [h2]
      have h3 : ENNReal.ofReal (n : ℝ) = (n : ENNReal) := by simp
      rw [h3] <;> rfl
    rw [h1]
    have h4 : (n : ℝ) * eps_real = min_gap := by
      dsimp only [eps_real]; field_simp [hn_pos.ne'] <;> ring
    rw [h4]
  have h_main : ∀ (i : Fin n), ∃ (K : Set Point3),
      K ⊆ Z.carrier i ∧ IsCompact K ∧ volume (Z.carrier i \ K) < eps := by
    intro i
    have h_meas : MeasurableSet (Z.carrier i) := Z.measurable_carrier i
    have h1 : Z.carrier i ⊆ Z.union := by intro x hx; exact ⟨i, hx⟩
    have h_fin : volume (Z.carrier i) ≠ ⊤ := ne_top_of_le_ne_top hZ_vol_lt_top (measure_mono h1)
    rcases h_meas.exists_isCompact_lt_add h_fin heps_ne_zero with ⟨K, hK_sub, hK_compact, h_vol_lt⟩
    have hK_meas : MeasurableSet K := hK_compact.measurableSet
    have hDiff_meas : MeasurableSet (Z.carrier i \ K) := h_meas.diff hK_meas
    have h_union_eq : K ∪ (Z.carrier i \ K) = Z.carrier i := by
      ext x; simp [hK_sub] <;> tauto
    have h_disj : Disjoint K (Z.carrier i \ K) := by
      rw [Set.disjoint_left]; intro x hx1 hx2; exact hx2.2 hx1
    have h10 : volume (K ∪ (Z.carrier i \ K)) = volume K + volume (Z.carrier i \ K) :=
      measure_union h_disj hDiff_meas
    have h_eq : volume (Z.carrier i) = volume K + volume (Z.carrier i \ K) := by
      have h11 : volume (K ∪ (Z.carrier i \ K)) = volume (Z.carrier i) := by rw [h_union_eq]
      rw [← h11]
      exact h10
    have hK_lt_top : volume K ≠ ⊤ := ne_top_of_le_ne_top h_fin (measure_mono hK_sub)
    have h_loss_lt : volume (Z.carrier i \ K) < eps := by
      have h_vol_lt2 : volume K + volume (Z.carrier i \ K) < volume K + eps := by
        rw [h_eq] at h_vol_lt; exact h_vol_lt
      exact (ENNReal.add_lt_add_iff_left hK_lt_top).mp h_vol_lt2
    exact ⟨K, hK_sub, hK_compact, h_loss_lt⟩
  choose K hK_sub hK_compact hK_loss using h_main
  let Z_comp : Kakeya.Streamlined.Shading BF :=
    { carrier := K
      measurable_carrier := fun i => (hK_compact i).measurableSet
      subset_body := fun i => Set.Subset.trans (hK_sub i) (Z.subset_body i) }
  have hZ_comp_sub : IsSubshadingGeneric Z_comp Z := fun i => hK_sub i
  have h_union_compact : IsCompact Z_comp.union := by
    have h_eq : Z_comp.union = ⋃ i : Fin n, K i := by
      ext x; simp [Kakeya.Streamlined.Shading.union, Z_comp] <;> aesop
    rw [h_eq]; exact isCompact_iUnion (fun i => hK_compact i)
  have h_nonempty : (Finset.univ : Finset (Fin n)).Nonempty := by
    exact ⟨⟨0, hn_pos⟩, by simp⟩
  have h_loss_sum : ∑ i : Fin n, volume (Z.carrier i \ K i) < (n : ENNReal) * eps := by
    have h4 : ∑ i : Fin n, volume (Z.carrier i \ K i) < ∑ i : Fin n, eps :=
      finset_sum_strict_lt h_nonempty (fun i _ => hK_loss i) (fun i _ => heps_lt_top)
    have h5 : ∑ i : Fin n, eps = (n : ENNReal) * eps := by
      simp [Finset.sum_const] <;> ring
    rw [h5] at h4; exact h4
  have h_diff_subset : Z.union \ Z_comp.union ⊆ ⋃ i : Fin n, (Z.carrier i \ K i) := by
    intro x hx
    rcases hx.1 with ⟨i, hi⟩
    have hxi : x ∉ K i := by
      intro h
      have h_in_union : x ∈ Z_comp.union := by
        simp only [Kakeya.Streamlined.Shading.union, Set.mem_setOf_eq]
        exact ⟨i, h⟩
      exact hx.2 h_in_union
    exact Set.mem_iUnion.mpr ⟨i, ⟨hi, hxi⟩⟩
  have h_vol_loss : volume (Z.union \ Z_comp.union) < (n : ENNReal) * eps := by
    calc volume (Z.union \ Z_comp.union)
      ≤ volume (⋃ i : Fin n, (Z.carrier i \ K i)) := measure_mono h_diff_subset
    _ ≤ ∑ i : Fin n, volume (Z.carrier i \ K i) := by
      simpa [tsum_fintype] using measure_iUnion_le (fun i : Fin n => Z.carrier i \ K i)
    _ < (n : ENNReal) * eps := h_loss_sum
  have hZ_union_meas : MeasurableSet Z.union := by
    have h : Z.union = ⋃ i : Fin n, Z.carrier i := by
      ext x; simp [Kakeya.Streamlined.Shading.union] <;> aesop
    rw [h]; exact MeasurableSet.iUnion (fun i => Z.measurable_carrier i)
  have hZ_comp_union_meas : MeasurableSet Z_comp.union := h_union_compact.measurableSet
  have h_diff_meas : MeasurableSet (Z.union \ Z_comp.union) := hZ_union_meas.diff hZ_comp_union_meas
  have h_vol_decomp : volume Z.union = volume Z_comp.union + volume (Z.union \ Z_comp.union) := by
    have h_sub : Z_comp.union ⊆ Z.union := hZ_comp_sub.union_subset
    have h_disj : Disjoint Z_comp.union (Z.union \ Z_comp.union) := by
      rw [Set.disjoint_left]; intro x hx1 hx2; exact hx2.2 hx1
    have h_eq : Z.union = Z_comp.union ∪ (Z.union \ Z_comp.union) := by
      ext x
      simp only [Set.mem_union, Set.mem_diff]
      constructor
      · intro hx
        by_cases h : x ∈ Z_comp.union
        · exact Or.inl h
        · exact Or.inr ⟨hx, h⟩
      · rintro (h | ⟨h, _⟩)
        · exact h_sub h
        · exact h
    have h_measure : volume (Z_comp.union ∪ (Z.union \ Z_comp.union)) =
        volume Z_comp.union + volume (Z.union \ Z_comp.union) :=
      measure_union h_disj h_diff_meas
    have h_vol : volume Z.union = volume (Z_comp.union ∪ (Z.union \ Z_comp.union)) :=
      congr_arg volume h_eq
    rw [h_vol, h_measure]
  have h_mass_decomp : Z.mass = Z_comp.mass + ∑ i : Fin n, volume (Z.carrier i \ K i) := by
    simp [Kakeya.Streamlined.Shading.mass]
    have h : ∀ (i : Fin n), volume (Z.carrier i) = volume (K i) + volume (Z.carrier i \ K i) := by
      intro i
      have hK_meas : MeasurableSet (K i) := (hK_compact i).measurableSet
      have hDiff_meas : MeasurableSet (Z.carrier i \ K i) := (Z.measurable_carrier i).diff hK_meas
      have h_union_eq : K i ∪ (Z.carrier i \ K i) = Z.carrier i := by
        ext x; simp [hK_sub i] <;> tauto
      have h_disj : Disjoint (K i) (Z.carrier i \ K i) := by
        rw [Set.disjoint_left]; intro x hx1 hx2; exact hx2.2 hx1
      have h_vol : volume (K i ∪ (Z.carrier i \ K i)) = volume (K i) + volume (Z.carrier i \ K i) :=
        measure_union h_disj hDiff_meas
      rw [← h_vol, h_union_eq]
    rw [Finset.sum_congr rfl (fun i _ => h i), Finset.sum_add_distrib] <;> ring
  have h_core_ret : ∀ t ∈ T, volumeInCoreGeneric Z_comp t > core_bound t := by
    intro t ht
    rcases h_core_data t ht with ⟨g, hg_pos, hg_works, h_min_le_g⟩
    let loss_t := volume ((Z.union \ Z_comp.union) ∩ horizontalSlab t.left t.right)
    have h_loss_t_lt : loss_t < ENNReal.ofReal min_gap := by
      calc loss_t
        ≤ volume (Z.union \ Z_comp.union) := measure_mono (fun x hx => hx.1)
      _ < (n : ENNReal) * eps := h_vol_loss
      _ = ENNReal.ofReal min_gap := h_total
    have h_loss_lt_gap : loss_t < ENNReal.ofReal g := by
      calc loss_t < ENNReal.ofReal min_gap := h_loss_t_lt
           _ ≤ ENNReal.ofReal g := ENNReal.ofReal_le_ofReal h_min_le_g
    have h_slab_meas : MeasurableSet (horizontalSlab t.left t.right) :=
      measurableSet_horizontalSlab t.left t.right
    have h_part2_meas : MeasurableSet ((Z.union \ Z_comp.union) ∩ horizontalSlab t.left t.right) :=
      h_diff_meas.inter h_slab_meas
    have h_decomp : volumeInCoreGeneric Z t = volumeInCoreGeneric Z_comp t + loss_t := by
      have h1 : Z.union ∩ horizontalSlab t.left t.right =
          (Z_comp.union ∩ horizontalSlab t.left t.right) ∪
          ((Z.union \ Z_comp.union) ∩ horizontalSlab t.left t.right) := by
        ext x
        simp only [Set.mem_inter_iff, Set.mem_union, Set.mem_diff]
        constructor
        · rintro ⟨hZ, hslab⟩
          by_cases h : x ∈ Z_comp.union
          · exact Or.inl ⟨h, hslab⟩
          · exact Or.inr ⟨⟨hZ, h⟩, hslab⟩
        · rintro (⟨hZcomp, hslab⟩ | ⟨⟨hZ, _⟩, hslab⟩)
          · exact ⟨hZ_comp_sub.union_subset hZcomp, hslab⟩
          · exact ⟨hZ, hslab⟩
      have h_disj : Disjoint (Z_comp.union ∩ horizontalSlab t.left t.right)
          ((Z.union \ Z_comp.union) ∩ horizontalSlab t.left t.right) := by
        rw [Set.disjoint_left]
        intro x hx1 hx2
        have h_in : x ∈ Z_comp.union := hx1.1
        have h_notin : x ∉ Z_comp.union := hx2.1.2
        exact h_notin h_in
      have h_goal : volume (Z.union ∩ horizontalSlab t.left t.right) =
          volume (Z_comp.union ∩ horizontalSlab t.left t.right) + loss_t := by
        rw [h1, measure_union h_disj h_part2_meas] <;> rfl
      have h_set_eq1 : Z.union ∩ horizontalSlab t.left t.right =
          Z.union ∩ {p : Point3 | p 2 ∈ Set.Icc t.left t.right} := by
        ext x; simp [horizontalSlab] <;> rfl
      have h_set_eq2 : Z_comp.union ∩ horizontalSlab t.left t.right =
          Z_comp.union ∩ {p : Point3 | p 2 ∈ Set.Icc t.left t.right} := by
        ext x; simp [horizontalSlab] <;> rfl
      rw [h_set_eq1, h_set_eq2] at h_goal
      simpa [volumeInCoreGeneric, volumeInSlabGeneric] using h_goal
    exact ennreal_retention h_decomp h_loss_lt_gap hg_works (by simp)
  have h_vol_ret : volume Z_comp.union ≥ vol_bound := by
    have h_loss_lt_gap : volume (Z.union \ Z_comp.union) < ENNReal.ofReal vol_gap := by
      calc volume (Z.union \ Z_comp.union) < (n : ENNReal) * eps := h_vol_loss
           _ = ENNReal.ofReal min_gap := h_total
           _ ≤ ENNReal.ofReal vol_gap := ENNReal.ofReal_le_ofReal h_min_gap_le_vol
    exact le_of_lt (ennreal_retention h_vol_decomp h_loss_lt_gap hvol_gap_works (by simp))
  have h_mass_loss_lt : ∑ i : Fin n, volume (Z.carrier i \ K i) < ENNReal.ofReal mass_gap := by
    calc ∑ i : Fin n, volume (Z.carrier i \ K i) < (n : ENNReal) * eps := h_loss_sum
         _ = ENNReal.ofReal min_gap := h_total
         _ ≤ ENNReal.ofReal mass_gap := ENNReal.ofReal_le_ofReal h_min_gap_le_mass
  have h_mass_ret : Z_comp.mass ≥ mass_bound := by
    exact le_of_lt (ennreal_retention h_mass_decomp h_mass_loss_lt hmass_gap_works (by simp))
  exact ⟨Z_comp, hZ_comp_sub, h_union_compact, h_core_ret, h_vol_ret, h_mass_ret⟩

/-- Compactify a finite BodyFamily shading while retaining all quantitative
bounds used by the Corollary 5.6 popularity argument.  Finite union volume is
provided explicitly; no tube-carrier or unit-ball hypothesis is used. -/
lemma compact_subshading_with_full_retention_generic
    {BF : Kakeya.Streamlined.BodyFamily}
    {Z : Kakeya.Streamlined.Shading BF}
    {T : Finset WZ1VerticalTrapezoid}
    {core_bound : WZ1VerticalTrapezoid → ENNReal} {vol_bound mass_bound : ENNReal}
    (hBF_card_pos : 0 < BF.card)
    (hZ_vol_lt_top : volume Z.union ≠ ⊤)
    (h_vol : ∀ t ∈ T, volumeInCoreGeneric Z t > core_bound t)
    (h_vol_bound : volume Z.union > vol_bound)
    (h_mass_bound : Z.mass > mass_bound)
    (h_core_bound_lt_top : ∀ t ∈ T, core_bound t ≠ ⊤)
    (h_vol_bound_lt_top : vol_bound ≠ ⊤)
    (h_mass_bound_lt_top : mass_bound ≠ ⊤) :
    ∃ (Z_comp : Kakeya.Streamlined.Shading BF),
      IsSubshadingGeneric Z_comp Z ∧
      IsCompact Z_comp.union ∧
      (∀ t ∈ T, volumeInCoreGeneric Z_comp t > core_bound t) ∧
      volume Z_comp.union ≥ vol_bound ∧
      Z_comp.mass ≥ mass_bound := by
  classical
  let n : ℕ := BF.card
  have hZ_mass_lt_top : Z.mass ≠ ⊤ := by
    have h : Z.mass = ∑ i : Fin n, volume (Z.carrier i) := by rfl
    rw [h]
    rw [ENNReal.sum_ne_top]
    intro i _
    have h1 : Z.carrier i ⊆ Z.union := by intro x hx; exact ⟨i, hx⟩
    exact ne_top_of_le_ne_top hZ_vol_lt_top (measure_mono h1)
  have h_core_vol_lt_top : ∀ t ∈ T, volumeInCoreGeneric Z t ≠ ⊤ := by
    intro t _
    have h1 : (Z.union ∩ horizontalSlab t.left t.right) ⊆ Z.union := fun x hx => hx.1
    exact ne_top_of_le_ne_top hZ_vol_lt_top (measure_mono h1)
  rcases ennreal_gap hZ_vol_lt_top h_vol_bound_lt_top h_vol_bound with ⟨vol_gap, hvol_gap_pos, hvol_gap_works⟩
  rcases ennreal_gap hZ_mass_lt_top h_mass_bound_lt_top h_mass_bound with ⟨mass_gap, hmass_gap_pos, hmass_gap_works⟩
  have h_core_gaps : ∀ t ∈ T, ∃ (g : ℝ), 0 < g ∧ volumeInCoreGeneric Z t > core_bound t + ENNReal.ofReal g := by
    intro t ht
    exact ennreal_gap (h_core_vol_lt_top t ht) (h_core_bound_lt_top t ht) (h_vol t ht)
  choose core_gap hcore_gap_pos hcore_gap_works using h_core_gaps
  by_cases hT_empty : T = ∅
  · let min_gap : ℝ := min vol_gap mass_gap
    have hmin_gap_pos : 0 < min_gap := lt_min hvol_gap_pos hmass_gap_pos
    exact compact_subshading_main_generic hBF_card_pos hZ_vol_lt_top hZ_mass_lt_top
      min_gap vol_gap mass_gap hmin_gap_pos
      (min_le_left _ _) (min_le_right _ _)
      hvol_gap_works hmass_gap_works
      (fun t ht => by rw [hT_empty] at ht; simp at ht)
  · have hT_nonempty : T.Nonempty := by
      rw [Finset.nonempty_iff_ne_empty]; exact hT_empty
    let core_gap_total : WZ1VerticalTrapezoid → ℝ := fun t =>
      if h : t ∈ T then core_gap t h else 0
    rcases Finset.exists_min_image T core_gap_total hT_nonempty with ⟨t0, ht0, h_min_core⟩
    let min_core_gap : ℝ := core_gap_total t0
    have hmin_core_gap_pos : 0 < min_core_gap := by
      dsimp only [min_core_gap, core_gap_total]
      rw [dif_pos ht0]
      exact hcore_gap_pos t0 ht0
    let min_gap : ℝ := min min_core_gap (min vol_gap mass_gap)
    have hmin_gap_pos : 0 < min_gap := by
      apply lt_min hmin_core_gap_pos
      apply lt_min hvol_gap_pos hmass_gap_pos
    have h_min_gap_le_core : ∀ (t) (ht : t ∈ T), min_gap ≤ core_gap t ht := by
      intro t ht
      have h_total_eq : core_gap_total t = core_gap t ht := by
        dsimp only [core_gap_total]; rw [dif_pos ht]
      calc min_gap ≤ min_core_gap := min_le_left _ _
           _ = core_gap_total t0 := by rfl
           _ ≤ core_gap_total t := h_min_core t ht
           _ = core_gap t ht := h_total_eq
    have h_min_gap_le_vol : min_gap ≤ vol_gap := by
      calc min_gap ≤ min vol_gap mass_gap := min_le_right _ _
           _ ≤ vol_gap := min_le_left _ _
    have h_min_gap_le_mass : min_gap ≤ mass_gap := by
      calc min_gap ≤ min vol_gap mass_gap := min_le_right _ _
           _ ≤ mass_gap := min_le_right _ _
    have h_core_data : ∀ t ∈ T, ∃ (g : ℝ), 0 < g ∧
        volumeInCoreGeneric Z t > core_bound t + ENNReal.ofReal g ∧ min_gap ≤ g := by
      intro t ht
      exact ⟨core_gap t ht, hcore_gap_pos t ht, hcore_gap_works t ht, h_min_gap_le_core t ht⟩
    exact compact_subshading_main_generic hBF_card_pos hZ_vol_lt_top hZ_mass_lt_top
      min_gap vol_gap mass_gap hmin_gap_pos
      h_min_gap_le_vol h_min_gap_le_mass
      hvol_gap_works hmass_gap_works h_core_data


/-! ## 9. Compact endpoint reanchoring -/

/-- Reanchor every popular core at the extreme active heights of a compact
BodyFamily shading, preserving coverage exactly as in Corollary 5.6. -/
lemma reanchor_with_coverage_generic
    {BF : Kakeya.Streamlined.BodyFamily}
    {Z : Kakeya.Streamlined.Shading BF}
    {T : Finset WZ1VerticalTrapezoid}
    {A_max : ENNReal} {L : ℝ}
    (hL_pos : 0 ≤ L)
    (hZ_compact : IsCompact Z.union)
    (h_slab_bound : ∀ (a b : ℝ), a ≤ b →
      volume (Z.union ∩ horizontalSlab a b) ≤ A_max * ENNReal.ofReal (b - a))
    (h_vol : ∀ t ∈ T, volumeInCoreGeneric Z t > A_max * ENNReal.ofReal L) :
    ∃ (shrunk : WZ1VerticalTrapezoid → WZ1VerticalTrapezoid)
      (T' : Finset WZ1VerticalTrapezoid),
      (∀ t ∈ T, (shrunk t).core ⊆ t.core ∧
        (shrunk t).slope = t.slope ∧ (shrunk t).intercept = t.intercept ∧
        (shrunk t).height = t.height ∧ L ≤ (shrunk t).length) ∧
      (∀ t ∈ T, shrunk t ∈ T') ∧
      (∀ t' ∈ T', ∃ t ∈ T, t' = shrunk t) ∧
      (∀ t' ∈ T', horizontalSlice Z.union t'.left ≠ ∅ ∧
                        horizontalSlice Z.union t'.right ≠ ∅) ∧
      (∀ t' ∈ T', L ≤ t'.length) ∧
      (∀ t' ∈ T', ∃ t ∈ T,
        t'.core ⊆ t.core ∧ t'.slope = t.slope ∧ t'.intercept = t.intercept ∧ t'.height = t.height) ∧
      (∀ (z : ℝ), horizontalSlice Z.union z ≠ ∅ →
        (∃ t ∈ T, z ∈ t.core) → (∃ t' ∈ T', z ∈ t'.core)) := by
  classical
  have h_proj_cont : Continuous (fun p : Point3 => p 2) :=
    PiLp.continuous_apply 2 (fun _ : Fin 3 => ℝ) 2
  have h_active_eq : activeSetOf Z.union = (fun p : Point3 => p 2) '' Z.union := by
    ext z
    simp only [activeSet, Set.mem_setOf_eq, Set.mem_image]
    constructor
    · intro h
      have hne : (horizontalSlice Z.union z).Nonempty := Set.nonempty_iff_ne_empty.mpr h
      rcases hne with ⟨p, hp⟩
      exact ⟨p, hp.1, hp.2⟩
    · rintro ⟨p, hp, rfl⟩
      have h : p ∈ horizontalSlice Z.union (p 2) := ⟨hp, rfl⟩
      exact Set.nonempty_iff_ne_empty.mp ⟨p, h⟩
  have h_active_compact : IsCompact (activeSetOf Z.union) :=
    h_active_eq.symm ▸ hZ_compact.image h_proj_cont
  let A (t : WZ1VerticalTrapezoid) : Set ℝ := activeSetOf Z.union ∩ t.core
  have hA_compact : ∀ t ∈ T, IsCompact (A t) := by
    intro t ht
    have h_core_compact : IsCompact (t.core) := isCompact_Icc
    exact h_active_compact.inter h_core_compact
  have hA_nonempty : ∀ t ∈ T, (A t).Nonempty := by
    intro t ht
    have h_main : ∃ (a b : ℝ), a ∈ A t ∧ b ∈ A t ∧ b - a > L :=
      active_points_from_volume_generic hL_pos (h_vol t ht) h_slab_bound
    rcases h_main with ⟨a, b, ha, _, _⟩
    exact ⟨a, ha⟩
  let minA (t : WZ1VerticalTrapezoid) (ht : t ∈ T) : ℝ := sInf (A t)
  let maxA (t : WZ1VerticalTrapezoid) (ht : t ∈ T) : ℝ := sSup (A t)
  have hmin_in : ∀ t ht, minA t ht ∈ A t := fun t ht =>
    (hA_compact t ht).sInf_mem (hA_nonempty t ht)
  have hmax_in : ∀ t ht, maxA t ht ∈ A t := fun t ht =>
    (hA_compact t ht).sSup_mem (hA_nonempty t ht)
  have hA_bdd_below : ∀ t ht, BddBelow (A t) := fun t ht =>
    (hA_compact t ht).bddBelow
  have hA_bdd_above : ∀ t ht, BddAbove (A t) := fun t ht =>
    (hA_compact t ht).bddAbove
  have hmin_le : ∀ t ht x, x ∈ A t → minA t ht ≤ x := fun t ht x hx =>
    csInf_le (hA_bdd_below t ht) hx
  have hle_max : ∀ t ht x, x ∈ A t → x ≤ maxA t ht := fun t ht x hx =>
    le_csSup (hA_bdd_above t ht) hx
  have h_diff : ∀ t ht, maxA t ht - minA t ht > L := by
    intro t ht
    have h_main : ∃ (a b : ℝ), a ∈ A t ∧ b ∈ A t ∧ b - a > L :=
      active_points_from_volume_generic hL_pos (h_vol t ht) h_slab_bound
    rcases h_main with ⟨a, b, ha, hb, hdiff⟩
    have h3 : minA t ht ≤ a := hmin_le t ht a ha
    have h4 : b ≤ maxA t ht := hle_max t ht b hb
    linarith
  let shrunk (t : WZ1VerticalTrapezoid) : WZ1VerticalTrapezoid :=
    if ht : t ∈ T then
      { left := minA t ht, right := maxA t ht,
        left_lt_right := by linarith [h_diff t ht],
        slope := t.slope, intercept := t.intercept,
        height := t.height, height_pos := t.height_pos }
    else t
  let T' : Finset WZ1VerticalTrapezoid := T.image shrunk
  have h_shrunk_spec : ∀ (t : WZ1VerticalTrapezoid) (ht : t ∈ T),
      (shrunk t).left = minA t ht ∧
      (shrunk t).right = maxA t ht ∧
      (shrunk t).slope = t.slope ∧
      (shrunk t).intercept = t.intercept ∧
      (shrunk t).height = t.height := by
    intro t ht
    have h_eq : shrunk t =
        { left := minA t ht, right := maxA t ht,
          left_lt_right := by linarith [h_diff t ht],
          slope := t.slope, intercept := t.intercept,
          height := t.height, height_pos := t.height_pos } := by
      dsimp only [shrunk]; rw [dif_pos ht]
    rw [h_eq] <;> simp
  refine ⟨shrunk, T', ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- Properties of shrunk trapezoids
    intro t ht
    have hs := h_shrunk_spec t ht
    constructor
    · -- core subset
      have h_left_in : minA t ht ∈ t.core := (hmin_in t ht).2
      have h_right_in : maxA t ht ∈ t.core := (hmax_in t ht).2
      have h_core_eq : (shrunk t).core = Set.Icc (minA t ht) (maxA t ht) := by
        simp [WZ1VerticalTrapezoid.core, hs.1, hs.2.1]
      rw [h_core_eq]
      exact Icc_subset_Icc h_left_in.1 h_right_in.2
    · exact ⟨hs.2.2.1, hs.2.2.2.1, hs.2.2.2.2, by
        have h_len : (shrunk t).length = maxA t ht - minA t ht := by
          simp [WZ1VerticalTrapezoid.length, hs.1, hs.2.1]
        rw [h_len]
        exact le_of_lt (h_diff t ht)⟩
  · -- shrunk t ∈ T'
    intro t ht
    exact Finset.mem_image.mpr ⟨t, ht, rfl⟩
  · -- preimage
    intro t' ht'
    rcases Finset.mem_image.mp ht' with ⟨t, ht, rfl⟩
    exact ⟨t, ht, rfl⟩
  · -- active endpoints
    intro t' ht'
    rcases Finset.mem_image.mp ht' with ⟨t, ht, rfl⟩
    have hs := h_shrunk_spec t ht
    have h_left_active : (shrunk t).left ∈ activeSetOf Z.union := by
      rw [hs.1]; exact (hmin_in t ht).1
    have h_right_active : (shrunk t).right ∈ activeSetOf Z.union := by
      rw [hs.2.1]; exact (hmax_in t ht).1
    have h_left_ne : horizontalSlice Z.union (shrunk t).left ≠ ∅ := by
      simpa [activeSetOf] using h_left_active
    have h_right_ne : horizontalSlice Z.union (shrunk t).right ≠ ∅ := by
      simpa [activeSetOf] using h_right_active
    exact ⟨h_left_ne, h_right_ne⟩
  · -- length bound
    intro t' ht'
    rcases Finset.mem_image.mp ht' with ⟨t, ht, rfl⟩
    have hs := h_shrunk_spec t ht
    have h_len : (shrunk t).length = maxA t ht - minA t ht := by
      simp [WZ1VerticalTrapezoid.length, hs.1, hs.2.1]
    rw [h_len]
    exact le_of_lt (h_diff t ht)
  · -- provenance
    intro t' ht'
    rcases Finset.mem_image.mp ht' with ⟨t, ht, rfl⟩
    have hs := h_shrunk_spec t ht
    refine ⟨t, ht, ?_⟩
    have h_left_in : minA t ht ∈ t.core := (hmin_in t ht).2
    have h_right_in : maxA t ht ∈ t.core := (hmax_in t ht).2
    constructor
    · have h_core_eq : (shrunk t).core = Set.Icc (minA t ht) (maxA t ht) := by
        simp [WZ1VerticalTrapezoid.core, hs.1, hs.2.1]
      rw [h_core_eq]
      exact Icc_subset_Icc h_left_in.1 h_right_in.2
    · exact ⟨hs.2.2.1, hs.2.2.2.1, hs.2.2.2.2⟩
  · -- coverage preservation
    intro z hz_active h_cover
    rcases h_cover with ⟨t, ht, hz_core⟩
    have hz_active' : z ∈ activeSetOf Z.union := by simpa [activeSetOf] using hz_active
    have hz_in_A : z ∈ A t := ⟨hz_active', hz_core⟩
    have h1 : minA t ht ≤ z := hmin_le t ht z hz_in_A
    have h2 : z ≤ maxA t ht := hle_max t ht z hz_in_A
    refine ⟨shrunk t, Finset.mem_image.mpr ⟨t, ht, rfl⟩, ?_⟩
    have hs := h_shrunk_spec t ht
    have h_core_eq : (shrunk t).core = Set.Icc (minA t ht) (maxA t ht) := by
      simp [WZ1VerticalTrapezoid.core, hs.1, hs.2.1]
    rw [h_core_eq]
    exact ⟨h1, h2⟩

/-! ## 10. Level-zero popularity from the global volume lower bound -/

/-- Paper level-0 popularity for an arbitrary body family.  This is the first
pigeonhole step in Corollary 5.6; only the explicit vertical-coordinate bound
is used in place of the historical unit-ball hypothesis. -/
lemma level0_popularity_from_volume_general_generic
    {N : ℕ} {delta sigma hierarchyLoss : ℝ}
    {BF : Kakeya.Streamlined.BodyFamily}
    {Z : Kakeya.Streamlined.Shading BF}
    {rawTrapezoids : Fin N → Finset WZ1VerticalTrapezoid}
    (hN_pos : 0 < N)
    (hdelta_pos : 0 < delta)
    (hdelta_lt_one : delta < 1)
    (hh_pos : 0 < hierarchyLoss)
    (hsigma_pos : 0 < sigma)
    (A_max : ENNReal)
    (hZ_vertical : ∀ p ∈ Z.union, -1 ≤ p 2 ∧ p 2 ≤ 1)
    (h_length : ∀ t ∈ rawTrapezoids (⟨0, hN_pos⟩ : Fin N),
        t.length ≤ Real.sqrt (wz1Corollary26Scale delta N (⟨0, hN_pos⟩ : Fin N)))
    (h_sep : ∀ t ∈ rawTrapezoids (⟨0, hN_pos⟩ : Fin N),
        ∀ u ∈ rawTrapezoids (⟨0, hN_pos⟩ : Fin N), t ≠ u →
        ∀ z ∈ t.core, ∀ w ∈ u.core,
          Real.sqrt (wz1Corollary26Scale delta N (⟨0, hN_pos⟩ : Fin N)) ≤ |z - w|)
    (h_coverage : ∀ z ∈ Set.Icc (-1 : ℝ) 1,
        horizontalSlice Z.union z ≠ ∅ →
        ∃ t ∈ rawTrapezoids (⟨0, hN_pos⟩ : Fin N), z ∈ t.core)
    (h_volume_lower : Kakeya.realRpowENN delta (sigma + hierarchyLoss / (4 * (N : ℝ))) ≤
        volume Z.union)
    (h_final_contradiction : A_max * ENNReal.ofReal (12 * Real.rpow delta (hierarchyLoss / (N : ℝ))) <
        Kakeya.realRpowENN delta (sigma + hierarchyLoss / (4 * (N : ℝ)))) :
    ∃ t ∈ rawTrapezoids (⟨0, hN_pos⟩ : Fin N),
      volumeInCoreGeneric Z t > A_max * ENNReal.ofReal
        (3 * Real.rpow (wz1Corollary26Scale delta N (⟨0, hN_pos⟩ : Fin N)) (1 / 2 + hierarchyLoss)) := by
  classical
  let i0 : Fin N := ⟨0, hN_pos⟩
  set d : ℝ := Real.sqrt (wz1Corollary26Scale delta N i0) with hd_def
  set L0 : ℝ := Real.rpow (wz1Corollary26Scale delta N i0) (1 / 2 + hierarchyLoss) with hL0_def
  set qh : ℝ := Real.rpow delta (hierarchyLoss / (N : ℝ)) with hqh_def
  set s : Finset WZ1VerticalTrapezoid :=
    (rawTrapezoids i0).filter (fun t => (t.core ∩ Set.Icc (-1 : ℝ) 1).Nonempty) with hs_def
  let zcoord : Point3 → ℝ := fun p => p (2 : Fin 3)
  let slab (t : WZ1VerticalTrapezoid) : Set Point3 := Z.union ∩ {p | zcoord p ∈ t.core}

  have hd_pos : 0 < d := by
    rw [hd_def]
    apply Real.sqrt_pos.mpr
    exact Real.rpow_pos_of_pos hdelta_pos _

  have hL0_pos : 0 < L0 := by
    rw [hL0_def]
    exact Real.rpow_pos_of_pos (Real.rpow_pos_of_pos hdelta_pos _) _

  have hqh_nonneg : 0 ≤ qh := Real.rpow_pos_of_pos hdelta_pos _ |>.le

  have h_card : (s.card : ℝ) ≤ 2 / d + 2 :=
    separated_intervals_card_bound hd_pos
      (fun t ht => h_length t (Finset.mem_filter.mp ht).1)
      (fun t ht u hu hne => h_sep t (Finset.mem_filter.mp ht).1 u (Finset.mem_filter.mp hu).1 hne)
      (fun t ht => Set.nonempty_iff_ne_empty.mp (Finset.mem_filter.mp ht).2)

  have h_d_eq : d = Real.rpow delta (1 / (2 * (N : ℝ))) := by
    rw [hd_def]
    have h1 : wz1Corollary26Scale delta N i0 = Real.rpow delta (1 / (N : ℝ)) := by
      simp [wz1Corollary26Scale, i0] <;> rfl
    rw [h1]
    rw [Real.sqrt_eq_rpow (Real.rpow delta (1 / (N : ℝ)))]
    have h3 : (Real.rpow delta (1 / (N : ℝ))) ^ (1 / 2 : ℝ) =
        Real.rpow delta ((1 / (N : ℝ)) * (1 / 2 : ℝ)) := by
      have h := Real.rpow_mul hdelta_pos.le (1 / (N : ℝ)) (1 / 2 : ℝ)
      exact h.symm
    rw [h3]
    have h4 : (1 / (N : ℝ)) * (1 / 2 : ℝ) = 1 / (2 * (N : ℝ)) := by ring
    rw [h4]

  have h_L0_eq : L0 = Real.rpow delta ((1 + 2 * hierarchyLoss) / (2 * (N : ℝ))) := by
    rw [hL0_def]
    have h1 : wz1Corollary26Scale delta N i0 = Real.rpow delta (1 / (N : ℝ)) := by
      simp [wz1Corollary26Scale, i0] <;> rfl
    rw [h1]
    have h2 : Real.rpow (Real.rpow delta (1 / (N : ℝ))) (1 / 2 + hierarchyLoss) =
        Real.rpow delta ((1 / (N : ℝ)) * (1 / 2 + hierarchyLoss)) := by
      have h := Real.rpow_mul hdelta_pos.le (1 / (N : ℝ)) (1 / 2 + hierarchyLoss)
      exact h.symm
    rw [h2]
    have h3 : (1 / (N : ℝ)) * (1 / 2 + hierarchyLoss) =
        (1 + 2 * hierarchyLoss) / (2 * (N : ℝ)) := by ring
    rw [h3]

  have h_d_le_one : d ≤ 1 := by
    rw [h_d_eq]
    apply Real.rpow_le_one hdelta_pos.le hdelta_lt_one.le <;> positivity

  have h2 : L0 = d * qh := by
    rw [h_L0_eq, h_d_eq, hqh_def]
    have h3 : (1 + 2 * hierarchyLoss) / (2 * (N : ℝ)) =
        1 / (2 * (N : ℝ)) + hierarchyLoss / (N : ℝ) := by ring
    rw [h3]
    have h4 : Real.rpow delta (1 / (2 * (N : ℝ)) + hierarchyLoss / (N : ℝ)) =
        Real.rpow delta (1 / (2 * (N : ℝ))) * Real.rpow delta (hierarchyLoss / (N : ℝ)) := by
      have h := Real.rpow_add hdelta_pos (1 / (2 * (N : ℝ))) (hierarchyLoss / (N : ℝ))
      exact h
    rw [h4] <;> rfl

  have h5 : (s.card : ℝ) * d ≤ 4 := by
    have h1 : (s.card : ℝ) ≤ 2 / d + 2 := h_card
    have h_pos : 0 < d := hd_pos
    calc (s.card : ℝ) * d ≤ (2 / d + 2) * d := by gcongr
      _ = 2 + 2 * d := by field_simp [h_pos.ne'] <;> ring
      _ ≤ 4 := by linarith [h_d_le_one]

  have h_card_L0 : (s.card : ℝ) * L0 ≤ 4 * qh := by
    rw [h2]
    have h6 : (s.card : ℝ) * (d * qh) = ((s.card : ℝ) * d) * qh := by ring
    rw [h6]
    exact mul_le_mul_of_nonneg_right h5 hqh_nonneg

  -- Trapezoids not intersecting [-1,1] have zero core volume
  have h_zero_outside : ∀ t ∈ rawTrapezoids i0, t ∉ s → volumeInCoreGeneric Z t = 0 := by
    intro t htin hnot
    have h_not_intersect : (t.core ∩ Set.Icc (-1 : ℝ) 1) = ∅ := by
      by_contra h
      have h' : (t.core ∩ Set.Icc (-1 : ℝ) 1).Nonempty := Set.nonempty_iff_ne_empty.mpr h
      exact hnot (Finset.mem_filter.mpr ⟨htin, h'⟩)
    have hZ_z : ∀ p ∈ Z.union, -1 ≤ zcoord p ∧ zcoord p ≤ 1 :=
      fun p hp => hZ_vertical p hp
    have h_empty : slab t = ∅ := by
      apply Set.ext
      intro x
      simp only [slab, Set.mem_empty_iff_false, iff_false, Set.mem_inter_iff, Set.mem_setOf_eq]
      intro hx
      have h4 : zcoord x ∈ t.core := hx.2
      have h5 : x ∈ Z.union := hx.1
      have h6 : -1 ≤ zcoord x ∧ zcoord x ≤ 1 := hZ_z x h5
      have h7 : zcoord x ∈ t.core ∩ Set.Icc (-1 : ℝ) 1 := ⟨h4, ⟨h6.1, h6.2⟩⟩
      rw [h_not_intersect] at h7
      simp at h7
    have h_vol : volumeInCoreGeneric Z t = 0 := by
      have h_eq : volumeInCoreGeneric Z t = volume (slab t) := by
        simp [volumeInCoreGeneric, volumeInSlabGeneric, WZ1VerticalTrapezoid.core, slab, zcoord] <;> rfl
      rw [h_eq, h_empty] <;> simp
    exact h_vol

  -- Disjointness of core slabs
  have h_disj : (↑(rawTrapezoids i0) : Set WZ1VerticalTrapezoid).PairwiseDisjoint slab := by
    intro t htin u huin hne
    have h1 : t.core ∩ u.core = ∅ := by
      ext z
      simp only [Set.mem_empty_iff_false, iff_false, Set.mem_inter_iff]
      intro ⟨hz1, hz2⟩
      have h2 : d ≤ |z - z| := h_sep t htin u huin hne z hz1 z hz2
      simp at h2 <;> linarith
    have h3 : Disjoint {p : Point3 | zcoord p ∈ t.core} {p : Point3 | zcoord p ∈ u.core} := by
      rw [Set.disjoint_left]
      intro x hx1 hx2
      have h6 : zcoord x ∈ t.core ∩ u.core := ⟨hx1, hx2⟩
      rw [h1] at h6
      simp at h6
    have h_sub1 : slab t ⊆ {p : Point3 | zcoord p ∈ t.core} := by
      intro x hx; exact hx.2
    have h_sub2 : slab u ⊆ {p : Point3 | zcoord p ∈ u.core} := by
      intro x hx; exact hx.2
    exact h3.mono h_sub1 h_sub2

  -- Measurability
  have h_meas_coord : Measurable zcoord := by
    have h_cont : Continuous zcoord := by fun_prop
    exact h_cont.measurable
  have h_meas : ∀ t ∈ rawTrapezoids i0, MeasurableSet (slab t) := by
    intro t _
    have h1 : MeasurableSet (Z.union) := by
      have h_union : Z.union = ⋃ i : Fin BF.card, Z.carrier i := by
        ext p
        change (∃ i : Fin BF.card, p ∈ Z.carrier i) ↔
          p ∈ ⋃ i : Fin BF.card, Z.carrier i
        constructor
        · rintro ⟨i, hi⟩
          exact Set.mem_iUnion.mpr ⟨i, hi⟩
        · intro hp
          rcases Set.mem_iUnion.mp hp with ⟨i, hi⟩
          exact ⟨i, hi⟩
      rw [h_union]
      exact MeasurableSet.iUnion Z.measurable_carrier
    have h2 : MeasurableSet ({p : Point3 | zcoord p ∈ t.core} : Set Point3) := by
      have h_core : t.core = Set.Icc t.left t.right := by
        simp [WZ1VerticalTrapezoid.core]
      have h_pre : {p : Point3 | zcoord p ∈ t.core} = zcoord ⁻¹' t.core := by
        ext x; simp [zcoord]
      rw [h_pre, h_core]
      exact measurableSet_Icc.preimage h_meas_coord
    exact h1.inter h2

  -- Coverage
  have h_cover : Z.union ⊆ ⋃ t ∈ rawTrapezoids i0, slab t := by
    intro p hp
    have hz : -1 ≤ zcoord p ∧ zcoord p ≤ 1 :=
      hZ_vertical p hp
    have h_slice_nonempty : horizontalSlice Z.union (zcoord p) ≠ ∅ := by
      have hpin : p ∈ horizontalSlice Z.union (zcoord p) := by
        simp [horizontalSlice, hp, zcoord]
      exact Set.nonempty_iff_ne_empty.mp ⟨p, hpin⟩
    have h9 : ∃ t ∈ rawTrapezoids i0, zcoord p ∈ t.core :=
      h_coverage (zcoord p) ⟨hz.1, hz.2⟩ h_slice_nonempty
    rcases h9 with ⟨t, htin, h10⟩
    have h11 : p ∈ slab t := ⟨hp, h10⟩
    have h12 : p ∈ ⋃ t ∈ rawTrapezoids i0, slab t :=
      Set.mem_biUnion htin h11
    exact h12

  -- Volume = sum of core volumes
  have h_vol_eq : volume Z.union = ∑ t ∈ rawTrapezoids i0, volumeInCoreGeneric Z t := by
    have h4 : Z.union = ⋃ t ∈ rawTrapezoids i0, slab t := by
      apply Set.Subset.antisymm h_cover
      intro x hx
      have h_exists : ∃ (t : WZ1VerticalTrapezoid), t ∈ rawTrapezoids i0 ∧ x ∈ slab t := by
        simpa [Set.mem_biUnion] using hx
      rcases h_exists with ⟨t, htin, hxt⟩
      exact hxt.1
    have h5 : ∀ t ∈ rawTrapezoids i0, volume (slab t) = volumeInCoreGeneric Z t := by
      intro t _
      simp [slab, volumeInCoreGeneric, volumeInSlabGeneric, WZ1VerticalTrapezoid.core, zcoord] <;> rfl
    rw [h4, MeasureTheory.measure_biUnion_finset h_disj h_meas]
    apply Finset.sum_congr rfl
    intro t ht
    exact (h5 t ht).symm

  -- Restrict sum to s
  have h_vol_restrict : volume Z.union = ∑ t ∈ s, volumeInCoreGeneric Z t := by
    rw [h_vol_eq]
    have h5 : ∑ t ∈ s, volumeInCoreGeneric Z t = ∑ t ∈ rawTrapezoids i0, volumeInCoreGeneric Z t := by
      apply Finset.sum_subset (Finset.filter_subset _ _)
      intro t htin hnot
      exact h_zero_outside t htin hnot
    exact h5.symm

  by_contra h_not_popular
  have h_all_unpopular : ∀ t ∈ s, volumeInCoreGeneric Z t ≤ A_max * ENNReal.ofReal (3 * L0) := by
    intro t ht
    have h_t_in : t ∈ rawTrapezoids i0 := (Finset.mem_filter.mp ht).1
    have h : ¬(volumeInCoreGeneric Z t > A_max * ENNReal.ofReal (3 * L0)) := by
      intro h_cont
      exact h_not_popular ⟨t, h_t_in, h_cont⟩
    exact le_of_not_gt h

  have h_card_L0_ENN : (s.card : ENNReal) * ENNReal.ofReal (3 * L0) =
      ENNReal.ofReal (3 * (s.card : ℝ) * L0) := by
    have h9 : (s.card : ENNReal) = ENNReal.ofReal (s.card : ℝ) := by simp
    rw [h9]
    have h10 : ENNReal.ofReal (s.card : ℝ) * ENNReal.ofReal (3 * L0) =
        ENNReal.ofReal ((s.card : ℝ) * (3 * L0)) := by
      rw [← ENNReal.ofReal_mul (by positivity)] <;> ring
    rw [h10]
    have h11 : (s.card : ℝ) * (3 * L0) = 3 * (s.card : ℝ) * L0 := by ring
    rw [h11]

  have h_upper : ∑ t ∈ s, volumeInCoreGeneric Z t ≤
      (s.card : ENNReal) * (A_max * ENNReal.ofReal (3 * L0)) := by
    calc ∑ t ∈ s, volumeInCoreGeneric Z t
        ≤ ∑ t ∈ s, (A_max * ENNReal.ofReal (3 * L0)) := by
          apply Finset.sum_le_sum
          intro t ht
          exact h_all_unpopular t ht
      _ = (s.card : ENNReal) * (A_max * ENNReal.ofReal (3 * L0)) := by
        simp [Finset.sum_const]

  have h_final_upper : volume Z.union ≤
      A_max * ENNReal.ofReal (3 * (s.card : ℝ) * L0) := by
    have h1 : volume Z.union = ∑ t ∈ s, volumeInCoreGeneric Z t := h_vol_restrict
    rw [h1]
    have h2 : ∑ t ∈ s, volumeInCoreGeneric Z t ≤ (s.card : ENNReal) * (A_max * ENNReal.ofReal (3 * L0)) := h_upper
    have h3 : (s.card : ENNReal) * (A_max * ENNReal.ofReal (3 * L0)) =
        A_max * ((s.card : ENNReal) * ENNReal.ofReal (3 * L0)) := by
      have h4 : (s.card : ENNReal) * (A_max * ENNReal.ofReal (3 * L0)) =
          ((s.card : ENNReal) * A_max) * ENNReal.ofReal (3 * L0) := by rw [mul_assoc]
      rw [h4]
      have h5 : (s.card : ENNReal) * A_max = A_max * (s.card : ENNReal) := mul_comm _ _
      rw [h5, mul_assoc]
    rw [h3] at h2
    rw [h_card_L0_ENN] at h2
    exact h2

  have h_bound_real : 3 * (s.card : ℝ) * L0 ≤ 12 * qh := by
    have h10 : (s.card : ℝ) * L0 ≤ 4 * qh := h_card_L0
    nlinarith [hqh_nonneg]

  have h_final : volume Z.union ≤ A_max * ENNReal.ofReal (12 * qh) := by
    have h : A_max * ENNReal.ofReal (3 * (s.card : ℝ) * L0) ≤ A_max * ENNReal.ofReal (12 * qh) :=
      mul_le_mul_left' (ENNReal.ofReal_le_ofReal h_bound_real) A_max
    exact le_trans h_final_upper h

  exact not_le.mpr (h_final.trans_lt h_final_contradiction) h_volume_lower



end Kakeya.Assouad.PureHierarchyGeneric

end
