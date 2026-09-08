import MyLeanRepo.Kakeya.Streamlined.GeometricLemmas.TubeContainment
import MyLeanRepo.Kakeya.Streamlined.GeometricLemmas.PositionGrid
import MyLeanRepo.Kakeya.Streamlined.Families
import MyLeanRepo.Kakeya.Streamlined.UniformRefinement.SingleScaleCover

/-!
# Coarse tube cover construction via phase-space gridding
-/

noncomputable section

open Kakeya.Streamlined.GeometricLemmas

namespace Kakeya.Streamlined

lemma construct_coarse_cover
    {δ ρ : ℝ} (hδ : 0 < δ) (hδρ : δ ≤ ρ) (hρ1 : ρ ≤ 1)
    (F : TubeFamily δ) (hF_ball : F.IsInUnitBall)
    (Y : TubeShading F) :
    ∃ (coarse : TubeFamily ρ)
      (cover : TubeCover F coarse)
      (weight : Fin coarse.card → ENNReal),
      (∀ j, weight j =
        ∑ i ∈ (Finset.univ.filter fun i : Fin F.card => cover.parent i = j),
          MeasureTheory.volume (Y.carrier i)) ∧
      (∀ i,
        ‖tubeMidpoint (F.tube i) -
            tubeMidpoint (coarse.tube (cover.parent i))‖ ≤ ρ) ∧
      (∀ i,
        ‖(F.tube i).direction -
            (coarse.tube (cover.parent i)).direction‖ ≤ 2 * ρ) := by
  classical
  by_cases h_eq : δ = ρ
  · -- Case δ = ρ: identity cover
    subst h_eq
    let coarse : TubeFamily δ :=
      { card := F.card
        tube := fun i =>
          { base := (F.tube i).base
            direction := (F.tube i).direction
            direction_unit := (F.tube i).direction_unit } }
    let cover : TubeCover F coarse :=
      { parent := id
        parent_surjective := Function.surjective_id
        nested := fun _ => Set.Subset.rfl }
    let weight : Fin coarse.card → ENNReal := fun j =>
      MeasureTheory.volume (Y.carrier j)
    refine ⟨coarse, cover, weight, ?_, ?_, ?_⟩
    · intro j
      have hfilter : (Finset.univ.filter fun i : Fin F.card => (id i) = j) = {j} := by
        ext i; simp
      rw [hfilter]
      simp [weight] <;> rfl
    · intro i
      simp [cover, coarse]
      positivity
    · intro i
      simp [cover, coarse]
      positivity
  · -- Case δ < ρ
    have h_lt : δ < ρ := lt_of_le_of_ne hδρ h_eq
    set s : ℝ := (ρ - δ) / 20 with hs_def
    have hs_pos : 0 < s := by positivity
    have hs_le : s ≤ 1 / 20 := by
      rw [hs_def]
      have h : ρ - δ ≤ 1 := by linarith
      exact div_le_div_of_nonneg_right h (by norm_num)

    rcases position_grid s hs_pos 1 (by norm_num) with ⟨midGrid, hmidCover, _, _⟩
    rcases position_grid s hs_pos 1 (by norm_num) with ⟨dirGrid, hdirCover, _, _⟩

    let midOf (i : Fin F.card) : Point3 := tubeMidpoint (F.tube i)
    let dirOf (i : Fin F.card) : Point3 := (F.tube i).direction

    have hmid_bound : ∀ i : Fin F.card, ‖midOf i‖ ≤ 1 := by
      intro i
      have hseg : midOf i ∈ Kakeya.unitSegment (F.tube i).base (F.tube i).direction := by
        refine ⟨1 / 2, ⟨by norm_num, by norm_num⟩, ?_⟩
        simp [midOf, tubeMidpoint] <;> abel
      have hdist0 : dist (midOf i) (midOf i) ≤ δ := by
        simpa using hδ.le
      have h1 : midOf i ∈ (F.tube i).carrier :=
        Metric.mem_cthickening_of_dist_le (midOf i) (midOf i) δ
          (Kakeya.unitSegment (F.tube i).base (F.tube i).direction) hseg hdist0
      have h2 : (F.tube i).carrier ⊆ Kakeya.DeltaTube.unitBall := hF_ball i
      have h3 : midOf i ∈ Kakeya.DeltaTube.unitBall := h2 h1
      simpa [Kakeya.DeltaTube.unitBall, Metric.mem_closedBall] using h3

    have hdir_bound : ∀ i : Fin F.card, ‖dirOf i‖ ≤ 1 := by
      intro i; have h : ‖dirOf i‖ = 1 := (F.tube i).direction_unit
      rw [h] <;> norm_num

    let chooseMid (i : Fin F.card) : Point3 :=
      Classical.choose (hmidCover (midOf i) (hmid_bound i))
    let chooseDir (i : Fin F.card) : Point3 :=
      Classical.choose (hdirCover (dirOf i) (hdir_bound i))

    have hchooseMid : ∀ i, chooseMid i ∈ midGrid ∧ ‖midOf i - chooseMid i‖ ≤ Real.sqrt 3 / 2 * s := by
      intro i; exact Classical.choose_spec (hmidCover (midOf i) (hmid_bound i))
    have hchooseDir : ∀ i, chooseDir i ∈ dirGrid ∧ ‖dirOf i - chooseDir i‖ ≤ Real.sqrt 3 / 2 * s := by
      intro i; exact Classical.choose_spec (hdirCover (dirOf i) (hdir_bound i))

    let cellOf (i : Fin F.card) : Point3 × Point3 := (chooseMid i, chooseDir i)
    let nonemptyCells : Finset (Point3 × Point3) := Finset.image cellOf Finset.univ
    let e : {c : Point3 × Point3 // c ∈ nonemptyCells} ≃ Fin nonemptyCells.card :=
      nonemptyCells.equivFin

    let witness (cell : Point3 × Point3) (hcell : cell ∈ nonemptyCells) : Fin F.card :=
      Classical.choose (Finset.mem_image.mp hcell)

    have h_witness_spec : ∀ cell hcell, cellOf (witness cell hcell) = cell := by
      intro cell hcell
      have h_spec := Classical.choose_spec (Finset.mem_image.mp hcell)
      exact h_spec.2

    have hq_pos : ∀ (cell : Point3 × Point3), cell ∈ nonemptyCells → 0 < ‖cell.2‖ := by
      intro cell hcell
      let i := witness cell hcell
      have hcell_eq : cellOf i = cell := h_witness_spec cell hcell
      have hq : cell.2 = chooseDir i := by
        have h : (cellOf i).2 = chooseDir i := by rfl
        rw [hcell_eq] at h; exact h
      rw [hq]
      have h1 : ‖dirOf i - chooseDir i‖ ≤ Real.sqrt 3 / 2 * s := (hchooseDir i).2
      have h2 : ‖dirOf i‖ = 1 := (F.tube i).direction_unit
      have h3 : ‖dirOf i‖ ≤ ‖dirOf i - chooseDir i‖ + ‖chooseDir i‖ := by
        have h_add : ‖(dirOf i - chooseDir i) + chooseDir i‖ ≤
            ‖dirOf i - chooseDir i‖ + ‖chooseDir i‖ := norm_add_le _ _
        have h_simp : (dirOf i - chooseDir i) + chooseDir i = dirOf i := by abel
        rw [h_simp] at h_add
        exact h_add
      have h4 : ‖chooseDir i‖ ≥ 1 - Real.sqrt 3 / 2 * s := by
        rw [h2] at h3
        linarith
      have h_sqrt3_lt_2 : Real.sqrt 3 < 2 := by
        have h : (3 : ℝ) < (2 : ℝ)^2 := by norm_num
        have h' : Real.sqrt 3 < 2 := by
          rw [Real.sqrt_lt] <;> norm_num
        exact h'
      have h5 : Real.sqrt 3 / 2 * s < 1 := by
        have h6 : Real.sqrt 3 / 2 * s ≤ Real.sqrt 3 / 40 := by
          have h61 : Real.sqrt 3 / 2 * s ≤ Real.sqrt 3 / 2 * (1 / 20 : ℝ) := by gcongr <;> linarith
          have h62 : Real.sqrt 3 / 2 * (1 / 20 : ℝ) = Real.sqrt 3 / 40 := by ring
          rw [h62] at h61
          exact h61
        have h7 : Real.sqrt 3 / 40 < 1 := by
          calc Real.sqrt 3 / 40 < 2 / 40 := by gcongr
            _ = 1 / 20 := by norm_num
            _ < 1 := by norm_num
        exact lt_of_le_of_lt h6 h7
      linarith

    let normalizedDir (q : Point3) (hpos : 0 < ‖q‖) : Point3 := (‖q‖)⁻¹ • q
    have normalizedDir_spec : ∀ (q : Point3) (hpos : 0 < ‖q‖), ‖normalizedDir q hpos‖ = 1 := by
      intro q hpos
      have h1 : ‖normalizedDir q hpos‖ = |(‖q‖)⁻¹| * ‖q‖ := by
        rw [norm_smul] <;> rfl
      rw [h1]
      have h2 : |(‖q‖)⁻¹| = (‖q‖)⁻¹ := by
        rw [abs_of_pos] <;> exact inv_pos.mpr hpos
      rw [h2]
      field_simp [hpos.ne'] <;> norm_num

    let coarse : TubeFamily ρ :=
      { card := nonemptyCells.card
        tube := fun j =>
          let cell : {c // c ∈ nonemptyCells} := e.symm j
          let p : Point3 := cell.val.1
          let q : Point3 := cell.val.2
          let hpos : 0 < ‖q‖ := hq_pos cell.val cell.property
          let d : Point3 := normalizedDir q hpos
          { base := p - (1 / 2 : ℝ) • d
            direction := d
            direction_unit := normalizedDir_spec q hpos } }

    let parent (i : Fin F.card) : Fin coarse.card :=
      e ⟨cellOf i, Finset.mem_image_of_mem cellOf (Finset.mem_univ i)⟩

    have hcover_surj : Function.Surjective parent := by
      intro j
      let cell : {c // c ∈ nonemptyCells} := e.symm j
      let i := witness cell.val cell.property
      have h_i : cellOf i = cell.val := h_witness_spec cell.val cell.property
      refine ⟨i, ?_⟩
      have h_cellOf_mem : cellOf i ∈ nonemptyCells := by
        rw [h_i]
        exact cell.property
      have h6 : (⟨cellOf i, h_cellOf_mem⟩ : {c // c ∈ nonemptyCells}) = cell := by
        apply Subtype.ext; exact h_i
      have h7 : parent i = j := by
        dsimp only [parent]
        rw [h6]
        exact e.apply_symm_apply j
      exact h7

    have hclose : ∀ i : Fin F.card,
        ‖tubeMidpoint (F.tube i) -
            tubeMidpoint (coarse.tube (parent i))‖ +
          ‖(F.tube i).direction -
            (coarse.tube (parent i)).direction‖ / 2 + δ ≤ ρ := by
      intro i
      let j := parent i
      let cell : {c // c ∈ nonemptyCells} :=
        ⟨cellOf i, Finset.mem_image_of_mem cellOf (Finset.mem_univ i)⟩
      let p : Point3 := cell.val.1
      let q : Point3 := cell.val.2
      let hpos : 0 < ‖q‖ := hq_pos cell.val cell.property
      let d : Point3 := normalizedDir q hpos
      have h_e_eq : e cell = j := by
        dsimp only [j, parent]
        <;> congr
        <;> exact Subtype.ext rfl
      have h_mid_dist : ‖midOf i - p‖ ≤ Real.sqrt 3 / 2 * s := (hchooseMid i).2
      have h_dir_dist1 : ‖dirOf i - q‖ ≤ Real.sqrt 3 / 2 * s := (hchooseDir i).2
      have h_dir_norm : ‖dirOf i‖ = 1 := (F.tube i).direction_unit
      have hq_near1 : |(1 : ℝ) - ‖q‖| ≤ Real.sqrt 3 / 2 * s := by
        have h3 : ‖dirOf i‖ ≤ ‖dirOf i - q‖ + ‖q‖ := by
          have h_add : ‖(dirOf i - q) + q‖ ≤ ‖dirOf i - q‖ + ‖q‖ := norm_add_le _ _
          have h_simp : (dirOf i - q) + q = dirOf i := by abel
          rw [h_simp] at h_add
          exact h_add
        have h4 : ‖q‖ ≤ ‖dirOf i‖ + ‖dirOf i - q‖ := by
          have h_sub : ‖dirOf i - (dirOf i - q)‖ ≤ ‖dirOf i‖ + ‖dirOf i - q‖ := norm_sub_le _ _
          have h_simp : dirOf i - (dirOf i - q) = q := by abel
          rw [h_simp] at h_sub
          exact h_sub
        rw [h_dir_norm] at h3 h4
        have h5 : 1 - Real.sqrt 3 / 2 * s ≤ ‖q‖ := by linarith
        have h6 : ‖q‖ ≤ 1 + Real.sqrt 3 / 2 * s := by linarith
        rw [abs_le] <;> constructor <;> linarith
      have h_dir_dist2 : ‖dirOf i - d‖ ≤ Real.sqrt 3 * s := by
        have h_triangle : ‖dirOf i - d‖ ≤ ‖dirOf i - q‖ + ‖q - d‖ := by
          have h_add : ‖(dirOf i - q) + (q - d)‖ ≤ ‖dirOf i - q‖ + ‖q - d‖ := norm_add_le _ _
          have h_simp : (dirOf i - q) + (q - d) = dirOf i - d := by abel
          rw [h_simp] at h_add
          exact h_add
        calc
          ‖dirOf i - d‖ ≤ ‖dirOf i - q‖ + ‖q - d‖ := h_triangle
          _ = ‖dirOf i - q‖ + |(1 : ℝ) - ‖q‖| := by
            have h5 : ‖q - d‖ = |(1 : ℝ) - ‖q‖| := by
              have h6 : q - d = (1 - (‖q‖)⁻¹) • q := by
                have h_d1 : d = (‖q‖)⁻¹ • q := by
                  simp [d, normalizedDir] <;> rfl
                rw [h_d1]
                have h : q - (‖q‖)⁻¹ • q = (1 - (‖q‖)⁻¹) • q := by
                  rw [sub_smul, one_smul]
                exact h
              rw [h6]
              have h7 : ‖(1 - (‖q‖)⁻¹) • q‖ = |1 - (‖q‖)⁻¹| * ‖q‖ := by
                rw [norm_smul] <;> rfl
              rw [h7]
              have h8 : |1 - (‖q‖)⁻¹| * ‖q‖ = |(1 : ℝ) - ‖q‖| := by
                have h91 : |‖q‖| = ‖q‖ := by
                  rw [abs_of_nonneg] <;> exact norm_nonneg _
                have h9 : |1 - (‖q‖)⁻¹| * ‖q‖ = |(1 - (‖q‖)⁻¹) * ‖q‖| := by
                  calc
                    |1 - (‖q‖)⁻¹| * ‖q‖
                      = |1 - (‖q‖)⁻¹| * |‖q‖| := by rw [h91]
                    _ = |(1 - (‖q‖)⁻¹) * ‖q‖| := by rw [← abs_mul]
                rw [h9]
                have h10 : (1 - (‖q‖)⁻¹) * ‖q‖ = ‖q‖ - 1 := by
                  field_simp [hpos.ne'] <;> ring
                rw [h10]
                have h11 : |‖q‖ - 1| = |1 - ‖q‖| := by
                  have h12 : ‖q‖ - 1 = -(1 - ‖q‖) := by ring
                  rw [h12, abs_neg]
                exact h11
              exact h8
            rw [h5]
          _ ≤ Real.sqrt 3 / 2 * s + Real.sqrt 3 / 2 * s := by gcongr
          _ = Real.sqrt 3 * s := by ring
      have h_symm : e.symm j = cell := by
        rw [← h_e_eq]
        exact e.symm_apply_apply cell
      have h_mid_eq : tubeMidpoint (coarse.tube j) = p := by
        simp [coarse, tubeMidpoint, h_symm] <;> abel
      have h_dir_eq : (coarse.tube j).direction = d := by
        simp [coarse, h_symm] <;> rfl
      have h_close : ‖tubeMidpoint (F.tube i) - tubeMidpoint (coarse.tube j)‖ +
            ‖(F.tube i).direction - (coarse.tube j).direction‖ / 2 + δ ≤ ρ := by
        rw [h_mid_eq, h_dir_eq]
        have h_total : ‖midOf i - p‖ + ‖dirOf i - d‖ / 2 + δ ≤
            Real.sqrt 3 / 2 * s + Real.sqrt 3 * s / 2 + δ := by gcongr <;> linarith
        have h_eq2 : Real.sqrt 3 / 2 * s + Real.sqrt 3 * s / 2 = Real.sqrt 3 * s := by ring
        rw [h_eq2] at h_total
        have h_final : Real.sqrt 3 * s + δ ≤ ρ := by
          rw [hs_def]
          have h_sqrt3_lt_20 : Real.sqrt 3 < 20 := by
            have h1 : Real.sqrt 3 ≤ 2 := by
              rw [Real.sqrt_le_left] <;> norm_num
            linarith
          nlinarith
        linarith
      exact h_close

    have hcontainment : ∀ i : Fin F.card,
        (F.tube i).carrier ⊆ (coarse.tube (parent i)).carrier := by
      intro i
      exact tube_contained_of_midpoint_direction_close hδ.le
        (F.tube i) (coarse.tube (parent i)) (hclose i)

    let cover : TubeCover F coarse :=
      { parent := parent
        parent_surjective := hcover_surj
        nested := hcontainment }

    let weight (j : Fin coarse.card) : ENNReal :=
      ∑ i ∈ (Finset.univ.filter fun i : Fin F.card => cover.parent i = j),
        MeasureTheory.volume (Y.carrier i)

    refine ⟨coarse, cover, weight, ?_, ?_, ?_⟩
    · intro j
      rfl
    · intro i
      have h := hclose i
      have hdir :
          0 ≤ ‖(F.tube i).direction -
            (coarse.tube (cover.parent i)).direction‖ / 2 := by
        positivity
      nlinarith [hδ]
    · intro i
      have h := hclose i
      have hmid :
          0 ≤ ‖tubeMidpoint (F.tube i) -
            tubeMidpoint (coarse.tube (cover.parent i))‖ := by
        positivity
      nlinarith [hδ]

end Kakeya.Streamlined
