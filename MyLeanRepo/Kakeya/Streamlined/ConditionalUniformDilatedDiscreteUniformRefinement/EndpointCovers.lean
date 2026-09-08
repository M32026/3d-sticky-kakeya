import MyLeanRepo.Kakeya.Streamlined.UniformRefinement.EndpointCovers
import MyLeanRepo.Kakeya.Streamlined.GeometricLemmas.SelfDilatedContainment
import MyLeanRepo.Kakeya.Streamlined.UniformRefinement.SingleScaleCover

/-!
# Endpoint `LocalDilatedTubeCover`s for the paper scale grid

Lifts the identity and unit-scale `TubeCover`s to `LocalDilatedTubeCover`
with the fixed dilation `A = 1000` and a geometric constant `C`.

## Main definitions

- `identityLocalDilatedTubeCover`: the finest-scale cover with `parent = id`.
- `unitScaleLocalDilatedTubeCover`: the coarsest-scale singleton cover.

## Main results

- `identityLocalDilatedTubeCover_injective`
- `identityLocalDilatedTubeCover_carrier_eq`
- `unitScaleTubeFamily_unique`
-/

noncomputable section

namespace Kakeya.Streamlined

open GeometricLemmas

/-- The norm of the transverse component is at most the full norm. -/
private lemma transverse_component_norm_le {d v : Point3} (hv : ‖v‖ = 1) :
    ‖d - inner ℝ d v • v‖ ≤ ‖d‖ := by
  set p : Point3 := inner ℝ d v • v with hp
  have h_ip1 : inner ℝ d p = (inner ℝ d v)^2 := by
    rw [hp, inner_smul_right]
    <;> ring
  have h_normp : ‖p‖^2 = (inner ℝ d v)^2 := by
    calc
      ‖p‖^2 = (|inner ℝ d v| * ‖v‖)^2 := by
        have h1 : ‖p‖ = |inner ℝ d v| * ‖v‖ := by
          rw [hp]; exact norm_smul _ _
        rw [h1]
      _ = (|inner ℝ d v|)^2 * ‖v‖^2 := by ring
      _ = (|inner ℝ d v|)^2 * (1 : ℝ) := by rw [hv] <;> norm_num
      _ = (inner ℝ d v)^2 := by simp [sq_abs] <;> ring
  have h_main : ‖d - p‖^2 = ‖d‖^2 - 2 * inner ℝ d p + ‖p‖^2 := by
    have h1 : inner ℝ (d - p) (d - p) = inner ℝ d (d - p) - inner ℝ p (d - p) := by
      rw [inner_sub_left]
    have h2 : inner ℝ d (d - p) = inner ℝ d d - inner ℝ d p := by
      rw [inner_sub_right]
    have h3 : inner ℝ p (d - p) = inner ℝ p d - inner ℝ p p := by
      rw [inner_sub_right]
    have h_expand : inner ℝ (d - p) (d - p) =
        inner ℝ d d - inner ℝ d p - inner ℝ p d + inner ℝ p p := by
      rw [h1, h2, h3] <;> ring
    have h_comm : inner ℝ p d = inner ℝ d p := real_inner_comm d p
    have h_isd : inner ℝ d d = ‖d‖^2 := real_inner_self_eq_norm_sq d
    have h_isp : inner ℝ p p = ‖p‖^2 := real_inner_self_eq_norm_sq p
    have h_isdp : inner ℝ (d - p) (d - p) = ‖d - p‖^2 := real_inner_self_eq_norm_sq (d - p)
    calc
      ‖d - p‖^2 = inner ℝ (d - p) (d - p) := h_isdp.symm
      _ = inner ℝ d d - inner ℝ d p - inner ℝ p d + inner ℝ p p := h_expand
      _ = inner ℝ d d - 2 * inner ℝ d p + inner ℝ p p := by rw [h_comm] <;> ring
      _ = ‖d‖^2 - 2 * inner ℝ d p + ‖p‖^2 := by rw [h_isd, h_isp] <;> ring
  have h_goal : ‖d - p‖^2 ≤ ‖d‖^2 := by
    calc
      ‖d - p‖^2 = ‖d‖^2 - 2 * inner ℝ d p + ‖p‖^2 := h_main
      _ = ‖d‖^2 - 2 * (inner ℝ d v)^2 + (inner ℝ d v)^2 := by rw [h_ip1, h_normp]
      _ = ‖d‖^2 - (inner ℝ d v)^2 := by ring
      _ ≤ ‖d‖^2 := by
        have h6 : 0 ≤ (inner ℝ d v)^2 := by positivity
        linarith
  have h7 : 0 ≤ ‖d - p‖ := by positivity
  have h8 : 0 ≤ ‖d‖ := by positivity
  nlinarith

/-- Helper: any two elements of `Fin 1` are equal. -/
private lemma fin_one_eq (j k : Fin 1) : j = k := by
  apply Fin.ext
  have hj : j.val < 1 := j.isLt
  have hk : k.val < 1 := k.isLt
  omega

/--
The identity cover at the finest paper scale, lifted to a
`LocalDilatedTubeCover`.  Every tube is its own parent after a universal
homothetic dilation, and all phase-space errors are zero.
-/
def identityLocalDilatedTubeCover {δ : ℝ} (F : TubeFamily δ)
    (C : ℝ) (hC : 0 ≤ C) (hδ : 0 ≤ δ) :
    LocalDilatedTubeCover 1000 C F F :=
  { toDilatedTubeCover :=
    { parent := id
      parent_surjective := Function.surjective_id
      nested := fun i =>
        self_dilated_containment 1000 (by norm_num) (F.tube i) }
    transverse_midpoint_close := by
      intro i
      simpa using mul_nonneg hC hδ
    direction_close_or_reverse := by
      intro i
      left
      simpa using mul_nonneg hC hδ }

/-- The identity cover parent is injective. -/
lemma identityLocalDilatedTubeCover_injective {δ : ℝ}
    (F : TubeFamily δ) {C hC hδ} :
    Function.Injective (identityLocalDilatedTubeCover F C hC hδ).parent := by
  delta identityLocalDilatedTubeCover
  exact Function.injective_id

/-- The identity cover preserves carriers exactly. -/
lemma identityLocalDilatedTubeCover_carrier_eq {δ : ℝ}
    (F : TubeFamily δ) {C hC hδ} (i : Fin F.card) :
    (F.tube ((identityLocalDilatedTubeCover F C hC hδ).parent i)).carrier =
      (F.tube i).carrier := by
  delta identityLocalDilatedTubeCover
  simp

/--
The singleton unit-scale cover, lifted to a `LocalDilatedTubeCover`.
A single unit-radius tube covers the entire unit ball.
-/
def unitScaleLocalDilatedTubeCover {δ : ℝ} (F : TubeFamily δ)
    (hF_nonempty : F.Nonempty) (hF_ball : F.IsInUnitBall)
    (C : ℝ) (hC : 2 ≤ C) :
    LocalDilatedTubeCover 1000 C F unitScaleTubeFamily :=
  let j0 : Fin unitScaleTubeFamily.card := ⟨0, by simp [unitScaleTubeFamily]⟩
  { toDilatedTubeCover :=
    { parent := fun _ => j0
      parent_surjective := by
        intro j
        refine ⟨⟨0, hF_nonempty⟩, ?_⟩
        exact fin_one_eq _ _
      nested := fun i =>
        (hF_ball i).trans
          (unitBall_subset_unitScaleTube.trans
            (self_dilated_containment 1000 (by norm_num) unitScaleTube)) }
    transverse_midpoint_close := by
      intro i
      have h_tube_eq : unitScaleTubeFamily.tube j0 = unitScaleTube := by
        simp [j0, unitScaleTubeFamily]
      rw [h_tube_eq]
      let m_f := tubeMidpoint (F.tube i)
      let m_c := tubeMidpoint unitScaleTube
      let v := unitScaleTube.direction
      have h_mf_in : m_f ∈ Kakeya.DeltaTube.unitBall :=
        (hF_ball i) (tubeMidpoint_mem_carrier (F.tube i))
      have h1 : ‖m_f‖ ≤ 1 := by
        simpa [Kakeya.DeltaTube.unitBall, Metric.mem_closedBall] using h_mf_in
      have h_dir1 : ‖v‖ = 1 := unitScaleTube.direction_unit
      have h2 : m_c = (1 / 2 : ℝ) • v := by
        simp [m_c, tubeMidpoint, unitScaleTube]
        <;> abel
      have h3 : ‖m_c‖ = 1 / 2 := by
        rw [h2]
        rw [norm_smul, h_dir1]
        <;> norm_num
      have h4 : ‖m_f - m_c‖ ≤ 3 / 2 := by
        calc ‖m_f - m_c‖ ≤ ‖m_f‖ + ‖m_c‖ := norm_sub_le _ _
          _ = ‖m_f‖ + 1 / 2 := by rw [h3]
          _ ≤ 1 + 1 / 2 := by linarith
          _ = 3 / 2 := by norm_num
      have h5 : ‖(m_f - m_c) - inner ℝ (m_f - m_c) v • v‖ ≤ ‖m_f - m_c‖ :=
        transverse_component_norm_le h_dir1
      have h6 : ‖(m_f - m_c) - inner ℝ (m_f - m_c) v • v‖ ≤ C := by
        calc _ ≤ ‖m_f - m_c‖ := h5
             _ ≤ 3 / 2 := h4
             _ ≤ (2 : ℝ) := by norm_num
             _ ≤ C := hC
      rw [mul_one]
      exact h6
    direction_close_or_reverse := by
      intro i
      have h_tube_eq : unitScaleTubeFamily.tube j0 = unitScaleTube := by
        simp [j0, unitScaleTubeFamily]
      rw [h_tube_eq]
      left
      have h_dir1 : ‖(F.tube i).direction‖ = 1 := (F.tube i).direction_unit
      have h_dir2 : ‖unitScaleTube.direction‖ = 1 := unitScaleTube.direction_unit
      have h3 : ‖(F.tube i).direction - unitScaleTube.direction‖ ≤ 2 := by
        calc ‖(F.tube i).direction - unitScaleTube.direction‖
          ≤ ‖(F.tube i).direction‖ + ‖unitScaleTube.direction‖ := norm_sub_le _ _
        _ = 1 + 1 := by rw [h_dir1, h_dir2] <;> norm_num
        _ = 2 := by norm_num
      have h4 : (2 : ℝ) ≤ C * (1 : ℝ) := by
        simpa using hC
      exact h3.trans h4 }

/-- The unit-scale family has exactly one member. -/
lemma unitScaleTubeFamily_unique :
    ∀ (j k : Fin unitScaleTubeFamily.card), j = k := by
  intro j k
  have h1 : unitScaleTubeFamily.card = 1 := by
    simp [unitScaleTubeFamily]
  rw [h1] at *
  exact fin_one_eq j k

end Kakeya.Streamlined
