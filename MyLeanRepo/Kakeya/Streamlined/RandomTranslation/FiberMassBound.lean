import MyLeanRepo.Kakeya.Streamlined.Estimates
import MyLeanRepo.Kakeya.Streamlined.GeometricLemmas.MidpointBound
import MyLeanRepo.Kakeya.Streamlined.GeometricLemmas.TubeVolume
import MyLeanRepo.Kakeya.Streamlined.RandomTranslation.FrostmanFromDeltaMax
import MyLeanRepo.Kakeya.Streamlined.RandomTranslation.DeterministicHelpers
import MyLeanRepo.Kakeya.Streamlined.IndependentDilatedCoverFullFiberMass

/-!
# Fiber mass lower bound from uniformity and Katz-Tao

Given a uniform tube structure on a family in the unit ball, the Katz-Tao
bound on each coarse family controls its total mass, which combined with
uniformity gives a lower bound on every fiber mass.

## Main result

`fiberMass_lower_bound`: for every admissible scale ρ,
`fiberMass j ≥ F.nominalMass * V_ρ / (C_KT * volume(B_5) * U.assignedUniformity)`.
-/

noncomputable section

open MeasureTheory Kakeya.Streamlined Kakeya.Streamlined.RandomTranslation Metric

namespace Kakeya.Streamlined

/-- Any point in a tube is within distance `ρ + 1/2` of the midpoint. -/
lemma tube_point_dist_to_midpoint {ρ : ℝ} (hρ : 0 ≤ ρ)
    (T : Kakeya.DeltaTube ρ) (y : Point3) (hy : y ∈ T.carrier) :
    dist y (GeometricLemmas.tubeMidpoint T) ≤ ρ + 1 / 2 := by
  let S := Kakeya.unitSegment T.base T.direction
  have hS_compact : IsCompact S := by
    apply IsCompact.image isCompact_Icc
    exact continuous_const.add (continuous_id.smul continuous_const)
  have hS_nonempty : S.Nonempty := ⟨T.base, 0, by norm_num, by simp⟩
  have h_inf : infEDist y S ≤ ENNReal.ofReal ρ := by
    have h : y ∈ cthickening ρ S := hy
    rw [Metric.mem_cthickening_iff] at h
    exact h
  rcases hS_compact.exists_infEDist_eq_edist hS_nonempty y with ⟨z, hz, h_inf_eq⟩
  have hxy : dist y z ≤ ρ := by
    have h_edist : edist y z ≤ ENNReal.ofReal ρ := by
      rw [← h_inf_eq]; exact h_inf
    rw [edist_dist] at h_edist
    exact (ENNReal.ofReal_le_ofReal_iff hρ).mp h_edist
  rcases hz with ⟨t, ht, rfl⟩
  let m := GeometricLemmas.tubeMidpoint T
  have h_zm : dist (T.base + t • T.direction) m ≤ 1 / 2 := by
    rw [dist_eq_norm]
    have h : (T.base + t • T.direction) - m = (t - 1 / 2 : ℝ) • T.direction := by
      simp [m, GeometricLemmas.tubeMidpoint] <;> ext i <;> simp <;> ring
    rw [h, norm_smul, T.direction_unit]
    have h2 : |t - 1 / 2| ≤ 1 / 2 := by
      rw [abs_le] <;> constructor <;> linarith [ht.1, ht.2]
    simpa [Real.norm_eq_abs] using h2
  calc dist y m
    ≤ dist y (T.base + t • T.direction) + dist (T.base + t • T.direction) m := dist_triangle _ _ _
  _ ≤ ρ + 1 / 2 := by linarith

/-- If midpoint norm ≤ 3 and ρ ≤ 1, then tube ⊆ closedBall(0, 5). -/
lemma tube_subset_ball5 {ρ : ℝ} (hρ : 0 ≤ ρ) (hρ1 : ρ ≤ 1)
    (T : Kakeya.DeltaTube ρ) (hmid : ‖GeometricLemmas.tubeMidpoint T‖ ≤ 3) :
    T.carrier ⊆ closedBall (0 : Point3) 5 := by
  intro y hy
  have h1 : dist y (GeometricLemmas.tubeMidpoint T) ≤ ρ + 1 / 2 :=
    tube_point_dist_to_midpoint hρ T y hy
  have h2 : ‖y‖ ≤ ‖GeometricLemmas.tubeMidpoint T‖ + dist y (GeometricLemmas.tubeMidpoint T) := by
    calc ‖y‖
      = ‖GeometricLemmas.tubeMidpoint T + (y - GeometricLemmas.tubeMidpoint T)‖ := by abel
    _ ≤ ‖GeometricLemmas.tubeMidpoint T‖ + ‖y - GeometricLemmas.tubeMidpoint T‖ := norm_add_le _ _
    _ = ‖GeometricLemmas.tubeMidpoint T‖ + dist y (GeometricLemmas.tubeMidpoint T) := by
      rw [← dist_eq_norm, dist_comm]
  have h5 : ‖y‖ ≤ 5 := by
    calc ‖y‖ ≤ ‖GeometricLemmas.tubeMidpoint T‖ + dist y (GeometricLemmas.tubeMidpoint T) := h2
         _ ≤ 3 + (ρ + 1 / 2) := by gcongr
         _ ≤ 5 := by linarith
  simpa [mem_closedBall] using h5

/-- Sum of fiber counts equals the fine cardinality. -/
private lemma sum_fiberCounts {δ ρ : ℝ} {F : TubeFamily δ} {G : TubeFamily ρ}
    (P : TubeCover F G) :
    ∑ k : Fin G.card, P.toFactoring.fiberCount k = F.enncard :=
  P.toFactoring.sum_fiberCount

/--
Cross-multiplied mass lower bound for every complete geometric containment
fiber of a public strict uniform structure.

The parent map is used only to partition all fine indices.  Each assigned
fiber is contained in the corresponding complete containment fiber, and the
public full-fiber uniformity compares those complete fibers.
-/
theorem fullFiberMass_lower_bound
    {δ : ℝ} {F : TubeFamily δ} (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hF_ball : F.IsInUnitBall)
    (U : UniformTubeStructure F)
    {C_KT : ENNReal} (hKT : U.IsKatzTaoAtEveryScale C_KT)
    (rho : AdmissibleScale δ) :
    ∀ j : Fin (U.coarse rho).card,
      F.nominalMass * Kakeya.deltaTubeVolume rho.val ≤
        C_KT * volume (closedBall (0 : Point3) 5) *
          U.uniformity *
          (F.containedCount (U.coarse rho) j *
            Kakeya.deltaTubeVolume δ) := by
  let G := U.coarse rho
  let cover := U.cover rho
  let Vδ := Kakeya.deltaTubeVolume δ
  let Vρ := Kakeya.deltaTubeVolume rho.val
  let B5 := closedBall (0 : Point3) 5
  have hrho_nonneg : 0 ≤ rho.val := by
    linarith [hδ, rho.2.1]
  have hrho_le_one : rho.val ≤ 1 := rho.2.2
  have hB5_top : volume B5 ≠ ⊤ :=
    isBounded_closedBall.measure_lt_top.ne
  have h_all_in :
      ∀ parent : Fin G.card,
        (G.tube parent).carrier ⊆ B5 := by
    intro parent
    have hmid :
        ‖GeometricLemmas.tubeMidpoint (G.tube parent)‖ ≤ 3 :=
      GeometricLemmas.coarse_tube_midpoint_bound
        cover hF_ball hrho_nonneg hrho_le_one parent
    exact tube_subset_ball5
      hrho_nonneg hrho_le_one (G.tube parent) hmid
  have hcoarseMass :
      G.toBodyFamily.mass ≤ C_KT * volume B5 := by
    have hcontained :
        G.toBodyFamily.containedMass B5 =
          G.toBodyFamily.mass :=
      BodyFamily.containedMass_eq_mass_of_all_contained
        G.toBodyFamily B5 (fun parent => h_all_in parent)
    have hdensity :
        G.toBodyFamily.density B5 ≤ C_KT :=
      BodyFamily.density_le_of_deltaMax_le
        (hKT rho) (convex_closedBall _ _)
    rw [BodyFamily.density, hcontained] at hdensity
    have hB5_pos : 0 < volume B5 := by
      have hsubset :
          ball (0 : Point3) 5 ⊆ B5 :=
        ball_subset_closedBall
      have hopen :
          0 < volume (ball (0 : Point3) 5) :=
        Metric.measure_ball_pos volume (0 : Point3) (by norm_num)
      exact hopen.trans_le (measure_mono hsubset)
    exact
      (ENNReal.div_le_iff hB5_pos.ne' hB5_top).mp hdensity
  have hcoarseMassEq :
      G.toBodyFamily.mass = G.enncard * Vρ := by
    rw [TubeFamily.bodyMass_eq_nominalMass]
    rfl
  have hcoarseCard :
      G.enncard * Vρ ≤ C_KT * volume B5 := by
    rwa [← hcoarseMassEq]
  have hassignedContained :
      ∀ parent,
        cover.toFactoring.fiberCount parent ≤
          F.containedCount G parent := by
    intro parent
    exact cover.factoringFiberCount_le_containedCount parent
  have hsum :
      F.enncard ≤
        ∑ parent : Fin G.card,
          F.containedCount G parent := by
    calc
      F.enncard =
          ∑ parent : Fin G.card,
            cover.toFactoring.fiberCount parent :=
        (sum_fiberCounts cover).symm
      _ ≤
          ∑ parent : Fin G.card,
            F.containedCount G parent :=
        Finset.sum_le_sum fun parent _ =>
          hassignedContained parent
  intro target
  have hassignedCount :
      F.enncard ≤
        G.enncard * U.uniformity *
          cover.toFactoring.fiberCount target := by
    calc
      F.enncard =
          ∑ parent : Fin G.card,
            cover.toFactoring.fiberCount parent :=
        (sum_fiberCounts cover).symm
      _ ≤
          ∑ _parent : Fin G.card,
            U.uniformity * cover.toFactoring.fiberCount target := by
        apply Finset.sum_le_sum
        intro parent _
        exact (U.uniform rho).2 parent target
      _ =
          G.enncard * U.uniformity *
            cover.toFactoring.fiberCount target := by
        simp [TubeFamily.enncard, Finset.sum_const,
          nsmul_eq_mul, mul_assoc]
  have hfiberCount :
      F.enncard ≤
        G.enncard * U.uniformity *
          F.containedCount G target := by
    exact hassignedCount.trans (by
      gcongr
      exact hassignedContained target)
  calc
    F.nominalMass * Vρ =
        (F.enncard * Vρ) * Vδ := by
      simp [TubeFamily.nominalMass]
      ring
    _ ≤
        ((G.enncard * U.uniformity *
            F.containedCount G target) * Vρ) * Vδ := by
      gcongr
    _ =
        (G.enncard * Vρ) * U.uniformity *
          (F.containedCount G target * Vδ) := by
      ring
    _ ≤
        (C_KT * volume B5) * U.uniformity *
          (F.containedCount G target * Vδ) := by
      gcongr
    _ =
        C_KT * volume B5 * U.uniformity *
          (F.containedCount G target * Vδ) := by
      ring

/-- Fiber mass lower bound at a single scale. -/
theorem fiberMass_lower_bound
    {δ : ℝ} {F : TubeFamily δ} (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hF_ball : F.IsInUnitBall)
    (U : AssignedUniformTubeStructure F)
    {C_KT : ENNReal} (hKT : U.IsKatzTaoAtEveryScale C_KT)
    (rho : AdmissibleScale δ) :
    ∀ (j : Fin (U.coarse rho).toBodyFamily.card),
      (U.cover rho).toFactoring.fiberMass j ≥
        F.nominalMass * Kakeya.deltaTubeVolume rho.val /
          (C_KT * volume (closedBall (0 : Point3) 5) * U.assignedUniformity) := by
  let G := U.coarse rho
  let cover := U.cover rho
  let Vδ := Kakeya.deltaTubeVolume δ
  let Vρ := Kakeya.deltaTubeVolume rho.val
  let B5 := closedBall (0 : Point3) 5
  have hrho_nonneg : 0 ≤ rho.val := by linarith [hδ, rho.2.1]
  have hrho_le_one : rho.val ≤ 1 := rho.2.2
  have hVδ_pos : 0 < Vδ := deltaTubeVolume_pos hδ
  have hVρ_pos : 0 < Vρ := deltaTubeVolume_pos (by linarith [rho.2.1])
  have hVρ_ne_top : Vρ ≠ ⊤ := deltaTubeVolume_ne_top
  have hB5_pos : 0 < volume B5 := by
    have h_ball : ball (0 : Point3) 5 ⊆ B5 := ball_subset_closedBall
    have h_pos : 0 < volume (ball (0 : Point3) 5) :=
      Metric.measure_ball_pos volume (0 : Point3) (by norm_num)
    exact lt_of_lt_of_le h_pos (measure_mono h_ball)
  have hB5_ne_top : volume B5 ≠ ⊤ := isBounded_closedBall.measure_lt_top.ne
  have h1_uniform : 1 ≤ U.assignedUniformity := (U.assignedUniform rho).1
  have hU_pos : 0 < U.assignedUniformity := zero_lt_one.trans_le h1_uniform
  have hU_ne_top : U.assignedUniformity ≠ ⊤ := U.assignedUniformity_ne_top

  -- Equivalence between Fin G.card and Fin G.toBodyFamily.card
  let eG : Fin G.toBodyFamily.card ≃ Fin G.card :=
    Equiv.cast (by simp [TubeFamily.toBodyFamily])
  let eF : Fin F.toBodyFamily.card ≃ Fin F.card :=
    Equiv.cast (by simp [TubeFamily.toBodyFamily])

  -- All coarse tubes are in B5
  have h_all_in : ∀ (j : Fin G.card), (G.tube j).carrier ⊆ B5 := by
    intro j
    have hmid : ‖GeometricLemmas.tubeMidpoint (G.tube j)‖ ≤ 3 :=
      GeometricLemmas.coarse_tube_midpoint_bound cover hF_ball
        hrho_nonneg hrho_le_one j
    exact tube_subset_ball5 hrho_nonneg hrho_le_one (G.tube j) hmid

  -- Coarse mass ≤ C_KT * volume(B5)
  have h_contained_all : G.toBodyFamily.containedIndices B5 = Finset.univ := by
    ext i
    simp only [BodyFamily.containedIndices, Finset.mem_filter, Finset.mem_univ, true_and]
    have h_eq : (G.toBodyFamily.body i).carrier = (G.tube (eG i)).carrier := by rfl
    simpa [h_eq] using h_all_in (eG i)
  have h_cm : G.toBodyFamily.containedMass B5 = G.toBodyFamily.mass := by
    rw [BodyFamily.containedMass, h_contained_all] <;> rfl
  have h_kt : G.toBodyFamily.deltaMax ≤ C_KT := hKT rho
  have h_density : G.toBodyFamily.density B5 ≤ C_KT :=
    BodyFamily.density_le_of_deltaMax_le h_kt (convex_closedBall _ _)
  have h_G_mass_le : G.toBodyFamily.mass ≤ C_KT * volume B5 := by
    have h : G.toBodyFamily.density B5 = G.toBodyFamily.mass / volume B5 := by
      rw [BodyFamily.density, h_cm] <;> rfl
    rw [h] at h_density
    exact (ENNReal.div_le_iff hB5_pos.ne' hB5_ne_top).mp h_density

  -- G.mass = G.enncard * Vρ
  have h_G_mass_eq : G.toBodyFamily.mass = G.enncard * Vρ := by
    have h1 : G.toBodyFamily.mass = ∑ i : Fin G.toBodyFamily.card, (G.toBodyFamily.body i).volume := by rfl
    rw [h1]
    have h2 : ∀ i, (G.toBodyFamily.body i).volume = Vρ := by
      intro i
      exact tube_volume_eq_deltaTubeVolume (G.tube (eG i))
    rw [Finset.sum_congr rfl (fun i _ => h2 i)]
    have h3 : ∑ i : Fin G.toBodyFamily.card, Vρ = (G.toBodyFamily.card : ENNReal) * Vρ := by
      rw [Finset.sum_const] <;> simp [nsmul_eq_mul]
    rw [h3]
    have h4 : (G.toBodyFamily.card : ENNReal) = G.enncard := by
      simp [TubeFamily.enncard, TubeFamily.toBodyFamily]
    rw [h4]
  have h_N_bound : G.enncard * Vρ ≤ C_KT * volume B5 := by
    rw [←h_G_mass_eq]
    exact h_G_mass_le

  -- If C_KT = ⊤, conclusion is trivial (RHS = 0)
  by_cases hCKT_top : C_KT = ⊤
  · intro j
    have hD_top : (C_KT * volume B5 * U.assignedUniformity) = ⊤ := by
      rw [hCKT_top]
      have h1 : (⊤ : ENNReal) * volume B5 = ⊤ := by
        exact ENNReal.top_mul hB5_pos.ne'
      rw [h1]
      exact ENNReal.top_mul hU_pos.ne'
    rw [hD_top] <;> simp
  have hCKT_ne_top : C_KT ≠ ⊤ := hCKT_top

  -- Handle empty G case
  by_cases hG0 : G.card = 0
  · intro j
    have h_lt : (eG j).val < G.card := (eG j).isLt
    have h_contra : (eG j).val < 0 := by simpa [hG0] using h_lt
    exact False.elim (Nat.not_lt_zero (eG j).val h_contra)
  have hG_pos : 0 < G.enncard := by
    have h : 0 < G.card := Nat.pos_of_ne_zero hG0
    simp [TubeFamily.enncard, h] <;> positivity

  -- C_KT > 0
  have hCKT_pos : 0 < C_KT := by
    by_contra h
    have h0 : C_KT = 0 := by simpa using h
    rw [h0] at h_N_bound
    have h' : G.enncard * Vρ ≤ 0 := by simpa using h_N_bound
    have h'' : G.enncard * Vρ = 0 := by simpa using h'
    have : G.enncard = 0 := (mul_eq_zero.mp h'').resolve_right hVρ_pos.ne'
    exact False.elim (lt_irrefl 0 (this ▸ hG_pos))

  have h_denom_pos : 0 < G.enncard * U.assignedUniformity := ENNReal.mul_pos hG_pos.ne' hU_pos.ne'
  have h_denom_ne_top : (G.enncard * U.assignedUniformity) ≠ ⊤ := by
    have h1 : G.enncard ≠ ⊤ := by simp [TubeFamily.enncard]
    exact ENNReal.mul_ne_top h1 hU_ne_top

  -- Total fiber count sum = F.enncard
  have h_sum_counts :
      ∑ k : Fin G.card, cover.toFactoring.fiberCount k = F.enncard :=
    sum_fiberCounts cover

  -- Each fiber count ≥ F.enncard / (G.enncard * U.assignedUniformity)
  have h_fiber_ge : ∀ (k : Fin G.card), cover.toFactoring.fiberCount k ≥
      F.enncard / (G.enncard * U.assignedUniformity) := by
    intro k
    have h_pointwise : ∀ j',
        cover.toFactoring.fiberCount j' ≤
          U.assignedUniformity * cover.toFactoring.fiberCount k := by
      intro j'; exact (U.assignedUniform rho).2 j' k
    have h_sum_le : ∑ j', cover.toFactoring.fiberCount j' ≤
        ∑ j' : Fin G.card,
          U.assignedUniformity * cover.toFactoring.fiberCount k :=
      Finset.sum_le_sum (fun j' _ => h_pointwise j')
    have h_sum_const :
        ∑ j' : Fin G.card,
            U.assignedUniformity * cover.toFactoring.fiberCount k =
          G.enncard *
            (U.assignedUniformity * cover.toFactoring.fiberCount k) := by
      rw [Finset.sum_const]
      <;> simp [TubeFamily.enncard, nsmul_eq_mul] <;> ring
    have h3 : F.enncard ≤
        G.enncard * (U.assignedUniformity *
          cover.toFactoring.fiberCount k) := by
      calc F.enncard
        = ∑ j', cover.toFactoring.fiberCount j' := h_sum_counts.symm
      _ ≤ ∑ j' : Fin G.card,
          U.assignedUniformity * cover.toFactoring.fiberCount k := h_sum_le
      _ = G.enncard *
          (U.assignedUniformity * cover.toFactoring.fiberCount k) :=
        h_sum_const
    have h5 :
        G.enncard *
            (U.assignedUniformity * cover.toFactoring.fiberCount k) =
          (G.enncard * U.assignedUniformity) *
            cover.toFactoring.fiberCount k := by
      ring
    have h4 : F.enncard ≤
        (G.enncard * U.assignedUniformity) *
          cover.toFactoring.fiberCount k := by
      rw [h5] at h3
      exact h3
    exact ENNReal.div_le_of_le_mul' h4

  -- Fiber mass = fiber count * Vδ (for Factoring indices)
  let P := cover.toFactoring
  have h_fiberMass_eq : ∀ (j : Fin G.toBodyFamily.card),
      P.fiberMass j = P.fiberCount j * Vδ := by
    intro j
    have h : P.fiberMass j = ∑ i ∈ P.fiberIndices j, (F.toBodyFamily.body i).volume := by rfl
    rw [h]
    have h2 : ∀ i ∈ P.fiberIndices j, (F.toBodyFamily.body i).volume = Vδ := by
      intro i _
      exact tube_volume_eq_deltaTubeVolume (F.tube (eF i))
    have h_sum1 : ∑ i ∈ P.fiberIndices j, (F.toBodyFamily.body i).volume = ∑ i ∈ P.fiberIndices j, Vδ :=
      Finset.sum_congr rfl h2
    rw [h_sum1]
    have h3 : ∑ i ∈ P.fiberIndices j, Vδ = (P.fiberIndices j).card * Vδ := by
      rw [Finset.sum_const] <;> simp [nsmul_eq_mul]
    rw [h3]
    rfl

  intro j
  -- fiberMass j ≥ F.enncard / (G.enncard * U.assignedUniformity) * Vδ
  have h6 : P.fiberMass j ≥ (F.enncard / (G.enncard * U.assignedUniformity)) * Vδ := by
    rw [h_fiberMass_eq j]
    have h7 : P.fiberCount j ≥
        F.enncard / (G.enncard * U.assignedUniformity) := by
      change cover.toFactoring.fiberCount j ≥
        F.enncard / (G.enncard * U.assignedUniformity)
      exact h_fiber_ge j
    gcongr
  have h_nominal : F.nominalMass = F.enncard * Vδ := by rfl
  have h8 : (F.enncard / (G.enncard * U.assignedUniformity)) * Vδ =
      F.nominalMass / (G.enncard * U.assignedUniformity) := by
    rw [h_nominal]
    have h9 : (F.enncard * Vδ) / (G.enncard * U.assignedUniformity) =
        (F.enncard / (G.enncard * U.assignedUniformity)) * Vδ := by
      rw [ENNReal.div_eq_inv_mul, ENNReal.div_eq_inv_mul]
      <;> rw [mul_assoc]
    exact h9.symm
  rw [h8] at h6

  -- D = C_KT * V(B5) * U.assignedUniformity
  let D := C_KT * volume B5 * U.assignedUniformity
  have hD_ne_zero : D ≠ 0 := by
    exact mul_ne_zero (mul_ne_zero hCKT_pos.ne' hB5_pos.ne') hU_pos.ne'
  have hD_ne_top : D ≠ ⊤ := by
    have h1 : C_KT * volume B5 ≠ ⊤ := ENNReal.mul_ne_top hCKT_ne_top hB5_ne_top
    exact ENNReal.mul_ne_top h1 hU_ne_top
  have h10 : G.enncard * U.assignedUniformity ≤ D / Vρ := by
    have h11 : (G.enncard * U.assignedUniformity) * Vρ ≤ D := by
      have h : G.enncard * Vρ * U.assignedUniformity ≤ (C_KT * volume B5) * U.assignedUniformity := by
        gcongr <;> exact h_N_bound
      have h_comm : G.enncard * Vρ * U.assignedUniformity = (G.enncard * U.assignedUniformity) * Vρ := by ring
      rw [h_comm] at h
      simpa [D] using h
    have h12 : (G.enncard * U.assignedUniformity) * Vρ / Vρ = G.enncard * U.assignedUniformity :=
      ENNReal.mul_div_cancel_right hVρ_pos.ne' hVρ_ne_top
    have h_div : (G.enncard * U.assignedUniformity) * Vρ / Vρ ≤ D / Vρ := by gcongr
    rw [h12] at h_div
    exact h_div
  have h13 : F.nominalMass / (G.enncard * U.assignedUniformity) ≥ F.nominalMass / (D / Vρ) := by
    apply ENNReal.div_le_div
    · exact le_refl _
    · exact h10
  have h14 : F.nominalMass / (D / Vρ) = F.nominalMass * Vρ / D := by
    have h_inv : (D / Vρ)⁻¹ = Vρ / D :=
      ENNReal.inv_div (Or.inl hVρ_ne_top) (Or.inl hVρ_pos.ne')
    calc F.nominalMass / (D / Vρ)
      = (D / Vρ)⁻¹ * F.nominalMass := by rw [ENNReal.div_eq_inv_mul]
    _ = (Vρ / D) * F.nominalMass := by rw [h_inv]
    _ = D⁻¹ * (Vρ * F.nominalMass) := by
      rw [ENNReal.div_eq_inv_mul, mul_assoc]
    _ = D⁻¹ * (F.nominalMass * Vρ) := by rw [mul_comm Vρ F.nominalMass]
    _ = (F.nominalMass * Vρ) / D := by rw [ENNReal.div_eq_inv_mul]
  rw [h14] at h13
  exact le_trans h13 h6

end Kakeya.Streamlined
