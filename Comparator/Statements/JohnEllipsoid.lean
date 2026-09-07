import Mathlib.Tactic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

noncomputable section

open MeasureTheory
open scoped Pointwise Real

namespace JohnEllipsoid

section Basic

variable {X : Type*} [PseudoMetricSpace X] [AddCommMonoid X] [Module ℝ X] [MeasurableSpace X]

def ellipsoid (c : X) (A : X ≃ₗ[ℝ] X) : Set (X) :=
  c +ᵥ A '' Metric.closedBall 0 1

def IsConvexBody (K : Set X) : Prop :=
  Convex ℝ K ∧ IsCompact K ∧ (interior K).Nonempty

def IsOuterJohnEllipsoid (K : Set X) (c : X) (A : X ≃ₗ[ℝ] X)
    (μ : Measure X := by volume_tac) : Prop :=
  K ⊆ ellipsoid c A ∧
    ∀ c' A', K ⊆ ellipsoid c' A' →
      μ (ellipsoid c A) ≤ μ (ellipsoid c' A')

end Basic

abbrev E (n : ℕ) := EuclideanSpace ℝ (Fin n)

namespace IsConvexBody

variable {n : ℕ} {K : Set (E n)}

theorem exists_isOuterJohnEllipsoid (hK : IsConvexBody K) :
    ∃ (c : E n) (A : E n ≃ₗ[ℝ] E n), IsOuterJohnEllipsoid K c A := by
  rcases hK with ⟨hconv, hcompact, hinterior⟩

  by_cases hn : n = 0
  · -- n = 0: E 0 is a singleton
    subst hn
    have h_subsingleton : Subsingleton (E 0) := by infer_instance
    have hK_univ : K = Set.univ := by
      rcases hinterior with ⟨x, _⟩
      have h1 : interior K = Set.univ := by
        apply Set.eq_univ_of_forall
        intro y
        have h2 : y = x := Subsingleton.elim y x
        rw [h2] <;> exact ‹x ∈ interior K›
      have h3 : Set.univ ⊆ K := by rw [←h1] <;> exact interior_subset
      exact Set.eq_univ_iff_forall.mpr (fun x => h3 (Set.mem_univ x))
    let A : E 0 ≃ₗ[ℝ] E 0 := LinearEquiv.refl ℝ (E 0)
    have h_ellipsoid : ∀ (c : E 0) (A' : E 0 ≃ₗ[ℝ] E 0), ellipsoid c A' = Set.univ := by
      intro c A'
      have h4 : Metric.closedBall (0 : E 0) 1 = Set.univ := by
        ext x; simp [Subsingleton.elim x (0 : E 0)]
      simp [ellipsoid, h4]
    refine' ⟨0, A, _⟩
    constructor
    · rw [h_ellipsoid 0 A, hK_univ]
    · intro c' A' _
      rw [h_ellipsoid 0 A, h_ellipsoid c' A']

  · -- n > 0
    have hn_pos : 0 < n := Nat.pos_of_ne_zero hn
    have hK_nonempty : K.Nonempty := hinterior.mono interior_subset
    rcases hK_nonempty with ⟨x0, hx0K⟩

    -- Step 1: Outer ball K ⊆ closedBall 0 R, R > 0
    have hK_bdd : Bornology.IsBounded K := hcompact.isBounded
    rcases hK_bdd.subset_closedBall x0 with ⟨r0, hr0⟩
    let R : ℝ := max r0 1 + ‖x0‖
    have hR_pos : 0 < R := by positivity
    have hKR : ∀ (x : E n), x ∈ K → ‖x‖ ≤ R := by
      intro x hx
      have h2 : dist x x0 ≤ r0 := hr0 hx
      have h3 : dist x 0 ≤ dist x x0 + dist x0 0 := dist_triangle x x0 0
      have h4 : dist x0 0 = ‖x0‖ := by simp
      have h5 : dist x 0 ≤ R := by
        calc dist x 0
          ≤ dist x x0 + ‖x0‖ := by rw [h4] at h3; exact h3
          _ ≤ r0 + ‖x0‖ := by linarith
          _ ≤ max r0 1 + ‖x0‖ := by linarith [le_max_left r0 1]
      have h6 : dist x 0 = ‖x‖ := by simp
      rw [h6] at h5
      exact h5

    -- Step 2: Inner ball closedBall z r' ⊆ K, r' > 0
    rcases hinterior with ⟨z, hz_int⟩
    rcases (Metric.isOpen_iff).mp isOpen_interior z hz_int with ⟨r, hr_pos, hball⟩
    let r' : ℝ := r / 2
    have hr'_pos : 0 < r' := by positivity
    have hr'_lt_r : r' < r := by
      dsimp only [r'] <;> linarith
    have hclosedball : Metric.closedBall z r' ⊆ K := by
      intro x hx
      have h' : dist x z ≤ r' := hx
      have h : dist x z < r := h'.trans_lt hr'_lt_r
      exact interior_subset (hball h)

    -- Step 3: Define feasible set F = {(B, y) | ∀ x ∈ K, ‖B x - y‖ ≤ 1}
    let F : Set ((E n →L[ℝ] E n) × E n) :=
      {p | ∀ x ∈ K, ‖p.1 x - p.2‖ ≤ 1}

    -- F is nonempty: B0 = (1/R) • id, y = 0
    let B0 : E n →L[ℝ] E n := (1 / R) • ContinuousLinearMap.id ℝ (E n)
    have hB0_feasible : (B0, (0 : E n)) ∈ F := by
      intro x hx
      have h_norm : ‖x‖ ≤ R := hKR x hx
      have h_smul : B0 x = (1 / R) • x := by rfl
      have h2 : ‖B0 x‖ = (1 / R) * ‖x‖ := by
        rw [h_smul, norm_smul]
        have h_pos_strict : 0 < 1 / R := by positivity
        have h_abs : ‖(1 / R : ℝ)‖ = 1 / R := by
          rw [Real.norm_eq_abs, abs_of_pos h_pos_strict]
        rw [h_abs] <;> ring
      have h_goal : ‖B0 x - (0 : E n)‖ = ‖B0 x‖ := by simp
      rw [h_goal, h2]
      have h3 : (1 / R) * ‖x‖ ≤ 1 := by
        calc (1 / R) * ‖x‖ ≤ (1 / R) * R := by gcongr <;> linarith
          _ = 1 := by field_simp [hR_pos.ne'] <;> ring
      exact h3

    -- F is bounded
    have hB_bound : ∀ (p : (E n →L[ℝ] E n) × E n), p ∈ F → ‖p.1‖ ≤ 1 / r' := by
      intro p hp
      have h1 : ∀ (v : E n), ‖v‖ ≤ 1 → ‖p.1 v‖ ≤ 1 / r' := by
        intro v hv
        have hpos1 : z + r' • v ∈ Metric.closedBall z r' := by
          simp [Metric.mem_closedBall, norm_smul, abs_of_pos hr'_pos]
          <;> exact mul_le_of_le_one_right hr'_pos.le hv
        have hpos2 : z - r' • v ∈ Metric.closedBall z r' := by
          simp [Metric.mem_closedBall, norm_smul, abs_of_pos hr'_pos]
          <;> exact mul_le_of_le_one_right hr'_pos.le hv
        have h3 : z + r' • v ∈ K := hclosedball hpos1
        have h4 : z - r' • v ∈ K := hclosedball hpos2
        have h5 : ‖p.1 (z + r' • v) - p.2‖ ≤ 1 := hp (z + r' • v) h3
        have h6 : ‖p.1 (z - r' • v) - p.2‖ ≤ 1 := hp (z - r' • v) h4
        have h_arg : (z + r' • v) - (z - r' • v) = (2 * r' : ℝ) • v := by
          have h_sum : (z + r' • v) - (z - r' • v) = r' • v + r' • v := by abel
          rw [h_sum]
          have h2 : r' • v + r' • v = (2 * r' : ℝ) • v := by
            have h3 : r' • v + r' • v = (2 : ℝ) • (r' • v) := by simp [two_smul]
            rw [h3, ← smul_smul] <;> ring
          exact h2
        have h7 : p.1 (z + r' • v) - p.1 (z - r' • v) = (2 * r' : ℝ) • p.1 v := by
          calc
            p.1 (z + r' • v) - p.1 (z - r' • v)
              = p.1 ((z + r' • v) - (z - r' • v)) := (p.1.map_sub _ _).symm
            _ = p.1 ((2 * r' : ℝ) • v) := by rw [h_arg]
            _ = (2 * r' : ℝ) • p.1 v := p.1.map_smul (2 * r' : ℝ) v
        have h8 : ‖((2 * r' : ℝ) • p.1 v)‖ ≤ 2 := by
          have h9 : p.1 (z + r' • v) - p.2 - (p.1 (z - r' • v) - p.2) = p.1 (z + r' • v) - p.1 (z - r' • v) := by abel
          have h10 : ‖p.1 (z + r' • v) - p.2 - (p.1 (z - r' • v) - p.2)‖ ≤ 2 := by
            have h11 := norm_sub_le_of_le h5 h6
            have h12 : (1 + 1 : ℝ) = 2 := by norm_num
            rw [h12] at h11
            exact h11
          rw [h9, h7] at h10
          exact h10
        have h11 : ‖((2 * r' : ℝ) • p.1 v)‖ = (2 * r') * ‖p.1 v‖ := by
          rw [norm_smul]
          have h_pos2 : 0 < (2 * r' : ℝ) := by positivity
          have h_abs : ‖(2 * r' : ℝ)‖ = 2 * r' := by
            rw [Real.norm_eq_abs, abs_of_pos h_pos2]
          rw [h_abs] <;> ring
        rw [h11] at h8
        have h12 : (2 * r') * ‖p.1 v‖ ≤ 2 := h8
        have h13 : ‖p.1 v‖ ≤ 1 / r' := by
          calc ‖p.1 v‖
            = ((2 * r') * ‖p.1 v‖) / (2 * r') := by field_simp [hr'_pos.ne'] <;> ring
            _ ≤ 2 / (2 * r') := by gcongr
            _ = 1 / r' := by field_simp [hr'_pos.ne'] <;> ring
        exact h13
      have h_op_norm : ‖p.1‖ ≤ 1 / r' := by
        apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
        intro x
        by_cases hx : x = 0
        · rw [hx] <;> simp <;> positivity
        · let v := (1 / ‖x‖) • x
          have hv1 : ‖v‖ = 1 := by
            simp [v, norm_smul, hx] <;> field_simp [hx] <;> ring
          have h4 : ‖p.1 v‖ ≤ 1 / r' := h1 v (by linarith)
          have h5 : p.1 x = ‖x‖ • p.1 v := by
            have h61 : ‖x‖ • v = x := by
              simp [v, hx] <;> field_simp [hx] <;> abel
            have h62 : p.1 (‖x‖ • v) = ‖x‖ • p.1 v := p.1.map_smul ‖x‖ v
            have h63 : p.1 x = p.1 (‖x‖ • v) := by rw [h61]
            rw [h63, h62]
          rw [h5, norm_smul]
          have h7 : ‖‖x‖‖ = ‖x‖ := by simp
          rw [h7]
          have h8 : ‖x‖ * ‖p.1 v‖ ≤ ‖x‖ * (1 / r') := by gcongr
          linarith
      exact h_op_norm

    have hy_bound : ∀ (p : (E n →L[ℝ] E n) × E n), p ∈ F → ‖p.2‖ ≤ (1 / r') * ‖x0‖ + 1 := by
      intro p hp
      have h9 : ‖p.1 x0 - p.2‖ ≤ 1 := hp x0 hx0K
      have h10 : ‖p.2‖ ≤ ‖p.1 x0‖ + 1 := by
        have h : ‖p.2‖ ≤ ‖p.1 x0 - p.2‖ + ‖p.1 x0‖ := by
          have h2 : ‖p.2‖ ≤ ‖p.1 x0‖ + ‖p.1 x0 - p.2‖ := norm_le_insert (p.1 x0) (p.2)
          linarith
        linarith
      have h11 : ‖p.1 x0‖ ≤ ‖p.1‖ * ‖x0‖ := p.1.le_opNorm x0
      have h12 : ‖p.1‖ ≤ 1 / r' := hB_bound p hp
      have h13 : ‖p.2‖ ≤ (1 / r') * ‖x0‖ + 1 := by
        have hx0_nonneg : 0 ≤ ‖x0‖ := by positivity
        have h14 : ‖p.1 x0‖ + 1 ≤ ‖p.1‖ * ‖x0‖ + 1 := by linarith [h11]
        have h15 : ‖p.1‖ * ‖x0‖ + 1 ≤ (1 / r') * ‖x0‖ + 1 := by
          have h16 : ‖p.1‖ * ‖x0‖ ≤ (1 / r') * ‖x0‖ := mul_le_mul_of_nonneg_right h12 hx0_nonneg
          linarith
        linarith [h10, h14, h15]
      exact h13

    have hF_bdd : Bornology.IsBounded F := by
      have h1set : (Prod.fst '' F) ⊆ Metric.closedBall (0 : E n →L[ℝ] E n) (1 / r') := by
        intro B hB
        rcases hB with ⟨p, hp, rfl⟩
        simpa [Metric.mem_closedBall] using hB_bound p hp
      have hball_compact : IsCompact (Metric.closedBall (0 : E n →L[ℝ] E n) (1 / r')) := by
        exact isCompact_closedBall 0 (1 / r')
      have h1 : Bornology.IsBounded (Prod.fst '' F) :=
        hball_compact.isBounded.subset h1set
      have h2set : (Prod.snd '' F) ⊆ Metric.closedBall (0 : E n) ((1 / r') * ‖x0‖ + 1) := by
        intro y hy
        rcases hy with ⟨p, hp, rfl⟩
        simpa [Metric.mem_closedBall] using hy_bound p hp
      have h2ball_compact :
          IsCompact (Metric.closedBall (0 : E n) ((1 / r') * ‖x0‖ + 1)) := by
        exact isCompact_closedBall 0 (1 / r' * ‖x0‖ + 1)
      have h2 : Bornology.IsBounded (Prod.snd '' F) :=
        h2ball_compact.isBounded.subset h2set
      have h3 : F ⊆ (Prod.fst '' F) ×ˢ (Prod.snd '' F) := by
        intro p hp
        have h4 : p.1 ∈ Prod.fst '' F := ⟨p, hp, rfl⟩
        have h5 : p.2 ∈ Prod.snd '' F := ⟨p, hp, rfl⟩
        exact ⟨h4, h5⟩
      have h4 : Bornology.IsBounded ((Prod.fst '' F) ×ˢ (Prod.snd '' F)) := h1.prod h2
      exact h4.subset h3

    -- F is closed
    have hF_closed : IsClosed F := by
      have h_set_eq : F = ⋂ (x : E n), ⋂ (_ : x ∈ K),
          {p : (E n →L[ℝ] E n) × E n | ‖p.1 x - p.2‖ ≤ 1} := by
        ext p
        simp [F]
        <;> rfl
      rw [h_set_eq]
      apply isClosed_iInter
      intro x
      apply isClosed_iInter
      intro hx
      have h_eval : Continuous (fun (B : E n →L[ℝ] E n) => B x) := by
        exact continuous_eval_const x
      have h_cont : Continuous (fun (p : (E n →L[ℝ] E n) × E n) => p.1 x - p.2) :=
        (h_eval.comp continuous_fst).sub continuous_snd
      exact isClosed_le (continuous_norm.comp h_cont) continuous_const

    have hF_compact : IsCompact F :=
      Metric.isCompact_of_isClosed_isBounded hF_closed hF_bdd

    -- Step 4: Maximize |det B| on F
    let g : ((E n →L[ℝ] E n) × E n) → ℝ := fun p => |p.1.det|
    have hg_cont : Continuous g :=
      Continuous.abs (ContinuousLinearMap.continuous_det.comp continuous_fst)
    have hF_nonempty : F.Nonempty := ⟨(B0, 0), hB0_feasible⟩
    have h_image_compact : IsCompact (g '' F) := hF_compact.image hg_cont
    have h_image_nonempty : (g '' F).Nonempty := hF_nonempty.image g
    rcases h_image_compact.exists_isGreatest h_image_nonempty with ⟨y, hy_in, hy_max⟩
    rcases hy_in with ⟨p_min, hp_min_in_F, rfl⟩
    let Bstar : E n →L[ℝ] E n := p_min.1
    let ystar : E n := p_min.2
    have hBstar_in_F : (Bstar, ystar) ∈ F := hp_min_in_F
    have hg_max' : ∀ p ∈ F, g p ≤ g (Bstar, ystar) := by
      intro p hp
      have hmem : g p ∈ g '' F := Set.mem_image_of_mem g hp
      exact hy_max hmem

    -- Bstar has positive determinant
    have h_det_B0 : B0.det = (1 / R) ^ n := by
      have h1 : (B0 : E n →ₗ[ℝ] E n) = (1 / R) • LinearMap.id := by rfl
      have h2 : B0.det = LinearMap.det (B0 : E n →ₗ[ℝ] E n) := by rfl
      have h_finrank : Module.finrank ℝ (E n) = n := by
        have h : Module.finrank ℝ (E n) = Fintype.card (Fin n) := by
          exact finrank_euclideanSpace
        rw [h, Fintype.card_fin]
      rw [h2, h1, LinearMap.det_smul, LinearMap.det_id, h_finrank]
      <;> ring
    have h_det_B0_pos : 0 < |B0.det| := by
      rw [h_det_B0] <;> positivity
    have h_det_Bstar_pos : 0 < |Bstar.det| := by
      have h : g (B0, (0 : E n)) ≤ g (Bstar, ystar) := hg_max' (B0, 0) hB0_feasible
      exact h_det_B0_pos.trans_le h

    -- Bstar is invertible
    have hBstar_det_ne_zero : Bstar.det ≠ 0 := by
      have h : 0 < |Bstar.det| := h_det_Bstar_pos
      exact abs_pos.mp h
    have h_ker : (Bstar : E n →ₗ[ℝ] E n).ker = ⊥ := by
      have h_iff : (Bstar : E n →ₗ[ℝ] E n).det = 0 ↔ (Bstar : E n →ₗ[ℝ] E n).ker ≠ ⊥ :=
        LinearMap.det_eq_zero_iff_ker_ne_bot
      have h_not : ¬((Bstar : E n →ₗ[ℝ] E n).ker ≠ ⊥) := by
        intro h_contra
        have h_det_zero : (Bstar : E n →ₗ[ℝ] E n).det = 0 := h_iff.mpr h_contra
        exact hBstar_det_ne_zero h_det_zero
      exact Classical.not_not.mp h_not
    let Bstar' : E n ≃ₗ[ℝ] E n :=
      LinearEquiv.ofInjectiveEndo (Bstar : E n →ₗ[ℝ] E n)
        (LinearMap.ker_eq_bot.mp h_ker)
    let Astar : E n ≃ₗ[ℝ] E n := Bstar'.symm
    let cstar : E n := Astar ystar

    -- Step 5: K ⊆ ellipsoid cstar Astar
    have hK_subset : K ⊆ ellipsoid cstar Astar := by
      intro x hx
      have h1 : ‖Bstar x - ystar‖ ≤ 1 := hBstar_in_F x hx
      have h3 : Bstar cstar = ystar := by
        have h_eq : Bstar cstar = Bstar' (Bstar'.symm ystar) := by rfl
        rw [h_eq]
        exact Bstar'.apply_symm_apply ystar
      have h2 : Bstar (x - cstar) = Bstar x - ystar := by
        have h : Bstar (x - cstar) = Bstar x - Bstar cstar := Bstar.map_sub x cstar
        rw [h, h3]
      have h4 : ‖Bstar (x - cstar)‖ ≤ 1 := by rw [h2] <;> exact h1
      let z : E n := Bstar (x - cstar)
      have hz_in : z ∈ Metric.closedBall (0 : E n) 1 := by
        have h4' : ‖z‖ ≤ 1 := by
          dsimp only [z]
          rw [h2] <;> exact h1
        simpa [Metric.mem_closedBall] using h4'
      have h5 : Astar z = x - cstar := by
        change Bstar'.symm z = x - cstar
        have h7 : z = Bstar (x - cstar) := by rfl
        rw [h7]
        exact Bstar'.symm_apply_apply (x - cstar)
      have h6 : cstar +ᵥ Astar z = x := by
        simpa [vadd_eq_add, h5] using by abel
      have h_y_in : Astar z ∈ Astar '' Metric.closedBall (0 : E n) 1 := Set.mem_image_of_mem Astar hz_in
      simpa [ellipsoid, Set.mem_vadd] using ⟨Astar z, h_y_in, h6⟩

    -- Step 6: Minimality
    have h_main : ∀ (c' : E n) (A' : E n ≃ₗ[ℝ] E n),
        K ⊆ ellipsoid c' A' → volume (ellipsoid cstar Astar) ≤ volume (ellipsoid c' A') := by
      intro c' A' h_sub'
      let B' : E n →L[ℝ] E n := A'.toContinuousLinearEquiv.symm
      let y' : E n := B' c'
      have h_feasible : (B', y') ∈ F := by
        intro x hx
        have h5 : x ∈ ellipsoid c' A' := h_sub' hx
        simp only [ellipsoid, Set.mem_vadd] at h5
        rcases h5 with ⟨y, hy, h6⟩
        rcases hy with ⟨w, hw, rfl⟩
        have hwnorm : ‖w‖ ≤ 1 := by simpa [Metric.mem_closedBall] using hw
        have h_xsub : x - c' = A' w := by
          have h_eq : c' +ᵥ A' w = x := h6
          simpa [vadd_eq_add] using (eq_sub_of_add_eq' h_eq).symm
        have h_B'xsub : B' (x - c') = w := by
          rw [h_xsub]
          exact A'.toContinuousLinearEquiv.symm_apply_apply w
        have h_goal : B' x - y' = B' (x - c') := by
          have h_y' : y' = B' c' := by rfl
          rw [h_y']
          exact (B'.map_sub x c').symm
        rw [h_goal, h_B'xsub]
        exact hwnorm
      have h8 : |Bstar.det| ≥ |B'.det| := hg_max' (B', y') h_feasible
      have h_det_A'_unit : IsUnit (LinearMap.det (A' : E n →ₗ[ℝ] E n)) := by
        exact LinearEquiv.isUnit_det' A'
      have h_det_A'_ne_zero : LinearMap.det (A' : E n →ₗ[ℝ] E n) ≠ 0 := h_det_A'_unit.ne_zero
      have h10 : LinearMap.det (Astar : E n →ₗ[ℝ] E n) = (Bstar.det)⁻¹ := by
        have h_symm : LinearMap.det (Astar : E n →ₗ[ℝ] E n) = (LinearMap.det (Bstar' : E n →ₗ[ℝ] E n))⁻¹ :=
          LinearEquiv.det_coe_symm Bstar'
        rw [h_symm] <;> rfl
      have h_B'_det_eq : B'.det = (LinearMap.det (A' : E n →ₗ[ℝ] E n))⁻¹ := by
        have h : B'.det = LinearMap.det (A'.symm : E n →ₗ[ℝ] E n) := by rfl
        rw [h, LinearEquiv.det_coe_symm A']
      have h11 : LinearMap.det (A' : E n →ₗ[ℝ] E n) = (B'.det)⁻¹ := by
        have h : (B'.det)⁻¹ = LinearMap.det (A' : E n →ₗ[ℝ] E n) := by
          rw [h_B'_det_eq]
          field_simp [h_det_A'_ne_zero]
        exact h.symm
      have h_B'_det_ne_zero : B'.det ≠ 0 := by
        rw [h_B'_det_eq]
        exact inv_ne_zero h_det_A'_ne_zero
      have h13 : 0 < |B'.det| := abs_pos.mpr h_B'_det_ne_zero
      have h14 : |(Bstar.det)⁻¹| = (|Bstar.det|)⁻¹ := by rw [abs_inv]
      have h15 : |(B'.det)⁻¹| = (|B'.det|)⁻¹ := by rw [abs_inv]
      have h16 : (|Bstar.det|)⁻¹ ≤ (|B'.det|)⁻¹ := by
        have h17 : |B'.det| ≤ |Bstar.det| := h8
        have h18 : 0 < |B'.det| := h13
        have h19 : 1 / |Bstar.det| ≤ 1 / |B'.det| := one_div_le_one_div_of_le h18 h17
        simpa [one_div] using h19
      have h9 : |LinearMap.det (Astar : E n →ₗ[ℝ] E n)| ≤ |LinearMap.det (A' : E n →ₗ[ℝ] E n)| := by
        rw [h10, h11, h14, h15]
        exact h16
      -- Volume comparison
      have hV_pos : 0 < volume (Metric.closedBall (0 : E n) 1) :=
        Metric.measure_closedBall_pos volume (0 : E n) (by norm_num)
      have hV_ne_top : volume (Metric.closedBall (0 : E n) 1) ≠ ⊤ := by
        have h_compact : IsCompact (Metric.closedBall (0 : E n) 1) :=
          ProperSpace.isCompact_closedBall (0 : E n) 1
        exact h_compact.measure_ne_top
      have h_vol_eq : ∀ (c : E n) (A : E n ≃ₗ[ℝ] E n),
          volume (ellipsoid c A) =
            ENNReal.ofReal |LinearMap.det (A : E n →ₗ[ℝ] E n)| *
              volume (Metric.closedBall (0 : E n) 1) := by
        intro c A
        have h1 : volume (ellipsoid c A) = volume (A '' Metric.closedBall (0 : E n) 1) := by
          simpa [ellipsoid] using measure_preimage_add volume (-c) _
        rw [h1]
        let Acl : E n →L[ℝ] E n := (A : E n →ₗ[ℝ] E n).toContinuousLinearMap
        exact Measure.addHaar_image_continuousLinearMap volume Acl (Metric.closedBall (0 : E n) 1)
      rw [h_vol_eq cstar Astar, h_vol_eq c' A']
      set d1 := ENNReal.ofReal |LinearMap.det (Astar : E n →ₗ[ℝ] E n)| with hd1
      set d2 := ENNReal.ofReal |LinearMap.det (A' : E n →ₗ[ℝ] E n)| with hd2
      have h_final : d1 * volume (Metric.closedBall (0 : E n) 1) ≤ d2 * volume (Metric.closedBall (0 : E n) 1) := by
        rw [ENNReal.mul_le_mul_iff_left hV_pos.ne' hV_ne_top]
        exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).mpr h9
      exact h_final

    exact ⟨cstar, Astar, hK_subset, h_main⟩


def outerJohnEllipsoidCenter (hK : IsConvexBody K) : E n :=
  (exists_isOuterJohnEllipsoid hK).choose

def outerJohnEllipsoidMap (hK : IsConvexBody K) : E n ≃ₗ[ℝ] E n :=
  (exists_isOuterJohnEllipsoid hK).choose_spec.choose

lemma outerJohnEllipsoid_spec (hK : IsConvexBody K) :
    IsOuterJohnEllipsoid K hK.outerJohnEllipsoidCenter
      hK.outerJohnEllipsoidMap :=
  (exists_isOuterJohnEllipsoid hK).choose_spec.choose_spec

abbrev outerJohnEllipsoid (hK : IsConvexBody K) : Set (E n) :=
  ellipsoid hK.outerJohnEllipsoidCenter hK.outerJohnEllipsoidMap

end IsConvexBody

end JohnEllipsoid
