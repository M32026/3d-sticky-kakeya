module

public import MyLeanRepo.Compat

@[expose] public section

/-!
# Covering number lower bound for (δ,s,C)-sets

## Main result

`covering_lower_bound`: Any nonempty (δ,s,C)-set P has δ-covering number
at least C^{-1} · δ^{-s}.

## Proof route

Apply the regularity condition at scale r=δ to a δ-cube containing a point of P.
Since P∩Q is nonempty, N_δ(P∩Q) ≥ 1, giving 1 ≤ C·N_δ(P)·δ^s.

## Whiteprint node

`covering_lower_bound`
-/

namespace ProductLikeIncidence

noncomputable section

open scoped ENNReal

/-- Any nonempty (δ,s,C)-set has covering number at least C^{-1}·δ^{-s}. -/
lemma covering_lower_bound {d : ℕ} {δ s C : ℝ}
    {P : Set (EuclideanSpace ℝ (Fin d))}
    (hP : IsDeltaSCSet δ s C P) :
    ENNReal.ofReal (C⁻¹ * δ ^ (-s)) ≤
      ENat.toENNReal (dyadicCoveringNumber δ P) := by
  rcases hP with ⟨hBounded, hNonempty, h1d, hδdyadic, hδpos, hsnonneg, hsdim, hCpos, hreg⟩
  rcases hNonempty with ⟨p, hp⟩
  let k : Fin d → ℤ := fun i => Int.floor (p i / δ)
  let Q : Set (EuclideanSpace ℝ (Fin d)) := dyadicCube δ k
  have hQ_in : Q ∈ dyadicCubes d δ := ⟨k, rfl⟩
  have hpQ : p ∈ Q := by
    intro i
    have h1 : (k i : ℝ) ≤ p i / δ := Int.floor_le (p i / δ)
    have h2 : p i / δ < (k i : ℝ) + 1 := Int.lt_floor_add_one (p i / δ)
    have h3 : δ * (k i : ℝ) ≤ p i := by
      have h31 : δ * (k i : ℝ) ≤ δ * (p i / δ) := by gcongr
      have h32 : δ * (p i / δ) = p i := by field_simp [hδpos.ne']
      rw [h32] at h31; exact h31
    have h4 : p i < δ * ((k i : ℝ) + 1) := by
      have h41 : p i = δ * (p i / δ) := by field_simp [hδpos.ne']
      rw [h41]; gcongr
    exact ⟨h3, h4⟩
  have hQinter : (Q ∩ P).Nonempty := ⟨p, hpQ, hp⟩
  have hQinter' : (Q ∩ (P ∩ Q)).Nonempty := by
    have h_eq : Q ∩ (P ∩ Q) = Q ∩ P := by ext x; simp [and_comm, and_left_comm] <;> tauto
    rw [h_eq]; exact hQinter
  have hδ_le_one : δ ≤ 1 := by
    rcases hδdyadic with ⟨n, rfl⟩
    cases n with
    | zero => norm_num
    | succ n' => simp [zpow_neg, zpow_ofNat] <;> field_simp <;> norm_num
  have hregδ := hreg hδdyadic hQ_in (le_refl δ) hδ_le_one
  have h_nonempty_cubes : (dyadicCubesMeeting δ (P ∩ Q)).Nonempty :=
    ⟨Q, hQ_in, hQinter'⟩
  have h1 : 1 ≤ (dyadicCubesMeeting δ (P ∩ Q)).encard :=
    Set.one_le_encard_iff_nonempty.mpr h_nonempty_cubes
  have h1' : (1 : ENNReal) ≤ ENat.toENNReal (dyadicCoveringNumber δ (P ∩ Q)) := by
    exact_mod_cast h1
  have hδs_pos : 0 < δ ^ s := Real.rpow_pos_of_pos hδpos s
  have hCδs_pos : 0 < C * δ ^ s := mul_pos hCpos hδs_pos
  set N_encard : ℕ∞ := dyadicCoveringNumber δ P with hN_def
  by_cases hN : N_encard = ⊤
  · rw [hN]; simp
  · have h_exists : ∃ (n : ℕ), N_encard = ↑n := by exact Option.ne_none_iff_exists'.mp hN
    rcases h_exists with ⟨n, hn⟩
    have hn2 : N_encard = (n : ℕ∞) := hn
    rw [hn2] at hregδ
    simp only [ENat.toENNReal_coe] at hregδ
    have h2 : (1 : ENNReal) ≤
        ENNReal.ofReal C * (↑n : ENNReal) * ENNReal.ofReal (δ ^ s) :=
      le_trans h1' hregδ
    have h_n_coe : (↑n : ENNReal) = ENNReal.ofReal (n : ℝ) := by simp
    have h3 : ENNReal.ofReal C * (↑n : ENNReal) * ENNReal.ofReal (δ ^ s) =
        ENNReal.ofReal (C * (n : ℝ) * δ ^ s) := by
      rw [h_n_coe]
      have h_pos1 : 0 ≤ C := by linarith
      have h_pos2 : 0 ≤ (n : ℝ) := by positivity
      have h_pos3 : 0 ≤ δ ^ s := by positivity
      rw [← ENNReal.ofReal_mul h_pos1, ← ENNReal.ofReal_mul (mul_nonneg h_pos1 h_pos2)] <;> ring
    rw [h3] at h2
    have h_pos4 : 0 ≤ C * (n : ℝ) * δ ^ s := by positivity
    have h2' : ENNReal.ofReal (1 : ℝ) ≤ ENNReal.ofReal (C * (n : ℝ) * δ ^ s) := by simpa using h2
    have h_iff1 : ENNReal.ofReal (1 : ℝ) ≤ ENNReal.ofReal (C * (n : ℝ) * δ ^ s) ↔
        (1 : ℝ) ≤ C * (n : ℝ) * δ ^ s :=
      ENNReal.ofReal_le_ofReal_iff (h := h_pos4)
    have h4 : (1 : ℝ) ≤ C * (n : ℝ) * δ ^ s := h_iff1.mp h2'
    have h7 : 0 < C * δ ^ s := hCδs_pos
    have h8 : (1 : ℝ) ≤ (C * δ ^ s) * (n : ℝ) := by
      have h_eq : C * (n : ℝ) * δ ^ s = (C * δ ^ s) * (n : ℝ) := by ring
      rw [h_eq] at h4; exact h4
    have h9 : 1 / (C * δ ^ s) ≤ (n : ℝ) := by
      calc 1 / (C * δ ^ s)
          ≤ ((C * δ ^ s) * (n : ℝ)) / (C * δ ^ s) := by gcongr
        _ = (n : ℝ) := by field_simp [h7.ne'] <;> ring
    have h6 : δ ^ (-s) = 1 / δ ^ s := by
      rw [Real.rpow_neg (by linarith)] <;> field_simp
    have h5 : C⁻¹ * δ ^ (-s) ≤ (n : ℝ) := by
      rw [h6]
      have h10 : C⁻¹ * (1 / δ ^ s) = 1 / (C * δ ^ s) := by
        field_simp [hCpos.ne', hδs_pos.ne'] <;> ring
      rw [h10]; exact h9
    have h11 : 0 ≤ C⁻¹ * δ ^ (-s) := by positivity
    have h_iff2 : ENNReal.ofReal (C⁻¹ * δ ^ (-s)) ≤ ENNReal.ofReal ((n : ℝ)) ↔
        C⁻¹ * δ ^ (-s) ≤ (n : ℝ) :=
      ENNReal.ofReal_le_ofReal_iff (h := by positivity)
    have h12 : ENNReal.ofReal (C⁻¹ * δ ^ (-s)) ≤ ENNReal.ofReal ((n : ℝ)) :=
      h_iff2.mpr h5
    have h16 : ENNReal.ofReal ((n : ℝ)) = (↑n : ENNReal) := by simp
    rw [h16] at h12
    rw [hn2]
    simpa using h12

end

end ProductLikeIncidence
