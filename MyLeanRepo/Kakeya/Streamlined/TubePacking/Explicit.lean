import MyLeanRepo.Kakeya.Streamlined.TubePacking.Proof

/-!
# Explicit tube packing constant

Exposes the explicit constant `C = 3000 * 202^4 * A^7` from the
`tube_packing_in_plank` theorem, which is otherwise hidden behind an
existential. This is needed for polynomial uniformity bounds in the
all-scale construction.
-/

noncomputable section

attribute [local instance] Classical.propDecidable

namespace Kakeya.Streamlined

open Classical Kakeya.Streamlined.GeometricLemmas MeasureTheory Metric Set Finset

theorem tube_packing_in_plank_explicit (A : ℝ) (hA : 1 ≤ A) :
    ∀ (delta a b : ℝ), 0 < delta → delta ≤ a → a ≤ b → b ≤ 1 →
    ∀ (plank : Body) (frame : Point3 ≃ᵃⁱ[ℝ] Point3),
      plank.HasDimensionsInFrame frame a b 1 A →
      ∀ (F : TubeFamily delta),
        F.IsEssentiallyDistinct →
        (∀ i, (F.tube i).carrier ⊆ plank.carrier) →
        F.enncard ≤ ENNReal.ofReal (3000 * (202 : ℝ)^4 * A^7 * (a * b / delta ^ 2) ^ 2) := by
  intro delta a b hdelta hdeltaa hab hb1 plank frame hdim F hdistinct hcontain
  let C : ℝ := 3000 * (202 : ℝ)^4 * A^7
  have hC_pos : 0 < C := by positivity
  let δ : ℝ := delta
  have hδ_def : δ = delta := by rfl
  have hδ : 0 < δ := hdelta
  have hδ1 : δ ≤ 1 := by linarith
  have ha : 0 < a := by linarith
  have hb : 0 < b := by linarith
  have hA_nonneg : 0 ≤ A := by linarith

  let F' : Kakeya.TubeFamily δ := tubeFamilyToFinset F
  have hdistinct' : F'.IsEssentiallyDistinct := by
    exact tubeFamilyToFinset_distinct F hdistinct
  have hcontain' : ∀ T ∈ F', T.carrier ⊆ plank.carrier := by
    intro T hT
    rcases Finset.mem_image.mp hT with ⟨i, _, rfl⟩
    exact hcontain i
  have hcard : F'.enncard = F.enncard := by
    have h_eq : F'.card = F.card := tubeFamilyToFinset_card F hdistinct hδ
    have h1 : F'.enncard = (F'.card : ENNReal) := by rfl
    have h2 : F.enncard = (F.card : ENNReal) := by rfl
    rw [h1, h2]
    exact congr_arg (fun n : ℕ => (n : ENNReal)) h_eq

  let pOrig (T : DeltaTube δ) : Point3 := frame.symm T.base
  let uOrig (T : DeltaTube δ) : Point3 :=
    frame.symm.linearIsometryEquiv T.direction

  have h_bounds : ∀ T ∈ F',
      |pOrig T 0| ≤ A * a / 2 ∧
      |pOrig T 1| ≤ A * b / 2 ∧
      |pOrig T 2| ≤ A / 2 ∧
      |uOrig T 0| ≤ A * a ∧
      |uOrig T 1| ≤ A * b ∧
      |uOrig T 2| ≤ A := by
    intro T hT
    have h := tube_in_frame_direction_bound T plank frame a b 1 A hdim (hcontain' T hT)
    simpa [pOrig, uOrig] using h

  have h_norm : ∀ T ∈ F', ‖uOrig T‖ = 1 := by
    intro T _
    have h1 : ‖uOrig T‖ = ‖T.direction‖ :=
      frame.symm.linearIsometryEquiv.norm_map T.direction
    rw [h1, T.direction_unit]

  let h_cl := capsule_lower_bound_instantiation
  let h_cu := capsule_upper_bound_instantiation

  let refl2 : Point3 ≃ₗᵢ[ℝ] Point3 := reflectCoord 2
  let perm02n : Point3 ≃ₗᵢ[ℝ] Point3 := perm02.trans refl2
  let perm12n : Point3 ≃ₗᵢ[ℝ] Point3 := perm12.trans refl2
  let idPerm : Point3 ≃ₗᵢ[ℝ] Point3 := LinearIsometryEquiv.refl ℝ Point3

  let G0pos : Kakeya.TubeFamily δ :=
    F'.filter (fun T => dominantAxis (uOrig T) = 0 ∧ uOrig T 0 ≥ 0)
  let G0neg : Kakeya.TubeFamily δ :=
    F'.filter (fun T => dominantAxis (uOrig T) = 0 ∧ uOrig T 0 < 0)
  let G1pos : Kakeya.TubeFamily δ :=
    F'.filter (fun T => dominantAxis (uOrig T) = 1 ∧ uOrig T 1 ≥ 0)
  let G1neg : Kakeya.TubeFamily δ :=
    F'.filter (fun T => dominantAxis (uOrig T) = 1 ∧ uOrig T 1 < 0)
  let G2pos : Kakeya.TubeFamily δ :=
    F'.filter (fun T => dominantAxis (uOrig T) = 2 ∧ uOrig T 2 ≥ 0)
  let G2neg : Kakeya.TubeFamily δ :=
    F'.filter (fun T => dominantAxis (uOrig T) = 2 ∧ uOrig T 2 < 0)

  have h_partition : F' = G0pos ∪ G0neg ∪ G1pos ∪ G1neg ∪ G2pos ∪ G2neg := by
    ext T
    constructor
    · intro hT
      set d := dominantAxis (uOrig T) with hd
      have h_all : ∀ (x : Fin 3), x = 0 ∨ x = 1 ∨ x = 2 := by
        intro x; fin_cases x <;> tauto
      have h0 : d = 0 ∨ d = 1 ∨ d = 2 := h_all d
      rcases h0 with (h0 | h0 | h0)
      · by_cases hsign : uOrig T 0 ≥ 0
        · have hG : T ∈ G0pos := by
            simp only [G0pos, Finset.mem_filter] <;> exact ⟨hT, hd.symm.trans h0, hsign⟩
          simp only [Finset.mem_union] <;> tauto
        · have hG : T ∈ G0neg := by
            simp only [G0neg, Finset.mem_filter] <;> exact ⟨hT, hd.symm.trans h0, by linarith⟩
          simp only [Finset.mem_union] <;> tauto
      · by_cases hsign : uOrig T 1 ≥ 0
        · have hG : T ∈ G1pos := by
            simp only [G1pos, Finset.mem_filter] <;> exact ⟨hT, hd.symm.trans h0, hsign⟩
          simp only [Finset.mem_union] <;> tauto
        · have hG : T ∈ G1neg := by
            simp only [G1neg, Finset.mem_filter] <;> exact ⟨hT, hd.symm.trans h0, by linarith⟩
          simp only [Finset.mem_union] <;> tauto
      · by_cases hsign : uOrig T 2 ≥ 0
        · have hG : T ∈ G2pos := by
            simp only [G2pos, Finset.mem_filter] <;> exact ⟨hT, hd.symm.trans h0, hsign⟩
          simp only [Finset.mem_union] <;> tauto
        · have hG : T ∈ G2neg := by
            simp only [G2neg, Finset.mem_filter] <;> exact ⟨hT, hd.symm.trans h0, by linarith⟩
          simp only [Finset.mem_union] <;> tauto
    · intro h
      simp only [G0pos, G0neg, G1pos, G1neg, G2pos, G2neg, Finset.mem_union, Finset.mem_filter] at h
      tauto

  have h_sum : F'.enncard =
      G0pos.enncard + G0neg.enncard + G1pos.enncard + G1neg.enncard +
      G2pos.enncard + G2neg.enncard := by
    have h1 : F' = G0pos ∪ G0neg ∪ G1pos ∪ G1neg ∪ G2pos ∪ G2neg := h_partition
    rw [h1]
    have h_disj_helper : ∀ (G H : Kakeya.TubeFamily δ),
        (∀ T, T ∈ G → T ∈ H → False) → Disjoint G H := by
      intro G H h
      rw [Finset.disjoint_left]
      exact h
    have h_d01 : Disjoint G0pos G0neg := by
      apply h_disj_helper
      intro T hT1 hT2
      have h1 : uOrig T 0 ≥ 0 := (Finset.mem_filter.mp hT1).2.2
      have h2 : uOrig T 0 < 0 := (Finset.mem_filter.mp hT2).2.2
      linarith
    have h_d02 : Disjoint G0pos G1pos := by
      apply h_disj_helper
      intro T hT1 hT2
      have h1 : dominantAxis (uOrig T) = 0 := (Finset.mem_filter.mp hT1).2.1
      have h2 : dominantAxis (uOrig T) = 1 := (Finset.mem_filter.mp hT2).2.1
      rw [h1] at h2; contradiction
    have h_d03 : Disjoint G0pos G1neg := by
      apply h_disj_helper
      intro T hT1 hT2
      have h1 : dominantAxis (uOrig T) = 0 := (Finset.mem_filter.mp hT1).2.1
      have h2 : dominantAxis (uOrig T) = 1 := (Finset.mem_filter.mp hT2).2.1
      rw [h1] at h2; contradiction
    have h_d04 : Disjoint G0pos G2pos := by
      apply h_disj_helper
      intro T hT1 hT2
      have h1 : dominantAxis (uOrig T) = 0 := (Finset.mem_filter.mp hT1).2.1
      have h2 : dominantAxis (uOrig T) = 2 := (Finset.mem_filter.mp hT2).2.1
      rw [h1] at h2; contradiction
    have h_d05 : Disjoint G0pos G2neg := by
      apply h_disj_helper
      intro T hT1 hT2
      have h1 : dominantAxis (uOrig T) = 0 := (Finset.mem_filter.mp hT1).2.1
      have h2 : dominantAxis (uOrig T) = 2 := (Finset.mem_filter.mp hT2).2.1
      rw [h1] at h2; contradiction
    have h_d12 : Disjoint G0neg G1pos := by
      apply h_disj_helper
      intro T hT1 hT2
      have h1 : dominantAxis (uOrig T) = 0 := (Finset.mem_filter.mp hT1).2.1
      have h2 : dominantAxis (uOrig T) = 1 := (Finset.mem_filter.mp hT2).2.1
      rw [h1] at h2; contradiction
    have h_d13 : Disjoint G0neg G1neg := by
      apply h_disj_helper
      intro T hT1 hT2
      have h1 : dominantAxis (uOrig T) = 0 := (Finset.mem_filter.mp hT1).2.1
      have h2 : dominantAxis (uOrig T) = 1 := (Finset.mem_filter.mp hT2).2.1
      rw [h1] at h2; contradiction
    have h_d14 : Disjoint G0neg G2pos := by
      apply h_disj_helper
      intro T hT1 hT2
      have h1 : dominantAxis (uOrig T) = 0 := (Finset.mem_filter.mp hT1).2.1
      have h2 : dominantAxis (uOrig T) = 2 := (Finset.mem_filter.mp hT2).2.1
      rw [h1] at h2; contradiction
    have h_d15 : Disjoint G0neg G2neg := by
      apply h_disj_helper
      intro T hT1 hT2
      have h1 : dominantAxis (uOrig T) = 0 := (Finset.mem_filter.mp hT1).2.1
      have h2 : dominantAxis (uOrig T) = 2 := (Finset.mem_filter.mp hT2).2.1
      rw [h1] at h2; contradiction
    have h_d23 : Disjoint G1pos G1neg := by
      apply h_disj_helper
      intro T hT1 hT2
      have h1 : uOrig T 1 ≥ 0 := (Finset.mem_filter.mp hT1).2.2
      have h2 : uOrig T 1 < 0 := (Finset.mem_filter.mp hT2).2.2
      linarith
    have h_d24 : Disjoint G1pos G2pos := by
      apply h_disj_helper
      intro T hT1 hT2
      have h1 : dominantAxis (uOrig T) = 1 := (Finset.mem_filter.mp hT1).2.1
      have h2 : dominantAxis (uOrig T) = 2 := (Finset.mem_filter.mp hT2).2.1
      rw [h1] at h2; contradiction
    have h_d25 : Disjoint G1pos G2neg := by
      apply h_disj_helper
      intro T hT1 hT2
      have h1 : dominantAxis (uOrig T) = 1 := (Finset.mem_filter.mp hT1).2.1
      have h2 : dominantAxis (uOrig T) = 2 := (Finset.mem_filter.mp hT2).2.1
      rw [h1] at h2; contradiction
    have h_d34 : Disjoint G1neg G2pos := by
      apply h_disj_helper
      intro T hT1 hT2
      have h1 : dominantAxis (uOrig T) = 1 := (Finset.mem_filter.mp hT1).2.1
      have h2 : dominantAxis (uOrig T) = 2 := (Finset.mem_filter.mp hT2).2.1
      rw [h1] at h2; contradiction
    have h_d35 : Disjoint G1neg G2neg := by
      apply h_disj_helper
      intro T hT1 hT2
      have h1 : dominantAxis (uOrig T) = 1 := (Finset.mem_filter.mp hT1).2.1
      have h2 : dominantAxis (uOrig T) = 2 := (Finset.mem_filter.mp hT2).2.1
      rw [h1] at h2; contradiction
    have h_d45 : Disjoint G2pos G2neg := by
      apply h_disj_helper
      intro T hT1 hT2
      have h1 : uOrig T 2 ≥ 0 := (Finset.mem_filter.mp hT1).2.2
      have h2 : uOrig T 2 < 0 := (Finset.mem_filter.mp hT2).2.2
      linarith
    have h_du01_23 : Disjoint (G0pos ∪ G0neg) G1pos := by
      rw [Finset.disjoint_union_left]; exact ⟨h_d02, h_d12⟩
    have h_du012_34 : Disjoint ((G0pos ∪ G0neg) ∪ G1pos) G1neg := by
      rw [Finset.disjoint_union_left]
      constructor
      · rw [Finset.disjoint_union_left]; exact ⟨h_d03, h_d13⟩
      · exact h_d23
    have h_du0123_45 : Disjoint (((G0pos ∪ G0neg) ∪ G1pos) ∪ G1neg) G2pos := by
      rw [Finset.disjoint_union_left]
      constructor
      · rw [Finset.disjoint_union_left]
        constructor
        · rw [Finset.disjoint_union_left]; exact ⟨h_d04, h_d14⟩
        · exact h_d24
      · exact h_d34
    have h_du01234_5 : Disjoint ((((G0pos ∪ G0neg) ∪ G1pos) ∪ G1neg) ∪ G2pos) G2neg := by
      rw [Finset.disjoint_union_left]
      constructor
      · rw [Finset.disjoint_union_left]
        constructor
        · rw [Finset.disjoint_union_left]
          constructor
          · rw [Finset.disjoint_union_left]; exact ⟨h_d05, h_d15⟩
          · exact h_d25
        · exact h_d35
      · exact h_d45
    have h_card : (G0pos ∪ G0neg ∪ G1pos ∪ G1neg ∪ G2pos ∪ G2neg).card =
        G0pos.card + G0neg.card + G1pos.card + G1neg.card + G2pos.card + G2neg.card := by
      have hc1 : (G0pos ∪ G0neg).card = G0pos.card + G0neg.card :=
        Finset.card_union_of_disjoint h_d01
      have hc2 : ((G0pos ∪ G0neg) ∪ G1pos).card = (G0pos ∪ G0neg).card + G1pos.card :=
        Finset.card_union_of_disjoint h_du01_23
      have hc3 : (((G0pos ∪ G0neg) ∪ G1pos) ∪ G1neg).card =
          ((G0pos ∪ G0neg) ∪ G1pos).card + G1neg.card :=
        Finset.card_union_of_disjoint h_du012_34
      have hc4 : ((((G0pos ∪ G0neg) ∪ G1pos) ∪ G1neg) ∪ G2pos).card =
          (((G0pos ∪ G0neg) ∪ G1pos) ∪ G1neg).card + G2pos.card :=
        Finset.card_union_of_disjoint h_du0123_45
      have hc5 : (((((G0pos ∪ G0neg) ∪ G1pos) ∪ G1neg) ∪ G2pos) ∪ G2neg).card =
          ((((G0pos ∪ G0neg) ∪ G1pos) ∪ G1neg) ∪ G2pos).card + G2neg.card :=
        Finset.card_union_of_disjoint h_du01234_5
      rw [hc5, hc4, hc3, hc2, hc1] <;> ring
    have h_enncard : Kakeya.TubeFamily.enncard (G0pos ∪ G0neg ∪ G1pos ∪ G1neg ∪ G2pos ∪ G2neg) =
        G0pos.enncard + G0neg.enncard + G1pos.enncard + G1neg.enncard + G2pos.enncard + G2neg.enncard := by
      simp only [Kakeya.TubeFamily.enncard, h_card]
      <;> norm_cast <;> ring
    exact h_enncard

  -- Numerical helper: 2 * Nat.ceil A + 2 ≤ 6 * A
  have h_ceil : (2 * Nat.ceil A + 2 : ℝ) ≤ 6 * A := by
    have h1 : (Nat.ceil A : ℝ) ≤ A + 1 := by
      by_contra h
      have h2 : (Nat.ceil A : ℝ) > A + 1 := by linarith
      have h3 : Nat.ceil A ≥ 1 := by
        by_contra h4; have h5 : Nat.ceil A = 0 := by omega
        rw [h5] at h2; norm_num at h2 <;> linarith
      let n : ℕ := Nat.ceil A - 1
      have h4 : A ≤ (n : ℝ) := by
        have h5 : (Nat.ceil A : ℝ) - 1 > A := by linarith
        have h6 : (n : ℝ) = (Nat.ceil A : ℝ) - 1 := by
          simp [n, Nat.cast_sub h3] <;> norm_num
        linarith
      have h7 : Nat.ceil A ≤ n := Nat.ceil_le.mpr h4
      omega
    have h_cast : (2 * Nat.ceil A + 2 : ℝ) = 2 * (Nat.ceil A : ℝ) + 2 := by norm_cast <;> ring
    rw [h_cast]; linarith

  -- Numerical helper: if X ≥ δ then 200 * X / δ + 2 ≤ 202 * X / δ
  have h_term : ∀ (X : ℝ), X ≥ δ → 200 * X / δ + 2 ≤ 202 * X / δ := by
    intro X hX
    have hpos : 0 < δ := hδ
    have h1 : 2 ≤ 2 * X / δ := by
      have h2 : δ ≤ X := hX
      calc 2
        = 2 * δ / δ := by field_simp [hpos.ne'] <;> ring
      _ ≤ 2 * X / δ := by
        apply div_le_div_of_nonneg_right
        · linarith
        · positivity
    calc 200 * X / δ + 2
      ≤ 200 * X / δ + 2 * X / δ := by gcongr
    _ = 202 * X / δ := by field_simp [hpos.ne'] <;> ring

  -- Generic group bound application
  let applyBound (G : Kakeya.TubeFamily δ) (hG_sub : G ⊆ F') (perm : Point3 ≃ₗᵢ[ℝ] Point3)
      (P1 P2 D1 D2 : ℝ)
      (hP1 : 0 ≤ P1) (hP2 : 0 ≤ P2) (hD1 : 0 < D1) (hD2 : 0 < D2)
      (h_p2 : ∀ T ∈ G, |(perm (pOrig T)) 2| ≤ A / 2)
      (h_p0 : ∀ T ∈ G, |(perm (pOrig T)) 0| ≤ P1)
      (h_p1 : ∀ T ∈ G, |(perm (pOrig T)) 1| ≤ P2)
      (h_u0 : ∀ T ∈ G, |(perm (uOrig T)) 0| ≤ D1)
      (h_u1 : ∀ T ∈ G, |(perm (uOrig T)) 1| ≤ D2)
      (h_u2_pos : ∀ T ∈ G, (perm (uOrig T)) 2 ≥ 1 / 2) :
      G.enncard ≤ ENNReal.ofReal ((2 * Nat.ceil A + 2 : ℕ) *
        (200 * (P1 + D1) / δ + 2) * (200 * (P2 + D2) / δ + 2) * 8 *
        (200 * D1 / δ + 2) * (200 * D2 / δ + 2)) := by
    let newFrame_symm : Point3 ≃ᵃⁱ[ℝ] Point3 :=
      frame.symm.trans perm.toAffineIsometryEquiv
    let newFrame : Point3 ≃ᵃⁱ[ℝ] Point3 := newFrame_symm.symm
    let p (T : DeltaTube δ) : Point3 := newFrame.symm T.base
    let u (T : DeltaTube δ) : Point3 := newFrame.symm.linearIsometryEquiv T.direction
    have hpe : ∀ T ∈ G, p T = newFrame.symm T.base := by intro T _; rfl
    have hue : ∀ T ∈ G, u T = newFrame.symm.linearIsometryEquiv T.direction := by
      intro T _; rfl
    have h_newFrame_symm : ∀ (x : Point3), newFrame.symm x = perm (frame.symm x) := by
      intro x; rfl
    have h_newFrame_linear : ∀ (v : Point3), newFrame.symm.linearIsometryEquiv v = perm (frame.symm.linearIsometryEquiv v) := by
      intro v
      have h_eq : newFrame.symm.linearIsometryEquiv = (frame.symm.linearIsometryEquiv).trans perm := by
        simp [newFrame] <;> rfl
      rw [h_eq] <;> rfl
    have hpe' : ∀ T ∈ G, p T = perm (pOrig T) := by
      intro T _
      calc p T = newFrame.symm T.base := by rfl
           _ = perm (frame.symm T.base) := h_newFrame_symm T.base
           _ = perm (pOrig T) := by rfl
    have hue' : ∀ T ∈ G, u T = perm (uOrig T) := by
      intro T _
      calc u T = newFrame.symm.linearIsometryEquiv T.direction := by rfl
           _ = perm (frame.symm.linearIsometryEquiv T.direction) := h_newFrame_linear T.direction
           _ = perm (uOrig T) := by rfl
    have hG_dist : G.IsEssentiallyDistinct := by
      intro T hT U hU hne
      exact hdistinct' (hG_sub hT) (hG_sub hU) hne
    have hG_contain : ∀ T ∈ G, T.carrier ⊆ plank.carrier := by
      intro T hT
      exact hcontain' T (hG_sub hT)
    have h_norm' : ∀ T ∈ G, ‖u T‖ = 1 := by
      intro T hT
      have h_eq : u T = perm (uOrig T) := hue' T hT
      rw [h_eq, perm.norm_map]
      exact h_norm T (hG_sub hT)
    exact general_positive_packing_bound hδ hδ1 hA hG_dist newFrame p u
      hpe hue h_norm'
      (fun T hT => by rw [hue' T hT]; exact h_u2_pos T hT)
      P1 P2 D1 D2 hP1 hP2 hD1 hD2
      (fun T hT => by rw [hpe' T hT]; exact h_p2 T hT)
      (fun T hT => by rw [hpe' T hT]; exact h_p0 T hT)
      (fun T hT => by rw [hpe' T hT]; exact h_p1 T hT)
      (fun T hT => by rw [hue' T hT]; exact h_u0 T hT)
      (fun T hT => by rw [hue' T hT]; exact h_u1 T hT)
      h_cl h_cu

  -- Coordinate action lemmas for permutations
  have h_perm02_0 : ∀ (x : Point3), (perm02 x) 0 = x 2 := by
    intro x; rfl
  have h_perm02_1 : ∀ (x : Point3), (perm02 x) 1 = x 1 := by
    intro x; rfl
  have h_perm02_2 : ∀ (x : Point3), (perm02 x) 2 = x 0 := by
    intro x; rfl
  have h_perm12_0 : ∀ (x : Point3), (perm12 x) 0 = x 0 := by
    intro x; rfl
  have h_perm12_1 : ∀ (x : Point3), (perm12 x) 1 = x 2 := by
    intro x; rfl
  have h_perm12_2 : ∀ (x : Point3), (perm12 x) 2 = x 1 := by
    intro x; rfl
  have h_refl2_0 : ∀ (x : Point3), (refl2 x) 0 = x 0 := by
    intro x
    rw [reflectCoord_apply 2 x 0] <;> simp
  have h_refl2_1 : ∀ (x : Point3), (refl2 x) 1 = x 1 := by
    intro x
    rw [reflectCoord_apply 2 x 1] <;> simp
  have h_refl2_2 : ∀ (x : Point3), (refl2 x) 2 = -x 2 := by
    intro x
    rw [reflectCoord_apply 2 x 2] <;> simp
  have h_perm02n_0 : ∀ (x : Point3), (perm02n x) 0 = x 2 := by
    intro x; simp [perm02n, h_refl2_0, h_perm02_0]
  have h_perm02n_1 : ∀ (x : Point3), (perm02n x) 1 = x 1 := by
    intro x; simp [perm02n, h_refl2_1, h_perm02_1]
  have h_perm02n_2 : ∀ (x : Point3), (perm02n x) 2 = -x 0 := by
    intro x; simp [perm02n, h_refl2_2, h_perm02_2]
  have h_perm12n_0 : ∀ (x : Point3), (perm12n x) 0 = x 0 := by
    intro x; simp [perm12n, h_refl2_0, h_perm12_0]
  have h_perm12n_1 : ∀ (x : Point3), (perm12n x) 1 = x 2 := by
    intro x; simp [perm12n, h_refl2_1, h_perm12_1]
  have h_perm12n_2 : ∀ (x : Point3), (perm12n x) 2 = -x 1 := by
    intro x; simp [perm12n, h_refl2_2, h_perm12_2]

  -- Subset and dominant-axis helpers for each group
  have h_G0pos_sub : G0pos ⊆ F' := Finset.filter_subset _ F'
  have h_G0neg_sub : G0neg ⊆ F' := Finset.filter_subset _ F'
  have h_G1pos_sub : G1pos ⊆ F' := Finset.filter_subset _ F'
  have h_G1neg_sub : G1neg ⊆ F' := Finset.filter_subset _ F'
  have h_G2pos_sub : G2pos ⊆ F' := Finset.filter_subset _ F'
  have h_G2neg_sub : G2neg ⊆ F' := Finset.filter_subset _ F'
  have h_G0pos_dom : ∀ T ∈ G0pos, dominantAxis (uOrig T) = 0 :=
    fun T hT => (Finset.mem_filter.mp hT).2.1
  have h_G0neg_dom : ∀ T ∈ G0neg, dominantAxis (uOrig T) = 0 :=
    fun T hT => (Finset.mem_filter.mp hT).2.1
  have h_G1pos_dom : ∀ T ∈ G1pos, dominantAxis (uOrig T) = 1 :=
    fun T hT => (Finset.mem_filter.mp hT).2.1
  have h_G1neg_dom : ∀ T ∈ G1neg, dominantAxis (uOrig T) = 1 :=
    fun T hT => (Finset.mem_filter.mp hT).2.1

  -- Bound-weakening helpers
  have h_weak_a : A * a / 2 ≤ A / 2 := by
    have ha1 : a ≤ 1 := by linarith
    have hA2 : 0 ≤ A := by linarith
    calc A * a / 2 ≤ A * 1 / 2 := by gcongr
      _ = A / 2 := by ring
  have h_weak_b : A * b / 2 ≤ A / 2 := by
    have hb1' : b ≤ 1 := hb1
    have hA2 : 0 ≤ A := by linarith
    calc A * b / 2 ≤ A * 1 / 2 := by gcongr
      _ = A / 2 := by ring

  -- Bounds for each group

  -- G0pos: perm02, P1=A/2, P2=A*b/2, D1=A, D2=A*b
  have h_G0pos_bound : G0pos.enncard ≤ ENNReal.ofReal ((2 * Nat.ceil A + 2 : ℕ) *
      (200 * (A / 2 + A) / δ + 2) * (200 * (A * b / 2 + A * b) / δ + 2) * 8 *
      (200 * A / δ + 2) * (200 * (A * b) / δ + 2)) := by
    apply applyBound G0pos h_G0pos_sub perm02 (A / 2) (A * b / 2) A (A * b)
      (by linarith) (by positivity) (by linarith) (by positivity)
    · intro T hT
      have h := (Finset.mem_filter.mp hT).2
      have h_b := h_bounds T (Finset.mem_filter.mp hT |>.1)
      have h : |pOrig T 0| ≤ A / 2 := le_trans h_b.1 h_weak_a
      simpa [h_perm02_2] using h
    · intro T hT
      have h_b := h_bounds T (Finset.mem_filter.mp hT |>.1)
      simpa [h_perm02_0] using h_b.2.2.1
    · intro T hT
      have h_b := h_bounds T (Finset.mem_filter.mp hT |>.1)
      simpa [h_perm02_1] using h_b.2.1
    · intro T hT
      have h_b := h_bounds T (Finset.mem_filter.mp hT |>.1)
      simpa [h_perm02_0] using h_b.2.2.2.2.2
    · intro T hT
      have h_b := h_bounds T (Finset.mem_filter.mp hT |>.1)
      simpa [h_perm02_1] using h_b.2.2.2.2.1
    · intro T hT
      have h := (Finset.mem_filter.mp hT).2
      have h_dom : dominantAxis (uOrig T) = 0 := h.1
      have h_sign : uOrig T 0 ≥ 0 := h.2
      have h_abs : |uOrig T 0| ≥ 1 / 2 := by
        have h_spec := dominantAxis_spec (uOrig T) (h_norm T (Finset.mem_filter.mp hT |>.1))
        rw [h_dom] at h_spec; exact h_spec
      have h_pos : uOrig T 0 ≥ 1 / 2 := by
        rw [abs_of_nonneg h_sign] at h_abs; exact h_abs
      simpa [h_perm02_2] using h_pos

  -- G0neg: perm02n, same bounds
  have h_G0neg_bound : G0neg.enncard ≤ ENNReal.ofReal ((2 * Nat.ceil A + 2 : ℕ) *
      (200 * (A / 2 + A) / δ + 2) * (200 * (A * b / 2 + A * b) / δ + 2) * 8 *
      (200 * A / δ + 2) * (200 * (A * b) / δ + 2)) := by
    apply applyBound G0neg h_G0neg_sub perm02n (A / 2) (A * b / 2) A (A * b)
      (by linarith) (by positivity) (by linarith) (by positivity)
    · intro T hT
      have h_b := h_bounds T (Finset.mem_filter.mp hT |>.1)
      have h : |pOrig T 0| ≤ A / 2 := le_trans h_b.1 h_weak_a
      simpa [h_perm02n_2, abs_neg] using h
    · intro T hT
      have h_b := h_bounds T (Finset.mem_filter.mp hT |>.1)
      simpa [h_perm02n_0] using h_b.2.2.1
    · intro T hT
      have h_b := h_bounds T (Finset.mem_filter.mp hT |>.1)
      simpa [h_perm02n_1] using h_b.2.1
    · intro T hT
      have h_b := h_bounds T (Finset.mem_filter.mp hT |>.1)
      simpa [h_perm02n_0] using h_b.2.2.2.2.2
    · intro T hT
      have h_b := h_bounds T (Finset.mem_filter.mp hT |>.1)
      simpa [h_perm02n_1] using h_b.2.2.2.2.1
    · intro T hT
      have h := (Finset.mem_filter.mp hT).2
      have h_dom : dominantAxis (uOrig T) = 0 := h.1
      have h_sign : uOrig T 0 < 0 := h.2
      have h_abs : |uOrig T 0| ≥ 1 / 2 := by
        have h_spec := dominantAxis_spec (uOrig T) (h_norm T (Finset.mem_filter.mp hT |>.1))
        rw [h_dom] at h_spec; exact h_spec
      have h_neg : uOrig T 0 ≤ -1 / 2 := by
        rw [abs_of_neg h_sign] at h_abs; linarith
      simpa [h_perm02n_2] using by linarith

  -- G1pos: perm12, P1=A*a/2, P2=A/2, D1=A*a, D2=A
  have h_G1pos_bound : G1pos.enncard ≤ ENNReal.ofReal ((2 * Nat.ceil A + 2 : ℕ) *
      (200 * (A * a / 2 + A * a) / δ + 2) * (200 * (A / 2 + A) / δ + 2) * 8 *
      (200 * (A * a) / δ + 2) * (200 * A / δ + 2)) := by
    apply applyBound G1pos h_G1pos_sub perm12 (A * a / 2) (A / 2) (A * a) A
      (by positivity) (by linarith) (by positivity) (by linarith)
    · intro T hT
      have h_b := h_bounds T (Finset.mem_filter.mp hT |>.1)
      have h : |pOrig T 1| ≤ A / 2 := le_trans h_b.2.1 h_weak_b
      simpa [h_perm12_2] using h
    · intro T hT
      have h_b := h_bounds T (Finset.mem_filter.mp hT |>.1)
      simpa [h_perm12_0] using h_b.1
    · intro T hT
      have h_b := h_bounds T (Finset.mem_filter.mp hT |>.1)
      simpa [h_perm12_1] using h_b.2.2.1
    · intro T hT
      have h_b := h_bounds T (Finset.mem_filter.mp hT |>.1)
      simpa [h_perm12_0] using h_b.2.2.2.1
    · intro T hT
      have h_b := h_bounds T (Finset.mem_filter.mp hT |>.1)
      simpa [h_perm12_1] using h_b.2.2.2.2.2
    · intro T hT
      have h := (Finset.mem_filter.mp hT).2
      have h_dom : dominantAxis (uOrig T) = 1 := h.1
      have h_sign : uOrig T 1 ≥ 0 := h.2
      have h_abs : |uOrig T 1| ≥ 1 / 2 := by
        have h_spec := dominantAxis_spec (uOrig T) (h_norm T (Finset.mem_filter.mp hT |>.1))
        rw [h_dom] at h_spec; exact h_spec
      have h_pos : uOrig T 1 ≥ 1 / 2 := by
        rw [abs_of_nonneg h_sign] at h_abs; exact h_abs
      simpa [h_perm12_2] using h_pos

  -- G1neg: perm12n
  have h_G1neg_bound : G1neg.enncard ≤ ENNReal.ofReal ((2 * Nat.ceil A + 2 : ℕ) *
      (200 * (A * a / 2 + A * a) / δ + 2) * (200 * (A / 2 + A) / δ + 2) * 8 *
      (200 * (A * a) / δ + 2) * (200 * A / δ + 2)) := by
    apply applyBound G1neg h_G1neg_sub perm12n (A * a / 2) (A / 2) (A * a) A
      (by positivity) (by linarith) (by positivity) (by linarith)
    · intro T hT
      have h_b := h_bounds T (Finset.mem_filter.mp hT |>.1)
      have h : |pOrig T 1| ≤ A / 2 := le_trans h_b.2.1 h_weak_b
      simpa [h_perm12n_2, abs_neg] using h
    · intro T hT
      have h_b := h_bounds T (Finset.mem_filter.mp hT |>.1)
      simpa [h_perm12n_0] using h_b.1
    · intro T hT
      have h_b := h_bounds T (Finset.mem_filter.mp hT |>.1)
      simpa [h_perm12n_1] using h_b.2.2.1
    · intro T hT
      have h_b := h_bounds T (Finset.mem_filter.mp hT |>.1)
      simpa [h_perm12n_0] using h_b.2.2.2.1
    · intro T hT
      have h_b := h_bounds T (Finset.mem_filter.mp hT |>.1)
      simpa [h_perm12n_1] using h_b.2.2.2.2.2
    · intro T hT
      have h := (Finset.mem_filter.mp hT).2
      have h_dom : dominantAxis (uOrig T) = 1 := h.1
      have h_sign : uOrig T 1 < 0 := h.2
      have h_abs : |uOrig T 1| ≥ 1 / 2 := by
        have h_spec := dominantAxis_spec (uOrig T) (h_norm T (Finset.mem_filter.mp hT |>.1))
        rw [h_dom] at h_spec; exact h_spec
      have h_neg : uOrig T 1 ≤ -1 / 2 := by
        rw [abs_of_neg h_sign] at h_abs; linarith
      simpa [h_perm12n_2] using by linarith

  -- G2pos: identity, P1=A*a/2, P2=A*b/2, D1=A*a, D2=A*b
  have h_G2pos_bound : G2pos.enncard ≤ ENNReal.ofReal ((2 * Nat.ceil A + 2 : ℕ) *
      (200 * (A * a / 2 + A * a) / δ + 2) * (200 * (A * b / 2 + A * b) / δ + 2) * 8 *
      (200 * (A * a) / δ + 2) * (200 * (A * b) / δ + 2)) := by
    apply applyBound G2pos h_G2pos_sub idPerm (A * a / 2) (A * b / 2) (A * a) (A * b)
      (by positivity) (by positivity) (by positivity) (by positivity)
    · intro T hT
      have h_b := h_bounds T (Finset.mem_filter.mp hT |>.1)
      exact h_b.2.2.1
    · intro T hT
      have h_b := h_bounds T (Finset.mem_filter.mp hT |>.1)
      exact h_b.1
    · intro T hT
      have h_b := h_bounds T (Finset.mem_filter.mp hT |>.1)
      exact h_b.2.1
    · intro T hT
      have h_b := h_bounds T (Finset.mem_filter.mp hT |>.1)
      exact h_b.2.2.2.1
    · intro T hT
      have h_b := h_bounds T (Finset.mem_filter.mp hT |>.1)
      exact h_b.2.2.2.2.1
    · intro T hT
      have h := (Finset.mem_filter.mp hT).2
      have h_dom : dominantAxis (uOrig T) = 2 := h.1
      have h_sign : uOrig T 2 ≥ 0 := h.2
      have h_abs : |uOrig T 2| ≥ 1 / 2 := by
        have h_spec := dominantAxis_spec (uOrig T) (h_norm T (Finset.mem_filter.mp hT |>.1))
        rw [h_dom] at h_spec; exact h_spec
      have h_pos : uOrig T 2 ≥ 1 / 2 := by
        rw [abs_of_nonneg h_sign] at h_abs; exact h_abs
      exact h_pos

  -- G2neg: refl2
  have h_G2neg_bound : G2neg.enncard ≤ ENNReal.ofReal ((2 * Nat.ceil A + 2 : ℕ) *
      (200 * (A * a / 2 + A * a) / δ + 2) * (200 * (A * b / 2 + A * b) / δ + 2) * 8 *
      (200 * (A * a) / δ + 2) * (200 * (A * b) / δ + 2)) := by
    apply applyBound G2neg h_G2neg_sub refl2 (A * a / 2) (A * b / 2) (A * a) (A * b)
      (by positivity) (by positivity) (by positivity) (by positivity)
    · intro T hT
      have h_b := h_bounds T (Finset.mem_filter.mp hT |>.1)
      simpa [h_refl2_2, abs_neg] using h_b.2.2.1
    · intro T hT
      have h_b := h_bounds T (Finset.mem_filter.mp hT |>.1)
      simpa [h_refl2_0] using h_b.1
    · intro T hT
      have h_b := h_bounds T (Finset.mem_filter.mp hT |>.1)
      simpa [h_refl2_1] using h_b.2.1
    · intro T hT
      have h_b := h_bounds T (Finset.mem_filter.mp hT |>.1)
      simpa [h_refl2_0] using h_b.2.2.2.1
    · intro T hT
      have h_b := h_bounds T (Finset.mem_filter.mp hT |>.1)
      simpa [h_refl2_1] using h_b.2.2.2.2.1
    · intro T hT
      have h := (Finset.mem_filter.mp hT).2
      have h_dom : dominantAxis (uOrig T) = 2 := h.1
      have h_sign : uOrig T 2 < 0 := h.2
      have h_abs : |uOrig T 2| ≥ 1 / 2 := by
        have h_spec := dominantAxis_spec (uOrig T) (h_norm T (Finset.mem_filter.mp hT |>.1))
        rw [h_dom] at h_spec; exact h_spec
      have h_neg : uOrig T 2 ≤ -1 / 2 := by
        rw [abs_of_neg h_sign] at h_abs; linarith
      simpa [h_refl2_2] using by linarith

  -- Absorption: axis 2 groups
  have h_absorb2 : ∀ (G : Kakeya.TubeFamily δ),
      G.enncard ≤ ENNReal.ofReal ((2 * Nat.ceil A + 2 : ℕ) *
        (200 * (A * a / 2 + A * a) / δ + 2) * (200 * (A * b / 2 + A * b) / δ + 2) * 8 *
        (200 * (A * a) / δ + 2) * (200 * (A * b) / δ + 2)) →
      G.enncard ≤ ENNReal.ofReal (C / 6 * (a * b / δ ^ 2) ^ 2) := by
    intro G hG
    have h1 : (A * a / 2 + A * a) = 3 * A * a / 2 := by ring
    have h2 : (A * b / 2 + A * b) = 3 * A * b / 2 := by ring
    have h_aδ : a ≥ δ := hdeltaa
    have h_bδ : b ≥ δ := by linarith [hdeltaa, hab]
    have hX1 : 3 * A * a / 2 ≥ δ := by nlinarith
    have hX2 : 3 * A * b / 2 ≥ δ := by nlinarith
    have hD1 : A * a ≥ δ := by nlinarith
    have hD2 : A * b ≥ δ := by nlinarith
    have h3 : (200 * (3 * A * a / 2) / δ + 2) ≤ 202 * (3 * A * a / 2) / δ :=
      h_term (3 * A * a / 2) hX1
    have h4 : (200 * (3 * A * b / 2) / δ + 2) ≤ 202 * (3 * A * b / 2) / δ :=
      h_term (3 * A * b / 2) hX2
    have h5 : (200 * (A * a) / δ + 2) ≤ 202 * (A * a) / δ := h_term (A * a) hD1
    have h6 : (200 * (A * b) / δ + 2) ≤ 202 * (A * b) / δ := h_term (A * b) hD2
    have h7 : ((2 * Nat.ceil A + 2 : ℕ) : ℝ) ≤ 6 * A := by exact_mod_cast h_ceil
    have h_main : ((2 * Nat.ceil A + 2 : ℕ) : ℝ) *
        (200 * (3 * A * a / 2) / δ + 2) * (200 * (3 * A * b / 2) / δ + 2) * 8 *
        (200 * (A * a) / δ + 2) * (200 * (A * b) / δ + 2) ≤
        C / 6 * (a * b / δ ^ 2) ^ 2 := by
      calc
        ((2 * Nat.ceil A + 2 : ℕ) : ℝ) *
          (200 * (3 * A * a / 2) / δ + 2) * (200 * (3 * A * b / 2) / δ + 2) * 8 *
          (200 * (A * a) / δ + 2) * (200 * (A * b) / δ + 2)
          ≤ (6 * A) * (202 * (3 * A * a / 2) / δ) * (202 * (3 * A * b / 2) / δ) * 8 *
              (202 * (A * a) / δ) * (202 * (A * b) / δ) := by gcongr <;> linarith
        _ = 48 * A * (202 : ℝ)^4 * (3 / 2 : ℝ)^2 * A^4 * a^2 * b^2 / δ^4 := by
          field_simp [hδ.ne'] <;> ring
        _ = 108 * (202 : ℝ)^4 * A^5 * (a * b / δ^2)^2 := by
          field_simp [hδ.ne'] <;> ring
        _ ≤ C / 6 * (a * b / δ^2)^2 := by
          have h_coeff : (108 : ℝ) * (202 : ℝ)^4 * A^5 ≤ C / 6 := by
            simp only [C]
            have h2 : (108 : ℝ) ≤ 500 * A^2 := by
              have h3 : A^2 ≥ 1 := by nlinarith
              nlinarith
            have h4 : (108 : ℝ) * (202 : ℝ)^4 * A^5 ≤ (500 : ℝ) * (202 : ℝ)^4 * A^7 := by
              have hA2 : 1 ≤ A^2 := by nlinarith
              have h5 : A^5 ≤ A^7 := by
                calc A^5 = A^5 * 1 := by ring
                  _ ≤ A^5 * A^2 := by gcongr <;> positivity
                  _ = A^7 := by ring
              have h6 : (108 : ℝ) * (202 : ℝ)^4 ≤ (500 : ℝ) * (202 : ℝ)^4 := by
                gcongr <;> norm_num
              exact mul_le_mul h6 h5 (by positivity) (by positivity)
            have hC6 : C / 6 = (500 : ℝ) * (202 : ℝ)^4 * A^7 := by
              simp [C] <;> ring
            rw [hC6]
            exact h4
          have h_pos : 0 ≤ (a * b / δ^2)^2 := by positivity
          exact mul_le_mul_of_nonneg_right h_coeff h_pos
    rw [h1, h2] at hG
    exact hG.trans (ENNReal.ofReal_le_ofReal h_main)

  -- Absorption: axis 0 groups (need a ≥ 1/(2A) if nonempty)
  have h_absorb0 : ∀ (G : Kakeya.TubeFamily δ) (hG_sub : G ⊆ F')
      (hG_dom : ∀ T ∈ G, dominantAxis (uOrig T) = 0),
      G.enncard ≤ ENNReal.ofReal ((2 * Nat.ceil A + 2 : ℕ) *
        (200 * (A / 2 + A) / δ + 2) * (200 * (A * b / 2 + A * b) / δ + 2) * 8 *
        (200 * A / δ + 2) * (200 * (A * b) / δ + 2)) →
      G.enncard ≤ ENNReal.ofReal (C / 6 * (a * b / δ^2)^2) := by
    intro G hG_sub hG_dom hG
    by_cases h_empty : G = ∅
    · have h_goal : G.enncard = 0 := by
        rw [h_empty]
        have h_eq : (∅ : Kakeya.TubeFamily δ).enncard =
            ↑((∅ : Kakeya.TubeFamily δ).card) := by rfl
        rw [h_eq, Finset.card_empty]
        <;> norm_num
      rw [h_goal]
      <;> positivity
    · have h_nonempty : ∃ T, T ∈ G := Finset.nonempty_iff_ne_empty.mpr h_empty
      rcases h_nonempty with ⟨T, hT⟩
      have h_in_F' : T ∈ F' := hG_sub hT
      have h_dom : dominantAxis (uOrig T) = 0 := hG_dom T hT
      have h_abs : |uOrig T 0| ≥ 1 / 2 := by
        have h_spec := dominantAxis_spec (uOrig T) (h_norm T h_in_F')
        rw [h_dom] at h_spec; exact h_spec
      have h_bound_u0 : |uOrig T 0| ≤ A * a := (h_bounds T h_in_F').2.2.2.1
      have ha_lower : A * a ≥ 1 / 2 := by
        have h : (1 / 2 : ℝ) ≤ |uOrig T 0| := h_abs
        exact le_trans h h_bound_u0
      have h1 : (A / 2 + A) = 3 * A / 2 := by ring
      have h2 : (A * b / 2 + A * b) = 3 * A * b / 2 := by ring
      have h_bδ : b ≥ δ := by linarith [hdeltaa, hab]
      have hC : C = 3000 * (202 : ℝ)^4 * A^7 := by rfl
      have h_main := absorb0_bound A a b δ C hA hδ hδ1 ha hb h_bδ ha_lower hC h_ceil
      rw [h1, h2] at hG
      exact hG.trans (ENNReal.ofReal_le_ofReal h_main)

  -- Absorption: axis 1 groups (need b ≥ 1/(2A) if nonempty)
  have h_absorb1 : ∀ (G : Kakeya.TubeFamily δ) (hG_sub : G ⊆ F')
      (hG_dom : ∀ T ∈ G, dominantAxis (uOrig T) = 1),
      G.enncard ≤ ENNReal.ofReal ((2 * Nat.ceil A + 2 : ℕ) *
        (200 * (A * a / 2 + A * a) / δ + 2) * (200 * (A / 2 + A) / δ + 2) * 8 *
        (200 * (A * a) / δ + 2) * (200 * A / δ + 2)) →
      G.enncard ≤ ENNReal.ofReal (C / 6 * (a * b / δ^2)^2) := by
    intro G hG_sub hG_dom hG
    by_cases h_empty : G = ∅
    · have h_goal : G.enncard = 0 := by
        rw [h_empty]
        have h_eq : (∅ : Kakeya.TubeFamily δ).enncard =
            ↑((∅ : Kakeya.TubeFamily δ).card) := by rfl
        rw [h_eq, Finset.card_empty]
        <;> norm_num
      rw [h_goal]
      <;> positivity
    · have h_nonempty : ∃ T, T ∈ G := Finset.nonempty_iff_ne_empty.mpr h_empty
      rcases h_nonempty with ⟨T, hT⟩
      have h_in_F' : T ∈ F' := hG_sub hT
      have h_dom : dominantAxis (uOrig T) = 1 := hG_dom T hT
      have h_abs : |uOrig T 1| ≥ 1 / 2 := by
        have h_spec := dominantAxis_spec (uOrig T) (h_norm T h_in_F')
        rw [h_dom] at h_spec; exact h_spec
      have h_bound_u1 : |uOrig T 1| ≤ A * b := (h_bounds T h_in_F').2.2.2.2.1
      have hb_lower : A * b ≥ 1 / 2 := by
        have h : (1 / 2 : ℝ) ≤ |uOrig T 1| := h_abs
        exact le_trans h h_bound_u1
      have h1 : (A * a / 2 + A * a) = 3 * A * a / 2 := by ring
      have h2 : (A / 2 + A) = 3 * A / 2 := by ring
      have h_aδ : a ≥ δ := hdeltaa
      have hC : C = 3000 * (202 : ℝ)^4 * A^7 := by rfl
      have h_main := absorb1_bound A a b δ C hA hδ hδ1 ha hb h_aδ hb_lower hC h_ceil
      rw [h1, h2] at hG
      exact hG.trans (ENNReal.ofReal_le_ofReal h_main)

  let Y : ℝ := C / 6 * (a * b / δ^2)^2
  have hY_nonneg : 0 ≤ Y := by positivity

  have h0pos' : G0pos.enncard ≤ ENNReal.ofReal Y := h_absorb0 G0pos h_G0pos_sub h_G0pos_dom h_G0pos_bound
  have h0neg' : G0neg.enncard ≤ ENNReal.ofReal Y := h_absorb0 G0neg h_G0neg_sub h_G0neg_dom h_G0neg_bound
  have h1pos' : G1pos.enncard ≤ ENNReal.ofReal Y := h_absorb1 G1pos h_G1pos_sub h_G1pos_dom h_G1pos_bound
  have h1neg' : G1neg.enncard ≤ ENNReal.ofReal Y := h_absorb1 G1neg h_G1neg_sub h_G1neg_dom h_G1neg_bound
  have h2pos' : G2pos.enncard ≤ ENNReal.ofReal Y := h_absorb2 G2pos h_G2pos_bound
  have h2neg' : G2neg.enncard ≤ ENNReal.ofReal Y := h_absorb2 G2neg h_G2neg_bound

  have h_sum_eq : ENNReal.ofReal Y + ENNReal.ofReal Y + ENNReal.ofReal Y + ENNReal.ofReal Y +
      ENNReal.ofReal Y + ENNReal.ofReal Y = ENNReal.ofReal ((6 : ℝ) * Y) := by
    have h1 : 0 ≤ Y + Y := by positivity
    have h2 : 0 ≤ Y + Y + Y := by positivity
    have h3 : 0 ≤ Y + Y + Y + Y := by positivity
    have h4 : 0 ≤ Y + Y + Y + Y + Y := by positivity
    rw [← ENNReal.ofReal_add hY_nonneg hY_nonneg,
        ← ENNReal.ofReal_add h1 hY_nonneg,
        ← ENNReal.ofReal_add h2 hY_nonneg,
        ← ENNReal.ofReal_add h3 hY_nonneg,
        ← ENNReal.ofReal_add h4 hY_nonneg]
    <;> congr 1 <;> ring

  have h_sum_bound : G0pos.enncard + G0neg.enncard + G1pos.enncard + G1neg.enncard +
      G2pos.enncard + G2neg.enncard ≤ ENNReal.ofReal ((6 : ℝ) * Y) := by
    have hs1 : G0pos.enncard + G0neg.enncard ≤
        ENNReal.ofReal Y + ENNReal.ofReal Y := add_le_add h0pos' h0neg'
    have hs2 : G0pos.enncard + G0neg.enncard + G1pos.enncard ≤
        ENNReal.ofReal Y + ENNReal.ofReal Y + ENNReal.ofReal Y :=
      add_le_add hs1 h1pos'
    have hs3 : G0pos.enncard + G0neg.enncard + G1pos.enncard + G1neg.enncard ≤
        ENNReal.ofReal Y + ENNReal.ofReal Y + ENNReal.ofReal Y + ENNReal.ofReal Y :=
      add_le_add hs2 h1neg'
    have hs4 : G0pos.enncard + G0neg.enncard + G1pos.enncard + G1neg.enncard + G2pos.enncard ≤
        ENNReal.ofReal Y + ENNReal.ofReal Y + ENNReal.ofReal Y + ENNReal.ofReal Y + ENNReal.ofReal Y :=
      add_le_add hs3 h2pos'
    have hs5 : G0pos.enncard + G0neg.enncard + G1pos.enncard + G1neg.enncard +
        G2pos.enncard + G2neg.enncard ≤
        ENNReal.ofReal Y + ENNReal.ofReal Y + ENNReal.ofReal Y + ENNReal.ofReal Y +
        ENNReal.ofReal Y + ENNReal.ofReal Y :=
      add_le_add hs4 h2neg'
    rw [h_sum_eq] at hs5
    exact hs5

  have h7 : (6 : ℝ) * Y = C * (a * b / δ^2)^2 := by
    dsimp only [Y] <;> ring

  have h_total : F'.enncard ≤ ENNReal.ofReal (C * (a * b / δ^2)^2) := by
    rw [h_sum]
    have h8 : G0pos.enncard + G0neg.enncard + G1pos.enncard + G1neg.enncard +
        G2pos.enncard + G2neg.enncard ≤ ENNReal.ofReal ((6 : ℝ) * Y) := h_sum_bound
    rw [h7] at h8
    exact h8

  rw [←hcard]
  exact h_total

end Kakeya.Streamlined
