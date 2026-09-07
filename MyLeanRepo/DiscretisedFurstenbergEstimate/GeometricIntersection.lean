module

/-
  Geometric intersection lemma for B1 induction.

  Fixes the counterexample where nearest-neighbor coarse rounding can push
  a tube strip just outside the containing coarse square.

  We consider all coarse tubes within L1 index distance 2 of the nearest
  rounding (parameter distance ≤ 2*δ_m), and prove at least one intersects
  the containing coarse square.

  Whiteprint: induction_on_scales / geometric_intersection
-/

public import MyLeanRepo.DiscretisedFurstenbergEstimate.DyadicTubes
public import MyLeanRepo.DiscretisedFurstenbergEstimate.InductionConfigurations
public import MyLeanRepo.DiscretisedFurstenbergEstimate.InductionSteps
public import MyLeanRepo.DiscretisedFurstenbergEstimate.B1_Sublemmas
public import MyLeanRepo.OSWPrelude

@[expose] public section

open scoped ENNReal NNReal Classical
attribute [local instance] Classical.propDecidable

open DirecretisedFurstenbergEstimate.InductionOnScales
open DiscretisedFurstenbergEstimate
open DiscretisedFurstenbergEstimate.InductionConfigurations

namespace DiscretisedFurstenbergEstimate.InductionOnScales

open DiscretisedFurstenbergEstimate

/-! ### Helper: strip center in target interval implies intersection -/

/-- If a strip center g lies in [c - δ, c + 2*δ), then there exists
    y ∈ [c, c+δ) with |y - g| ≤ δ. -/
lemma strip_center_intersects_interval {g c δ : ℝ} (hδ : 0 < δ)
    (h1 : c - δ ≤ g) (h2 : g < c + 2 * δ) :
    ∃ (y : ℝ), c ≤ y ∧ y < c + δ ∧ |y - g| ≤ δ := by
  by_cases h3 : g < c
  · refine' ⟨c, by linarith, by linarith, _⟩
    have h4 : c - g ≥ 0 := by linarith
    rw [abs_of_nonneg h4] <;> linarith
  · have h3' : g ≥ c := by linarith
    by_cases h4 : g < c + δ
    · have h_abs : |g - g| ≤ δ := by
        have h : |g - g| = 0 := by simp
        rw [h] <;> linarith
      exact ⟨g, by linarith, by linarith, h_abs⟩
    · have h5 : g - δ ≥ c := by linarith
      have h6 : g - δ < c + δ := by linarith
      refine' ⟨g - δ, h5, h6, _⟩
      have h7 : (g - δ) - g = -δ := by ring
      rw [h7, abs_neg, abs_of_pos hδ] <;> linarith

/-! ### squareContained → toSet subset -/

/-- A fine square is contained in its containing coarse square as sets. -/
lemma squareContained_toSet_subset {n m : ℕ} (hnm : m ≤ n)
    {p : DyadicSquare n} {Q : DyadicSquare m}
    (h : squareContained hnm p Q) :
    p.toSet ⊆ Q.toSet := by
  let rf : ℕ := InductionConfigurations.refinementFactor n m
  have hrf_pos : 0 < rf := by
    dsimp only [rf, InductionConfigurations.refinementFactor] <;> positivity
  have hδn_pos : 0 < dyadicDelta n := dyadicDelta_pos n
  have hmul : dyadicDelta n * (rf : ℝ) = dyadicDelta m :=
    dyadicDelta_mul_refinement n m hnm
  intro x hx
  have hxi1 : (p.i : ℝ) * dyadicDelta n ≤ x 0 := hx.1
  have hxi2 : x 0 < ((p.i : ℝ) + 1) * dyadicDelta n := hx.2.1
  have hxj1 : (p.j : ℝ) * dyadicDelta n ≤ x 1 := hx.2.2.1
  have hxj2 : x 1 < ((p.j : ℝ) + 1) * dyadicDelta n := hx.2.2.2
  have h9i : (Q.i : ℝ) * (rf : ℝ) ≤ (p.i : ℝ) := by exact_mod_cast h.1
  have h10i : (p.i : ℝ) + 1 ≤ ((Q.i + 1 : ℤ) : ℝ) * (rf : ℝ) := by
    have h := h.2.1
    exact_mod_cast h
  have h9j : (Q.j : ℝ) * (rf : ℝ) ≤ (p.j : ℝ) := by exact_mod_cast h.2.2.1
  have h10j : (p.j : ℝ) + 1 ≤ ((Q.j + 1 : ℤ) : ℝ) * (rf : ℝ) := by
    have h := h.2.2.2
    exact_mod_cast h
  have hQ1 : (Q.i : ℝ) * dyadicDelta m ≤ x 0 := by
    calc (Q.i : ℝ) * dyadicDelta m
        = (Q.i : ℝ) * (dyadicDelta n * (rf : ℝ)) := by rw [hmul]
      _ = ((Q.i : ℝ) * (rf : ℝ)) * dyadicDelta n := by ring
      _ ≤ (p.i : ℝ) * dyadicDelta n := by
        exact mul_le_mul_of_nonneg_right h9i hδn_pos.le
      _ ≤ x 0 := hxi1
  have hQ2 : x 0 < ((Q.i : ℝ) + 1) * dyadicDelta m := by
    calc x 0
        < ((p.i : ℝ) + 1) * dyadicDelta n := hxi2
      _ ≤ (((Q.i + 1 : ℤ) : ℝ) * (rf : ℝ)) * dyadicDelta n := by
        exact mul_le_mul_of_nonneg_right h10i hδn_pos.le
      _ = ((Q.i : ℝ) + 1) * (dyadicDelta n * (rf : ℝ)) := by
        have h_eq : ((Q.i + 1 : ℤ) : ℝ) = (Q.i : ℝ) + 1 := by simp
        rw [h_eq] <;> ring
      _ = ((Q.i : ℝ) + 1) * dyadicDelta m := by rw [hmul]
  have hQ3 : (Q.j : ℝ) * dyadicDelta m ≤ x 1 := by
    calc (Q.j : ℝ) * dyadicDelta m
        = (Q.j : ℝ) * (dyadicDelta n * (rf : ℝ)) := by rw [hmul]
      _ = ((Q.j : ℝ) * (rf : ℝ)) * dyadicDelta n := by ring
      _ ≤ (p.j : ℝ) * dyadicDelta n := by
        exact mul_le_mul_of_nonneg_right h9j hδn_pos.le
      _ ≤ x 1 := hxj1
  have hQ4 : x 1 < ((Q.j : ℝ) + 1) * dyadicDelta m := by
    calc x 1
        < ((p.j : ℝ) + 1) * dyadicDelta n := hxj2
      _ ≤ (((Q.j + 1 : ℤ) : ℝ) * (rf : ℝ)) * dyadicDelta n := by
        exact mul_le_mul_of_nonneg_right h10j hδn_pos.le
      _ = ((Q.j : ℝ) + 1) * (dyadicDelta n * (rf : ℝ)) := by
        have h_eq : ((Q.j + 1 : ℤ) : ℝ) = (Q.j : ℝ) + 1 := by simp
        rw [h_eq] <;> ring
      _ = ((Q.j : ℝ) + 1) * dyadicDelta m := by rw [hmul]
  exact ⟨hQ1, hQ2, hQ3, hQ4⟩

/-! ### Nearby coarse tubes -/

/-- The nearest coarse rounding of a fine tube, at scale m. -/
def coarseImage {n m : ℕ} (hnm : m ≤ n) (t : DyadicTube n) : DyadicTube m :=
  coarseRoundToM hnm (coarseRound n m hnm t) (coarse_rounding_divisible hnm t)

/-- coarseImage has the same slope and intercept as coarseRound(t). -/
lemma coarseImage_eq {n m : ℕ} (hnm : m ≤ n) (t : DyadicTube n) :
    (coarseImage hnm t).slope = (coarseRound n m hnm t).slope ∧
    (coarseImage hnm t).intercept = (coarseRound n m hnm t).intercept :=
  coarseRoundToM_eq hnm (coarseRound n m hnm t) (coarse_rounding_divisible hnm t)

/-- All coarse tubes within L1 index distance 2 of the nearest rounding. -/
noncomputable def nearbyCoarseTubes {n m : ℕ} (hnm : m ≤ n) (t : DyadicTube n) :
    Finset (DyadicTube m) :=
  let U₀ := coarseImage hnm t
  (Finset.Icc (-2 : ℤ) 2).biUnion (fun da =>
    (Finset.Icc (-2 : ℤ) 2).filter (fun db => |da| + |db| ≤ 2)
      |>.image (fun db => ⟨U₀.a + da, U₀.b + db⟩))

/-- Membership in nearbyCoarseTubes iff L1 index distance ≤ 2. -/
lemma mem_nearbyCoarseTubes_iff {n m : ℕ} (hnm : m ≤ n) (t : DyadicTube n)
    (U : DyadicTube m) :
    U ∈ nearbyCoarseTubes hnm t ↔
      |U.a - (coarseImage hnm t).a| + |U.b - (coarseImage hnm t).b| ≤ 2 := by
  let U₀ := coarseImage hnm t
  constructor
  · intro h
    rcases Finset.mem_biUnion.mp h with ⟨da, _, hmem⟩
    rcases Finset.mem_image.mp hmem with ⟨db, hdb, rfl⟩
    have h : |da| + |db| ≤ 2 := (Finset.mem_filter.mp hdb).2
    simpa [U₀] using h
  · intro h
    let da : ℤ := U.a - U₀.a
    let db : ℤ := U.b - U₀.b
    have h2 : |da| ≤ 2 := by linarith [abs_nonneg db, h]
    have h3 : |db| ≤ 2 := by linarith [abs_nonneg da, h]
    have hda2 : da ∈ Finset.Icc (-2 : ℤ) 2 := by
      simp only [Finset.mem_Icc]; exact ⟨by linarith [abs_le.mp h2], by linarith [abs_le.mp h2]⟩
    have hdb2 : db ∈ Finset.Icc (-2 : ℤ) 2 := by
      simp only [Finset.mem_Icc]; exact ⟨by linarith [abs_le.mp h3], by linarith [abs_le.mp h3]⟩
    have hfilter : db ∈ (Finset.Icc (-2 : ℤ) 2).filter (fun db => |da| + |db| ≤ 2) := by
      simp only [Finset.mem_filter]; exact ⟨hdb2, h⟩
    have hU : U = ⟨U₀.a + da, U₀.b + db⟩ := by
      cases U <;> simp [da, db] <;> omega
    rw [hU]
    exact Finset.mem_biUnion.mpr ⟨da, hda2, Finset.mem_image.mpr ⟨db, hfilter, rfl⟩⟩

/-- Parameter distance bound for nearby tubes. -/
lemma nearby_dist_bound {n m : ℕ} (hnm : m ≤ n) (t : DyadicTube n)
    (U : DyadicTube m) (hU : U ∈ nearbyCoarseTubes hnm t) :
    DyadicTube.dist U (coarseImage hnm t) ≤ 2 * dyadicDelta m := by
  have h1 : |U.a - (coarseImage hnm t).a| + |U.b - (coarseImage hnm t).b| ≤ 2 :=
    (mem_nearbyCoarseTubes_iff hnm t U).mp hU
  set U₀ := coarseImage hnm t with hU₀
  have hslope : |U.slope - U₀.slope| = (|U.a - U₀.a| : ℝ) * dyadicDelta m := by
    have h : U.slope - U₀.slope = ((U.a : ℝ) - (U₀.a : ℝ)) * dyadicDelta m := by
      simp [DyadicTube.slope] <;> ring
    rw [h]
    rw [abs_mul, abs_of_pos (dyadicDelta_pos m)]
    <;> ring
  have hint : |U.intercept - U₀.intercept| = (|U.b - U₀.b| : ℝ) * dyadicDelta m := by
    have h : U.intercept - U₀.intercept = ((U.b : ℝ) - (U₀.b : ℝ)) * dyadicDelta m := by
      simp [DyadicTube.intercept] <;> ring
    rw [h]
    rw [abs_mul, abs_of_pos (dyadicDelta_pos m)]
    <;> ring
  have h2 : DyadicTube.dist U U₀ = |U.slope - U₀.slope| + |U.intercept - U₀.intercept| := by rfl
  rw [h2, hslope, hint]
  have h3 : 0 ≤ dyadicDelta m := dyadicDelta_pos m |>.le
  have h4 : (|U.a - U₀.a| : ℝ) + (|U.b - U₀.b| : ℝ) ≤ 2 := by exact_mod_cast h1
  nlinarith

/-- coarseImage is always in nearbyCoarseTubes. -/
lemma coarseImage_mem_nearby {n m : ℕ} (hnm : m ≤ n) (t : DyadicTube n) :
    coarseImage hnm t ∈ nearbyCoarseTubes hnm t := by
  rw [mem_nearbyCoarseTubes_iff] <;> simp

/-- Cardinality of nearbyCoarseTubes is at most 13 (L1 ball radius 2 in Z²). -/
lemma nearbyCoarseTubes_card_le {n m : ℕ} (hnm : m ≤ n) (t : DyadicTube n) :
    (nearbyCoarseTubes hnm t).card ≤ 13 := by
  let U₀ := coarseImage hnm t
  let f : ℤ × ℤ → DyadicTube m := fun p => ⟨U₀.a + p.1, U₀.b + p.2⟩
  let S : Finset (ℤ × ℤ) :=
    (Finset.Icc (-2 : ℤ) 2 ×ˢ Finset.Icc (-2 : ℤ) 2).filter
      (fun p : ℤ × ℤ => |p.1| + |p.2| ≤ 2)
  have hS13 : S.card = 13 := by
    decide
  have hS_prop : ∀ (da db : ℤ), (da, db) ∈ S ↔ |da| + |db| ≤ 2 := by
    intro da db
    constructor
    · intro h
      have h' : |da| + |db| ≤ 2 := (Finset.mem_filter.mp h).2
      exact h'
    · intro h
      have hda : |da| ≤ 2 := by
        calc |da| ≤ |da| + |db| := by exact le_add_of_nonneg_right (abs_nonneg db)
             _ ≤ 2 := h
      have hdb : |db| ≤ 2 := by
        calc |db| ≤ |da| + |db| := by exact le_add_of_nonneg_left (abs_nonneg da)
             _ ≤ 2 := h
      have h1 : -2 ≤ da := by linarith [abs_le.mp hda]
      have h2 : da ≤ 2 := by linarith [abs_le.mp hda]
      have h3 : -2 ≤ db := by linarith [abs_le.mp hdb]
      have h4 : db ≤ 2 := by linarith [abs_le.mp hdb]
      have h_in_prod : (da, db) ∈ (Finset.Icc (-2 : ℤ) 2 ×ˢ Finset.Icc (-2 : ℤ) 2) := by
        simp only [Finset.mem_product, Finset.mem_Icc] <;> exact ⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩
      exact Finset.mem_filter.mpr ⟨h_in_prod, h⟩
  have h_main : nearbyCoarseTubes hnm t = S.image f := by
    ext U
    have h_iff : U ∈ nearbyCoarseTubes hnm t ↔
        |U.a - U₀.a| + |U.b - U₀.b| ≤ 2 := mem_nearbyCoarseTubes_iff hnm t U
    rw [h_iff]
    simp only [Finset.mem_image]
    constructor
    · intro h
      let da : ℤ := U.a - U₀.a
      let db : ℤ := U.b - U₀.b
      have hsum : |da| + |db| ≤ 2 := h
      have h_inS : (da, db) ∈ S := (hS_prop da db).mpr hsum
      refine' ⟨(da, db), h_inS, _⟩
      cases U <;> simp [f, da, db] <;> omega
    · rintro ⟨p, hp, rfl⟩
      have hsum : |p.1| + |p.2| ≤ 2 := (hS_prop p.1 p.2).mp hp
      simpa [f] using hsum
  rw [h_main]
  have h_inj : Set.InjOn f S := by
    intro p1 hp1 p2 hp2 h
    have h1 : U₀.a + p1.1 = U₀.a + p2.1 := congr_arg DyadicTube.a h
    have h2 : U₀.b + p1.2 = U₀.b + p2.2 := congr_arg DyadicTube.b h
    have h3 : p1.1 = p2.1 := by linarith
    have h4 : p1.2 = p2.2 := by linarith
    exact Prod.ext h3 h4
  rw [Finset.card_image_of_injOn h_inj, hS13]
  <;> norm_num

/-! ### Main geometric intersection lemma -/

/-- If a fine tube t intersects a fine square p, and p is contained in coarse square Q,
    then there exists a coarse tube U near the rounding of t that intersects Q.

    Requires |x 0| ≤ 1 for points in p (unit-ball setup). -/
lemma nearby_geometric_intersection
    {n m : ℕ} (hnm : m ≤ n)
    (t : DyadicTube n) (p : DyadicSquare n) (Q : DyadicSquare m)
    (h_common : (t.toSet ∩ p.toSet).Nonempty)
    (h_contain : squareContained hnm p Q)
    (h_x_bound : ∀ x ∈ p.toSet, |x 0| ≤ 1) :
    ∃ (U : DyadicTube m), U ∈ nearbyCoarseTubes hnm t ∧
      (U.toSet ∩ Q.toSet).Nonempty := by
  rcases h_common with ⟨z, hz_t, hz_p⟩
  have hz_Q : z ∈ Q.toSet := squareContained_toSet_subset hnm h_contain hz_p
  have h_x : |z 0| ≤ 1 := h_x_bound z hz_p
  set δ_n := dyadicDelta n with hδn
  set δ_m := dyadicDelta m with hδm
  set U₀ := coarseImage hnm t with hU₀
  let g₀ : ℝ → ℝ := fun x => U₀.slope * x + U₀.intercept

  have hδ_pos : 0 < δ_m := dyadicDelta_pos m
  have hδ_le : δ_n ≤ δ_m := by
    have h1 : (m : ℝ) ≤ (n : ℝ) := by exact_mod_cast hnm
    have h2 : (2 : ℝ)^(-(n : ℝ)) ≤ (2 : ℝ)^(-(m : ℝ)) := by gcongr <;> linarith
    simpa [hδn, hδm, dyadicDelta] using h2

  have h_strip : |z 1 - t.slope * z 0 - t.intercept| ≤ δ_n := by
    simpa [DyadicTube.toSet] using hz_t

  have h_dist : |t.slope - U₀.slope| + |t.intercept - U₀.intercept| ≤ δ_m := by
    have h_eq1 : U₀.slope = (coarseRound n m hnm t).slope := (coarseImage_eq hnm t).1
    have h_eq2 : U₀.intercept = (coarseRound n m hnm t).intercept := (coarseImage_eq hnm t).2
    rw [h_eq1, h_eq2]
    exact coarseRound_dist n m hnm t

  have h1 : |U₀.slope * z 0 + U₀.intercept - (t.slope * z 0 + t.intercept)| ≤ δ_m := by
    have h : U₀.slope * z 0 + U₀.intercept - (t.slope * z 0 + t.intercept) =
        (U₀.slope - t.slope) * z 0 + (U₀.intercept - t.intercept) := by ring
    rw [h]
    have h_abs : |(U₀.slope - t.slope) * z 0 + (U₀.intercept - t.intercept)|
        ≤ |(U₀.slope - t.slope) * z 0| + |U₀.intercept - t.intercept| := by
      exact real_abs_add ((U₀.slope - t.slope) * z.ofLp 0) (U₀.intercept - t.intercept)
    have h_mul : |(U₀.slope - t.slope) * z 0| = |z 0| * |U₀.slope - t.slope| := by
      rw [abs_mul] <;> ring
    rw [h_mul] at h_abs
    calc _
        ≤ |z 0| * |U₀.slope - t.slope| + |U₀.intercept - t.intercept| := h_abs
      _ ≤ 1 * |U₀.slope - t.slope| + |U₀.intercept - t.intercept| := by gcongr <;> linarith
      _ = |U₀.slope - t.slope| + |U₀.intercept - t.intercept| := by ring
      _ ≤ δ_m := by
        have hs1 : |U₀.slope - t.slope| = |t.slope - U₀.slope| := by
          have h : U₀.slope - t.slope = -(t.slope - U₀.slope) := by ring
          rw [h, abs_neg]
        have hs2 : |U₀.intercept - t.intercept| = |t.intercept - U₀.intercept| := by
          have h : U₀.intercept - t.intercept = -(t.intercept - U₀.intercept) := by ring
          rw [h, abs_neg]
        have h_sym : |U₀.slope - t.slope| + |U₀.intercept - t.intercept| =
            |t.slope - U₀.slope| + |t.intercept - U₀.intercept| := by
          rw [hs1, hs2]
        rw [h_sym]; exact h_dist

  have h3 : |g₀ (z 0) - z 1| ≤ δ_m + δ_n := by
    have h4 : g₀ (z 0) - z 1 = (U₀.slope * z 0 + U₀.intercept - (t.slope * z 0 + t.intercept)) +
        (t.slope * z 0 + t.intercept - z 1) := by ring
    rw [h4]
    have h_abs2 : |t.slope * z 0 + t.intercept - z 1| = |z 1 - t.slope * z 0 - t.intercept| := by
      rw [show t.slope * z 0 + t.intercept - z 1 = -(z 1 - t.slope * z 0 - t.intercept) by ring]
      rw [abs_neg]
    calc |(U₀.slope * z 0 + U₀.intercept - (t.slope * z 0 + t.intercept)) + (t.slope * z 0 + t.intercept - z 1)|
        ≤ |U₀.slope * z 0 + U₀.intercept - (t.slope * z 0 + t.intercept)| +
            |t.slope * z 0 + t.intercept - z 1| := by
          exact real_abs_add
            (U₀.slope * z.ofLp 0 + U₀.intercept - (t.slope * z.ofLp 0 + t.intercept))
            (t.slope * z.ofLp 0 + t.intercept - z.ofLp 1)
      _ = |U₀.slope * z 0 + U₀.intercept - (t.slope * z 0 + t.intercept)| + |z 1 - t.slope * z 0 - t.intercept| := by rw [h_abs2]
      _ ≤ δ_m + δ_n := by linarith [h1, h_strip]

  set c : ℝ := (Q.j : ℝ) * δ_m with hc
  have hc1 : c ≤ z 1 := hz_Q.2.2.1
  have hc2 : z 1 < c + δ_m := by
    have h : z 1 < ((Q.j : ℝ) + 1) * δ_m := hz_Q.2.2.2
    have h' : ((Q.j : ℝ) + 1) * δ_m = c + δ_m := by
      simp [hc] <;> ring
    rw [h'] at h
    exact h

  let gval := g₀ (z 0)

  -- Helper to construct a point with x-coordinate z 0
  let mkPoint (y1 : ℝ) : EuclideanSpace ℝ (Fin 2) :=
    WithLp.toLp 2 (fun i : Fin 2 => if i = 0 then z 0 else y1)
  have hmk0 : ∀ (y1 : ℝ), (mkPoint y1) 0 = z 0 := by
    intro y1; simp [mkPoint, WithLp.toLp]
  have hmk1 : ∀ (y1 : ℝ), (mkPoint y1) 1 = y1 := by
    intro y1; simp [mkPoint, WithLp.toLp]
  have hx1 : (Q.i : ℝ) * δ_m ≤ z 0 := hz_Q.1
  have hx2 : z 0 < ((Q.i : ℝ) + 1) * δ_m := hz_Q.2.1
  have h_point_in_Q : ∀ (y1 : ℝ), c ≤ y1 → y1 < c + δ_m → (mkPoint y1) ∈ Q.toSet := by
    intro y1 hy1 hy2
    have h1 : (Q.i : ℝ) * δ_m ≤ (mkPoint y1) 0 := by rw [hmk0 y1]; exact hx1
    have h2 : (mkPoint y1) 0 < ((Q.i : ℝ) + 1) * δ_m := by rw [hmk0 y1]; exact hx2
    have h3 : (Q.j : ℝ) * δ_m ≤ (mkPoint y1) 1 := by
      rw [hmk1 y1]
      have h_c_eq : c = (Q.j : ℝ) * δ_m := hc.symm
      linarith [hy1, h_c_eq]
    have h4 : (mkPoint y1) 1 < ((Q.j : ℝ) + 1) * δ_m := by
      rw [hmk1 y1]
      have h_eq : c + δ_m = ((Q.j : ℝ) + 1) * δ_m := by
        simp [hc] <;> ring
      linarith [hy2, h_eq]
    exact ⟨h1, h2, h3, h4⟩
  have h_point_in_strip : ∀ (V : DyadicTube m) (y1 : ℝ),
      |y1 - V.slope * (z 0) - V.intercept| ≤ δ_m → (mkPoint y1) ∈ V.toSet := by
    intro V y1 h
    simpa [mkPoint, DyadicTube.toSet] using h

  by_cases h4 : gval < c - δ_m
  · -- Too low: shift up by δ_m (db = +1)
    let U : DyadicTube m := ⟨U₀.a, U₀.b + 1⟩
    have hU_near : U ∈ nearbyCoarseTubes hnm t := by
      rw [mem_nearbyCoarseTubes_iff] <;> simp [U, U₀] <;> norm_num <;> omega
    have hg : U.slope * z 0 + U.intercept = gval + δ_m := by
      have hs : U.slope = U₀.slope := by
        simp [U, U₀, DyadicTube.slope] <;> ring
      have hi : U.intercept = U₀.intercept + δ_m := by
        simp [U, U₀, DyadicTube.intercept, hδm] <;> ring
      rw [hs, hi]
      have hgval : gval = U₀.slope * z 0 + U₀.intercept := by rfl
      rw [hgval] <;> ring
    have h5 : c - δ_m ≤ gval + δ_m := by
      have h9 : |gval - z 1| ≤ δ_m + δ_n := h3
      have h10 : gval ≥ z 1 - (δ_m + δ_n) := by linarith [abs_le.mp h9]
      have h11 : z 1 ≥ c := hc1
      linarith [hδ_le]
    have h7 : gval + δ_m < c + 2 * δ_m := by linarith
    rcases strip_center_intersects_interval hδ_pos h5 h7 with ⟨y, hy1, hy2, hy3⟩
    have h_strip : |y - U.slope * (z 0) - U.intercept| ≤ δ_m := by
      have h_eq : y - U.slope * (z 0) - U.intercept = y - (U.slope * (z 0) + U.intercept) := by ring
      rw [h_eq, hg] <;> exact hy3
    exact ⟨U, hU_near, mkPoint y, h_point_in_strip U y h_strip, h_point_in_Q y hy1 hy2⟩
  · -- Not too low
    by_cases h5 : gval ≥ c + 2 * δ_m
    · -- Too high: shift down by δ_m (db = -1)
      let U : DyadicTube m := ⟨U₀.a, U₀.b - 1⟩
      have hU_near : U ∈ nearbyCoarseTubes hnm t := by
        rw [mem_nearbyCoarseTubes_iff] <;> simp [U, U₀] <;> norm_num <;> omega
      have hg : U.slope * z 0 + U.intercept = gval - δ_m := by
        have hs : U.slope = U₀.slope := by
          simp [U, U₀, DyadicTube.slope] <;> ring
        have hi : U.intercept = U₀.intercept - δ_m := by
          simp [U, U₀, DyadicTube.intercept, hδm] <;> ring
        rw [hs, hi]
        have hgval : gval = U₀.slope * z 0 + U₀.intercept := by rfl
        rw [hgval] <;> ring
      have h6 : c - δ_m ≤ gval - δ_m := by linarith
      have h7 : gval - δ_m < c + 2 * δ_m := by
        have h8 : gval ≤ z 1 + δ_m + δ_n := by
          have h9 : |gval - z 1| ≤ δ_m + δ_n := h3
          linarith [abs_le.mp h9]
        linarith [hc2, hδ_le]
      rcases strip_center_intersects_interval hδ_pos h6 h7 with ⟨y, hy1, hy2, hy3⟩
      have h_strip : |y - U.slope * (z 0) - U.intercept| ≤ δ_m := by
        have h_eq : y - U.slope * (z 0) - U.intercept = y - (U.slope * (z 0) + U.intercept) := by ring
        rw [h_eq, hg] <;> exact hy3
      exact ⟨U, hU_near, mkPoint y, h_point_in_strip U y h_strip, h_point_in_Q y hy1 hy2⟩
    · -- Just right: gval ∈ [c - δ_m, c + 2*δ_m)
      have h4' : c - δ_m ≤ gval := by linarith
      have h5' : gval < c + 2 * δ_m := by linarith
      let U := U₀
      have hU_near : U ∈ nearbyCoarseTubes hnm t := coarseImage_mem_nearby hnm t
      rcases strip_center_intersects_interval hδ_pos h4' h5' with ⟨y, hy1, hy2, hy3⟩
      have h_strip : |y - U.slope * (z 0) - U.intercept| ≤ δ_m := by
        have h_eq : y - U.slope * (z 0) - U.intercept = y - (U.slope * (z 0) + U.intercept) := by ring
        rw [h_eq]
        simpa [U, g₀] using hy3
      exact ⟨U, hU_near, mkPoint y, h_point_in_strip U y h_strip, h_point_in_Q y hy1 hy2⟩

/-! ### Parameter strip and fiber overlap lemmas -/

lemma abs_tri (x y : ℝ) : |x| ≤ |y| + |x - y| := by
  have h1 : -(|y| + |x - y|) ≤ y + (x - y) := by
    have h2 : -|y| ≤ y := neg_abs_le y
    have h3 : -|x - y| ≤ x - y := neg_abs_le (x - y)
    linarith
  have h4 : y + (x - y) ≤ |y| + |x - y| := by
    have h5 : y ≤ |y| := le_abs_self y
    have h6 : x - y ≤ |x - y| := le_abs_self (x - y)
    linarith
  have h : |y + (x - y)| ≤ |y| + |x - y| := abs_le.mpr ⟨h1, h4⟩
  have h' : y + (x - y) = x := by ring
  rw [h'] at h
  exact h

lemma pow_plus_three_le {k : ℕ} (hk : 1 ≤ k) : (2^(k+1) : ℤ) + 3 ≤ 2^(k+2) := by
  have h1 : (3 : ℤ) ≤ (2 : ℤ)^(k+1) := by
    have h2 : k + 1 ≥ 2 := by omega
    have h3 : (2 : ℤ)^2 ≤ (2 : ℤ)^(k+1) := by gcongr <;> omega
    norm_num at h3 ⊢ <;> omega
  have h6 : (2 : ℤ)^(k+2) = 2 * (2 : ℤ)^(k+1) := by simp [pow_succ] <;> ring
  rw [h6]; linarith

lemma pow_plus_three_le2 {k : ℕ} (hk : 1 ≤ k) : (2^(k+2) : ℤ) + 3 ≤ 2^(k+3) := by
  have h1 : (3 : ℤ) ≤ (2 : ℤ)^(k+2) := by
    have h2 : k + 2 ≥ 3 := by omega
    have h3 : (2 : ℤ)^3 ≤ (2 : ℤ)^(k+2) := by gcongr <;> omega
    norm_num at h3 ⊢ <;> omega
  have h6 : (2 : ℤ)^(k+3) = 2 * (2 : ℤ)^(k+2) := by simp [pow_succ] <;> ring
  rw [h6]; linarith

/-- From slope distance ≤ δ_m, derive |T.a/rf - U.a| ≤ 1. -/
lemma slope_dist_to_index_bound {n m : ℕ} (hnm : m ≤ n)
    (T : DyadicTube n) (U : DyadicTube m)
    (h : |T.slope - U.slope| ≤ dyadicDelta m) :
    |(T.a : ℝ) / (DirecretisedFurstenbergEstimate.InductionOnScales.refinementFactor n m : ℝ) - (U.a : ℝ)| ≤ 1 := by
  set rf : ℕ := DirecretisedFurstenbergEstimate.InductionOnScales.refinementFactor n m with hrf_def
  have hrf_pos : 0 < rf := DirecretisedFurstenbergEstimate.InductionOnScales.refinementFactor_pos n m
  have h_mul : dyadicDelta n * (rf : ℝ) = dyadicDelta m := dyadicDelta_mul_refinement n m hnm
  have hδn : dyadicDelta n = dyadicDelta m / (rf : ℝ) := by
    field_simp [(show (rf : ℝ) ≠ 0 by exact_mod_cast hrf_pos.ne')] <;> linarith
  have h1 : |T.slope - U.slope| = |(T.a : ℝ) * dyadicDelta n - (U.a : ℝ) * dyadicDelta m| := by rfl
  rw [h1] at h
  rw [hδn] at h
  have h_pos : 0 < dyadicDelta m := dyadicDelta_pos m
  have h2 : |((T.a : ℝ) * (dyadicDelta m / (rf : ℝ)) - (U.a : ℝ) * dyadicDelta m)| ≤ dyadicDelta m := h
  have h3 : |((T.a : ℝ) / (rf : ℝ) - (U.a : ℝ)) * dyadicDelta m| ≤ dyadicDelta m := by
    have h4 : ((T.a : ℝ) * (dyadicDelta m / (rf : ℝ)) - (U.a : ℝ) * dyadicDelta m) =
        ((T.a : ℝ) / (rf : ℝ) - (U.a : ℝ)) * dyadicDelta m := by ring
    rw [h4] at h2
    exact h2
  have h5 : |((T.a : ℝ) / (rf : ℝ) - (U.a : ℝ))| * dyadicDelta m ≤ dyadicDelta m := by
    have h6 : |((T.a : ℝ) / (rf : ℝ) - (U.a : ℝ)) * dyadicDelta m| =
        |((T.a : ℝ) / (rf : ℝ) - (U.a : ℝ))| * dyadicDelta m := by
      rw [abs_mul, abs_of_nonneg h_pos.le] <;> ring
    rw [h6] at h3
    exact h3
  nlinarith

/-- From intercept distance ≤ δ_m, derive |T.b/rf - U.b| ≤ 1. -/
lemma intercept_dist_to_index_bound {n m : ℕ} (hnm : m ≤ n)
    (T : DyadicTube n) (U : DyadicTube m)
    (h : |T.intercept - U.intercept| ≤ dyadicDelta m) :
    |(T.b : ℝ) / (DirecretisedFurstenbergEstimate.InductionOnScales.refinementFactor n m : ℝ) - (U.b : ℝ)| ≤ 1 := by
  set rf : ℕ := DirecretisedFurstenbergEstimate.InductionOnScales.refinementFactor n m with hrf_def
  have hrf_pos : 0 < rf := DirecretisedFurstenbergEstimate.InductionOnScales.refinementFactor_pos n m
  have h_mul : dyadicDelta n * (rf : ℝ) = dyadicDelta m := dyadicDelta_mul_refinement n m hnm
  have hδn : dyadicDelta n = dyadicDelta m / (rf : ℝ) := by
    field_simp [(show (rf : ℝ) ≠ 0 by exact_mod_cast hrf_pos.ne')] <;> linarith
  have h1 : |T.intercept - U.intercept| = |(T.b : ℝ) * dyadicDelta n - (U.b : ℝ) * dyadicDelta m| := by rfl
  rw [h1] at h
  rw [hδn] at h
  have h_pos : 0 < dyadicDelta m := dyadicDelta_pos m
  have h3 : |((T.b : ℝ) / (rf : ℝ) - (U.b : ℝ)) * dyadicDelta m| ≤ dyadicDelta m := by
    have h4 : ((T.b : ℝ) * (dyadicDelta m / (rf : ℝ)) - (U.b : ℝ) * dyadicDelta m) =
        ((T.b : ℝ) / (rf : ℝ) - (U.b : ℝ)) * dyadicDelta m := by ring
    rw [h4] at h
    exact h
  have h5 : |((T.b : ℝ) / (rf : ℝ) - (U.b : ℝ))| * dyadicDelta m ≤ dyadicDelta m := by
    have h6 : |((T.b : ℝ) / (rf : ℝ) - (U.b : ℝ)) * dyadicDelta m| =
        |((T.b : ℝ) / (rf : ℝ) - (U.b : ℝ))| * dyadicDelta m := by
      rw [abs_mul, abs_of_nonneg h_pos.le] <;> ring
    rw [h6] at h3
    exact h3
  nlinarith

/-- coarseImage index bounds at scale m. -/
lemma coarseImage_index_bound {n m : ℕ} (hnm : m ≤ n) (T : DyadicTube n)
    (hT_a : |T.a| ≤ (2^(n+1) : ℤ))
    (hT_b : |T.b| ≤ (2^(n+2) : ℤ)) :
    |(coarseImage hnm T).a| ≤ (2^(m+1) : ℤ) + 1 ∧
    |(coarseImage hnm T).b| ≤ (2^(m+2) : ℤ) + 1 := by
  set U := coarseImage hnm T with hU
  set T' := coarseRound n m hnm T with hT'
  have h_eq_slope : U.slope = T'.slope := (coarseImage_eq hnm T).1
  have h_eq_intercept : U.intercept = T'.intercept := (coarseImage_eq hnm T).2
  have h_dist : dist T T' ≤ dyadicDelta m := coarseRound_dist n m hnm T
  have h_dist_eq : dist T T' = |T.slope - T'.slope| + |T.intercept - T'.intercept| := by rfl
  rw [h_dist_eq] at h_dist
  have h_slope_dist : |T.slope - T'.slope| ≤ dyadicDelta m := by linarith [abs_nonneg (T.intercept - T'.intercept)]
  have h_intercept_dist : |T.intercept - T'.intercept| ≤ dyadicDelta m := by linarith [abs_nonneg (T.slope - T'.slope)]
  have h_slope_U : |T.slope - U.slope| ≤ dyadicDelta m := by
    rw [h_eq_slope] <;> exact h_slope_dist
  have h_intercept_U : |T.intercept - U.intercept| ≤ dyadicDelta m := by
    rw [h_eq_intercept] <;> exact h_intercept_dist

  set rf : ℕ := DirecretisedFurstenbergEstimate.InductionOnScales.refinementFactor n m with hrf_def
  have hrf_pos : 0 < rf := DirecretisedFurstenbergEstimate.InductionOnScales.refinementFactor_pos n m
  have h_rf_eq : (rf : ℝ) = (2^(n-m) : ℝ) := by
    simp [rf, hrf_def, DirecretisedFurstenbergEstimate.InductionOnScales.refinementFactor] <;> norm_cast

  have h_a1 := slope_dist_to_index_bound hnm T U h_slope_U
  have h_b1 := intercept_dist_to_index_bound hnm T U h_intercept_U

  have hTa : (|T.a| : ℝ) ≤ (2^(n+1) : ℝ) := by exact_mod_cast hT_a
  have hTb : (|T.b| : ℝ) ≤ (2^(n+2) : ℝ) := by exact_mod_cast hT_b

  have h_a2 : |(U.a : ℝ)| ≤ |(T.a : ℝ)| / (rf : ℝ) + 1 := by
    have h3 : |(U.a : ℝ)| ≤ |(T.a : ℝ) / (rf : ℝ)| + |(U.a : ℝ) - (T.a : ℝ) / (rf : ℝ)| :=
      abs_tri (U.a : ℝ) ((T.a : ℝ) / (rf : ℝ))
    have h4 : |(T.a : ℝ) / (rf : ℝ)| = |(T.a : ℝ)| / (rf : ℝ) := by
      rw [abs_div, abs_of_nonneg (show (0 : ℝ) ≤ (rf : ℝ) by exact_mod_cast hrf_pos.le)]
    have h5 : |(U.a : ℝ) - (T.a : ℝ) / (rf : ℝ)| = |(T.a : ℝ) / (rf : ℝ) - (U.a : ℝ)| := by
      rw [show (U.a : ℝ) - (T.a : ℝ) / (rf : ℝ) = -((T.a : ℝ) / (rf : ℝ) - (U.a : ℝ)) by ring]
      rw [abs_neg]
    rw [h4, h5] at h3
    linarith [h_a1]
  have h_a3 : |(U.a : ℝ)| ≤ (2^(m+1) : ℝ) + 1 := by
    have h4 : |(T.a : ℝ)| / (rf : ℝ) ≤ (2^(m+1) : ℝ) := by
      rw [h_rf_eq]
      have h5 : (n+1 : ℕ) = (n-m) + (m+1) := by omega
      have h6 : |(T.a : ℝ)| ≤ (2 : ℝ)^((n-m) + (m+1)) := by
        rw [h5] at hTa; exact hTa
      have h7 : (2 : ℝ)^((n-m) + (m+1)) / (2 : ℝ)^(n-m) = (2 : ℝ)^(m+1) := by
        field_simp [pow_add] <;> ring
      calc |(T.a : ℝ)| / (2 : ℝ)^(n-m)
        ≤ (2 : ℝ)^((n-m) + (m+1)) / (2 : ℝ)^(n-m) := by gcongr <;> positivity
      _ = (2 : ℝ)^(m+1) := h7
    linarith
  have h_a4 : |U.a| ≤ (2^(m+1) : ℤ) + 1 := by exact_mod_cast h_a3

  have h_b2 : |(U.b : ℝ)| ≤ |(T.b : ℝ)| / (rf : ℝ) + 1 := by
    have h3 : |(U.b : ℝ)| ≤ |(T.b : ℝ) / (rf : ℝ)| + |(U.b : ℝ) - (T.b : ℝ) / (rf : ℝ)| :=
      abs_tri (U.b : ℝ) ((T.b : ℝ) / (rf : ℝ))
    have h4 : |(T.b : ℝ) / (rf : ℝ)| = |(T.b : ℝ)| / (rf : ℝ) := by
      rw [abs_div, abs_of_nonneg (show (0 : ℝ) ≤ (rf : ℝ) by exact_mod_cast hrf_pos.le)]
    have h5 : |(U.b : ℝ) - (T.b : ℝ) / (rf : ℝ)| = |(T.b : ℝ) / (rf : ℝ) - (U.b : ℝ)| := by
      rw [show (U.b : ℝ) - (T.b : ℝ) / (rf : ℝ) = -((T.b : ℝ) / (rf : ℝ) - (U.b : ℝ)) by ring]
      rw [abs_neg]
    rw [h4, h5] at h3
    linarith [h_b1]
  have h_b3 : |(U.b : ℝ)| ≤ (2^(m+2) : ℝ) + 1 := by
    have h4 : |(T.b : ℝ)| / (rf : ℝ) ≤ (2^(m+2) : ℝ) := by
      rw [h_rf_eq]
      have h5 : (n+2 : ℕ) = (n-m) + (m+2) := by omega
      have h6 : |(T.b : ℝ)| ≤ (2 : ℝ)^((n-m) + (m+2)) := by
        rw [h5] at hTb; exact hTb
      have h7 : (2 : ℝ)^((n-m) + (m+2)) / (2 : ℝ)^(n-m) = (2 : ℝ)^(m+2) := by
        field_simp [pow_add] <;> ring
      calc |(T.b : ℝ)| / (2 : ℝ)^(n-m)
        ≤ (2 : ℝ)^((n-m) + (m+2)) / (2 : ℝ)^(n-m) := by gcongr <;> positivity
      _ = (2 : ℝ)^(m+2) := h7
    linarith
  have h_b4 : |U.b| ≤ (2^(m+2) : ℤ) + 1 := by exact_mod_cast h_b3

  exact ⟨h_a4, h_b4⟩

/-- Nearby coarse tubes satisfy relaxed index bounds. -/
lemma nearbyCoarseTubes_index_bound {n m : ℕ} (hnm : m ≤ n) (hm_pos : 1 ≤ m)
    (T : DyadicTube n)
    (hT_a : |T.a| ≤ (2^(n+1) : ℤ))
    (hT_b : |T.b| ≤ (2^(n+2) : ℤ))
    (U : DyadicTube m) (hU : U ∈ nearbyCoarseTubes hnm T) :
    |U.a| ≤ (2^(m+2) : ℤ) ∧ |U.b| ≤ (2^(m+3) : ℤ) := by
  set U₀ := coarseImage hnm T with hU₀
  have h_bound := coarseImage_index_bound hnm T hT_a hT_b
  have h1 : |U₀.a| ≤ (2^(m+1) : ℤ) + 1 := h_bound.1
  have h2 : |U₀.b| ≤ (2^(m+2) : ℤ) + 1 := h_bound.2
  have h3 : |U.a - U₀.a| + |U.b - U₀.b| ≤ 2 :=
    (mem_nearbyCoarseTubes_iff hnm T U).mp hU
  have h4 : |U.a - U₀.a| ≤ 2 := by linarith [abs_nonneg (U.b - U₀.b)]
  have h5 : |U.b - U₀.b| ≤ 2 := by linarith [abs_nonneg (U.a - U₀.a)]
  have h6 : |(U.a : ℝ)| ≤ |(U₀.a : ℝ)| + |(U.a : ℝ) - (U₀.a : ℝ)| :=
    abs_tri (U.a : ℝ) (U₀.a : ℝ)
  have h7 : |(U.b : ℝ)| ≤ |(U₀.b : ℝ)| + |(U.b : ℝ) - (U₀.b : ℝ)| :=
    abs_tri (U.b : ℝ) (U₀.b : ℝ)
  have h8 : |(U.a : ℝ)| ≤ ((2^(m+1) : ℤ) + 3 : ℝ) := by
    have h9 : |(U₀.a : ℝ)| ≤ ((2^(m+1) : ℤ) + 1 : ℝ) := by exact_mod_cast h1
    have h10 : |(U.a : ℝ) - (U₀.a : ℝ)| ≤ (2 : ℝ) := by exact_mod_cast h4
    linarith
  have h9 : |(U.b : ℝ)| ≤ ((2^(m+2) : ℤ) + 3 : ℝ) := by
    have h10 : |(U₀.b : ℝ)| ≤ ((2^(m+2) : ℤ) + 1 : ℝ) := by exact_mod_cast h2
    have h11 : |(U.b : ℝ) - (U₀.b : ℝ)| ≤ (2 : ℝ) := by exact_mod_cast h5
    linarith
  have h12 : |U.a| ≤ (2^(m+1) : ℤ) + 3 := by exact_mod_cast h8
  have h13 : |U.b| ≤ (2^(m+2) : ℤ) + 3 := by exact_mod_cast h9
  have h10 : (2^(m+1) : ℤ) + 3 ≤ (2^(m+2) : ℤ) := pow_plus_three_le hm_pos
  have h11 : (2^(m+2) : ℤ) + 3 ≤ (2^(m+3) : ℤ) := pow_plus_three_le2 hm_pos
  exact ⟨by linarith, by linarith⟩

/-! ### L1 ball of radius 2 -/

noncomputable def l1Ball2 {m : ℕ} (U : DyadicTube m) : Finset (DyadicTube m) :=
  (Finset.Icc (-2 : ℤ) 2).biUnion (fun da =>
    (Finset.Icc (-2 : ℤ) 2).filter (fun db => |da| + |db| ≤ 2)
      |>.image (fun db => ⟨U.a + da, U.b + db⟩))

lemma mem_l1Ball2_iff {m : ℕ} (U V : DyadicTube m) :
    V ∈ l1Ball2 U ↔ |V.a - U.a| + |V.b - U.b| ≤ 2 := by
  constructor
  · intro h
    rcases Finset.mem_biUnion.mp h with ⟨da, _, hmem⟩
    rcases Finset.mem_image.mp hmem with ⟨db, hdb, rfl⟩
    have h : |da| + |db| ≤ 2 := (Finset.mem_filter.mp hdb).2
    simpa using h
  · intro h
    let da : ℤ := V.a - U.a
    let db : ℤ := V.b - U.b
    have h2 : |da| ≤ 2 := by linarith [abs_nonneg db, h]
    have h3 : |db| ≤ 2 := by linarith [abs_nonneg da, h]
    have hda2 : da ∈ Finset.Icc (-2 : ℤ) 2 := by
      simp only [Finset.mem_Icc]; exact ⟨by linarith [abs_le.mp h2], by linarith [abs_le.mp h2]⟩
    have hdb2 : db ∈ Finset.Icc (-2 : ℤ) 2 := by
      simp only [Finset.mem_Icc]; exact ⟨by linarith [abs_le.mp h3], by linarith [abs_le.mp h3]⟩
    have hfilter : db ∈ (Finset.Icc (-2 : ℤ) 2).filter (fun db => |da| + |db| ≤ 2) := by
      simp only [Finset.mem_filter]; exact ⟨hdb2, h⟩
    have hV : V = ⟨U.a + da, U.b + db⟩ := by
      cases V <;> simp [da, db] <;> omega
    rw [hV]
    exact Finset.mem_biUnion.mpr ⟨da, hda2, Finset.mem_image.mpr ⟨db, hfilter, rfl⟩⟩

lemma l1Ball2_card_eq {m : ℕ} (U : DyadicTube m) : (l1Ball2 U).card = 13 := by
  let f : ℤ × ℤ → DyadicTube m := fun p => ⟨U.a + p.1, U.b + p.2⟩
  let S : Finset (ℤ × ℤ) :=
    (Finset.Icc (-2 : ℤ) 2 ×ˢ Finset.Icc (-2 : ℤ) 2).filter
      (fun p : ℤ × ℤ => |p.1| + |p.2| ≤ 2)
  have hS13 : S.card = 13 := by decide
  have h_main : l1Ball2 U = S.image f := by
    ext V
    have h_iff : V ∈ l1Ball2 U ↔ |V.a - U.a| + |V.b - U.b| ≤ 2 := mem_l1Ball2_iff U V
    rw [h_iff]
    simp only [Finset.mem_image]
    constructor
    · intro h
      let da : ℤ := V.a - U.a
      let db : ℤ := V.b - U.b
      have hsum : |da| + |db| ≤ 2 := h
      have hda : -2 ≤ da := by linarith [abs_le.mp (show |da| ≤ 2 from by linarith [abs_nonneg db, hsum])]
      have hda' : da ≤ 2 := by linarith [abs_le.mp (show |da| ≤ 2 from by linarith [abs_nonneg db, hsum])]
      have hdb : -2 ≤ db := by linarith [abs_le.mp (show |db| ≤ 2 from by linarith [abs_nonneg da, hsum])]
      have hdb' : db ≤ 2 := by linarith [abs_le.mp (show |db| ≤ 2 from by linarith [abs_nonneg da, hsum])]
      have h_inS : (da, db) ∈ S := by
        simp only [S, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc]
        exact ⟨⟨⟨hda, hda'⟩, ⟨hdb, hdb'⟩⟩, hsum⟩
      refine' ⟨(da, db), h_inS, _⟩
      cases V <;> simp [f, da, db] <;> omega
    · rintro ⟨p, hp, rfl⟩
      have hsum : |p.1| + |p.2| ≤ 2 := (Finset.mem_filter.mp hp).2
      simpa [f] using hsum
  rw [h_main]
  have h_inj : Set.InjOn f S := by
    intro p1 hp1 p2 hp2 h
    have h1 : U.a + p1.1 = U.a + p2.1 := congr_arg DyadicTube.a h
    have h2 : U.b + p1.2 = U.b + p2.2 := congr_arg DyadicTube.b h
    have h3 : p1.1 = p2.1 := by linarith
    have h4 : p1.2 = p2.2 := by linarith
    exact Prod.ext h3 h4
  rw [Finset.card_image_of_injOn h_inj, hS13]

lemma nearbyCoarseTubes_eq_l1Ball2 {n m : ℕ} (hnm : m ≤ n) (T : DyadicTube n) :
    nearbyCoarseTubes hnm T = l1Ball2 (coarseImage hnm T) := by
  ext U
  rw [mem_nearbyCoarseTubes_iff, mem_l1Ball2_iff]

/-- Symmetry of l1Ball2: V ∈ l1Ball2 U ↔ U ∈ l1Ball2 V. -/
lemma l1Ball2_symm {m : ℕ} (U V : DyadicTube m) :
    V ∈ l1Ball2 U ↔ U ∈ l1Ball2 V := by
  rw [mem_l1Ball2_iff, mem_l1Ball2_iff]
  have h1 : |V.a - U.a| = |U.a - V.a| := by
    rw [show V.a - U.a = -(U.a - V.a) by ring]; rw [abs_neg]
  have h2 : |V.b - U.b| = |U.b - V.b| := by
    rw [show V.b - U.b = -(U.b - V.b) by ring]; rw [abs_neg]
  rw [h1, h2]

/-! ### Fiber overlap lemmas -/

lemma fiber_g_subset_union_f {n m : ℕ}
    (Tubes : Finset (DyadicTube n))
    (g : DyadicSquare n → DyadicTube n → DyadicTube m)
    (f : DyadicTube n → DyadicTube m)
    (p : DyadicSquare n) (U : DyadicTube m)
    (h_near : ∀ T ∈ Tubes,
      |(g p T).a - (f T).a| + |(g p T).b - (f T).b| ≤ 2) :
    (Tubes.filter (fun T => g p T = U)) ⊆
    (Tubes.filter (fun T => f T ∈ l1Ball2 U)) := by
  intro T hT
  have h1 : g p T = U := (Finset.mem_filter.mp hT).2
  have h2 : T ∈ Tubes := (Finset.mem_filter.mp hT).1
  have h4 := h_near T h2
  rw [h1] at h4
  have h5 : |(f T).a - U.a| + |(f T).b - U.b| ≤ 2 := by
    have h6 : |U.a - (f T).a| + |U.b - (f T).b| ≤ 2 := h4
    have h7 : |(f T).a - U.a| = |U.a - (f T).a| := by
      rw [show (f T).a - U.a = -(U.a - (f T).a) by ring]; rw [abs_neg]
    have h8 : |(f T).b - U.b| = |U.b - (f T).b| := by
      rw [show (f T).b - U.b = -(U.b - (f T).b) by ring]; rw [abs_neg]
    linarith
  have h9 : f T ∈ l1Ball2 U := (mem_l1Ball2_iff U (f T)).mpr h5
  exact Finset.mem_filter.mpr ⟨h2, h9⟩

lemma fiber_f_subset_union_g {n m : ℕ}
    (Tubes : Finset (DyadicTube n))
    (g : DyadicSquare n → DyadicTube n → DyadicTube m)
    (f : DyadicTube n → DyadicTube m)
    (p : DyadicSquare n) (U : DyadicTube m)
    (h_near : ∀ T ∈ Tubes,
      |(g p T).a - (f T).a| + |(g p T).b - (f T).b| ≤ 2) :
    (Tubes.filter (fun T => f T = U)) ⊆
    (Tubes.filter (fun T => g p T ∈ l1Ball2 U)) := by
  intro T hT
  have h1 : f T = U := (Finset.mem_filter.mp hT).2
  have h2 : T ∈ Tubes := (Finset.mem_filter.mp hT).1
  have h4 := h_near T h2
  rw [h1] at h4
  have h5 : |(g p T).a - U.a| + |(g p T).b - U.b| ≤ 2 := h4
  have h9 : g p T ∈ l1Ball2 U := (mem_l1Ball2_iff U (g p T)).mpr h5
  exact Finset.mem_filter.mpr ⟨h2, h9⟩

lemma fiber_g_card_le_13 {n m : ℕ}
    (Tubes : Finset (DyadicTube n))
    (g : DyadicSquare n → DyadicTube n → DyadicTube m)
    (f : DyadicTube n → DyadicTube m)
    (p : DyadicSquare n) (U : DyadicTube m) (C : ℕ)
    (h_near : ∀ T ∈ Tubes,
      |(g p T).a - (f T).a| + |(g p T).b - (f T).b| ≤ 2)
    (h_max : ∀ V ∈ l1Ball2 U,
      (Tubes.filter (fun T => f T = V)).card ≤ C) :
    (Tubes.filter (fun T => g p T = U)).card ≤ 13 * C := by
  let F_fib (V : DyadicTube m) := Tubes.filter (fun T => f T = V)
  have h_sub := fiber_g_subset_union_f Tubes g f p U h_near
  have h1 : (Tubes.filter (fun T => g p T = U)).card ≤
      (Tubes.filter (fun T => f T ∈ l1Ball2 U)).card :=
    Finset.card_le_card h_sub
  have h2 : (Tubes.filter (fun T => f T ∈ l1Ball2 U)) =
      (l1Ball2 U).biUnion F_fib := by
    ext T
    simp only [Finset.mem_filter, Finset.mem_biUnion, F_fib]
    <;> aesop
  rw [h2] at h1
  have h3 : ((l1Ball2 U).biUnion F_fib).card ≤ ∑ V ∈ (l1Ball2 U), (F_fib V).card :=
    Finset.card_biUnion_le
  have h4 : ∑ V ∈ (l1Ball2 U), (F_fib V).card ≤ (l1Ball2 U).card * C := by
    calc ∑ V ∈ (l1Ball2 U), (F_fib V).card
      ≤ ∑ _V ∈ (l1Ball2 U), C := Finset.sum_le_sum (fun V hV => h_max V hV)
    _ = (l1Ball2 U).card * C := by simp [Finset.sum_const] <;> ring
  have h5 : (l1Ball2 U).card = 13 := l1Ball2_card_eq U
  have h6 : ((l1Ball2 U).biUnion F_fib).card ≤ 13 * C := by
    calc ((l1Ball2 U).biUnion F_fib).card
      ≤ ∑ V ∈ (l1Ball2 U), (F_fib V).card := h3
    _ ≤ (l1Ball2 U).card * C := h4
    _ = 13 * C := by rw [h5] <;> ring
  exact h1.trans h6

end DiscretisedFurstenbergEstimate.InductionOnScales
