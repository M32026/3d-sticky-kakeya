/-
The `sigma`-direction calculus for the Wang--Zahl assertions.

Source: `blueprint/src/WZ2/250224e_K3.tex`, Definition `defnCDE` and the
paragraph following Proposition `improvingProp` (Section 1.3), where the two
elementary facts

  `FS(T) * (#T) |T|^{1/2} >= 1`      and      `#T <~ delta^{-4}`

are used to (a) raise `sigma`, (b) close the set of admissible `sigma` from
above, and (c) trade a gain in `omega` for a gain in `sigma`.
-/
module

public import Kakeya.DimensionThree.MainLemma2.WangZahl.AssertionCalculus

@[expose] public section

open MeasureTheory

namespace Kakeya.WangZahl

noncomputable section

universe u

/-- The Wang--Zahl currency `X = (#T) |T|^{1/2}` of a family of `delta`-tubes.
It is the quantity raised to the power `-sigma` in Assertion `D`. -/
def wzCurrency (δ : NNReal) (n : ℕ) : ENNReal :=
  (n : ENNReal) * (tubeVolume δ) ^ (1 / 2 : ℝ)

lemma wzCurrency_pos {δ : NNReal} (hδ : 0 < δ) {n : ℕ} (hn : 0 < n) :
    0 < wzCurrency δ n := by
  have hV := tubeVolume_pos_and_ne_top hδ
  refine ENNReal.mul_pos ?_ ?_
  · exact_mod_cast hn.ne'
  · exact (ENNReal.rpow_pos hV.1 hV.2).ne'

lemma wzCurrency_ne_top {δ : NNReal} (hδ : 0 < δ) {n : ℕ} :
    wzCurrency δ n ≠ ⊤ := by
  have hV := tubeVolume_pos_and_ne_top hδ
  exact ENNReal.mul_ne_top (by simp)
    (ENNReal.rpow_ne_top_of_nonneg (by norm_num) hV.2)

/-- **Lower** size bound on the Wang--Zahl currency `X = (#T)|T|^{1/2}`.

This is the observation recorded immediately after Definition `defnCDE` in the
source: a slab of thickness `|T|^{1/2}` containing one tube of the family
forces `FS(T) (#T)|T|^{1/2} >= 1`; with the Frostman hypothesis
`FS(T) <= delta^{-eta}` this gives `X >= C⁻¹ delta^{eta}`. -/
def CurrencyLowerBound (C : NNReal) : Prop :=
  ∀ {δ : NNReal}, 0 < δ → δ ≤ 1 → ∀ {η : ℝ}, 0 < η →
    ∀ {ι : Type u} (s : Finset ι) (T : ι → ShadedTube δ Space3),
      s.Nonempty → IsTubeShadingFamily s T →
      katzTaoConvexWolffConstant s T ≤ (δ : ENNReal) ^ (-η) →
      frostmanSlabWolffConstant s T ≤ (δ : ENNReal) ^ (-η) →
      ((C : ENNReal))⁻¹ * (δ : ENNReal) ^ η ≤ wzCurrency δ s.card

/-- **Upper** size bound on the Wang--Zahl currency `X = (#T)|T|^{1/2}`,
obtained from the Katz--Tao hypothesis applied to the unit ball. -/
def CurrencyUpperBound (C : NNReal) : Prop :=
  ∀ {δ : NNReal}, 0 < δ → δ ≤ 1 → ∀ {η : ℝ}, 0 < η →
    ∀ {ι : Type u} (s : Finset ι) (T : ι → ShadedTube δ Space3),
      s.Nonempty → IsTubeShadingFamily s T →
      katzTaoConvexWolffConstant s T ≤ (δ : ENNReal) ^ (-η) →
      frostmanSlabWolffConstant s T ≤ (δ : ENNReal) ^ (-η) →
      wzCurrency δ s.card ≤ (C : ENNReal) * (δ : ENNReal) ^ (-η - 1)

/-- Both elementary size bounds on the Wang--Zahl currency, with one constant. -/
def CurrencyBounds (C : NNReal) : Prop :=
  CurrencyLowerBound.{u} C ∧ CurrencyUpperBound.{u} C

/-- Antitonicity of `ENNReal` rpow in the base at a nonpositive exponent. -/
lemma rpow_le_rpow_of_nonpos {x y : ENNReal} {z : ℝ} (h : x ≤ y) (hz : z ≤ 0) :
    y ^ z ≤ x ^ z := by
  have h1 : x ^ (-z) ≤ y ^ (-z) := ENNReal.rpow_le_rpow h (by linarith)
  have h2 := ENNReal.inv_le_inv.mpr h1
  rwa [ENNReal.rpow_neg, ENNReal.rpow_neg, inv_inv, inv_inv] at h2

/-- The purely algebraic step shared by the three `sigma`-transfer lemmas:
having compared the two scalar prefactors, the assertion-`D` conclusion
transfers by splitting `X ^ (-(sg - t)) = X ^ (-sg) * X ^ t`. -/
lemma assertionD_conclusion_transfer {A V X vol κ κ₀ a b : ENNReal} {sg t : ℝ}
    (hX0 : X ≠ 0) (hXtop : X ≠ ⊤)
    (hbase : κ₀ * a * A * V * X ^ (-sg) ≤ vol)
    (hscal : κ * b * X ^ t ≤ κ₀ * a) :
    κ * b * A * V * X ^ (-(sg - t)) ≤ vol := by
  have hsplit : X ^ (-(sg - t)) = X ^ (-sg) * X ^ t := by
    rw [← ENNReal.rpow_add _ _ hX0 hXtop]
    ring_nf
  calc
    κ * b * A * V * X ^ (-(sg - t))
        = (κ * b * X ^ t) * A * V * X ^ (-sg) := by rw [hsplit]; ring
    _ ≤ (κ₀ * a) * A * V * X ^ (-sg) := by gcongr
    _ ≤ vol := by simpa [mul_assoc] using hbase

/-- Tail of the two scalar comparisons. -/
lemma scalar_tail {C κ₀ δ X : ENNReal} {t a b c : ℝ} {n : ℕ}
    (hCn0 : C ^ n ≠ 0) (hCntop : C ^ n ≠ ⊤)
    (hδ0 : δ ≠ 0) (hδtop : δ ≠ ⊤) (hδ1 : δ ≤ 1)
    (hXt : X ^ t ≤ C ^ n * δ ^ c) (hab : a ≤ b + c) :
    (κ₀ * (C ^ n)⁻¹) * δ ^ b * X ^ t ≤ κ₀ * δ ^ a := by
  calc
    (κ₀ * (C ^ n)⁻¹) * δ ^ b * X ^ t
        ≤ (κ₀ * (C ^ n)⁻¹) * δ ^ b * (C ^ n * δ ^ c) := by gcongr
    _ = κ₀ * ((C ^ n)⁻¹ * C ^ n) * (δ ^ b * δ ^ c) := by ring
    _ = κ₀ * (δ ^ b * δ ^ c) := by
          rw [ENNReal.inv_mul_cancel hCn0 hCntop, mul_one]
    _ = κ₀ * δ ^ (b + c) := by rw [ENNReal.rpow_add _ _ hδ0 hδtop]
    _ ≤ κ₀ * δ ^ a :=
          mul_le_mul_left' (ENNReal.rpow_le_rpow_of_exponent_ge hδ1 hab) _

/-- Scalar comparison using the upper bound on the currency (`t >= 0`). -/
lemma scalar_le_of_upper {C κ₀ δ X : ENNReal} {η t a b : ℝ} {n : ℕ}
    (hC1 : 1 ≤ C) (hCtop : C ≠ ⊤)
    (hδ0 : δ ≠ 0) (hδtop : δ ≠ ⊤) (hδ1 : δ ≤ 1)
    (ht : 0 ≤ t) (htn : t ≤ n)
    (hX : X ≤ C * δ ^ (-η - 1))
    (hab : a ≤ b + (-η - 1) * t) :
    (κ₀ * (C ^ n)⁻¹) * δ ^ b * X ^ t ≤ κ₀ * δ ^ a := by
  have hC0 : C ≠ 0 := by
    intro h; rw [h] at hC1; simp at hC1
  have hCn0 : C ^ n ≠ 0 := pow_ne_zero _ hC0
  have hCntop : C ^ n ≠ ⊤ := ENNReal.pow_ne_top hCtop
  refine scalar_tail hCn0 hCntop hδ0 hδtop hδ1 ?_ hab
  have h1 : X ^ t ≤ (C * δ ^ (-η - 1)) ^ t := ENNReal.rpow_le_rpow hX ht
  have h2 : (C * δ ^ (-η - 1)) ^ t = C ^ t * δ ^ ((-η - 1) * t) := by
    rw [ENNReal.mul_rpow_of_ne_top hCtop
      (ENNReal.rpow_ne_top_of_ne_zero hδ0 hδtop), ← ENNReal.rpow_mul]
  have h3 : C ^ t ≤ C ^ n := by
    rw [← ENNReal.rpow_natCast C n]
    exact ENNReal.rpow_le_rpow_of_exponent_le hC1 htn
  calc X ^ t ≤ C ^ t * δ ^ ((-η - 1) * t) := by rw [← h2]; exact h1
    _ ≤ C ^ n * δ ^ ((-η - 1) * t) := by gcongr

/-- Scalar comparison using the lower bound on the currency (`t <= 0`). -/
lemma scalar_le_of_lower {C κ₀ δ X : ENNReal} {η t a b : ℝ} {n : ℕ}
    (hC1 : 1 ≤ C) (hCtop : C ≠ ⊤)
    (hδ0 : δ ≠ 0) (hδtop : δ ≠ ⊤) (hδ1 : δ ≤ 1)
    (ht : t ≤ 0) (htn : -t ≤ n)
    (hX : C⁻¹ * δ ^ η ≤ X)
    (hab : a ≤ b + η * t) :
    (κ₀ * (C ^ n)⁻¹) * δ ^ b * X ^ t ≤ κ₀ * δ ^ a := by
  have hC0 : C ≠ 0 := by
    intro h; rw [h] at hC1; simp at hC1
  have hCn0 : C ^ n ≠ 0 := pow_ne_zero _ hC0
  have hCntop : C ^ n ≠ ⊤ := ENNReal.pow_ne_top hCtop
  refine scalar_tail hCn0 hCntop hδ0 hδtop hδ1 ?_ hab
  have h1 : X ^ t ≤ (C⁻¹ * δ ^ η) ^ t := rpow_le_rpow_of_nonpos hX ht
  have h2 : (C⁻¹ * δ ^ η) ^ t = (C ^ t)⁻¹ * δ ^ (η * t) := by
    rw [ENNReal.mul_rpow_of_ne_top (ENNReal.inv_ne_top.mpr hC0)
      (ENNReal.rpow_ne_top_of_ne_zero hδ0 hδtop), ← ENNReal.rpow_mul,
      ENNReal.inv_rpow]
  have h3 : (C ^ t)⁻¹ ≤ C ^ n := by
    rw [← ENNReal.rpow_neg, ← ENNReal.rpow_natCast C n]
    exact ENNReal.rpow_le_rpow_of_exponent_le hC1 htn
  calc X ^ t ≤ (C ^ t)⁻¹ * δ ^ (η * t) := by rw [← h2]; exact h1
    _ ≤ C ^ n * δ ^ (η * t) := by gcongr

/-- Assertion `D` is monotone upward in `sigma`: the currency `X` is bounded
below by `C⁻¹ delta^{eta}`, so raising the exponent `sigma` costs at most
`delta^{eta (sigma' - sigma)}`, which the accuracy budget absorbs.

This is the step "if `D(sigma,omega)` is true for some `sigma`, then so is
`D(sigma',omega)` for all `sigma' >= sigma`" used in the proof of Theorem
`cDAndcEAreTrue` in the source. -/
theorem assertionD_mono_sigma {C : NNReal} (hC1 : 1 ≤ C)
    (hCB : CurrencyBounds.{u} C) {σ σ' ω : ℝ} (hσ : σ ≤ σ') :
    AssertionD.{u} σ ω → AssertionD.{u} σ' ω := by
  have hC1E : (1 : ENNReal) ≤ (C : ENNReal) := by exact_mod_cast hC1
  have hC0 : (0 : NNReal) < C := lt_of_lt_of_le zero_lt_one hC1
  intro hD ε hε
  set d : ℝ := σ' - σ with hd
  have hd0 : 0 ≤ d := by rw [hd]; linarith
  obtain ⟨κ₀, η₀, hκ₀, hη₀, hDall⟩ := hD (ε / 2) (by linarith)
  set η : ℝ := min η₀ (ε / (2 * (d + 1))) with hηdef
  have hη : 0 < η := lt_min hη₀ (by positivity)
  have hηη₀ : η ≤ η₀ := min_le_left _ _
  have hηd : η * d ≤ ε / 2 := by
    have h1 : η ≤ ε / (2 * (d + 1)) := min_le_right _ _
    have hpos : (0 : ℝ) < 2 * (d + 1) := by positivity
    have h2 : η * (2 * (d + 1)) ≤ ε := (le_div_iff₀ hpos).mp h1
    have h3 : η * (2 * (d + 1)) = 2 * (η * d) + 2 * η := by ring
    linarith
  set n : ℕ := ⌈d⌉₊ with hn
  refine ⟨κ₀ * (C ^ n)⁻¹, η, ?_, hη, ?_⟩
  · exact mul_pos hκ₀ (by positivity)
  intro δ hδ ι s T hfamily hdense hm hell
  by_cases hs : s.Nonempty
  · by_cases hδ1 : δ ≤ 1
    · have hδ1R : (δ : ℝ) ≤ 1 := by exact_mod_cast hδ1
      have hδ1E : (δ : ENNReal) ≤ 1 := by exact_mod_cast hδ1
      have hδ0E : (δ : ENNReal) ≠ 0 := ENNReal.coe_ne_zero.mpr hδ.ne'
      have hδtopE : (δ : ENNReal) ≠ ⊤ := ENNReal.coe_ne_top
      have hdense₀ : IsDense s T
          ⟨(δ : ℝ) ^ η₀, Real.rpow_nonneg δ.coe_nonneg η₀⟩ := by
        rw [IsDense] at hdense ⊢
        refine (mul_le_mul_right' ?_ _).trans hdense
        exact_mod_cast
          Real.rpow_le_rpow_of_exponent_ge (NNReal.coe_pos.mpr hδ) hδ1R hηη₀
      have hpow : (δ : ENNReal) ^ (-η) ≤ (δ : ENNReal) ^ (-η₀) :=
        ENNReal.rpow_le_rpow_of_exponent_ge hδ1E (by linarith)
      have hbase := hDall δ hδ s T hfamily hdense₀ (hm.trans hpow) (hell.trans hpow)
      have hlow := hCB.1 hδ hδ1 hη s T hs hfamily hm hell
      rw [wzCurrency] at hlow
      have hV := tubeVolume_pos_and_ne_top hδ
      have hX0 : ((s.card : ENNReal) * (tubeVolume δ) ^ (1 / 2 : ℝ)) ≠ 0 := by
        have := wzCurrency_pos hδ (Finset.card_pos.mpr hs)
        rw [wzCurrency] at this
        exact this.ne'
      have hXtop : ((s.card : ENNReal) * (tubeVolume δ) ^ (1 / 2 : ℝ)) ≠ ⊤ := by
        have := wzCurrency_ne_top (n := s.card) hδ
        rwa [wzCurrency] at this
      have hscal :
          ((κ₀ * (C ^ n)⁻¹ : NNReal) : ENNReal) * (δ : ENNReal) ^ (ω + ε) *
              (((s.card : ENNReal) * (tubeVolume δ) ^ (1 / 2 : ℝ)) ^ (-d)) ≤
            (κ₀ : ENNReal) * (δ : ENNReal) ^ (ω + ε / 2) := by
        have hcast : ((κ₀ * (C ^ n)⁻¹ : NNReal) : ENNReal) =
            (κ₀ : ENNReal) * ((C : ENNReal) ^ n)⁻¹ := by
          push_cast
          rw [ENNReal.coe_inv (by positivity)]
          push_cast
          ring
        rw [hcast]
        refine scalar_le_of_lower (η := η) (t := -d) (n := n) hC1E
          ENNReal.coe_ne_top hδ0E hδtopE hδ1E (by linarith) ?_ hlow ?_
        · simpa using Nat.le_ceil d
        · have : η * (-d) = -(η * d) := by ring
          rw [this]
          linarith
      have hgoal : -σ' = -(σ - (-d)) := by rw [hd]; ring
      rw [hgoal]
      exact assertionD_conclusion_transfer hX0 hXtop hbase hscal
    · have hm1 : 1 ≤ katzTaoConvexWolffConstant s T :=
        one_le_katzTaoConvexWolffConstant_of_nonempty hδ s T hs
      have hδ_gt : (1 : ENNReal) < (δ : ENNReal) := by
        exact_mod_cast lt_of_not_ge hδ1
      have hpow_lt : (δ : ENNReal) ^ (-η) < 1 :=
        ENNReal.rpow_lt_one_of_one_lt_of_neg hδ_gt (by linarith)
      exact ((not_lt_of_ge (hm1.trans hm)) hpow_lt).elim
  · have hs0 : s = ∅ := Finset.not_nonempty_iff_eq_empty.mp hs
    subst hs0
    simp [iUnionShade_empty]

/-- Assertion `D` is closed from above in `sigma`.  The currency `X` is
bounded above by `C delta^{-eta-1}`, so lowering `sigma` by an amount
comparable to the accuracy budget costs at most half of it.

This is the relative closedness of `{sigma : D(sigma,omega)}` used in the
proof of Theorem `cDAndcEAreTrue` in the source. -/
theorem assertionD_of_forall_gt_sigma {C : NNReal} (hC1 : 1 ≤ C)
    (hCB : CurrencyBounds.{u} C) {σ σmax ω : ℝ} (hσ : σ < σmax)
    (hD : ∀ σ', σ < σ' → σ' ≤ σmax → AssertionD.{u} σ' ω) :
    AssertionD.{u} σ ω := by
  have hC1E : (1 : ENNReal) ≤ (C : ENNReal) := by exact_mod_cast hC1
  have hC0 : (0 : NNReal) < C := lt_of_lt_of_le zero_lt_one hC1
  intro ε hε
  set t : ℝ := min (ε / 4) (σmax - σ) with ht
  have ht0 : 0 < t := lt_min (by linarith) (by linarith)
  have htε : t ≤ ε / 4 := min_le_left _ _
  set σ' : ℝ := σ + t with hσ'
  obtain ⟨κ₀, η₀, hκ₀, hη₀, hDall⟩ :=
    hD σ' (by linarith) (by
      have := min_le_right (ε / 4) (σmax - σ)
      rw [hσ', ht]; linarith) (ε / 2) (by linarith)
  set η : ℝ := min η₀ 1 with hηdef
  have hη : 0 < η := lt_min hη₀ zero_lt_one
  have hηη₀ : η ≤ η₀ := min_le_left _ _
  have hη1 : η ≤ 1 := min_le_right _ _
  set n : ℕ := ⌈t⌉₊ with hn
  refine ⟨κ₀ * (C ^ n)⁻¹, η, mul_pos hκ₀ (by positivity), hη, ?_⟩
  intro δ hδ ι s T hfamily hdense hm hell
  by_cases hs : s.Nonempty
  · by_cases hδ1 : δ ≤ 1
    · have hδ1R : (δ : ℝ) ≤ 1 := by exact_mod_cast hδ1
      have hδ1E : (δ : ENNReal) ≤ 1 := by exact_mod_cast hδ1
      have hδ0E : (δ : ENNReal) ≠ 0 := ENNReal.coe_ne_zero.mpr hδ.ne'
      have hδtopE : (δ : ENNReal) ≠ ⊤ := ENNReal.coe_ne_top
      have hdense₀ : IsDense s T
          ⟨(δ : ℝ) ^ η₀, Real.rpow_nonneg δ.coe_nonneg η₀⟩ := by
        rw [IsDense] at hdense ⊢
        refine (mul_le_mul_right' ?_ _).trans hdense
        exact_mod_cast
          Real.rpow_le_rpow_of_exponent_ge (NNReal.coe_pos.mpr hδ) hδ1R hηη₀
      have hpow : (δ : ENNReal) ^ (-η) ≤ (δ : ENNReal) ^ (-η₀) :=
        ENNReal.rpow_le_rpow_of_exponent_ge hδ1E (by linarith)
      have hbase := hDall δ hδ s T hfamily hdense₀ (hm.trans hpow) (hell.trans hpow)
      have hup := hCB.2 hδ hδ1 hη s T hs hfamily hm hell
      rw [wzCurrency] at hup
      have hX0 : ((s.card : ENNReal) * (tubeVolume δ) ^ (1 / 2 : ℝ)) ≠ 0 := by
        have := wzCurrency_pos hδ (Finset.card_pos.mpr hs)
        rw [wzCurrency] at this
        exact this.ne'
      have hXtop : ((s.card : ENNReal) * (tubeVolume δ) ^ (1 / 2 : ℝ)) ≠ ⊤ := by
        have := wzCurrency_ne_top (n := s.card) hδ
        rwa [wzCurrency] at this
      have hscal :
          ((κ₀ * (C ^ n)⁻¹ : NNReal) : ENNReal) * (δ : ENNReal) ^ (ω + ε) *
              (((s.card : ENNReal) * (tubeVolume δ) ^ (1 / 2 : ℝ)) ^ t) ≤
            (κ₀ : ENNReal) * (δ : ENNReal) ^ (ω + ε / 2) := by
        have hcast : ((κ₀ * (C ^ n)⁻¹ : NNReal) : ENNReal) =
            (κ₀ : ENNReal) * ((C : ENNReal) ^ n)⁻¹ := by
          push_cast
          rw [ENNReal.coe_inv (by positivity)]
          push_cast
          ring
        rw [hcast]
        refine scalar_le_of_upper (η := η) (t := t) (n := n) hC1E
          ENNReal.coe_ne_top hδ0E hδtopE hδ1E ht0.le (Nat.le_ceil t) hup ?_
        nlinarith
      have hgoal : -σ = -(σ' - t) := by rw [hσ']; ring
      rw [hgoal]
      exact assertionD_conclusion_transfer hX0 hXtop hbase hscal
    · have hm1 : 1 ≤ katzTaoConvexWolffConstant s T :=
        one_le_katzTaoConvexWolffConstant_of_nonempty hδ s T hs
      have hδ_gt : (1 : ENNReal) < (δ : ENNReal) := by
        exact_mod_cast lt_of_not_ge hδ1
      have hpow_lt : (δ : ENNReal) ^ (-η) < 1 :=
        ENNReal.rpow_lt_one_of_one_lt_of_neg hδ_gt (by linarith)
      exact ((not_lt_of_ge (hm1.trans hm)) hpow_lt).elim
  · have hs0 : s = ∅ := Finset.not_nonempty_iff_eq_empty.mp hs
    subst hs0
    simp [iUnionShade_empty]

/-- The source's "trade an improvement in `omega` for an improvement in
`sigma`" step: since `X <= C delta^{-eta-1}`, a gain `g` in `omega` buys a gain
`g/2` in `sigma`.  (The source uses the cruder bound `#T <~ delta^{-4}` and
obtains `g/4`.) -/
theorem assertionD_sigma_sub_of_omega_sub {C : NNReal} (hC1 : 1 ≤ C)
    (hCB : CurrencyBounds.{u} C) {σ ω g : ℝ} (hg : 0 < g) :
    AssertionD.{u} σ (ω - g) → AssertionD.{u} (σ - g / 2) ω := by
  have hC1E : (1 : ENNReal) ≤ (C : ENNReal) := by exact_mod_cast hC1
  have hC0 : (0 : NNReal) < C := lt_of_lt_of_le zero_lt_one hC1
  intro hD ε hε
  obtain ⟨κ₀, η₀, hκ₀, hη₀, hDall⟩ := hD (ε / 2) (by linarith)
  set η : ℝ := min η₀ 1 with hηdef
  have hη : 0 < η := lt_min hη₀ zero_lt_one
  have hηη₀ : η ≤ η₀ := min_le_left _ _
  have hη1 : η ≤ 1 := min_le_right _ _
  set n : ℕ := ⌈g / 2⌉₊ with hn
  refine ⟨κ₀ * (C ^ n)⁻¹, η, mul_pos hκ₀ (by positivity), hη, ?_⟩
  intro δ hδ ι s T hfamily hdense hm hell
  by_cases hs : s.Nonempty
  · by_cases hδ1 : δ ≤ 1
    · have hδ1R : (δ : ℝ) ≤ 1 := by exact_mod_cast hδ1
      have hδ1E : (δ : ENNReal) ≤ 1 := by exact_mod_cast hδ1
      have hδ0E : (δ : ENNReal) ≠ 0 := ENNReal.coe_ne_zero.mpr hδ.ne'
      have hδtopE : (δ : ENNReal) ≠ ⊤ := ENNReal.coe_ne_top
      have hdense₀ : IsDense s T
          ⟨(δ : ℝ) ^ η₀, Real.rpow_nonneg δ.coe_nonneg η₀⟩ := by
        rw [IsDense] at hdense ⊢
        refine (mul_le_mul_right' ?_ _).trans hdense
        exact_mod_cast
          Real.rpow_le_rpow_of_exponent_ge (NNReal.coe_pos.mpr hδ) hδ1R hηη₀
      have hpow : (δ : ENNReal) ^ (-η) ≤ (δ : ENNReal) ^ (-η₀) :=
        ENNReal.rpow_le_rpow_of_exponent_ge hδ1E (by linarith)
      have hbase := hDall δ hδ s T hfamily hdense₀ (hm.trans hpow) (hell.trans hpow)
      have hup := hCB.2 hδ hδ1 hη s T hs hfamily hm hell
      rw [wzCurrency] at hup
      have hX0 : ((s.card : ENNReal) * (tubeVolume δ) ^ (1 / 2 : ℝ)) ≠ 0 := by
        have := wzCurrency_pos hδ (Finset.card_pos.mpr hs)
        rw [wzCurrency] at this
        exact this.ne'
      have hXtop : ((s.card : ENNReal) * (tubeVolume δ) ^ (1 / 2 : ℝ)) ≠ ⊤ := by
        have := wzCurrency_ne_top (n := s.card) hδ
        rwa [wzCurrency] at this
      have hscal :
          ((κ₀ * (C ^ n)⁻¹ : NNReal) : ENNReal) * (δ : ENNReal) ^ (ω + ε) *
              (((s.card : ENNReal) * (tubeVolume δ) ^ (1 / 2 : ℝ)) ^ (g / 2)) ≤
            (κ₀ : ENNReal) * (δ : ENNReal) ^ (ω - g + ε / 2) := by
        have hcast : ((κ₀ * (C ^ n)⁻¹ : NNReal) : ENNReal) =
            (κ₀ : ENNReal) * ((C : ENNReal) ^ n)⁻¹ := by
          push_cast
          rw [ENNReal.coe_inv (by positivity)]
          push_cast
          ring
        rw [hcast]
        refine scalar_le_of_upper (η := η) (t := g / 2) (n := n) hC1E
          ENNReal.coe_ne_top hδ0E hδtopE hδ1E (by linarith) (Nat.le_ceil _) hup ?_
        nlinarith
      have hgoal : -(σ - g / 2) = -(σ - g / 2) := rfl
      have hbase' :
          (κ₀ : ENNReal) * (δ : ENNReal) ^ (ω - g + ε / 2) * (s.card : ENNReal) *
              tubeVolume δ *
              (((s.card : ENNReal) * (tubeVolume δ) ^ (1 / 2 : ℝ)) ^ (-σ)) ≤
            volume (ShadedBody.iUnionShade s fun i => (T i).toShadedBody) := by
        simpa only [show ω - g + ε / 2 = ω - g + ε / 2 from rfl] using hbase
      exact assertionD_conclusion_transfer hX0 hXtop hbase' hscal
    · have hm1 : 1 ≤ katzTaoConvexWolffConstant s T :=
        one_le_katzTaoConvexWolffConstant_of_nonempty hδ s T hs
      have hδ_gt : (1 : ENNReal) < (δ : ENNReal) := by
        exact_mod_cast lt_of_not_ge hδ1
      have hpow_lt : (δ : ENNReal) ^ (-η) < 1 :=
        ENNReal.rpow_lt_one_of_one_lt_of_neg hδ_gt (by linarith)
      exact ((not_lt_of_ge (hm1.trans hm)) hpow_lt).elim
  · have hs0 : s = ∅ := Finset.not_nonempty_iff_eq_empty.mp hs
    subst hs0
    simp [iUnionShade_empty]

/-- The `sigma`-descent of the source proof of Theorem `cDAndcEAreTrue`:
the set of admissible `sigma` in `[0,2/3]` is an up-set (`assertionD_mono_sigma`),
relatively closed (`assertionD_of_forall_gt_sigma`) and relatively open
(`hstep`), hence all of `[0,2/3]`; in particular it contains `0`.

`hstep` is only ever needed at a *strictly positive* `sigma`: if some member of
the admissible set were `0` the goal would already be in hand, so under the
`by_contra` hypothesis every member is positive (`hSpos`).  This is what makes
the source's own restriction `sigma in (0,2/3]` --- carried by every lemma of
the supporting chain --- sufficient, and it is why no separate `sigma = 0`
endpoint obligation is needed. -/
theorem assertionD_zero_of_descent {C : NNReal} (hC1 : 1 ≤ C)
    (hCB : CurrencyBounds.{u} C) {ω : ℝ}
    (hbase : ∃ σ₀ : ℝ, 0 ≤ σ₀ ∧ σ₀ ≤ 2 / 3 ∧ AssertionD.{u} σ₀ ω)
    (hstep : ∀ σ : ℝ, 0 < σ → σ ≤ 2 / 3 → AssertionD.{u} σ ω →
      ∃ c : ℝ, 0 < c ∧ AssertionD.{u} (σ - c) ω) :
    AssertionD.{u} 0 ω := by
  by_contra hzero
  set S : Set ℝ := {x : ℝ | 0 ≤ x ∧ x ≤ 2 / 3 ∧ AssertionD.{u} x ω} with hS
  obtain ⟨σ₀, hσ₀0, hσ₀1, hσ₀D⟩ := hbase
  have hSne : S.Nonempty := ⟨σ₀, hσ₀0, hσ₀1, hσ₀D⟩
  have hSbd : BddBelow S := ⟨0, fun x hx => hx.1⟩
  -- under `hzero`, no member of `S` is `0`, so the descent step is never needed at `0`
  have hSpos : ∀ x ∈ S, 0 < x := fun x hx =>
    lt_of_le_of_ne hx.1 (fun h => hzero (by rw [h]; exact hx.2.2))
  -- descending one step from any member either finishes or produces a smaller member
  have hdown : ∀ x ∈ S, ∃ y ∈ S, y < x := by
    intro x hx
    obtain ⟨c, hc, hDc⟩ := hstep x (hSpos x hx) hx.2.1 hx.2.2
    by_cases hxc : 0 ≤ x - c
    · exact ⟨x - c, ⟨hxc, by linarith [hx.2.1], hDc⟩, by linarith⟩
    · exact absurd (assertionD_mono_sigma hC1 hCB (by linarith : x - c ≤ 0) hDc) hzero
  set m : ℝ := sInf S with hm
  have hm0 : 0 ≤ m := le_csInf hSne (fun x hx => hx.1)
  have hmle : m ≤ σ₀ := csInf_le hSbd ⟨hσ₀0, hσ₀1, hσ₀D⟩
  -- `m < 2/3`
  obtain ⟨y, hyS, hyx⟩ := hdown σ₀ ⟨hσ₀0, hσ₀1, hσ₀D⟩
  have hm23 : m < 2 / 3 := lt_of_le_of_lt (csInf_le hSbd hyS) (by linarith [hyS.2.1])
  -- everything strictly above `m` is admissible
  have hgt : ∀ σ', m < σ' → σ' ≤ 2 / 3 → AssertionD.{u} σ' ω := by
    intro σ' hlt _
    obtain ⟨x, hxS, hxlt⟩ := exists_lt_of_csInf_lt hSne hlt
    exact assertionD_mono_sigma hC1 hCB hxlt.le hxS.2.2
  have hmD : AssertionD.{u} m ω :=
    assertionD_of_forall_gt_sigma hC1 hCB hm23 hgt
  obtain ⟨z, hzS, hzlt⟩ := hdown m ⟨hm0, hm23.le, hmD⟩
  exact absurd (csInf_le hSbd hzS) (not_le_of_gt hzlt)

/-! ### The upper currency bound, proved -/

/-- Volume of the closed unit ball of `Space3`, as a positive finite number. -/
lemma volume_unitBall_ne_top : volume (Metric.closedBall (0 : Space3) 1) ≠ ⊤ :=
  measure_closedBall_lt_top.ne

lemma volume_unitBall_ne_zero : volume (Metric.closedBall (0 : Space3) 1) ≠ 0 := by
  have h1 : (0 : ENNReal) < volume (Metric.ball (0 : Space3) 1) :=
    Metric.measure_ball_pos volume 0 one_pos
  exact (h1.trans_le (measure_mono Metric.ball_subset_closedBall)).ne'

/-- The Katz--Tao convex Wolff constant applied to the unit ball bounds the
total volume of the family. -/
lemma card_mul_tubeVolume_le {δ : NNReal} (hδ : 0 < δ) {ι : Type u} (s : Finset ι)
    (T : ι → ShadedTube δ Space3)
    (hball : ∀ i ∈ s, (T i).carrier ⊆ Metric.closedBall (0 : Space3) 1)
    {m : ENNReal} (hm : katzTaoConvexWolffConstant s T ≤ m) :
    (s.card : ENNReal) * tubeVolume δ ≤
      m * volume (Metric.closedBall (0 : Space3) 1) := by
  have hV := tubeVolume_pos_and_ne_top hδ
  have hBtop := volume_unitBall_ne_top
  have hB0 := volume_unitBall_ne_zero
  let W : ConvexTestSet :=
    ⟨Metric.closedBall (0 : Space3) 1, convex_closedBall _ _⟩
  have hfilter : (@Finset.filter ι (fun i => (T i).carrier ⊆ W.carrier)
      (Classical.decPred _) s) = s :=
    @Finset.filter_true_of_mem ι (fun i => (T i).carrier ⊆ W.carrier)
      (Classical.decPred _) s (fun i hi => hball i hi)
  have hq : (s.card : ENNReal) * tubeVolume δ *
      (volume (Metric.closedBall (0 : Space3) 1))⁻¹ ≤
      katzTaoConvexWolffConstant s T := by
    rw [katzTaoConvexWolffConstant]
    refine le_sInf ?_
    rintro C ⟨-, hC⟩
    have h := hC W
    rw [hfilter] at h
    have hWvol : volume W.carrier = volume (Metric.closedBall (0 : Space3) 1) := rfl
    rw [hWvol] at h
    calc (s.card : ENNReal) * tubeVolume δ *
          (volume (Metric.closedBall (0 : Space3) 1))⁻¹
        ≤ (C * volume (Metric.closedBall (0 : Space3) 1) * (tubeVolume δ)⁻¹) *
            tubeVolume δ * (volume (Metric.closedBall (0 : Space3) 1))⁻¹ := by
          gcongr
      _ = C * (volume (Metric.closedBall (0 : Space3) 1) *
            (volume (Metric.closedBall (0 : Space3) 1))⁻¹) *
            ((tubeVolume δ)⁻¹ * tubeVolume δ) := by ring
      _ = C := by
          rw [ENNReal.mul_inv_cancel hB0 hBtop,
            ENNReal.inv_mul_cancel hV.1.ne' hV.2, mul_one, mul_one]
  calc (s.card : ENNReal) * tubeVolume δ
      = ((s.card : ENNReal) * tubeVolume δ *
          (volume (Metric.closedBall (0 : Space3) 1))⁻¹) *
          volume (Metric.closedBall (0 : Space3) 1) := by
        rw [mul_assoc, ENNReal.inv_mul_cancel hB0 hBtop, mul_one]
    _ ≤ m * volume (Metric.closedBall (0 : Space3) 1) := by
        gcongr
        exact hq.trans hm

/-- `|T|^{1/2} >= c^{1/2} delta`, from the tube volume lower bound. -/
lemma sqrt_tubeVolume_ge {δ : NNReal} :
    ((Tube.le_volume.c 3 : NNReal) : ENNReal) ^ (1 / 2 : ℝ) * (δ : ENNReal) ≤
      (tubeVolume δ) ^ (1 / 2 : ℝ) := by
  have hlow : ((Tube.le_volume.c 3 : NNReal) : ENNReal) * (δ : ENNReal) ^ (3 - 1) ≤
      tubeVolume δ := by
    simpa [tubeVolume] using Tube.le_volume (modelTube δ)
  have hmono := ENNReal.rpow_le_rpow hlow (by norm_num : (0:ℝ) ≤ 1 / 2)
  refine le_trans (le_of_eq ?_) hmono
  rw [ENNReal.mul_rpow_of_ne_top ENNReal.coe_ne_top
    (ENNReal.pow_ne_top ENNReal.coe_ne_top)]
  congr 1
  rw [show (3 - 1 : ℕ) = 2 from rfl, ← ENNReal.rpow_natCast (δ : ENNReal) 2,
    ← ENNReal.rpow_mul]
  norm_num

/-- The upper currency bound of Section 1.3 of the source, proved. -/
theorem exists_currencyUpperBound :
    ∃ C : NNReal, 1 ≤ C ∧ CurrencyUpperBound.{u} C := by
  have hc0 : (0 : NNReal) < Tube.le_volume.c 3 := Tube.le_volume.c_pos 3
  set cs : ENNReal := ((Tube.le_volume.c 3 : NNReal) : ENNReal) ^ (1 / 2 : ℝ) with hcs
  have hcs0 : cs ≠ 0 := by
    rw [hcs]
    exact (ENNReal.rpow_pos (by exact_mod_cast hc0) ENNReal.coe_ne_top).ne'
  have hcstop : cs ≠ ⊤ := by
    rw [hcs]
    exact ENNReal.rpow_ne_top_of_ne_zero (by exact_mod_cast hc0.ne') ENNReal.coe_ne_top
  set Bc : ENNReal := volume (Metric.closedBall (0 : Space3) 1) * cs⁻¹ with hBc
  have hBctop : Bc ≠ ⊤ :=
    ENNReal.mul_ne_top volume_unitBall_ne_top (ENNReal.inv_ne_top.mpr hcs0)
  refine ⟨max 1 Bc.toNNReal, le_max_left _ _, ?_⟩
  have hBcle : Bc ≤ ((max 1 Bc.toNNReal : NNReal) : ENNReal) := by
    have : (Bc.toNNReal : ENNReal) = Bc := ENNReal.coe_toNNReal hBctop
    rw [← this]
    exact_mod_cast le_max_right (1 : NNReal) Bc.toNNReal
  intro δ hδ hδ1 η hη ι s T hs hfamily hm _hell
  have hV := tubeVolume_pos_and_ne_top hδ
  have hδ0E : (δ : ENNReal) ≠ 0 := ENNReal.coe_ne_zero.mpr hδ.ne'
  have hδtopE : (δ : ENNReal) ≠ ⊤ := ENNReal.coe_ne_top
  have hVhalf0 : (tubeVolume δ) ^ (1 / 2 : ℝ) ≠ 0 :=
    (ENNReal.rpow_pos hV.1 hV.2).ne'
  have hVhalftop : (tubeVolume δ) ^ (1 / 2 : ℝ) ≠ ⊤ :=
    ENNReal.rpow_ne_top_of_ne_zero hV.1.ne' hV.2
  -- rewrite the currency as `(#T * |T|) * (|T|^{1/2})⁻¹`
  have hsplit : wzCurrency δ s.card =
      ((s.card : ENNReal) * tubeVolume δ) * ((tubeVolume δ) ^ (1 / 2 : ℝ))⁻¹ := by
    have hVV : tubeVolume δ = (tubeVolume δ) ^ (1 / 2 : ℝ) * (tubeVolume δ) ^ (1 / 2 : ℝ) := by
      rw [← ENNReal.rpow_add _ _ hV.1.ne' hV.2]
      norm_num
    rw [wzCurrency]
    calc (s.card : ENNReal) * (tubeVolume δ) ^ (1 / 2 : ℝ)
        = (s.card : ENNReal) * ((tubeVolume δ) ^ (1 / 2 : ℝ) *
            ((tubeVolume δ) ^ (1 / 2 : ℝ) * ((tubeVolume δ) ^ (1 / 2 : ℝ))⁻¹)) := by
          rw [ENNReal.mul_inv_cancel hVhalf0 hVhalftop, mul_one]
      _ = ((s.card : ENNReal) * ((tubeVolume δ) ^ (1 / 2 : ℝ) *
            (tubeVolume δ) ^ (1 / 2 : ℝ))) * ((tubeVolume δ) ^ (1 / 2 : ℝ))⁻¹ := by ring
      _ = _ := by rw [← hVV]
  have hcard := card_mul_tubeVolume_le hδ s T hfamily.1 hm
  have hinv : ((tubeVolume δ) ^ (1 / 2 : ℝ))⁻¹ ≤ cs⁻¹ * (δ : ENNReal)⁻¹ := by
    have h1 : cs * (δ : ENNReal) ≤ (tubeVolume δ) ^ (1 / 2 : ℝ) := sqrt_tubeVolume_ge
    have := ENNReal.inv_le_inv.mpr h1
    rwa [ENNReal.mul_inv (Or.inl hcs0) (Or.inl hcstop)] at this
  calc wzCurrency δ s.card
      = ((s.card : ENNReal) * tubeVolume δ) * ((tubeVolume δ) ^ (1 / 2 : ℝ))⁻¹ := hsplit
    _ ≤ ((δ : ENNReal) ^ (-η) * volume (Metric.closedBall (0 : Space3) 1)) *
          (cs⁻¹ * (δ : ENNReal)⁻¹) := by gcongr
    _ = Bc * ((δ : ENNReal) ^ (-η) * (δ : ENNReal) ^ (-1 : ℝ)) := by
        rw [hBc, ENNReal.rpow_neg_one]
        ring
    _ = Bc * (δ : ENNReal) ^ (-η - 1) := by
        rw [← ENNReal.rpow_add _ _ hδ0E hδtopE]
        ring_nf
    _ ≤ ((max 1 Bc.toNNReal : NNReal) : ENNReal) * (δ : ENNReal) ^ (-η - 1) := by
        gcongr

/-- Both currency bounds weaken as the constant grows. -/
theorem CurrencyLowerBound.mono {C C' : NNReal} (h : C ≤ C')
    (hC : CurrencyLowerBound.{u} C) : CurrencyLowerBound.{u} C' := by
  intro δ hδ hδ1 η hη ι s T hs hfamily hm hell
  refine le_trans ?_ (hC hδ hδ1 hη s T hs hfamily hm hell)
  gcongr

theorem CurrencyUpperBound.mono {C C' : NNReal} (h : C ≤ C')
    (hC : CurrencyUpperBound.{u} C) : CurrencyUpperBound.{u} C' := by
  intro δ hδ hδ1 η hη ι s T hs hfamily hm hell
  refine le_trans (hC hδ hδ1 hη s T hs hfamily hm hell) ?_
  gcongr

end

end Kakeya.WangZahl
