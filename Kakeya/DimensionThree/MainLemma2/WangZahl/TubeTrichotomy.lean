/-
Wang--Zahl Definition `convexAtEveryScaleFromAssouadPaper` (:2257) and
Proposition `tubeTricotProp` (:2284), the factoring trichotomy that drives the
proof of Lemma `weakerPropEquivDE` (:2307).

Source: `blueprint/src/WZ2/250224e_K3.tex`, Section `cEIffcDSec`.

Both statements quantify over the *rescaled* subfamilies `T^{T_rho}`,
`T_tau^{T_rho}` and `T^W`; the rescaling map `phi_W` and the Wolff constants of
a general convex family that they need are in `WangZahl/Rescaling.lean`.
-/
module

public import Kakeya.DimensionThree.MainLemma2.WangZahl.Rescaling
public import Kakeya.DimensionThree.MainLemma2.WangZahl.WZMultiScale

@[expose] public section

open MeasureTheory

namespace Kakeya.WangZahl

noncomputable section

universe u

/-! ### Covers and factoring

Wang--Zahl Definition `defnOfCover` (:919) and Definition :1001/:1004.  A
family of convex sets is presented here as a family of `Frame3`s: every convex
set the source factors through is a box, and its frame is exactly the data
`phi_W` is built from.
-/

/-- `U < W`, Wang--Zahl Definition `defnOfCover`(A) (:922): every member of the
family is contained in some member of the cover. -/
def IsCoverOf {ι κ : Type u} (s : Finset ι) (U : ι → Set Space3)
    (w : Finset κ) (W : κ → Set Space3) : Prop :=
  ∀ i ∈ s, ∃ k ∈ w, U i ⊆ W k

/-- Wang--Zahl Definition :1001(A) for the Frostman Convex Wolff axioms: `W`
covers `U` and `W` itself satisfies those axioms with error `K`. -/
def FactorsFromAboveFCW {ι κ : Type u} (s : Finset ι) (U : ι → Set Space3)
    (w : Finset κ) (F : κ → Frame3) (K : ENNReal) : Prop :=
  IsCoverOf s U w (fun k => (F k).box) ∧
    frostmanConvexWolffConstantSets w (fun k => (F k).box) ≤ K

/-- Wang--Zahl Definition :1004(B) for the Frostman Convex Wolff axioms: `W`
covers `U` and each *rescaled* set `U^W` satisfies those axioms with error
`K`.  This is the clause that needs `phi_W`. -/
def FactorsFromBelowFCW {ι κ : Type u} (s : Finset ι) (U : ι → Set Space3)
    (w : Finset κ) (F : κ → Frame3) (K : ENNReal) : Prop :=
  IsCoverOf s U w (fun k => (F k).box) ∧
    ∀ k ∈ w, frostmanConvexWolffConstantSets
        (subfamilyIn s U (F k).box) (rescaleCarriers (F k) U) ≤ K

/-! ### The Frostman Convex Wolff Axioms at every scale -/

/-- **Wang--Zahl Definition `convexAtEveryScaleFromAssouadPaper`**
(`blueprint/src/WZ2/250224e_K3.tex:2257`, Definition 2.12 of [WZ23]).

*Let `K >= 1`, `delta > 0`.  A set `T` of `delta`-tubes in `R^3` satisfies the
Frostman Convex Wolff Axioms at every scale with error `K` if the tubes in `T`
are essentially distinct, and for every `rho_0 in [delta,1]` there exists
`rho in [rho_0, K rho_0)` and a set of `rho`-tubes `T_rho` such that*

* *(i) `T_rho` is a `K`-balanced partitioning cover of `T`;*
* *(ii) for each `T_rho in T_rho`, `T^{T_rho}` satisfies the Frostman Convex
  Wolff Axioms with error `K`.*

Clause (i) is `BalancedNodeCover`, the project's encoding of a `K`-balanced
partitioning cover (the one used by `KatzTaoEveryScale`, :4734).  Clause (ii)
is the new content: `T^{T_rho}` is the family `T[T_rho]` of tubes of `T`
contained in the parent tube, pushed forward by `phi_{T_rho}`, and the constant
taken of it is `CFC` for a *general* convex family
(`frostmanConvexWolffConstantSets`), because `phi_{T_rho}` of a `delta`-tube is
not a tube.

Contrast with `KatzTaoEveryScale` (:4734), whose clause (ii) bounds
`CKT(T_rho)` on the *parent* family instead: the source distinguishes the two
at :4729, and `stickyKakeyaEveryScale` is the Katz--Tao one. -/
def ConvexAtEveryScale {δ : NNReal} {ι : Type u} (s : Finset ι)
    (T : ι → ShadedTube δ Space3) (K : NNReal) : Prop :=
  (s : Set ι).Pairwise (fun i j => IsEssentiallyDistinct (T i).carrier (T j).carrier) ∧
    ∀ ρ₀ : NNReal, δ ≤ ρ₀ → ρ₀ ≤ 1 →
      ∃ ρ : NNReal, ∃ hρ : 0 < ρ, ρ₀ ≤ ρ ∧ ρ < K * ρ₀ ∧
        ∃ B : BalancedNodeCover (rho := ρ) s (fun i => (T i).toTube) K,
          ∀ j ∈ B.parent,
            frostmanConvexWolffConstantSets
                (subfamilyIn s (fun i => (T i).carrier) (B.parentTube j).carrier)
                (rescaleCarriers (tubeFrame3 hρ (B.parentTube j))
                  (fun i => (T i).carrier))
              ≤ (K : ENNReal)

/-! ### The three conclusions of the trichotomy

The source writes the bounds of clauses (B) and (C) with the implicit-constant
relations `<~` and `<~~_delta` (:794).  Both are made explicit here by a single
constant `C >= 1`, quantified once alongside `eta` and independent of `delta`
and of the family; for `<~~_delta A <= B` (which unfolds to *for all `eps > 0`
there is `K_eps` with `A <= K_eps delta^{-eps} B`*) the accuracy is taken at
`eps = eta`, giving the exponent `-2 eta` in clause (B)(iii).
-/

/-- **Conclusion (B)** of Wang--Zahl Proposition `tubeTricotProp` (:2288):
a two-scale factorisation `delta <= tau < rho <= 1` with `tau <= delta^{z1/5}
rho`, a balanced partitioning cover `T_tau` of `T` and a balanced partitioning
cover `T_rho` of `T_tau`, such that

* (i)   `CFC(T^{T_tau}) <~ delta^{-z2}` for each `T_tau in T_tau`;
* (ii)  `CKT(T_tau^{T_rho}) <~ delta^{-z2}` and
        `#T_tau^{T_rho} >= delta^{z2} (rho/tau)^2` for each `T_rho in T_rho`;
* (iii) `CFC(T_rho) <~~_delta delta^{-eta}`. -/
def TrichotomyB {δ : NNReal} {ι : Type u} (ζ₁ ζ₂ η : ℝ) (C : NNReal)
    (s : Finset ι) (T : ι → ShadedTube δ Space3) : Prop :=
  ∃ τ ρ : NNReal, ∃ hτ : 0 < τ, ∃ hρ : 0 < ρ,
    δ ≤ τ ∧ τ < ρ ∧ ρ ≤ 1 ∧ (τ : ℝ) ≤ (δ : ℝ) ^ (ζ₁ / 5) * (ρ : ℝ) ∧
      ∃ Bτ : BalancedNodeCover (rho := τ) s (fun i => (T i).toTube) C,
        ∃ Bρ : BalancedNodeCover (rho := ρ) Bτ.parent Bτ.parentTube C,
          (∀ j ∈ Bτ.parent,
              frostmanConvexWolffConstantSets
                  (subfamilyIn s (fun i => (T i).carrier) (Bτ.parentTube j).carrier)
                  (rescaleCarriers (tubeFrame3 hτ (Bτ.parentTube j))
                    (fun i => (T i).carrier))
                ≤ (C : ENNReal) * (δ : ENNReal) ^ (-ζ₂)) ∧
          (∀ l ∈ Bρ.parent,
              katzTaoConvexWolffConstantSets
                  (subfamilyIn Bτ.parent (fun j => (Bτ.parentTube j).carrier)
                    (Bρ.parentTube l).carrier)
                  (rescaleCarriers (tubeFrame3 hρ (Bρ.parentTube l))
                    (fun j => (Bτ.parentTube j).carrier))
                ≤ (C : ENNReal) * (δ : ENNReal) ^ (-ζ₂) ∧
              (δ : ENNReal) ^ ζ₂ * ((ρ : ENNReal) / (τ : ENNReal)) ^ (2 : ℕ) ≤
                ((subfamilyIn Bτ.parent (fun j => (Bτ.parentTube j).carrier)
                  (Bρ.parentTube l).carrier).card : ENNReal)) ∧
          frostmanConvexWolffConstantSets Bρ.parent
              (fun l => (Bρ.parentTube l).carrier)
            ≤ (C : ENNReal) * (δ : ENNReal) ^ (-2 * η)

/-- **Conclusion (C)** of Wang--Zahl Proposition `tubeTricotProp` (:2297):
scales `delta <= a < b <= 1` with `a <= delta^{z2/100} b` and a set `W` of
`a x b x 1` prisms satisfying the hypotheses of Proposition `aLLbProp`(B) --
`W` factors `T` from above and from below with respect to the Frostman Convex
Wolff Axioms with error `O(delta^{-z3})` -- and with
`CKT(W[N_b(W)]) <~ delta^{-z3}` for each `W in W`.

An `a x b x 1` prism is the box of a `Frame3` with half-widths
`a/2, b/2, 1/2` (the project's `Prism3D` stores half-widths, so its
`Prism3D (a/2) (b/2) (1/2)` has dimensions `a x b x 1`; see
`carrier_eq_prismFrame3_box`). -/
def TrichotomyC {δ : NNReal} {ι : Type u} (ζ₂ ζ₃ : ℝ) (C : NNReal)
    (s : Finset ι) (T : ι → ShadedTube δ Space3) : Prop :=
  ∃ a b : NNReal, ∃ _ha : 0 < a,
    δ ≤ a ∧ a < b ∧ b ≤ 1 ∧ (a : ℝ) ≤ (δ : ℝ) ^ (ζ₂ / 100) * (b : ℝ) ∧
      ∃ (κ : Type u) (w : Finset κ) (F : κ → Frame3),
        (∀ k ∈ w, (F k).len = ![(a : ℝ) / 2, (b : ℝ) / 2, 1 / 2]) ∧
        FactorsFromAboveFCW s (fun i => (T i).carrier) w F
          ((C : ENNReal) * (δ : ENNReal) ^ (-ζ₃)) ∧
        FactorsFromBelowFCW s (fun i => (T i).carrier) w F
          ((C : ENNReal) * (δ : ENNReal) ^ (-ζ₃)) ∧
        ∀ k ∈ w,
          katzTaoConvexWolffConstantSets
              (subfamilyIn w (fun k' => (F k').box)
                (Metric.cthickening (b : ℝ) ((F k).box)))
              (fun k' => (F k').box)
            ≤ (C : ENNReal) * (δ : ENNReal) ^ (-ζ₃)

/-! ### The factoring trichotomy -/



/-! ### Non-vacuity

A definition is worthless if nothing satisfies it, and a hypothesis bundle that
is unsatisfiable makes everything under it vacuously true while `#print axioms`
sees nothing.  The three certificates below are the analogue of
`assertionTE_two` for this file.
-/

/-- If every member of a family has volume at least `v > 0`, then the family's
Frostman convex Wolff constant is at most `v⁻¹`.  (Any test set containing one
member of the family already has volume at least `v`.) -/
theorem frostmanConvexWolffConstantSets_le_inv {ι : Type u} (s : Finset ι)
    (U : ι → Set Space3) {v : ENNReal} (hv0 : v ≠ 0) (hvtop : v ≠ ⊤)
    (h : ∀ i ∈ s, v ≤ volume (U i)) :
    frostmanConvexWolffConstantSets s U ≤ v⁻¹ := by
  refine sInf_le ⟨ENNReal.inv_pos.mpr hvtop, fun W => ?_⟩
  rcases Finset.eq_empty_or_nonempty (subfamilyIn s U W.carrier) with he | ⟨i₀, hi₀⟩
  · simp [he]
  · have hmem := mem_subfamilyIn.mp hi₀
    have hle : v ≤ volume W.carrier := (h i₀ hmem.1).trans (measure_mono hmem.2)
    have h1 : (1 : ENNReal) ≤ v⁻¹ * volume W.carrier := by
      calc (1 : ENNReal) = v⁻¹ * v := (ENNReal.inv_mul_cancel hv0 hvtop).symm
        _ ≤ v⁻¹ * volume W.carrier := by gcongr
    calc ∑ i ∈ subfamilyIn s U W.carrier, volume (U i)
        ≤ ∑ i ∈ s, volume (U i) :=
          Finset.sum_le_sum_of_subset (subfamilyIn_subset s U _)
      _ = 1 * ∑ i ∈ s, volume (U i) := (one_mul _).symm
      _ ≤ v⁻¹ * volume W.carrier * ∑ i ∈ s, volume (U i) := by gcongr

/-- The model `delta`-tube with the trivial shading. -/
def witnessTube (δ : NNReal) : ShadedTube δ Space3 where
  toTube := modelTube δ
  shade := (modelTube δ).carrier
  measurableSet_shade := (modelTube δ).isCompact.isClosed.measurableSet
  shade_subset := subset_rfl

@[simp] theorem witnessTube_carrier (δ : NNReal) :
    (witnessTube δ).carrier = (modelTube δ).carrier := rfl

/-- The model tubes are nested in their radius. -/
theorem modelTube_carrier_mono {δ ρ : NNReal} (h : δ ≤ ρ) :
    (modelTube δ).carrier ⊆ (modelTube ρ).carrier := by
  rw [(modelTube δ).carrier_eq, (modelTube ρ).carrier_eq]
  refine Set.iUnion₂_mono fun z _ => Metric.closedBall_subset_closedBall ?_
  exact_mod_cast h

/-- The rescaling of a `delta`-tube inside a `rho`-tube (`rho <= 1`) still has
volume at least `(2/3) |T|`: the frame half-widths are `rho, rho, 1/2 + rho`,
all at most `3/2`, so `phi` never shrinks by more than that factor. -/
theorem volume_rescale_ge {δ ρ : NNReal} (hρ0 : 0 < ρ) (hρ1 : ρ ≤ 1)
    (P : Tube ρ Space3) {A : Set Space3} (hA : volume A = tubeVolume δ) :
    ENNReal.ofReal (2 / 3) * tubeVolume δ ≤
      volume ((tubeFrame3 hρ0 P).map '' A) := by
  have hρ0' : (0 : ℝ) < (ρ : ℝ) := by exact_mod_cast hρ0
  have hρ1' : (ρ : ℝ) ≤ 1 := by exact_mod_cast hρ1
  rw [Frame3.volume_image_map, hA]
  gcongr
  rw [Fin.prod_univ_three]
  have h0 : (1 : ℝ) ≤ ((tubeFrame3 hρ0 P).len 0)⁻¹ := by
    rw [tubeFrame3_len]
    simp only [Matrix.cons_val_zero]
    rw [le_inv_comm₀ one_pos hρ0']
    simpa using hρ1'
  have h1 : (1 : ℝ) ≤ ((tubeFrame3 hρ0 P).len 1)⁻¹ := by
    rw [tubeFrame3_len]
    simp only [Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_zero]
    rw [le_inv_comm₀ one_pos hρ0']
    simpa using hρ1'
  have h2 : (2 / 3 : ℝ) ≤ ((tubeFrame3 hρ0 P).len 2)⁻¹ := by
    rw [tubeFrame3_len]
    simp only [Matrix.cons_val]
    rw [le_inv_comm₀ (by norm_num) (by linarith),
      show ((2 : ℝ) / 3)⁻¹ = 3 / 2 by norm_num]
    linarith
  calc (2 / 3 : ℝ) = 1 * 1 * (2 / 3) := by ring
    _ ≤ ((tubeFrame3 hρ0 P).len 0)⁻¹ * ((tubeFrame3 hρ0 P).len 1)⁻¹ *
          ((tubeFrame3 hρ0 P).len 2)⁻¹ := by
        gcongr <;> norm_num

/-- The one-tube balanced partitioning cover at scale `rho`: a single parent
tube, the `rho`-dilate of the same model segment. -/
def witnessCover {δ ρ : NNReal} (h : δ ≤ ρ) {K : NNReal} (hK : 1 ≤ K) :
    BalancedNodeCover (rho := ρ) (Finset.univ : Finset PUnit.{u + 1})
      (fun _ => (witnessTube δ).toTube) K where
  parent := Finset.univ
  assign := fun _ => PUnit.unit
  part := fun j => Tube.coverClass Finset.univ (fun _ => PUnit.unit) j
  part_eq := fun _ => rfl
  mem_part_iff := fun i j => by
    simp [Tube.coverClass, Subsingleton.elim PUnit.unit j]
  parentTube := fun _ => modelTube ρ
  branch := 1
  assign_mem := fun _ _ => Finset.mem_univ _
  leaf_le_parent := fun _ _ => modelTube_carrier_mono h
  parentTube_injOn := fun a _ b _ _ => Subsingleton.elim a b
  card_class_le := fun j _ => by
    have hc : (Tube.coverClass (Finset.univ : Finset PUnit.{u + 1})
        (fun _ => PUnit.unit) j) = Finset.univ := by
      ext i
      simp [Tube.coverClass, Subsingleton.elim PUnit.unit j]
    rw [hc]
    simpa using hK
  le_card_class := fun j _ => by
    have hc : (Tube.coverClass (Finset.univ : Finset PUnit.{u + 1})
        (fun _ => PUnit.unit) j) = Finset.univ := by
      ext i
      simp [Tube.coverClass, Subsingleton.elim PUnit.unit j]
    rw [hc]
    simpa using hK

/-- **Non-vacuity of Definition `convexAtEveryScaleFromAssouadPaper`**
(`ConvexAtEveryScale`, :2257).

The single-tube family satisfies the Frostman Convex Wolff Axioms at every
scale, with an error constant depending only on `delta`.  This is a *nonempty*
witness: without it, Conclusion (A) of `tubeTricotProp` would be a dead branch
and the new definition would be satisfied by nothing at all.

The error constant is genuinely `delta`-dependent, as it must be: a single
tube is the extreme opposite of Frostman-spread, and the rescaled family
`T^{T_rho}` is one convex set of volume `~ |T| = delta^2`, so its `CFC` is
`~ delta^{-2}`. -/
theorem exists_convexAtEveryScale {δ : NNReal} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) :
    ∃ K : NNReal, 1 < K ∧
      ConvexAtEveryScale.{u} (Finset.univ : Finset PUnit.{u + 1})
        (fun _ => witnessTube δ) K := by
  obtain ⟨hV0, hVtop⟩ := tubeVolume_pos_and_ne_top hδ0
  set v : ENNReal := ENNReal.ofReal (2 / 3) * tubeVolume δ with hvdef
  have hv0 : v ≠ 0 := by
    refine mul_ne_zero ?_ hV0.ne'
    simp [ENNReal.ofReal_eq_zero]
  have hvtop : v ≠ ⊤ := by
    refine ENNReal.mul_ne_top ENNReal.ofReal_ne_top hVtop
  have hvinv_ne_top : v⁻¹ ≠ ⊤ := by simpa using hv0
  set K : NNReal := max 2 (v⁻¹).toNNReal with hKdef
  have hK2 : (2 : NNReal) ≤ K := le_max_left _ _
  have hK1 : (1 : NNReal) ≤ K := le_trans (by norm_num) hK2
  have hK1' : (1 : NNReal) < K := lt_of_lt_of_le (by norm_num) hK2
  have hKv : v⁻¹ ≤ (K : ENNReal) := by
    have : ((v⁻¹).toNNReal : ENNReal) = v⁻¹ := ENNReal.coe_toNNReal hvinv_ne_top
    rw [← this]
    exact_mod_cast le_max_right (2 : NNReal) (v⁻¹).toNNReal
  refine ⟨K, hK1', ?_, ?_⟩
  · exact fun i _ j _ hij => absurd (Subsingleton.elim i j) hij
  · intro ρ₀ hδρ hρ1
    have hρ0 : 0 < ρ₀ := lt_of_lt_of_le hδ0 hδρ
    refine ⟨ρ₀, hρ0, le_rfl, ?_, witnessCover hδρ hK1, ?_⟩
    · calc ρ₀ = 1 * ρ₀ := (one_mul _).symm
        _ < K * ρ₀ := by
            exact mul_lt_mul_of_pos_right hK1' hρ0
    · intro j _
      refine le_trans (frostmanConvexWolffConstantSets_le_inv _ _ hv0 hvtop ?_) hKv
      intro i _
      exact volume_rescale_ge hρ0 hρ1 (modelTube ρ₀) rfl

/-- **Non-vacuity of `FactorsFromAboveFCW` and `FactorsFromBelowFCW`**
(Definition :1001/:1004): a single `rho`-tube's frame factors the one-tube
family both from above and from below, with a finite error. -/
theorem exists_factorsFCW {δ ρ : NNReal} (hδ0 : 0 < δ) (hρ0 : 0 < ρ)
    (hδρ : δ ≤ ρ) (hρ1 : ρ ≤ 1) :
    ∃ K : ENNReal, K ≠ ⊤ ∧
      FactorsFromAboveFCW.{u} (Finset.univ : Finset PUnit.{u + 1})
          (fun _ => (witnessTube δ).carrier) (Finset.univ : Finset PUnit.{u + 1})
          (fun _ => tubeFrame3 hρ0 (modelTube ρ)) K ∧
      FactorsFromBelowFCW.{u} (Finset.univ : Finset PUnit.{u + 1})
          (fun _ => (witnessTube δ).carrier) (Finset.univ : Finset PUnit.{u + 1})
          (fun _ => tubeFrame3 hρ0 (modelTube ρ)) K := by
  obtain ⟨hVδ0, hVδtop⟩ := tubeVolume_pos_and_ne_top hδ0
  obtain ⟨hVρ0, hVρtop⟩ := tubeVolume_pos_and_ne_top hρ0
  set v₂ : ENNReal := ENNReal.ofReal (2 / 3) * tubeVolume δ with hv₂def
  have hv₂0 : v₂ ≠ 0 := mul_ne_zero (by simp [ENNReal.ofReal_eq_zero]) hVδ0.ne'
  have hv₂top : v₂ ≠ ⊤ := ENNReal.mul_ne_top ENNReal.ofReal_ne_top hVδtop
  have hbox : (modelTube ρ).carrier ⊆ (tubeFrame3 hρ0 (modelTube ρ)).box :=
    carrier_subset_tubeFrame3_box hρ0 (modelTube ρ)
  have hcover : (witnessTube δ).carrier ⊆ (tubeFrame3 hρ0 (modelTube ρ)).box :=
    (modelTube_carrier_mono hδρ).trans hbox
  have hvolbox : tubeVolume ρ ≤ volume (tubeFrame3 hρ0 (modelTube ρ)).box :=
    measure_mono hbox
  refine ⟨max (tubeVolume ρ)⁻¹ v₂⁻¹, ?_, ⟨fun i _ => ⟨PUnit.unit, Finset.mem_univ _, hcover⟩, ?_⟩,
    ⟨fun i _ => ⟨PUnit.unit, Finset.mem_univ _, hcover⟩, ?_⟩⟩
  · exact (max_lt (ENNReal.inv_lt_top.mpr hVρ0) (ENNReal.inv_lt_top.mpr
      (pos_iff_ne_zero.mpr hv₂0))).ne
  · refine le_trans (frostmanConvexWolffConstantSets_le_inv _ _ hVρ0.ne' hVρtop
      fun i _ => hvolbox) (le_max_left _ _)
  · intro k _
    refine le_trans (frostmanConvexWolffConstantSets_le_inv _ _ hv₂0 hv₂top ?_)
      (le_max_right _ _)
    intro i _
    exact volume_rescale_ge hρ0 hρ1 (modelTube ρ) rfl

/-- The empty family satisfies the Frostman Convex Wolff Axioms at every
scale. -/
theorem convexAtEveryScale_empty {δ : NNReal} {ι : Type u}
    (T : ι → ShadedTube δ Space3) {K : NNReal} (hK : 1 < K) (hδ0 : 0 < δ) :
    ConvexAtEveryScale.{u} (∅ : Finset ι) T K := by
  refine ⟨by simp, ?_⟩
  intro ρ₀ hδρ hρ1
  have hρ0 : 0 < ρ₀ := lt_of_lt_of_le hδ0 hδρ
  refine ⟨ρ₀, hρ0, le_rfl, ?_, ?_, ?_⟩
  · calc ρ₀ = 1 * ρ₀ := (one_mul _).symm
      _ < K * ρ₀ := mul_lt_mul_of_pos_right hK hρ0
  · exact
      { parent := ∅
        assign := id
        part := fun j => Tube.coverClass ∅ id j
        part_eq := fun _ => rfl
        mem_part_iff := fun i j => by simp [Tube.coverClass]
        parentTube := fun _ => modelTube ρ₀
        branch := 0
        assign_mem := fun i hi => absurd hi (Finset.notMem_empty i)
        leaf_le_parent := fun i hi => absurd hi (Finset.notMem_empty i)
        parentTube_injOn := fun a ha => absurd ha (Finset.notMem_empty a)
        card_class_le := fun j hj => absurd hj (Finset.notMem_empty j)
        le_card_class := fun j hj => absurd hj (Finset.notMem_empty j) }
  · intro j hj
    exact absurd hj (Finset.notMem_empty j)

/-- **The hypothesis bundle of `tubeTricotProp` is satisfiable, and at a point
where it is satisfied the conclusion is independently provable.**

This is the analogue of `assertionTE_two` + `assertionE_two` for the
trichotomy: an unsatisfiable hypothesis bundle would make `tubeTricotProp`
vacuously true, and `#print axioms` could not see it.

The witness here is the empty family, which is a genuine but degenerate point
of the hypothesis.  The *nonempty* certificate is
`exists_convexAtEveryScale`, which shows Conclusion (A) is inhabited by a
family with a tube in it; a nonempty family satisfying the *hypothesis*
`CFC(T) <= delta^{-eta}` for small `eta` would have to carry `~ delta^{-2}`
essentially distinct tubes, which is a construction this file does not
attempt. -/
theorem tubeTricotProp_satisfiable {δ : NNReal} (hδ0 : 0 < δ) (hδ1 : δ < 1)
    {ι : Type u} (T : ι → ShadedTube δ Space3) {η ζ₁ : ℝ} (hη : 0 < η)
    (hζ₁ : 0 < ζ₁) :
    IsTubeShadingFamily (∅ : Finset ι) T ∧
      frostmanConvexWolffConstant (∅ : Finset ι) T ≤ (δ : ENNReal) ^ (-η) ∧
      IsWZRefinement (∅ : Finset ι) T ∅ T (rpowNN δ η) ∧
      ConvexAtEveryScale.{u} (∅ : Finset ι) T (rpowNN δ (-ζ₁)) := by
  have hδ0E : (δ : ENNReal) ≠ 0 := ENNReal.coe_ne_zero.mpr hδ0.ne'
  have hδtopE : (δ : ENNReal) ≠ ⊤ := ENNReal.coe_ne_top
  refine ⟨⟨by simp, by simp⟩, ?_, ⟨Finset.Subset.refl _, by simp, by simp, by simp⟩, ?_⟩
  · refine sInf_le ⟨?_, fun W => ?_⟩
    · rw [pos_iff_ne_zero]
      simp [ENNReal.rpow_eq_zero_iff, hδ0E, hδtopE]
    · simp
  · refine convexAtEveryScale_empty T ?_ hδ0
    have h1 : (rpowNN δ (-ζ₁) : ℝ) = (δ : ℝ) ^ (-ζ₁) := rfl
    have hδpos : (0:ℝ) < (δ:ℝ) := by exact_mod_cast hδ0
    have : (1 : ℝ) < (δ : ℝ) ^ (-ζ₁) :=
      (Real.one_lt_rpow_iff_of_pos hδpos).mpr
        (Or.inr ⟨by exact_mod_cast hδ1, by linarith⟩)
    exact_mod_cast this

end

end Kakeya.WangZahl
