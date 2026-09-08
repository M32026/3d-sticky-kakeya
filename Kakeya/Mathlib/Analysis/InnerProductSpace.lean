/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.InnerProductSpace.TwoDim

/-!
# Orthonormal basis and frame helpers for inner product spaces

Auxiliary lemmas about orthonormal bases and frames in finite-dimensional inner
product spaces: extending an orthonormal basis of a codimension-one subspace to
the whole space, building an orthonormal basis from an orthonormal family whose
cardinality matches the dimension, the Parseval identity and area-form bounds in
an oriented plane, and compactness of the set of orthonormal frames.
-/

@[expose] public section

variable
  {𝕜} [RCLike 𝕜]
  {E} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E]

namespace OrthonormalBasis
theorem exists_extend_codim_one {m : ℕ}
    {L : Submodule 𝕜 E} (b : OrthonormalBasis (Fin m) 𝕜 L)
    (h : Module.finrank 𝕜 E = m + 1) :
    ∃ (b' : OrthonormalBasis (Fin m.succ) 𝕜 E), ∀ i : Fin m, b i = b' (i.castSucc) := by
  set v : Fin m.succ → E := Fin.snoc (fun i => (b i : E)) 0 with hv_def
  set s : Set (Fin m.succ) := Set.range Fin.castSucc with hs_def
  have card_ι : Module.finrank 𝕜 E = Fintype.card (Fin m.succ) := by
    rw [h, Fintype.card_fin]
  have hortho : Orthonormal 𝕜 (s.restrict v) := by
    let f : s → Fin m := fun x =>
      Fin.castLT x.1 (by obtain ⟨_, i, rfl⟩ := x; exact i.2)
    have hf : Function.Injective f := fun ⟨x, _⟩ ⟨y, _⟩ h => by
      simpa [f, Fin.ext_iff] using h
    have heq : s.restrict v = (fun i : Fin m => (b i : E)) ∘ f := by
      funext x
      obtain ⟨_, i, rfl⟩ := x
      simp [Set.restrict, v, f]
    rw [heq]
    exact (b.orthonormal.comp_linearIsometry L.subtypeₗᵢ).comp _ hf
  obtain ⟨b', hb'⟩ := hortho.exists_orthonormalBasis_extension_of_card_eq card_ι
  exact ⟨b', fun i => by simpa [v] using (hb' i.castSucc (Set.mem_range_self i)).symm⟩

/-- Extend an orthonormal basis `b` of a codimension-one subspace `L` to an orthonormal
basis of the whole space `E` (of dimension `m + 1`), agreeing with `b` on the first `m`
coordinates. -/
@[nolint defsWithUnderscore]
noncomputable def extend_codim_one {m : ℕ}
    {L : Submodule 𝕜 E} (b : OrthonormalBasis (Fin m) 𝕜 L)
    (h : Module.finrank 𝕜 E = m + 1) : OrthonormalBasis (Fin m.succ) 𝕜 E :=
  (exists_extend_codim_one b h).choose

theorem extend_codim_one_apply {m : ℕ}
    {L : Submodule 𝕜 E} (b : OrthonormalBasis (Fin m) 𝕜 L)
    (h : Module.finrank 𝕜 E = m + 1) (i : Fin m) :
    extend_codim_one b h i.castSucc = b i :=
  (exists_extend_codim_one b h).choose_spec i |>.symm

/-- If an orthonormal basis `b'` of `E` extends an orthonormal basis `b` of a submodule `L`
at the first `m` indices, then the remaining basis vector lies in `Lᗮ`. -/
theorem last_mem_orthogonal_of_extend {m : ℕ}
    {L : Submodule 𝕜 E} (b : OrthonormalBasis (Fin m) 𝕜 L)
    (h : Module.finrank 𝕜 E = m + 1) :
    extend_codim_one b h (Fin.last m) ∈ Lᗮ := by
  set b' := extend_codim_one b h with hb'_def
  intro u hu
  set u' : L := ⟨u, hu⟩
  have h_decompose : u = ∑ i, b.repr u' i • (b i : E) := by
    have h₁ : ∑ i, b.repr u' i • b i = u' := b.sum_repr u'
    have h₂ : ((∑ i, b.repr u' i • b i : L) : E) = u := by rw [h₁]
    rw [← h₂, AddSubmonoidClass.coe_finsetSum]
    rfl
  rw [h_decompose, sum_inner]
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [inner_smul_left, ← extend_codim_one_apply b h i,
      b'.orthonormal.inner_eq_zero (Fin.castSucc_lt_last i).ne, mul_zero]

theorem extend_codim_one_repr_apply {m : ℕ}
    {L : Submodule 𝕜 E} (b : OrthonormalBasis (Fin m) 𝕜 L)
    (h : Module.finrank 𝕜 E = m + 1) (v : E) (i : Fin m) :
    (extend_codim_one b h).repr v i.castSucc = inner 𝕜 (b i).val v := by
  rw [OrthonormalBasis.repr_apply_apply, extend_codim_one_apply]

end OrthonormalBasis

/-- An orthonormal family indexed by a type whose cardinality equals `finrank 𝕜 E` is an
orthonormal basis of `E`. Unlike `basisOfOrthonormalOfCardEqFinrank`, this needs no `Nonempty ι`
assumption: in finite dimension the spanning property holds even when `ι` is empty. -/
noncomputable def orthonormalBasisOfCardEqFinrank
    {ι : Type*} [Fintype ι] {v : ι → E} (hv : Orthonormal 𝕜 v)
    (card_eq : Fintype.card ι = Module.finrank 𝕜 E) : OrthonormalBasis ι 𝕜 E :=
  OrthonormalBasis.mk hv (hv.linearIndependent.span_eq_top_of_card_eq_finrank' card_eq).ge

@[simp]
theorem coe_orthonormalBasisOfCardEqFinrank
    {ι : Type*} [Fintype ι] {v : ι → E} (hv : Orthonormal 𝕜 v)
    (card_eq : Fintype.card ι = Module.finrank 𝕜 E) :
    ⇑(orthonormalBasisOfCardEqFinrank hv card_eq) = v :=
  OrthonormalBasis.coe_mk hv _

/-- The set of orthonormal `n`-frames in `E` is compact: it is closed (`orthonormal_iff_ite`) and
bounded in the proper finite-dimensional space `Fin n → E`. -/
theorem isCompact_orthonormal {n : ℕ} :
    IsCompact {v : Fin n → E | Orthonormal 𝕜 v} := by
  haveI : ProperSpace E := FiniteDimensional.proper_rclike 𝕜 E
  apply Metric.isCompact_of_isClosed_isBounded
  · rw [show {v : Fin n → E | Orthonormal 𝕜 v}
          = ⋂ (i : Fin n), ⋂ (j : Fin n),
              {v : Fin n → E | inner 𝕜 (v i) (v j) = if i = j then (1 : 𝕜) else 0} by
        ext v
        simp only [Set.mem_setOf_eq, Set.mem_iInter, orthonormal_iff_ite]]
    refine isClosed_iInter fun i => isClosed_iInter fun j => ?_
    exact isClosed_eq ((continuous_apply i).inner (continuous_apply j)) continuous_const
  · apply Metric.isBounded_iff.mpr
    refine ⟨2, fun v hv w hw => ?_⟩
    have hv1 : ∀ i, ‖v i‖ = 1 := fun i => hv.1 i
    have hw1 : ∀ i, ‖w i‖ = 1 := fun i => hw.1 i
    rw [dist_pi_le_iff (by norm_num)]
    intro i
    calc dist (v i) (w i) ≤ ‖v i‖ + ‖w i‖ := dist_le_norm_add_norm _ _
      _ = 2 := by rw [hv1, hw1]; norm_num

/-- **Inner-product transversality bound.** Let `o` be an orientation of a `2`-dimensional real
inner product space `V`, with associated signed-area form `ω = o.areaForm`.  If `u`, `v` are unit
vectors and `w` satisfies `|⟪w, u⟫| ≤ r₁` and `|⟪w, v⟫| ≤ r₂`, then the norm of `w` is controlled by
`r₁ + r₂` divided by the area `ω u v` (the sine of the angle between `u` and `v`).  Stated
multiplicatively to avoid division by the possibly-zero area: `‖w‖ · |ω u v| ≤ r₁ + r₂`.

Proof idea (coordinate-free): `Orientation.inner_mul_areaForm_sub` gives
`‖w‖² · ω u v = ⟪w,u⟫ · ω w v - ω w u · ⟪w,v⟫`; bounding `|ω w u|, |ω w v| ≤ ‖w‖`
(`Orientation.abs_areaForm_le`, unit `u, v`) and `|⟪w,u⟫| ≤ r₁`, `|⟪w,v⟫| ≤ r₂` yields
`‖w‖² |ω u v| ≤ (r₁ + r₂) ‖w‖`, then divide by `‖w‖`. -/
theorem Orientation.norm_mul_abs_areaForm_le
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [Fact (Module.finrank ℝ V = 2)] (o : Orientation ℝ V (Fin 2))
    {u v w : V} (hu : ‖u‖ = 1) (hv : ‖v‖ = 1)
    {r₁ r₂ : ℝ} (hwu : |inner ℝ w u| ≤ r₁) (hwv : |inner ℝ w v| ≤ r₂) :
    ‖w‖ * |o.areaForm u v| ≤ r₁ + r₂ := by
  have hr₁ : 0 ≤ r₁ := (abs_nonneg _).trans hwu
  have hr₂ : 0 ≤ r₂ := (abs_nonneg _).trans hwv
  have h_id := o.inner_mul_areaForm_sub w u v
  have h_abs_ineq : |‖w‖ ^ 2 * o.areaForm u v| ≤ (r₁ + r₂) * ‖w‖ := by
    rw [← h_id]
    calc
      |inner ℝ w u * o.areaForm w v - o.areaForm w u * inner ℝ w v|
          ≤ |inner ℝ w u * o.areaForm w v| + |o.areaForm w u * inner ℝ w v| :=
        abs_sub (inner ℝ w u * o.areaForm w v) (o.areaForm w u * inner ℝ w v)
      _ = |inner ℝ w u| * |o.areaForm w v| + |o.areaForm w u| * |inner ℝ w v| := by simp [abs_mul]
      _ ≤ r₁ * |o.areaForm w v| + |o.areaForm w u| * r₂ :=
        add_le_add (mul_le_mul_of_nonneg_right hwu (abs_nonneg _))
          (mul_le_mul_of_nonneg_left hwv (abs_nonneg _))
      _ ≤ r₁ * (‖w‖ * ‖v‖) + (‖w‖ * ‖u‖) * r₂ :=
        add_le_add (mul_le_mul_of_nonneg_left (o.abs_areaForm_le w v) hr₁)
          (mul_le_mul_of_nonneg_right (o.abs_areaForm_le w u) hr₂)
      _ = r₁ * ‖w‖ + ‖w‖ * r₂ := by rw [hu, hv]; ring
      _ = (r₁ + r₂) * ‖w‖ := by ring
  have h_abs_sq : |‖w‖ ^ 2 * o.areaForm u v| = ‖w‖ ^ 2 * |o.areaForm u v| := by
    rw [abs_mul, abs_of_nonneg (pow_nonneg (norm_nonneg _) 2)]
  rw [h_abs_sq] at h_abs_ineq
  by_cases hw0 : ‖w‖ = 0
  · simp only [hw0, zero_mul]; linarith
  · have hwpos : 0 < ‖w‖ := (Ne.symm hw0).lt_of_le (norm_nonneg _)
    nlinarith

/-- **Parseval identity for an orthonormal basis of a plane.** For an orthonormal basis `b` of a
`2`-dimensional real inner product space and any vector `x`, the squared coordinates sum to the
squared norm: `⟪x, b 0⟫² + ⟪x, b 1⟫² = ‖x‖²`. -/
theorem OrthonormalBasis.inner_sq_add_inner_sq
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (b : OrthonormalBasis (Fin 2) ℝ V) (x : V) :
    inner ℝ x (b 0) ^ 2 + inner ℝ x (b 1) ^ 2 = ‖x‖ ^ 2 := by
  have h := b.sum_inner_mul_inner x x
  rw [Fin.sum_univ_two, real_inner_self_eq_norm_sq, real_inner_comm x (b 0),
    real_inner_comm x (b 1)] at h
  linear_combination h

/-- **Absolute area form equals the complementary inner product.** For an orthonormal basis `b`
of an oriented plane and any vector `x`, the absolute signed area `|ω x (b i)|` equals the
absolute inner product `|⟪x, b i.rev⟫|` with the *other* basis vector.  This is the
orientation-magnitude form of "areaForm = inner product": it follows from Mathlib's
`inner_sq_add_areaForm_sq` (`⟪x, bᵢ⟫² + ω(x, bᵢ)² = ‖x‖²`) together with Parseval
(`inner_sq_add_inner_sq`). -/
theorem Orientation.abs_areaForm_basis_eq_abs_inner
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [Fact (Module.finrank ℝ V = 2)] (o : Orientation ℝ V (Fin 2))
    (b : OrthonormalBasis (Fin 2) ℝ V) (x : V) (i : Fin 2) :
    |o.areaForm x (b i)| = |inner ℝ x (b i.rev)| := by
  have hsq : o.areaForm x (b i) ^ 2 = inner ℝ x (b i.rev) ^ 2 := by
    have hpar := b.inner_sq_add_inner_sq x
    fin_cases i
    · have hia := o.inner_sq_add_areaForm_sq x (b 0)
      rw [b.norm_eq_one 0, one_pow, mul_one] at hia
      change o.areaForm x (b 0) ^ 2 = inner ℝ x (b 1) ^ 2
      linarith
    · have hia := o.inner_sq_add_areaForm_sq x (b 1)
      rw [b.norm_eq_one 1, one_pow, mul_one] at hia
      change o.areaForm x (b 1) ^ 2 = inner ℝ x (b 0) ^ 2
      linarith
  have hsqrt := congrArg Real.sqrt hsq
  rwa [Real.sqrt_sq_eq_abs, Real.sqrt_sq_eq_abs] at hsqrt

/-- **A linear isometry matching two vectors of equal norm** (blueprint
`lem:reflectionMatchingVectors`): the reflection in the hyperplane `(ℝ ∙ (f - f'))ᗮ` sends `f`
to `f'` (`Submodule.reflection_sub`).  No case distinction is needed: for `f = f'` the span is
`⊥`, its orthogonal complement is everything and the reflection is the identity. -/
theorem exists_linearIsometryEquiv_apply_eq_of_norm_eq {F : Type*} [NormedAddCommGroup F]
    [InnerProductSpace ℝ F] [FiniteDimensional ℝ F] {f f' : F} (h : ‖f‖ = ‖f'‖) :
    ∃ R : F ≃ₗᵢ[ℝ] F, R f = f' := by
  exact ⟨Submodule.reflection (ℝ ∙ (f - f'))ᗮ, Submodule.reflection_sub h⟩

/-- An orthonormal-basis coordinate of `u -ᵥ v` is bounded by `dist u v`
(1-Lipschitz projection). -/
lemma abs_repr_vsub_le_dist_basis {E S : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MetricSpace S] [NormedAddTorsor E S] (b : OrthonormalBasis (Fin 3) ℝ E)
    (u v : S) (i : Fin 3) : |b.repr (u -ᵥ v) i| ≤ dist u v := by
  rw [b.repr_apply_apply, dist_eq_norm_vsub E]
  simpa [b.norm_eq_one i] using abs_real_inner_le_norm (b i) (u -ᵥ v)

/-- **Probe-difference bound.**  If the two probe points `p ± t·v`, measured from `q`, both have
`n`-coordinate at most `M`, then `|⟪n, v⟫| ≤ M / t`: subtracting the two coordinates cancels
`p - q` and leaves `2t⟪n, v⟫`. -/
lemma abs_inner_le_of_probes {n v p q : EuclideanSpace ℝ (Fin 3)} {t M : ℝ} (ht : 0 < t)
    (hp : |inner ℝ n (p + t • v -ᵥ q)| ≤ M) (hm : |inner ℝ n (p - t • v -ᵥ q)| ≤ M) :
    |inner ℝ n v| ≤ M / t := by
  have key : inner ℝ n (p + t • v -ᵥ q) - inner ℝ n (p - t • v -ᵥ q) = 2 * t * inner ℝ n v := by
    rw [← inner_sub_right, show (p + t • v -ᵥ q) - (p - t • v -ᵥ q) = (2 * t) • v from by
      simp only [vsub_eq_sub]; module, real_inner_smul_right]
  have habs := abs_sub (inner ℝ n (p + t • v -ᵥ q)) (inner ℝ n (p - t • v -ᵥ q))
  rw [key, abs_mul, abs_of_pos (by linarith : (0 : ℝ) < 2 * t)] at habs
  rw [le_div_iff₀ ht]
  linarith
