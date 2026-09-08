/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.Frostman

/-!
# Changing the container of a Frostman lower bound

This file isolates the last leaf of item (iv) of
`Kakeya.ml1Boot.exists_fineNormalization_lower`: the **container change**.  Item (iv) has to
turn a Frostman lower bound read at a source container `K₁` into a Frostman lower bound read
at a larger container `K₂ ⊇ K₁` of comparable volume, the family being read at an ambient
index set in both cases.

The two halves of that change behave completely differently, and separating them is the point
of this file.

* **Growing the container with the index set held fixed is free.**
  `ConvexSpaceBody.frostmanConstIn_le_of_container_le`: if every member of `s` lies in `K₁`
  and `K₁ ≤ K₂`, then `C_F(s, 𝕎, K₁) ≤ C_F(s, 𝕎, K₂)` with **no** loss and **no** volume
  comparability hypothesis.  Enlarging the container only lowers the reference density
  `Δ(𝕎, K)`, which sits in the denominator of the Frostman constant.
* **Growing the index set is not free, and it is not a matter of volume comparability.**
  What the enlarged container adds is *members*: bodies of the ambient family that lie in `K₂`
  and not in `K₁`.  Their mass inflates the reference density `Δ(𝕎, K₂)` and deflates the
  Frostman constant.  `ConvexSpaceBody.frostmanConstIn_le_of_subfamily_of_densityIn_le` pays
  for exactly that, at exactly the density ratio, and
  `ConvexSpaceBody.container_change_false_of_no_density_comparison` shows the ratio cannot be
  dropped: with `K₂` a `2`-dilate of `K₁` — *any* fixed volume ratio would do — the Frostman
  constant at `K₁` is `≥ 1/(2t)` while the constant at `K₂` is `≤ 1`, for every `t > 0`.

So the hypothesis of item (iv) is **not** a statement about the normalization, and no
amount of construction visibility supplies it: it is a *doubling clause on the ambient family*,

> the members of the ambient family lying in a bounded enlargement of the window container
> carry at most `O(1)` times the mass of those lying in the container itself,

which is a hypothesis about `𝕌` at the window scales and has to be assumed.
-/

@[expose] public section

open MeasureTheory Kakeya

namespace ConvexSpaceBody

section General

variable
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {ι : Type*}
  {s s₁ s₂ : Finset ι} {W : ι → ConvexSpaceBody E} {K K₁ K₂ : ConvexSpaceBody E} {C : ENNReal}

/-- **Growing the container is free when the index set is held fixed.**

If every body of the family `s` lies in `K₁` and `K₁ ≤ K₂`, then the Frostman constant read at
the smaller container is at most the one read at the larger container.  There is no constant
and no volume-comparability hypothesis: the family is the same on both sides, so the only
change is that the reference density `Δ(𝕎, K)` — the denominator of the Frostman constant —
drops when `K` grows.

This is the exact converse direction to `ConvexSpaceBody.frostmanConstIn_ambient_mono`, which
bounds the constant at the *larger* container by the volume ratio times the constant at the
smaller one. -/
theorem frostmanConstIn_le_of_container_le (hK : K₁ ≤ K₂) (hsK : ∀ i ∈ s, W i ≤ K₁) :
    frostmanConstIn s W K₁ ≤ frostmanConstIn s W K₂ := by
  refine frostmanConstIn_le ?_
  intro K' hK'
  refine (isFrostmanIn_frostmanConstIn s W K₂ K' (hK'.trans hK)).trans ?_
  gcongr
  rw [densityIn_of_all_le hsK, densityIn_of_all_le (fun i hi => (hsK i hi).trans hK)]
  exact ENNReal.div_le_div_left (measure_mono hK) _

/-- **Growing the index set costs exactly the density ratio.**

If `s₁ ⊆ s₂` and the reference density of the larger family in `K` is at most `C` times that of
the smaller one, then `C_F(s₁, 𝕎, K) ≤ C * C_F(s₂, 𝕎, K)`.

This is the half of the container change that is *not* free.  The hypothesis is a statement
about the ambient family alone, and
`ConvexSpaceBody.container_change_false_of_no_density_comparison` below shows that no hypothesis on the *containers* can replace it. -/
theorem frostmanConstIn_le_of_subfamily_of_densityIn_le (hs : s₁ ⊆ s₂)
    (hd : densityIn s₂ W K ≤ C * densityIn s₁ W K) :
    frostmanConstIn s₁ W K ≤ C * frostmanConstIn s₂ W K := by
  refine frostmanConstIn_le ?_
  intro K' hK'
  calc densityIn s₁ W K' ≤ densityIn s₂ W K' := densityIn_mono' W K' s₁ s₂ hs
    _ ≤ frostmanConstIn s₂ W K * densityIn s₂ W K :=
        isFrostmanIn_frostmanConstIn s₂ W K K' hK'
    _ ≤ frostmanConstIn s₂ W K * (C * densityIn s₁ W K) := by gcongr
    _ = C * frostmanConstIn s₂ W K * densityIn s₁ W K := by ring

/-- **The container change, in the form item (iv) needs it.**

A Frostman lower bound read at `K₁` on the index set `s₁` descends to one read at the larger
container `K₂` on the larger index set `s₂`, at the cost of the density ratio `C` alone.  Note
what is *not* assumed: no comparability of the two volumes, and nothing at all about how the
bodies of `s₂ \ s₁` sit. -/
theorem frostmanConstIn_le_of_container_change (hK : K₁ ≤ K₂) (hs : s₁ ⊆ s₂)
    (hsK : ∀ i ∈ s₁, W i ≤ K₁)
    (hd : densityIn s₂ W K₂ ≤ C * densityIn s₁ W K₂) :
    frostmanConstIn s₁ W K₁ ≤ C * frostmanConstIn s₂ W K₂ :=
  (frostmanConstIn_le_of_container_le hK hsK).trans
    (frostmanConstIn_le_of_subfamily_of_densityIn_le hs hd)

/-- The `familyIn` reading of `ConvexSpaceBody.frostmanConstIn_le_of_container_change`: the two
index sets are the two subfamilies cut out by the two containers, and the density hypothesis is
the **doubling clause** on the ambient family `s`,
`Δ(𝕎, K₂) ≤ C * Δ(𝕎[K₁], K₂)`, i.e. the members caught by the enlarged container carry at most
`C` times the mass of those caught by the original one. -/
theorem frostmanConstIn_familyIn_le_of_container_change (hK : K₁ ≤ K₂)
    (hd : densityIn s W K₂ ≤ C * densityIn (familyIn s W K₁) W K₂) :
    frostmanConstIn (familyIn s W K₁) W K₁ ≤ C * frostmanConstIn (familyIn s W K₂) W K₂ := by
  refine frostmanConstIn_le_of_container_change hK ?_ ?_ ?_
  · exact fun i hi => Finset.mem_filter.mpr
      ⟨(Finset.mem_filter.mp hi).1, (Finset.mem_filter.mp hi).2.trans hK⟩
  · exact fun i hi => (Finset.mem_filter.mp hi).2
  · simpa only [familyIn] using hd.trans_eq' (densityIn_eq_densityIn_filter s W K₂)

/-- **The doubling clause is free exactly when the enlargement catches nothing new.**

If every member of the family that fits inside the enlarged container `K₂` already fits inside
`K₁`, then the reference density at `K₂` is at most the reference density at `K₁` — with no
constant at all, since the numerators agree and the denominator only grew.  This is the
satisfiability witness for the doubling clause installed on `hFb` in
`Kakeya.ml1Boot.exists_fineNormalization_lower`: the clause is a restriction on how the ambient
family is distributed just outside the window container, and it is vacuous when there is nothing
just outside.

The `1 ≤ C` slack is carried so that the statement matches the clause as it is written (with the
concrete constant `Kakeya.ml1Boot.fineFactor.C`), not because the proof needs it. -/
theorem densityIn_le_of_forall_le (hC : 1 ≤ C) (hK : K₁ ≤ K₂)
    (h : ∀ i ∈ s, W i ≤ K₂ → W i ≤ K₁) :
    densityIn s W K₂ ≤ C * densityIn s W K₁ := by
  have hsum : ∑ i ∈ s with W i ≤ K₂, volume (W i).carrier
      = ∑ i ∈ s with W i ≤ K₁, volume (W i).carrier := by
    refine Finset.sum_congr (Finset.filter_congr ?_) (fun _ _ => rfl)
    intro i hi
    exact ⟨fun h2 => h i hi h2, fun h1 => h1.trans hK⟩
  have hstep : densityIn s W K₂ ≤ densityIn s W K₁ := by
    show (∑ i ∈ s with W i ≤ K₂, volume (W i).carrier) / volume K₂.carrier
        ≤ (∑ i ∈ s with W i ≤ K₁, volume (W i).carrier) / volume K₁.carrier
    rw [hsum]
    have hvol : volume K₁.carrier ≤ volume K₂.carrier := measure_mono hK
    exact ENNReal.div_le_div_left hvol _
  refine hstep.trans ?_
  calc densityIn s W K₁ = 1 * densityIn s W K₁ := (one_mul _).symm
    _ ≤ C * densityIn s W K₁ := mul_le_mul_right' hC _

/-- The doubling clause of `ConvexSpaceBody.frostmanConstIn_familyIn_le_of_container_change` is
satisfiable, and the lemma is not vacuous: when the enlarged container catches no new member,
`C = 1` works.  (This is the degenerate case `familyIn s W K₂ = familyIn s W K₁`.) -/
theorem densityIn_le_of_familyIn_eq (h : familyIn s W K₂ = familyIn s W K₁) :
    densityIn s W K₂ ≤ 1 * densityIn (familyIn s W K₁) W K₂ := by
  rw [one_mul, ← h]
  simpa only [familyIn] using (densityIn_eq_densityIn_filter s W K₂).le

end General

section ItemIV

variable
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {ι : Type*}
  {s : Finset ι} {W V : ι → ConvexSpaceBody E} {Q Q' K : ConvexSpaceBody E} {A C D : ENNReal}

/-- **The whole transport chain of item (iv), with its two hypothesis named.**

Read `W = Ψ ∘ 𝕌` (the normalization's image of the source family), `V = 𝕋̃` (the normalized
family), `Q = Ψ(T_σ)` (the transported source container), `Q'` its enlargement, and
`K = 2 · T_ρ` (the container item (iv) reads at).  Then a Frostman lower bound `A` at
`(𝕎[Q], Q)` descends to one at `(𝕍[K], K)`, at the cost `C ^ 2 * D`, given:

* `hdilate` — the enlargement clause of `ConvexSpaceBody.frostmanConstIn_ge_of_comparable`,
  which `ConvexSpaceBody.exists_dilate_witness_of_enlargement` reduces to a purely local
  per-body statement, and which the construction has to supply;
* `hdoubling` — the **doubling clause on the ambient family**: the members caught by the
  enlarged container `K` carry at most `D` times the mass of those caught by `Q`.

Every other step is free.  Growing the container is free
(`ConvexSpaceBody.frostmanConstIn_le_of_container_le`), and the affine step before this one is
an exact equality (`ConvexSpaceBody.frostmanConstIn_affineImage`).  So these two clauses are
the *entire* remaining content of item (iv), and
`ConvexSpaceBody.container_change_false_of_no_density_comparison` shows `hdoubling` cannot be
derived from volume comparability of the containers: it is a genuine hypothesis about how the
ambient family is distributed at the window scales. -/
theorem le_frostmanConstIn_of_transport (hC : 1 ≤ C)
    (hQQ' : Q ≤ Q') (hQ'K : Q' ≤ K)
    (hVQ' : ∀ i ∈ familyIn s W Q, V i ≤ Q')
    (hWV : ∀ i ∈ familyIn s W Q, W i ≤ V i)
    (hvol : ∀ i ∈ familyIn s W Q, volume (V i).carrier ≤ C * volume (W i).carrier)
    (hdilate : ∀ K'' ≤ Q', ∃ L ≤ Q', K'' ≤ L ∧ volume L.carrier ≤ C * volume K''.carrier ∧
      ∀ i ∈ familyIn s W Q, W i ≤ K'' → V i ≤ L)
    (hdoubling : densityIn (familyIn s V K) V K ≤ D * densityIn (familyIn s W Q) V K)
    (hsrc : A ≤ frostmanConstIn (familyIn s W Q) W Q) :
    A ≤ C ^ 2 * D * frostmanConstIn (familyIn s V K) V K := by
  have hWQ : ∀ i ∈ familyIn s W Q, W i ≤ Q := fun i hi => (Finset.mem_filter.mp hi).2
  have hsub : familyIn s W Q ⊆ familyIn s V K := by
    intro i hi
    exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hi).1, (hVQ' i hi).trans hQ'K⟩
  calc A ≤ frostmanConstIn (familyIn s W Q) W Q := hsrc
    _ ≤ frostmanConstIn (familyIn s W Q) W Q' :=
        frostmanConstIn_le_of_container_le hQQ' hWQ
    _ ≤ C ^ 2 * frostmanConstIn (familyIn s W Q) V Q' :=
        (frostmanConstIn_ge_of_comparable hC hVQ' hWV hvol hdilate).1
    _ ≤ C ^ 2 * frostmanConstIn (familyIn s W Q) V K := by
        gcongr
        exact frostmanConstIn_le_of_container_le hQ'K hVQ'
    _ ≤ C ^ 2 * (D * frostmanConstIn (familyIn s V K) V K) := by
        gcongr
        exact frostmanConstIn_le_of_subfamily_of_densityIn_le hsub hdoubling
    _ = C ^ 2 * D * frostmanConstIn (familyIn s V K) V K := by ring

/-- **The `hdoubling` clause of the transport chain, from a doubling clause on the *source*
family.**

`ConvexSpaceBody.le_frostmanConstIn_of_transport` consumes its doubling clause in the
*normalized* coordinates: it compares the mass of the `V`-bodies caught by the outer container
`K` with the mass of the `V`-bodies whose `W`-shadow is caught by `Q`.  What
`Kakeya.ml1Boot.exists_fineNormalization_lower` now assumes on `hFb`, by contrast, is a doubling
clause on the *source* family: `Δ(𝕎, K) ≤ C_d Δ(𝕎, Q)` for the same two containers, read on the
whole ambient index set and with the source bodies.  This lemma is the bridge, and it says the
source clause is enough, at the cost of the two comparabilities the construction already
supplies:

* `hvol` — each normalized body is within `C` of its shadow in volume (the visibility clause
  `|T̃ k| ≤ (4 C_N) ^ 6 |Ψ(U k)|`);
* `hvolQK` — the outer container is within `C_v` of the inner one in volume (here
  `|2 · T_ρ| ≤ 8 (4 C_N) ^ 6 |Ψ(T_σ)|`).

The one hypothesis that is **not** bookkeeping is `hVK`: every ambient body whose shadow lies in
`Q` must have its normalized body inside `K`.  That is the per-body enlargement clause of the
construction, *pinned to the container `K`* rather than existentially quantified — see the
"Proof status" section of `Kakeya.ml1Boot.exists_fineNormalization_lower`.  Without it the
right-hand side of `hdoubling`, whose index set is silently intersected with `{i | V i ≤ K}`
by `Kakeya.densityIn`, cannot be recognised as the source subfamily at all. -/
theorem densityIn_familyIn_transport_of_doubling {Cd Cv : ENNReal}
    (hK0 : volume K.carrier ≠ 0) (hKtop : volume K.carrier ≠ ⊤)
    (hQ0 : volume Q.carrier ≠ 0) (hQtop : volume Q.carrier ≠ ⊤)
    (hWV : ∀ i ∈ s, W i ≤ V i)
    (hvol : ∀ i ∈ s, volume (V i).carrier ≤ C * volume (W i).carrier)
    (hVK : ∀ i ∈ s, W i ≤ Q → V i ≤ K)
    (hvolQK : volume K.carrier ≤ Cv * volume Q.carrier)
    (hdoub : densityIn s W K ≤ Cd * densityIn s W Q) :
    densityIn (familyIn s V K) V K
      ≤ C * Cd * Cv * densityIn (familyIn s W Q) V K := by
  have hAll1 : ∀ i ∈ familyIn s V K, V i ≤ K := fun i hi => (Finset.mem_filter.mp hi).2
  have hAll2 : ∀ i ∈ familyIn s W Q, V i ≤ K := fun i hi =>
    hVK i (Finset.mem_filter.mp hi).1 (Finset.mem_filter.mp hi).2
  have hsub1 : familyIn s V K ⊆ familyIn s W K := fun i hi =>
    Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hi).1,
      (hWV i (Finset.mem_filter.mp hi).1).trans (Finset.mem_filter.mp hi).2⟩
  -- Step 1: replace the normalized bodies by their shadows, and enlarge the index set to `𝕎[K]`.
  have h1 : ∑ i ∈ familyIn s V K, volume (V i).carrier
      ≤ C * ∑ i ∈ familyIn s W K, volume (W i).carrier := by
    calc ∑ i ∈ familyIn s V K, volume (V i).carrier
        ≤ ∑ i ∈ familyIn s V K, C * volume (W i).carrier :=
          Finset.sum_le_sum fun i hi => hvol i (Finset.mem_filter.mp hi).1
      _ = C * ∑ i ∈ familyIn s V K, volume (W i).carrier := by rw [Finset.mul_sum]
      _ ≤ C * ∑ i ∈ familyIn s W K, volume (W i).carrier := by
          gcongr
  -- Step 2: the source doubling clause, cleared of its two denominators.
  have h2 : ∑ i ∈ familyIn s W K, volume (W i).carrier
      ≤ Cd * Cv * ∑ i ∈ familyIn s W Q, volume (W i).carrier := by
    have hSK : densityIn s W K * volume K.carrier
        = ∑ i ∈ familyIn s W K, volume (W i).carrier :=
      ENNReal.div_mul_cancel hK0 hKtop
    have hSQ : densityIn s W Q * volume Q.carrier
        = ∑ i ∈ familyIn s W Q, volume (W i).carrier :=
      ENNReal.div_mul_cancel hQ0 hQtop
    calc ∑ i ∈ familyIn s W K, volume (W i).carrier
        = densityIn s W K * volume K.carrier := hSK.symm
      _ ≤ Cd * densityIn s W Q * (Cv * volume Q.carrier) := by gcongr
      _ = Cd * Cv * (densityIn s W Q * volume Q.carrier) := by ring
      _ = Cd * Cv * ∑ i ∈ familyIn s W Q, volume (W i).carrier := by rw [hSQ]
  -- Step 3: back from shadows to normalized bodies on the inner index set.
  have h3 : ∑ i ∈ familyIn s W Q, volume (W i).carrier
      ≤ ∑ i ∈ familyIn s W Q, volume (V i).carrier :=
    Finset.sum_le_sum fun i hi => measure_mono (hWV i (Finset.mem_filter.mp hi).1)
  have hfinal : ∑ i ∈ familyIn s V K, volume (V i).carrier
      ≤ C * Cd * Cv * ∑ i ∈ familyIn s W Q, volume (V i).carrier := by
    calc ∑ i ∈ familyIn s V K, volume (V i).carrier
        ≤ C * ∑ i ∈ familyIn s W K, volume (W i).carrier := h1
      _ ≤ C * (Cd * Cv * ∑ i ∈ familyIn s W Q, volume (W i).carrier) := by gcongr
      _ ≤ C * (Cd * Cv * ∑ i ∈ familyIn s W Q, volume (V i).carrier) := by gcongr
      _ = C * Cd * Cv * ∑ i ∈ familyIn s W Q, volume (V i).carrier := by ring
  rw [densityIn_of_all_le hAll1, densityIn_of_all_le hAll2, ← mul_div_assoc]
  exact ENNReal.div_le_div_right hfinal _

/-- **Item (iv)'s inequality, from the clauses that are actually available.**

`ConvexSpaceBody.le_frostmanConstIn_of_transport` with its `hdoubling` clause replaced by the
*source* doubling clause of `Kakeya.ml1Boot.exists_fineNormalization_lower`'s `hFb`, via
`ConvexSpaceBody.densityIn_familyIn_transport_of_doubling`.  This is the exact shape in which
item (iv) can consume what it is given, and reading off its hypotheses is the cleanest statement
of what is still owed:

* `hVQ'`, `hdilate` and `hVK` are the construction's per-body enlargement clause — the one
  requested from the producer of the normalized family.  Note that `hVK` pins the enlargement to
  the outer container `K = 2 · T_ρ`; the existentially-quantified form (`∃ D` of comparable
  volume) does **not** give it, because nothing places that `D` inside `K`.
* `hdoub` is the doubling clause on the ambient family, now a hypothesis of `hFb`.
* `hvolQK` is volume comparability of the two containers, which the container route
  (`Kakeya.ml1Boot.exists_rescaled_source_container`) supplies.

Everything else — the affine step, both container growths — is free. -/
theorem le_frostmanConstIn_of_transport_of_source_doubling {Cd Cv : ENNReal} (hC : 1 ≤ C)
    (hK0 : volume K.carrier ≠ 0) (hKtop : volume K.carrier ≠ ⊤)
    (hQ0 : volume Q.carrier ≠ 0) (hQtop : volume Q.carrier ≠ ⊤)
    (hQQ' : Q ≤ Q') (hQ'K : Q' ≤ K)
    (hVQ' : ∀ i ∈ familyIn s W Q, V i ≤ Q')
    (hWV : ∀ i ∈ s, W i ≤ V i)
    (hvol : ∀ i ∈ s, volume (V i).carrier ≤ C * volume (W i).carrier)
    (hdilate : ∀ K'' ≤ Q', ∃ L ≤ Q', K'' ≤ L ∧ volume L.carrier ≤ C * volume K''.carrier ∧
      ∀ i ∈ familyIn s W Q, W i ≤ K'' → V i ≤ L)
    (hVK : ∀ i ∈ s, W i ≤ Q → V i ≤ K)
    (hvolQK : volume K.carrier ≤ Cv * volume Q.carrier)
    (hdoub : densityIn s W K ≤ Cd * densityIn s W Q)
    (hsrc : A ≤ frostmanConstIn (familyIn s W Q) W Q) :
    A ≤ C ^ 2 * (C * Cd * Cv) * frostmanConstIn (familyIn s V K) V K :=
  le_frostmanConstIn_of_transport hC hQQ' hQ'K hVQ'
    (fun i hi => hWV i (Finset.mem_filter.mp hi).1)
    (fun i hi => hvol i (Finset.mem_filter.mp hi).1)
    hdilate
    (densityIn_familyIn_transport_of_doubling hK0 hKtop hQ0 hQtop hWV hvol hVK hvolQK hdoub)
    hsrc

/-- The chain of `ConvexSpaceBody.le_frostmanConstIn_of_transport` is not vacuous: at
`W = V`, `Q = Q' = K`, `C = D = 1` every hypothesis holds and the conclusion is the identity.
This is the satisfiability witness for the hypothesis bundle. -/
theorem le_frostmanConstIn_of_transport_refl (K : ConvexSpaceBody E) (W : ι → ConvexSpaceBody E)
    (s : Finset ι) :
    frostmanConstIn (familyIn s W K) W K
      ≤ 1 ^ 2 * 1 * frostmanConstIn (familyIn s W K) W K :=
  le_frostmanConstIn_of_transport (V := W) le_rfl le_rfl le_rfl
    (fun i hi => (Finset.mem_filter.mp hi).2) (fun _ _ => le_rfl) (fun _ _ => by simp)
    (fun K'' hK'' => ⟨K'', hK'', le_rfl, by simp, fun _ _ h => h⟩)
    (by rw [one_mul]) le_rfl

end ItemIV

section Counterexample

/-- **The container change is false without the density clause.**

For every `t > 0` there is a two-body family `𝕎` in `ℝ` and a pair of containers `K₁ ≤ K₂`
with `|K₂| = 2 |K₁|` such that

* `C_F(𝕎[K₁], K₁) ≥ 1 / (2 t)`, while
* `C_F(𝕎[K₂], K₂) ≤ 1`.

Letting `t → 0` the ratio is unbounded, so **no** constant `c` makes
`c * C_F(𝕎[K₁], K₁) ≤ C_F(𝕎[K₂], K₂)` true under volume comparability of the containers alone.
The mechanism is the one item (iv) meets: the enlarged container catches a member the smaller
one misses, and that member's mass floods the reference density.

The witness: `K₁ = B(0,1)`, `K₂ = B(0,2)`, `W 0 = B(0,t)` and `W 1 = B(0,2) = K₂`.  Inside `K₁`
the family is the single tiny body `W 0`, which concentrates all of its mass in a set of
relative volume `t`; inside `K₂` the family additionally contains a body filling `K₂`, and a
family containing its own container is `1`-Frostman in it.

This is a statement about `frostmanConstIn` and containers only; it uses no tube geometry, and
the same phenomenon occurs with many equal-sized members in place of the single large `W 1`. -/
theorem container_change_false_of_no_density_comparison {t : ℝ} (ht0 : 0 < t) (ht1 : t ≤ 1) :
    ∃ (W : Fin 2 → ConvexSpaceBody ℝ) (K₁ K₂ : ConvexSpaceBody ℝ),
      K₁ ≤ K₂ ∧
      volume K₂.carrier = 2 * volume K₁.carrier ∧
      frostmanConstIn (familyIn Finset.univ W K₂) W K₂ ≤ 1 ∧
      ENNReal.ofReal (1 / (2 * t))
        ≤ frostmanConstIn (familyIn Finset.univ W K₁) W K₁ := by
  classical
  set K₁ : ConvexSpaceBody ℝ := ConvexSpaceBody.closedBall 0 1 zero_le_one with hK₁
  set K₂ : ConvexSpaceBody ℝ := ConvexSpaceBody.closedBall 0 2 (by norm_num) with hK₂
  set W : Fin 2 → ConvexSpaceBody ℝ := fun i => if i = 0 then
    ConvexSpaceBody.closedBall 0 t ht0.le else K₂ with hW
  have hW0 : W 0 = ConvexSpaceBody.closedBall 0 t ht0.le := by simp [hW]
  have hW1 : W 1 = K₂ := by simp [hW]
  have hvol0 : volume (W 0).carrier = ENNReal.ofReal (2 * t) := by
    rw [hW0]; simp [Real.volume_closedBall]
  have hvolK₁ : volume K₁.carrier = ENNReal.ofReal 2 := by
    rw [hK₁]; simp [Real.volume_closedBall]
  have hvolK₂ : volume K₂.carrier = ENNReal.ofReal 4 := by
    rw [hK₂]; simp [Real.volume_closedBall, show (2 : ℝ) * 2 = 4 by norm_num]
  have hK₁K₂ : K₁ ≤ K₂ := by
    refine SetLike.coe_subset_coe.mp ?_
    simp only [hK₁, hK₂]
    exact Metric.closedBall_subset_closedBall (by norm_num)
  have hW0K₁ : W 0 ≤ K₁ := by
    refine SetLike.coe_subset_coe.mp ?_
    simp only [hW0, hK₁]
    exact Metric.closedBall_subset_closedBall ht1
  have hW1K₁ : ¬ (W 1 ≤ K₁) := by
    intro h
    have hc : K₂.carrier ⊆ K₁.carrier := by
      rw [← hW1]; exact SetLike.coe_subset_coe.mpr h
    have h2 : (2 : ℝ) ∈ K₁.carrier := by
      refine hc ?_
      simp only [hK₂, ConvexSpaceBody.closedBall_carrier, Metric.mem_closedBall, Real.dist_eq]
      norm_num
    rw [hK₁] at h2
    simp only [ConvexSpaceBody.closedBall_carrier, Metric.mem_closedBall] at h2
    norm_num at h2
  have hW0K₂ : W 0 ≤ K₂ := hW0K₁.trans hK₁K₂
  have hW1K₂ : W 1 ≤ K₂ := le_of_eq hW1
  have hfam₂ : familyIn (Finset.univ : Finset (Fin 2)) W K₂ = Finset.univ := by
    ext i
    fin_cases i <;> simp [familyIn, hW0K₂, hW1K₂]
  have hfam₁ : familyIn (Finset.univ : Finset (Fin 2)) W K₁ = {0} := by
    ext i
    fin_cases i <;> simp [familyIn, hW0K₁, hW1K₁]
  refine ⟨W, K₁, K₂, hK₁K₂, ?_, ?_, ?_⟩
  · rw [hvolK₁, hvolK₂, ← ENNReal.ofReal_ofNat 2, ← ENNReal.ofReal_mul (by norm_num)]
    norm_num
  · -- the family fills its own container, so it is `1`-Frostman there
    rw [hfam₂]
    refine frostmanConstIn_le ?_
    intro K' hK'
    have hden₂ : (1 : ENNReal) ≤ densityIn (Finset.univ : Finset (Fin 2)) W K₂ := by
      have hsum : volume K₂.carrier ≤ ∑ i ∈ Finset.univ with W i ≤ K₂, volume (W i).carrier := by
        have hmem : (1 : Fin 2) ∈ Finset.univ.filter (fun i => W i ≤ K₂) := by
          simp [hW1]
        calc volume K₂.carrier = volume (W 1).carrier := by rw [hW1]
          _ ≤ _ := Finset.single_le_sum (f := fun i => volume (W i).carrier)
                (fun i _ => bot_le) hmem
      have h0 : volume K₂.carrier ≠ 0 := by rw [hvolK₂]; simp
      have htop : volume K₂.carrier ≠ ⊤ := by rw [hvolK₂]; simp
      rw [show densityIn (Finset.univ : Finset (Fin 2)) W K₂
        = (∑ i ∈ Finset.univ with W i ≤ K₂, volume (W i).carrier) / volume K₂.carrier from rfl]
      exact ENNReal.le_div_iff_mul_le (Or.inl h0) (Or.inl htop) |>.mpr (by simpa using hsum)
    by_cases h1 : W 1 ≤ K'
    · have : K' = K₂ := le_antisymm hK' (hW1 ▸ h1)
      rw [this, one_mul]
    · refine le_trans ?_ (by simpa using hden₂)
      have hfil : (Finset.univ : Finset (Fin 2)).filter (fun i => W i ≤ K')
          = if W 0 ≤ K' then {0} else ∅ := by
        ext i
        fin_cases i <;> by_cases h0 : W 0 ≤ K' <;> simp [h0, h1]
      have hsum : (∑ i ∈ Finset.univ with W i ≤ K', volume (W i).carrier)
          ≤ volume K'.carrier := by
        by_cases h0 : W 0 ≤ K'
        · rw [hfil, if_pos h0, Finset.sum_singleton]
          exact measure_mono (SetLike.coe_subset_coe.mpr h0)
        · rw [hfil, if_neg h0, Finset.sum_empty]
          exact bot_le
      exact ENNReal.div_le_of_le_mul (by simpa using hsum)
  · -- inside `K₁` the family is the single tiny body, and it concentrates
    rw [hfam₁]
    refine le_frostmanConstIn_of_lt_densityIn hW0K₁ ?_
    have hd₁ : densityIn ({0} : Finset (Fin 2)) W K₁ = ENNReal.ofReal t := by
      rw [densityIn_of_all_le (fun i hi => by simpa using (Finset.mem_singleton.mp hi) ▸ hW0K₁)]
      rw [Finset.sum_singleton, hvol0, hvolK₁, ← ENNReal.ofReal_div_of_pos (by norm_num)]
      norm_num
    have hd₂ : densityIn ({0} : Finset (Fin 2)) W (W 0) = 1 := by
      rw [densityIn_of_all_le (fun i hi => by simpa using (Finset.mem_singleton.mp hi) ▸
        (le_refl (W 0)))]
      rw [Finset.sum_singleton, hvol0]
      refine ENNReal.div_self ?_ ?_
      · simp; positivity
      · exact ENNReal.ofReal_ne_top
    rw [hd₁, hd₂, ← ENNReal.ofReal_mul (by positivity)]
    refine ENNReal.ofReal_lt_one.mpr ?_
    rw [div_mul_eq_mul_div, one_mul]
    rw [div_lt_one (by positivity)]
    linarith

end Counterexample

end ConvexSpaceBody
