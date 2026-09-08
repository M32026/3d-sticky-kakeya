module

public import Kakeya.Uniform.Tree

@[expose] public section

open MeasureTheory Real
open scoped ENNReal NNReal

namespace Kakeya.ml1Boot.TrialRestartW94

noncomputable section
set_option autoImplicit false

universe uE uI

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace Real E]
  [FiniteDimensional Real E] [Nontrivial E]
  [MeasurableSpace E] [BorelSpace E]

open Classical in
/-- Proposed H2 interface. Awaiting formalization review; no proof is adopted. -/
theorem exists_actual_raw_tree_close_w96
    {iota : Type uI} {delta : NNReal} (hdelta : 0 < delta) (hdelta_one : delta < 1)
    (F : Finset iota) (T : iota -> Tube delta E)
    (hinj : Set.InjOn (fun i => (T i).carrier) (F : Set iota))
    (M : Nat) (hM : 0 < M)
    (hgap : (delta : Real) ^ ((1 : Real) / (M : Real)) <= 1 / 2)
    (hball : ∀ ⦃i⦄, i ∈ F -> (T i).carrier ⊆ Metric.closedBall (0 : E) 1)
    (hF : F.Nonempty) :
    let rho : Nat -> NNReal := fun k => delta ^ ((k : Real) / (M : Real))
    ∃ (parent : Nat -> Finset iota) (assign : Nat -> iota -> iota) (root : iota)
      (W : ∀ k, iota -> Tube (rho k) E),
      (∀ k, k <= M -> ∀ ⦃i⦄, i ∈ F -> assign k i ∈ parent k) ∧
      (∀ ⦃i⦄, i ∈ F -> assign M i = i) ∧
      (∀ k, k < M -> ∀ ⦃i j⦄, i ∈ F -> j ∈ F ->
        assign (k + 1) i = assign (k + 1) j -> assign k i = assign k j) ∧
      (∀ k, k <= M -> ∀ ⦃i⦄, i ∈ F ->
        (T i).toConvexSpaceBody <= (W k (assign k i)).toConvexSpaceBody) ∧
      (∀ ⦃i⦄, i ∈ F -> (W M i).toConvexSpaceBody = (T i).toConvexSpaceBody) ∧
      (∀ ⦃i⦄, i ∈ F -> (W M i).carrier = (T i).carrier) ∧
      (∀ k, k <= M -> Set.InjOn (W k) (parent k : Set iota)) ∧
      (∀ k, k <= M -> ∀ (V : Tube (rho k) E),
        ((parent k).filter (fun v => ∃ i ∈ F,
          (T i).toConvexSpaceBody <= (W k v).toConvexSpaceBody ∧
          (T i).toConvexSpaceBody <= V.toConvexSpaceBody)).card <=
            Tube.overlapConstBOTight (Module.finrank Real E)) ∧
      (∀ k, 1 <= k -> k <= M -> ∀ ⦃i j⦄, i ∈ F -> j ∈ F -> assign k i = assign k j ->
        (T i).toConvexSpaceBody <= ((T j).rescale (rho k)).toConvexSpaceBody) ∧
      (∀ k, k < M -> ((parent k).card : Real) <=
        (641 : Real) ^ (2 * Module.finrank Real E) *
          ((4 : Real) / ((rho k : NNReal) : Real)) ^ (2 * Module.finrank Real E)) ∧
      (∀ k, k < M -> ∀ ⦃i⦄, i ∈ F ->
        (W (k + 1) (assign (k + 1) i)).toConvexSpaceBody <=
          (W k (assign k i)).toConvexSpaceBody) ∧
      (∀ k, k <= M -> ∀ ⦃i⦄, i ∈ F ->
        ‖(T i).midpoint - (W k (assign k i)).midpoint‖ <= (rho k : Real) / 16) ∧
      (∀ k, k <= M -> ∀ ⦃i⦄, i ∈ F ->
        ‖(T i).direction - (W k (assign k i)).direction‖ <= (rho k : Real) / 8) := by
  exact (open _root_.Tube in by
    have hL4 {ι : Type uI} {δ : NNReal} (_hδ : 0 < δ) (_hδ1 : δ < 1)
        (s : Finset ι) (T : ι → Tube δ E)
        (M : ℕ) (hM_pos : 0 < M) (ρ : ℕ → NNReal) (_hρ : ρ = fun k : ℕ => δ ^ ((k : ℝ) / (M : ℝ)))
        (P : ∀ k, Finset (Tube (ρ k) E))
        (chain_proj : ∀ k, k < M → ∀ w ∈ P (k + 1),
          ∃ w' ∈ P k, w.toConvexSpaceBody ≤ w'.toConvexSpaceBody ∧
            ‖w.midpoint - w'.midpoint‖ ≤ ((ρ k : NNReal) : ℝ) / 32 ∧
            ‖w.direction - w'.direction‖ ≤ ((ρ k : NNReal) : ℝ) / 16)
        (_hcover : ∀ k ≤ M, ∀ ⦃i⦄, i ∈ s →
          ∃ W ∈ P k, (T i).toConvexSpaceBody ≤ W.toConvexSpaceBody)
        (hleaf : ∀ ⦃i⦄, i ∈ s → ∃ W ∈ P M, W.carrier = (T i).carrier ∧
          W.midpoint = (T i).midpoint ∧ W.direction = (T i).direction)
        (hs_B1 : ∀ ⦃i⦄, i ∈ s → (T i).carrier ⊆ Metric.closedBall (0 : E) 1)
        (hs_ne : s.Nonempty)
        (hT_inj : Set.InjOn (fun i => (T i).carrier) (s : Set ι))
        (hgapρ : ∀ k, k < M → 2 * ((ρ (k + 1) : NNReal) : ℝ) ≤ ((ρ k : NNReal) : ℝ))
        (h2δ : ∀ k, k < M → 2 * (δ : ℝ) ≤ ((ρ k : NNReal) : ℝ))
        (hoverlap : ∀ k ≤ M, ∀ (V : Tube (ρ k) E),
            ((P k).filter (fun W => ∃ (U : Tube δ E),
                U.carrier ⊆ Metric.closedBall (0 : E) 1 ∧
                U.toConvexSpaceBody ≤ W.toConvexSpaceBody ∧
                U.toConvexSpaceBody ≤ V.toConvexSpaceBody)).card ≤
              2 * (3073 * Module.finrank ℝ E + 1) ^ (2 * Module.finrank ℝ E))
        (hPcard : ∀ k, k < M → ((P k).card : ℝ) ≤
            (641 : ℝ) ^ (2 * Module.finrank ℝ E)
              * ((4 : ℝ) / ((ρ k : NNReal) : ℝ)) ^ (2 * Module.finrank ℝ E)) :
        ∃ (parent : ℕ → Finset ι) (assign : ℕ → ι → ι) (_root : ι)
          (W : ∀ k, ι → Tube (ρ k) E),
          (∀ k ≤ M, ∀ ⦃i⦄, i ∈ s → assign k i ∈ parent k) ∧
          (∀ ⦃i⦄, i ∈ s → assign M i = i) ∧
          (∀ k, k < M → ∀ ⦃i j⦄, i ∈ s → j ∈ s →
            assign (k + 1) i = assign (k + 1) j → assign k i = assign k j) ∧
          (∀ k ≤ M, ∀ ⦃i⦄, i ∈ s →
            (T i).toConvexSpaceBody ≤ (W k (assign k i)).toConvexSpaceBody) ∧
          (∀ ⦃i⦄, i ∈ s → (W M i).toConvexSpaceBody = (T i).toConvexSpaceBody) ∧
          (∀ ⦃i⦄, i ∈ s → (W M i).carrier = (T i).carrier) ∧
          (∀ k ≤ M, Set.InjOn (W k) (parent k : Set ι)) ∧
          (∀ k ≤ M, ∀ (V : Tube (ρ k) E),
            ((parent k).filter (fun v => ∃ i ∈ s,
                (T i).toConvexSpaceBody ≤ (W k v).toConvexSpaceBody ∧
                (T i).toConvexSpaceBody ≤ V.toConvexSpaceBody)).card ≤
              2 * (3073 * Module.finrank ℝ E + 1) ^ (2 * Module.finrank ℝ E)) ∧
          (∀ k, 1 ≤ k → k ≤ M → ∀ ⦃i j⦄, i ∈ s → j ∈ s → assign k i = assign k j →
            (T i).toConvexSpaceBody ≤ ((T j).rescale (ρ k)).toConvexSpaceBody) ∧
          (∀ k, k < M → ((parent k).card : ℝ) ≤
            (641 : ℝ) ^ (2 * Module.finrank ℝ E)
              * ((4 : ℝ) / ((ρ k : NNReal) : ℝ)) ^ (2 * Module.finrank ℝ E)) ∧
          (∀ k, k < M → ∀ ⦃i⦄, i ∈ s →
            (W (k + 1) (assign (k + 1) i)).toConvexSpaceBody ≤
              (W k (assign k i)).toConvexSpaceBody) ∧
          (∀ k ≤ M, ∀ ⦃i⦄, i ∈ s →
            ‖(T i).midpoint - (W k (assign k i)).midpoint‖ ≤ (ρ k : ℝ) / 16) ∧
          (∀ k ≤ M, ∀ ⦃i⦄, i ∈ s →
            ‖(T i).direction - (W k (assign k i)).direction‖ ≤ (ρ k : ℝ) / 8) := by
      classical
      set D : ℕ := 2 * (3073 * Module.finrank ℝ E + 1) ^ (2 * Module.finrank ℝ E) with hD
      set ρ' : Fin (M + 1) → NNReal := fun j => ρ j.val with hρ'
      set P' : ∀ j : Fin (M + 1), Finset (Tube (ρ' j) E) := fun j => P j.val with hP'
      obtain ⟨i0, hi0⟩ := hs_ne
      set Pbar : ∀ k : ℕ, Finset (Tube (ρ k) E) := P with hPbar
      have hPbar_pos : ∀ {k : ℕ}, k ≠ 0 → Pbar k = P k := fun _ => rfl
      have cproj_bar : ∀ k, k < M → ∀ w ∈ Pbar (k + 1),
          ∃ w' ∈ Pbar k, w.toConvexSpaceBody ≤ w'.toConvexSpaceBody ∧
            ‖w.midpoint - w'.midpoint‖ ≤ ((ρ k : NNReal) : ℝ) / 32 ∧
            ‖w.direction - w'.direction‖ ≤ ((ρ k : NNReal) : ℝ) / 16 := chain_proj
      set Q' : ∀ j : Fin (M + 1), Finset (Tube (ρ' j) E) := fun j => Pbar j.val with hQ'
      have hQ'_ne0 : ∀ j : Fin (M + 1), j ≠ 0 → Q' j = P' j := by
        intro j _
        change Pbar j.val = P j.val
        rfl
      have cproj_Q : ∀ m : Fin M, ∀ w ∈ Q' m.succ, ∃ w' ∈ Q' m.castSucc,
          w.toConvexSpaceBody ≤ w'.toConvexSpaceBody ∧
          ‖w.midpoint - w'.midpoint‖ ≤ ((ρ' m.castSucc : NNReal) : ℝ) / 32 ∧
          ‖w.direction - w'.direction‖ ≤ ((ρ' m.castSucc : NNReal) : ℝ) / 16 := by
        intro m w hw
        have hw' : w ∈ Pbar (m.val + 1) := hw
        obtain ⟨w', hw'mem, hbody, hmid, hdir⟩ := cproj_bar m.val m.isLt w hw'
        exact ⟨w', hw'mem, hbody, hmid, hdir⟩
      have hgap_Q : ∀ m : Fin M, 2 * ((ρ' m.succ : NNReal) : ℝ) ≤ ((ρ' m.castSucc : NNReal) : ℝ) :=
        fun m => hgapρ m.val m.isLt
      have body_of_carrier : ∀ {r₁ r₂ : NNReal} (W₁ : Tube r₁ E) (W₂ : Tube r₂ E),
          W₁.carrier = W₂.carrier → W₁.toConvexSpaceBody = W₂.toConvexSpaceBody := by
        intro r₁ r₂ W₁ W₂ h
        exact ConvexSpaceBody.ext h
      have hlast_ne : (Fin.last M) ≠ 0 := by
        intro h
        rw [← Fin.val_eq_zero_iff, Fin.val_last] at h
        omega
      set leafTube : (i : ι) → i ∈ s → Tube (ρ' (Fin.last M)) E :=
        fun i hi => (hleaf hi).choose with hleafTube
      have leafMem : ∀ (i : ι) (hi : i ∈ s), leafTube i hi ∈ P' (Fin.last M) :=
        fun i hi => (hleaf hi).choose_spec.1
      have leafMem_Q : ∀ (i : ι) (hi : i ∈ s), leafTube i hi ∈ Q' (Fin.last M) := by
        intro i hi; rw [hQ'_ne0 _ hlast_ne]; exact leafMem i hi
      have leafCarrier : ∀ (i : ι) (hi : i ∈ s), (leafTube i hi).carrier = (T i).carrier :=
        fun i hi => (hleaf hi).choose_spec.2.1
      have leafMid : ∀ (i : ι) (hi : i ∈ s), (leafTube i hi).midpoint = (T i).midpoint :=
        fun i hi => (hleaf hi).choose_spec.2.2.1
      have leafDir : ∀ (i : ι) (hi : i ∈ s), (leafTube i hi).direction = (T i).direction :=
        fun i hi => (hleaf hi).choose_spec.2.2.2
      set anc : (i : ι) → i ∈ s → (j : Fin (M + 1)) → Tube (ρ' j) E :=
        fun i hi j => chainOfClose ρ' Q' cproj_Q hgap_Q j (leafTube i hi) (leafMem_Q i hi) with hanc
      have ancMem : ∀ (i : ι) (hi : i ∈ s) (j : Fin (M + 1)), anc i hi j ∈ Q' j :=
        fun i hi j => chainOfClose_mem ρ' Q' cproj_Q hgap_Q j (leafTube i hi) (leafMem_Q i hi)
      have ancLeafBody : ∀ (i : ι) (hi : i ∈ s) (j : Fin (M + 1)),
          (leafTube i hi).toConvexSpaceBody ≤ (anc i hi j).toConvexSpaceBody :=
        fun i hi j => chainOfClose_body_le ρ' Q' cproj_Q hgap_Q j (leafTube i hi) (leafMem_Q i hi)
      have ancLast : ∀ (i : ι) (hi : i ∈ s), anc i hi (Fin.last M) = leafTube i hi :=
        fun i hi => chainOfClose_last ρ' Q' cproj_Q hgap_Q (leafTube i hi) (leafMem_Q i hi)
      have ancCover : ∀ (i : ι) (hi : i ∈ s) (j : Fin (M + 1)),
          (T i).toConvexSpaceBody ≤ (anc i hi j).toConvexSpaceBody := by
        intro i hi j
        have hTleaf : (T i).toConvexSpaceBody = (leafTube i hi).toConvexSpaceBody :=
          (body_of_carrier (T i) (leafTube i hi) (leafCarrier i hi).symm)
        rw [hTleaf]; exact ancLeafBody i hi j
      have ancStepDet : ∀ (m : Fin M) (i i' : ι) (hi : i ∈ s) (hi' : i' ∈ s),
          anc i hi m.succ = anc i' hi' m.succ → anc i hi m.castSucc = anc i' hi' m.castSucc :=
        fun m i i' hi hi' h => chainOfClose_castSucc_determined ρ' Q' cproj_Q hgap_Q m
          (leafTube i hi) (leafTube i' hi') (leafMem_Q i hi) (leafMem_Q i' hi') h
      have ancCloseMid : ∀ (i : ι) (hi : i ∈ s) (j : Fin (M + 1)),
          ‖(T i).midpoint - (anc i hi j).midpoint‖ ≤ ((ρ' j : NNReal) : ℝ) / 16 := by
        intro i hi j
        have h := chainOfClose_close_mid ρ' Q' cproj_Q hgap_Q j (leafTube i hi) (leafMem_Q i hi)
        rwa [leafMid i hi] at h
      have ancCloseDir : ∀ (i : ι) (hi : i ∈ s) (j : Fin (M + 1)),
          ‖(T i).direction - (anc i hi j).direction‖ ≤ ((ρ' j : NNReal) : ℝ) / 8 := by
        intro i hi j
        have h := chainOfClose_close_dir ρ' Q' cproj_Q hgap_Q j (leafTube i hi) (leafMem_Q i hi)
        rwa [leafDir i hi] at h
      set kf : ℕ → Fin (M + 1) := fun k => if h : k ≤ M then ⟨k, by omega⟩ else Fin.last M with hkf
      have kf_val : ∀ {k : ℕ}, k ≤ M → (kf k).val = k := by
        intro k hk; simp only [hkf, dif_pos hk]
      set repOf : (j : Fin (M + 1)) → Tube (ρ' j) E → ι :=
        fun j v => if h : ∃ r, ∃ hr : r ∈ s, anc r hr j = v then h.choose else i0 with hrepOf
      have repOf_spec : ∀ (j : Fin (M + 1)) (i : ι) (hi : i ∈ s),
          ∃ (hr : repOf j (anc i hi j) ∈ s), anc (repOf j (anc i hi j)) hr j = anc i hi j := by
        intro j i hi
        have hex : ∃ r, ∃ hr : r ∈ s, anc r hr j = anc i hi j := ⟨i, hi, rfl⟩
        have heq : repOf j (anc i hi j) = hex.choose := by simp only [hrepOf, dif_pos hex]
        rw [heq]; exact hex.choose_spec
      have repOf_mem : ∀ (j : Fin (M + 1)) (v : Tube (ρ' j) E), repOf j v ∈ s := by
        intro j v
        by_cases h : ∃ r, ∃ hr : r ∈ s, anc r hr j = v
        · have heq : repOf j v = h.choose := by simp only [hrepOf, dif_pos h]
          rw [heq]; obtain ⟨hr, _⟩ := h.choose_spec; exact hr
        · have heq : repOf j v = i0 := by simp only [hrepOf, dif_neg h]
          rw [heq]; exact hi0
      have repOf_anc : ∀ (j : Fin (M + 1)) (i : ι) (hi : i ∈ s),
          anc (repOf j (anc i hi j)) (repOf_mem j (anc i hi j)) j = anc i hi j := by
        intro j i hi
        obtain ⟨hr, hrr⟩ := repOf_spec j i hi
        convert hrr using 2
      set assignA : ℕ → ι → ι :=
        fun k i => if hi : i ∈ s then (if k = M then i else repOf (kf k) (anc i hi (kf k))) else i
        with hassignA
      set assignBO : ℕ → ι → ι := fun k i => if k = 0 then assignA k i else assignA k i with hassignBO
      set parentBO : ℕ → Finset ι := fun k => s.image (assignBO k) with hparentBO
      set WA : ∀ k, ι → Tube (ρ k) E :=
        fun k v => if hv : v ∈ s then Tube.mk' (ρ k) (anc v hv (kf k)).dist_eq_one
          else Tube.mk' (ρ k) (T i0).dist_eq_one with hWA
      set WBO : ∀ k, ι → Tube (ρ k) E :=
        fun k v => if _hk0 : k = 0 then WA k v else WA k v with hWBO
      have cast_carrier : ∀ {a b : NNReal} (e : a = b) (U : Tube a E),
          (e ▸ U).carrier = U.carrier := by
        intro a b e U; cases e; rfl
      have hρeq : ∀ {k : ℕ}, k ≤ M → ρ k = ρ' (kf k) := by
        intro k hk; simp only [hρ', kf_val hk]
      have Wcarrier : ∀ {k : ℕ} (hk : k ≤ M) {v : ι} (hv : v ∈ s),
          (WA k v).carrier = (anc v hv (kf k)).carrier := by
        intro k hk v hv
        simp only [hWA, dif_pos hv]
        rw [Tube.mk'_carrier, (anc v hv (kf k)).carrier_eq, hρeq hk]
      have Wbody : ∀ {k : ℕ} (hk : k ≤ M) {v : ι} (hv : v ∈ s),
          (WA k v).toConvexSpaceBody = (anc v hv (kf k)).toConvexSpaceBody := by
        intro k hk v hv
        exact body_of_carrier _ _ (Wcarrier hk hv)
      have hWBO_pos : ∀ {k : ℕ}, k ≠ 0 → ∀ v, WBO k v = WA k v := by
        intro k hk v; simp only [hWBO, dif_neg hk]
      have hWBO_all : ∀ (k : ℕ) (v : ι), WBO k v = WA k v := by
        intro k v; simp only [hWBO]; split <;> rfl
      have hassignBO_all : ∀ (k : ℕ) (i : ι), assignBO k i = assignA k i := by
        intro k i; simp only [hassignBO]; split <;> rfl
      have assignA_mem : ∀ (k : ℕ) {i : ι}, i ∈ s → assignA k i ∈ s := by
        intro k i hi
        simp only [hassignA, dif_pos hi]
        split
        · exact hi
        · exact repOf_mem _ _
      have assignBO_mem : ∀ (k : ℕ) {i : ι}, i ∈ s → assignBO k i ∈ s := by
        intro k i hi
        rw [hassignBO_all]
        exact assignA_mem k hi
      have anc_congr : ∀ {a b : ι} (ha : a ∈ s) (hb : b ∈ s) (j : Fin (M + 1)),
          a = b → anc a ha j = anc b hb j := by
        intro a b ha hb j hab; subst hab; rfl
      have assignA_anc : ∀ {k : ℕ}, k ≤ M → ∀ {i : ι} (hi : i ∈ s),
          anc (assignA k i) (assignA_mem k hi) (kf k) = anc i hi (kf k) := by
        intro k hk i hi
        by_cases hkM : k = M
        · have hai : assignA k i = i := by simp only [hassignA, dif_pos hi, if_pos hkM]
          exact anc_congr (assignA_mem k hi) hi (kf k) hai
        · have hai : assignA k i = repOf (kf k) (anc i hi (kf k)) := by
            simp only [hassignA, dif_pos hi, if_neg hkM]
          rw [anc_congr (assignA_mem k hi) (repOf_mem _ _) (kf k) hai]
          exact repOf_anc (kf k) i hi
      have Wmid : ∀ {k : ℕ} {v : ι} (hv : v ∈ s),
          (WA k v).midpoint = (anc v hv (kf k)).midpoint := by
        intro k v hv
        simp only [hWA, dif_pos hv, Tube.midpoint, Tube.mk'_x, Tube.mk'_y]
      have Wdir : ∀ {k : ℕ} {v : ι} (hv : v ∈ s),
          (WA k v).direction = (anc v hv (kf k)).direction := by
        intro k v hv
        simp only [hWA, dif_pos hv, Tube.direction, Tube.mk'_x, Tube.mk'_y]
      refine ⟨parentBO, assignBO, i0, WBO, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · intro k _ i hi
        exact Finset.mem_image_of_mem (assignBO k) hi
      · intro i hi
        simp only [hassignBO, if_neg hM_pos.ne', hassignA, dif_pos hi, if_true]
      · intro k hkM i j hi hj hsucc
        · rw [hassignBO_all (k + 1) i, hassignBO_all (k + 1) j] at hsucc
          rw [hassignBO_all k i, hassignBO_all k j]
          by_cases hk1 : k + 1 = M
          · have hai : assignA (k + 1) i = i := by simp only [hassignA, dif_pos hi, if_pos hk1]
            have haj : assignA (k + 1) j = j := by simp only [hassignA, dif_pos hj, if_pos hk1]
            rw [hai, haj] at hsucc
            rw [hsucc]
          · have hk1M : k + 1 ≤ M := hkM
            have hk1lt : k + 1 < M := lt_of_le_of_ne hk1M hk1
            have hai : assignA (k + 1) i = repOf (kf (k + 1)) (anc i hi (kf (k + 1))) := by
              simp only [hassignA, dif_pos hi, if_neg hk1]
            have haj : assignA (k + 1) j = repOf (kf (k + 1)) (anc j hj (kf (k + 1))) := by
              simp only [hassignA, dif_pos hj, if_neg hk1]
            rw [hai, haj] at hsucc
            have hanceq1 : anc i hi (kf (k + 1)) = anc j hj (kf (k + 1)) := by
              have h1 := repOf_anc (kf (k + 1)) i hi
              have h2 := repOf_anc (kf (k + 1)) j hj
              rw [← h1, ← h2]
              exact anc_congr (repOf_mem _ _) (repOf_mem _ _) (kf (k + 1)) hsucc
            set m : Fin M := ⟨k, by omega⟩ with hm
            have hkk : k ≤ M := by omega
            have hsucc_eq : kf (k + 1) = m.succ := by
              apply Fin.ext; rw [kf_val hk1M, Fin.val_succ]
            have hcast_eq : kf k = m.castSucc := by
              apply Fin.ext; rw [kf_val hkk, Fin.val_castSucc]
            have hanceq0 : anc i hi (kf k) = anc j hj (kf k) := by
              rw [hcast_eq]; rw [hsucc_eq] at hanceq1
              exact ancStepDet m i j hi hj hanceq1
            have hkne : k ≠ M := by omega
            have haik : assignA k i = repOf (kf k) (anc i hi (kf k)) := by
              simp only [hassignA, dif_pos hi, if_neg hkne]
            have hajk : assignA k j = repOf (kf k) (anc j hj (kf k)) := by
              simp only [hassignA, dif_pos hj, if_neg hkne]
            rw [haik, hajk, hanceq0]
      · intro k hk i hi
        · have hassignBO_eq : assignBO k i = assignA k i := hassignBO_all k i
          rw [hWBO_all k (assignBO k i), Wbody hk (assignBO_mem k hi),
              anc_congr (assignBO_mem k hi) (assignA_mem k hi) (kf k) hassignBO_eq,
              assignA_anc hk hi]
          exact ancCover i hi (kf k)
      · intro i hi
        rw [hWBO_pos hM_pos.ne' i, Wbody (le_refl M) hi]
        have hkfM : kf M = Fin.last M := by apply Fin.ext; rw [kf_val (le_refl M), Fin.val_last]
        rw [hkfM, ancLast i hi]
        exact body_of_carrier _ _ (leafCarrier i hi)
      · intro i hi
        rw [hWBO_pos hM_pos.ne' i, Wcarrier (le_refl M) hi]
        have hkfM : kf M = Fin.last M := by apply Fin.ext; rw [kf_val (le_refl M), Fin.val_last]
        rw [hkfM, ancLast i hi]
        exact leafCarrier i hi
      · intro k hk a ha b hb hWab
        · have hparent_sub : ∀ {x : ι}, x ∈ parentBO k → x ∈ s := by
            intro x hx; rw [hparentBO, Finset.mem_image] at hx
            obtain ⟨i, hi, rfl⟩ := hx; exact assignBO_mem k hi
          have haS : a ∈ s := hparent_sub (Finset.mem_coe.mp ha)
          have hbS : b ∈ s := hparent_sub (Finset.mem_coe.mp hb)
          rw [hWBO_all k a, hWBO_all k b] at hWab
          have hanc_eq : anc a haS (kf k) = anc b hbS (kf k) := by
            refine Tube.ext ?_ ?_ ?_
            · rw [← Wcarrier hk haS, ← Wcarrier hk hbS, hWab]
            · have hxa : (WA k a).x = (anc a haS (kf k)).x := by
                simp only [hWA, dif_pos haS, Tube.mk'_x]
              have hxb : (WA k b).x = (anc b hbS (kf k)).x := by
                simp only [hWA, dif_pos hbS, Tube.mk'_x]
              rw [← hxa, ← hxb, hWab]
            · have hya : (WA k a).y = (anc a haS (kf k)).y := by
                simp only [hWA, dif_pos haS, Tube.mk'_y]
              have hyb : (WA k b).y = (anc b hbS (kf k)).y := by
                simp only [hWA, dif_pos hbS, Tube.mk'_y]
              rw [← hya, ← hyb, hWab]
          by_cases hkM : k = M
          · have hkfM : kf k = Fin.last M := by
              apply Fin.ext; rw [kf_val hk, Fin.val_last, hkM]
            rw [hkfM, ancLast a haS, ancLast b hbS] at hanc_eq
            have hcar : (T a).carrier = (T b).carrier := by
              rw [← leafCarrier a haS, ← leafCarrier b hbS, hanc_eq]
            exact hT_inj (Finset.mem_coe.mpr haS) (Finset.mem_coe.mpr hbS) hcar
          · rw [hparentBO, Finset.mem_coe, Finset.mem_image] at ha hb
            obtain ⟨i, hi, hai⟩ := ha
            obtain ⟨j, hj, hbj⟩ := hb
            have haik : a = repOf (kf k) (anc i hi (kf k)) := by
              rw [← hai]; simp only [hassignBO_all, hassignA, dif_pos hi, if_neg hkM]
            have hbjk : b = repOf (kf k) (anc j hj (kf k)) := by
              rw [← hbj]; simp only [hassignBO_all, hassignA, dif_pos hj, if_neg hkM]
            have hAi : anc a haS (kf k) = anc i hi (kf k) :=
              (anc_congr haS (repOf_mem _ _) (kf k) haik).trans (repOf_anc (kf k) i hi)
            have hBj : anc b hbS (kf k) = anc j hj (kf k) :=
              (anc_congr hbS (repOf_mem _ _) (kf k) hbjk).trans (repOf_anc (kf k) j hj)
            rw [haik, hbjk, ← hAi, ← hBj, hanc_eq]
      · intro k hk V
        · have hparent_sub : ∀ {x : ι}, x ∈ parentBO k → x ∈ s := by
            intro x hx; rw [hparentBO, Finset.mem_image] at hx
            obtain ⟨i, hi, rfl⟩ := hx; exact assignBO_mem k hi
          have hkfkM : (kf k).val ≤ M := by rw [kf_val hk]; exact hk
          have hQ'P : Q' (kf k) = P ((kf k).val) := rfl
          have hρVk : ρ ((kf k).val) = ρ k := by rw [kf_val hk]
          set g : ι → Tube (ρ ((kf k).val)) E :=
            fun v => if hv : v ∈ s then anc v hv (kf k) else anc i0 hi0 (kf k) with hg
          set V' : Tube (ρ ((kf k).val)) E := hρVk ▸ V with hV'
          set LHS := (parentBO k).filter (fun v => ∃ i ∈ s,
              (T i).toConvexSpaceBody ≤ (WBO k v).toConvexSpaceBody ∧
              (T i).toConvexSpaceBody ≤ V.toConvexSpaceBody) with hLHS
          set RHS := (P ((kf k).val)).filter (fun WW => ∃ (U : Tube δ E),
              U.carrier ⊆ Metric.closedBall (0 : E) 1 ∧
              U.toConvexSpaceBody ≤ WW.toConvexSpaceBody ∧
              U.toConvexSpaceBody ≤ V'.toConvexSpaceBody) with hRHS
          have hcardRHS : RHS.card ≤ D := by
            have h := hoverlap ((kf k).val) hkfkM V'
            simpa only [hRHS, hD] using h
          have hV'carrier : V'.carrier = V.carrier := by rw [hV']; exact cast_carrier hρVk.symm V
          have hV'body : V'.toConvexSpaceBody = V.toConvexSpaceBody :=
            body_of_carrier _ _ hV'carrier
          refine le_trans (Finset.card_le_card_of_injOn g ?_ ?_) hcardRHS
          · intro v hv
            rw [Finset.mem_coe, hLHS, Finset.mem_filter] at hv
            obtain ⟨hvP, i, hiS, hTiW, hTiV⟩ := hv
            have hvS : v ∈ s := hparent_sub hvP
            rw [Finset.mem_coe, hRHS, Finset.mem_filter]
            have hgv : g v = anc v hvS (kf k) := by simp only [hg, dif_pos hvS]
            refine ⟨?_, ?_⟩
            · rw [hgv, ← hQ'P]; exact ancMem v hvS (kf k)
            · refine ⟨T i, hs_B1 hiS, ?_, ?_⟩
              · have hbody : (g v).toConvexSpaceBody = (WBO k v).toConvexSpaceBody := by
                  rw [hgv, hWBO_all k v, Wbody hk hvS]
                rw [hbody]; exact hTiW
              · rw [hV'body]; exact hTiV
          · intro a haL b hbL hgab
            rw [Finset.mem_coe, hLHS, Finset.mem_filter] at haL hbL
            have haS : a ∈ s := hparent_sub haL.1
            have hbS : b ∈ s := hparent_sub hbL.1
            have hga : g a = anc a haS (kf k) := by simp only [hg, dif_pos haS]
            have hgb : g b = anc b hbS (kf k) := by simp only [hg, dif_pos hbS]
            rw [hga, hgb] at hgab
            by_cases hkM : k = M
            · have hkfM : kf k = Fin.last M := by
                apply Fin.ext; rw [kf_val hk, Fin.val_last, hkM]
              rw [hkfM, ancLast a haS, ancLast b hbS] at hgab
              have hcar : (T a).carrier = (T b).carrier := by
                rw [← leafCarrier a haS, ← leafCarrier b hbS, hgab]
              exact hT_inj (Finset.mem_coe.mpr haS) (Finset.mem_coe.mpr hbS) hcar
            · rw [hparentBO, Finset.mem_image] at haL hbL
              obtain ⟨i, hi, hai⟩ := haL.1
              obtain ⟨j, hj, hbj⟩ := hbL.1
              have haik : a = repOf (kf k) (anc i hi (kf k)) := by
                rw [← hai]; simp only [hassignBO_all, hassignA, dif_pos hi, if_neg hkM]
              have hbjk : b = repOf (kf k) (anc j hj (kf k)) := by
                rw [← hbj]; simp only [hassignBO_all, hassignA, dif_pos hj, if_neg hkM]
              have hAi : anc a haS (kf k) = anc i hi (kf k) :=
                (anc_congr haS (repOf_mem _ _) (kf k) haik).trans (repOf_anc (kf k) i hi)
              have hBj : anc b hbS (kf k) = anc j hj (kf k) :=
                (anc_congr hbS (repOf_mem _ _) (kf k) hbjk).trans (repOf_anc (kf k) j hj)
              rw [haik, hbjk, ← hAi, ← hBj, hgab]
      · intro k hk1 hkM i j hi hj hassign
        have hAij : assignA k i = assignA k j := by
          rw [← hassignBO_all k i, ← hassignBO_all k j]
          exact hassign
        rcases eq_or_lt_of_le hkM with hkMeq | hkMlt
        · have hii : assignA k i = i := by simp only [hassignA, dif_pos hi, if_pos hkMeq]
          have hjj : assignA k j = j := by simp only [hassignA, dif_pos hj, if_pos hkMeq]
          have hij : i = j := by rw [← hii, ← hjj, hAij]
          subst hij
          have hρkδ : ρ k = δ := by rw [hkMeq, _hρ]; exact rho_M δ hM_pos
          have hcarr : ((T i).rescale (ρ k)).carrier = (T i).carrier := leaf_carrier_eq hρkδ (T i)
          exact le_of_eq (body_of_carrier (T i) ((T i).rescale (ρ k)) hcarr.symm)
        · have hanc_ij : anc i hi (kf k) = anc j hj (kf k) := by
            rw [← assignA_anc hkM hi, ← assignA_anc hkM hj]
            exact anc_congr (assignA_mem k hi) (assignA_mem k hj) (kf k) hAij
          have hρ'k : ((ρ' (kf k) : NNReal) : ℝ) = ((ρ k : NNReal) : ℝ) := by
            simp only [hρ']; rw [kf_val hkM]
          have hmidI : ‖(T i).midpoint - (anc i hi (kf k)).midpoint‖ ≤ ((ρ k : NNReal) : ℝ) / 16 := by
            have := ancCloseMid i hi (kf k); rwa [hρ'k] at this
          have hmidJ : ‖(T j).midpoint - (anc i hi (kf k)).midpoint‖ ≤ ((ρ k : NNReal) : ℝ) / 16 := by
            have h := ancCloseMid j hj (kf k); rw [hρ'k, ← hanc_ij] at h; exact h
          have hmid : ‖(T i).midpoint - (T j).midpoint‖ ≤ ((ρ k : NNReal) : ℝ) / 8 := by
            have htri : ‖(T i).midpoint - (T j).midpoint‖
                ≤ ‖(T i).midpoint - (anc i hi (kf k)).midpoint‖
                  + ‖(anc i hi (kf k)).midpoint - (T j).midpoint‖ := by
              rw [← dist_eq_norm, ← dist_eq_norm, ← dist_eq_norm]; exact dist_triangle _ _ _
            have hmidJ' : ‖(anc i hi (kf k)).midpoint - (T j).midpoint‖
                ≤ ((ρ k : NNReal) : ℝ) / 16 := by rw [norm_sub_rev]; exact hmidJ
            linarith
          have hdirI : ‖(T i).direction - (anc i hi (kf k)).direction‖ ≤ ((ρ k : NNReal) : ℝ) / 8 := by
            have := ancCloseDir i hi (kf k); rwa [hρ'k] at this
          have hdirJ : ‖(T j).direction - (anc i hi (kf k)).direction‖ ≤ ((ρ k : NNReal) : ℝ) / 8 := by
            have h := ancCloseDir j hj (kf k); rw [hρ'k, ← hanc_ij] at h; exact h
          have hdir : ‖(T i).direction - (T j).direction‖ ≤ ((ρ k : NNReal) : ℝ) / 4 := by
            have htri : ‖(T i).direction - (T j).direction‖
                ≤ ‖(T i).direction - (anc i hi (kf k)).direction‖
                  + ‖(anc i hi (kf k)).direction - (T j).direction‖ := by
              rw [← dist_eq_norm, ← dist_eq_norm, ← dist_eq_norm]; exact dist_triangle _ _ _
            have hdirJ' : ‖(anc i hi (kf k)).direction - (T j).direction‖
                ≤ ((ρ k : NNReal) : ℝ) / 8 := by rw [norm_sub_rev]; exact hdirJ
            linarith
          have hcond : ((ρ k : NNReal) : ℝ) / 8 + (((ρ k : NNReal) : ℝ) / 4) / 2 + (δ : ℝ)
              ≤ ((ρ k : NNReal) : ℝ) := by
            have hρ0 : (0 : ℝ) ≤ ((ρ k : NNReal) : ℝ) := (ρ k).coe_nonneg
            have := h2δ k hkMlt
            linarith
          exact tube_le_rescale_of_close (T i) (T j) hmid hdir hcond
      · intro k hkM
        have hk : k ≤ M := hkM.le
        · have hkM' : k ≠ M := hkM.ne
          have hparent_sub : ∀ {x : ι}, x ∈ parentBO k → x ∈ s := by
            intro x hx; rw [hparentBO, Finset.mem_image] at hx
            obtain ⟨i, hi, rfl⟩ := hx; exact assignBO_mem k hi
          have hQ'P : Q' (kf k) = P ((kf k).val) := rfl
          set g : ι → Tube (ρ ((kf k).val)) E :=
            fun v => if hv : v ∈ s then anc v hv (kf k) else anc i0 hi0 (kf k) with hg
          have hcard_le : (parentBO k).card ≤ (P ((kf k).val)).card := by
            refine Finset.card_le_card_of_injOn g ?_ ?_
            · intro v hv
              have hvS : v ∈ s := hparent_sub hv
              have hgv : g v = anc v hvS (kf k) := by simp only [hg, dif_pos hvS]
              rw [Finset.mem_coe, hgv, ← hQ'P]
              exact ancMem v hvS (kf k)
            · intro a ha b hb hgab
              have haS : a ∈ s := hparent_sub (Finset.mem_coe.mp ha)
              have hbS : b ∈ s := hparent_sub (Finset.mem_coe.mp hb)
              have hga : g a = anc a haS (kf k) := by simp only [hg, dif_pos haS]
              have hgb : g b = anc b hbS (kf k) := by simp only [hg, dif_pos hbS]
              rw [hga, hgb] at hgab
              rw [Finset.mem_coe, hparentBO, Finset.mem_image] at ha hb
              obtain ⟨i, hi, hai⟩ := ha
              obtain ⟨j, hj, hbj⟩ := hb
              have haik : a = repOf (kf k) (anc i hi (kf k)) := by
                rw [← hai]; simp only [hassignBO_all, hassignA, dif_pos hi, if_neg hkM']
              have hbjk : b = repOf (kf k) (anc j hj (kf k)) := by
                rw [← hbj]; simp only [hassignBO_all, hassignA, dif_pos hj, if_neg hkM']
              have hAi : anc a haS (kf k) = anc i hi (kf k) :=
                (anc_congr haS (repOf_mem _ _) (kf k) haik).trans (repOf_anc (kf k) i hi)
              have hBj : anc b hbS (kf k) = anc j hj (kf k) :=
                (anc_congr hbS (repOf_mem _ _) (kf k) hbjk).trans (repOf_anc (kf k) j hj)
              rw [haik, hbjk, ← hAi, ← hBj, hgab]
          have hkfk_lt : (kf k).val < M := by rw [kf_val hk]; exact hkM
          have hPc := hPcard ((kf k).val) hkfk_lt
          have hρcoe : ((ρ ((kf k).val) : NNReal) : ℝ) = ((ρ k : NNReal) : ℝ) := by
            rw [kf_val hk]
          calc ((parentBO k).card : ℝ)
              ≤ ((P ((kf k).val)).card : ℝ) := by exact_mod_cast hcard_le
            _ ≤ (641 : ℝ) ^ (2 * Module.finrank ℝ E)
                  * ((4 : ℝ) / ((ρ ((kf k).val) : NNReal) : ℝ)) ^ (2 * Module.finrank ℝ E) := hPc
            _ = (641 : ℝ) ^ (2 * Module.finrank ℝ E)
                  * ((4 : ℝ) / ((ρ k : NNReal) : ℝ)) ^ (2 * Module.finrank ℝ E) := by rw [hρcoe]
      · intro k hkM i hi
        have hkp1 : k + 1 ≤ M := by omega
        have hk_le_M : k ≤ M := by omega
        rw [hWBO_all (k + 1) (assignBO (k + 1) i), hWBO_all k (assignBO k i)]
        rw [hassignBO_all (k + 1) i, hassignBO_all k i]
        rw [Wbody hkp1 (assignA_mem (k + 1) hi), Wbody hk_le_M (assignA_mem k hi)]
        rw [assignA_anc hkp1 hi, assignA_anc hk_le_M hi]
        rw [hanc]
        set m : Fin M := ⟨k, hkM⟩ with hm
        have hsucc_eq : kf (k + 1) = m.succ := by
          apply Fin.ext
          simp [kf_val hkp1, hm]
        have hcast_eq : kf k = m.castSucc := by
          apply Fin.ext
          simp [kf_val hk_le_M, hm]
        rw [hsucc_eq, hcast_eq]
        exact chainOfClose_step_body_le ρ' Q' cproj_Q hgap_Q m (leafTube i hi) (leafMem_Q i hi)
      · intro k hk i hi
        rw [hWBO_all, hassignBO_all, Wmid (assignA_mem k hi), assignA_anc hk hi]
        simpa only [hρ', kf_val hk] using ancCloseMid i hi (kf k)
      · intro k hk i hi
        rw [hWBO_all, hassignBO_all, Wdir (assignA_mem k hi), assignA_anc hk hi]
        simpa only [hρ', kf_val hk] using ancCloseDir i hi (kf k)
    intro ρ
    classical
    have hρ : ρ = fun k : ℕ => delta ^ ((k : ℝ) / (M : ℝ)) := rfl
    have coe_rho : ∀ j : ℕ, ((ρ j : NNReal) : ℝ) = (delta : ℝ) ^ ((j : ℝ) / (M : ℝ)) := by
      intro j
      change (((delta ^ ((j : ℝ) / (M : ℝ)) : NNReal)) : ℝ) = _
      rw [NNReal.coe_rpow]
    have hgapρ : ∀ k, k < M → 2 * ((ρ (k + 1) : NNReal) : ℝ) ≤ ((ρ k : NNReal) : ℝ) := by
      intro k _hk
      rw [coe_rho (k + 1), coe_rho k, Nat.cast_add, Nat.cast_one]
      exact rho_scale_gap hdelta hM hgap k
    have h2delta : ∀ k, k < M → 2 * (delta : ℝ) ≤ ((ρ k : NNReal) : ℝ) := by
      intro k hk
      rw [coe_rho k]
      exact two_delta_le_rho hdelta hM hgap hk
    obtain ⟨P, chain_proj, _hloc, hcover, hoverlap, hleaf, hPcard⟩ :=
      L2_chain_bo_tight hdelta hdelta_one F T hinj M hM hgap hball
    exact hL4 hdelta hdelta_one F T M hM ρ hρ P chain_proj hcover hleaf hball hF
      hinj hgapρ h2delta hoverlap hPcard
  )

end

end Kakeya.ml1Boot.TrialRestartW94
