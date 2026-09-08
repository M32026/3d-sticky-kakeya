import MyLeanRepo.Kakeya.Streamlined.DilatedCoverUniformization

/-!
# Parent proportions across independent uniform covers

For a uniform surjective cover, the proportion of selected parent indices and
the proportion of their fine preimage differ by at most the uniformity
constant.  Comparing two independent covers of the same fine family therefore
costs the product of their two uniformity constants.

This is the exact finite counting source of the `uniformity^2` loss at one
Section 7 split.
-/

noncomputable section

namespace Kakeya.Streamlined

namespace DilatedTubeCover

/-- A nonempty fine family gives a nonempty coarse family. -/
lemma coarse_nonempty
    {delta rho A : ℝ}
    {fine : TubeFamily delta} {coarse : TubeFamily rho}
    (P : DilatedTubeCover A fine coarse)
    (hfine : fine.Nonempty) :
    coarse.Nonempty := by
  let i : Fin fine.card := ⟨0, hfine⟩
  exact lt_of_le_of_lt (Nat.zero_le _) (P.parent i).isLt

/-- Every surjective assigned cover fiber is nonempty. -/
lemma factoringFiberCount_pos
    {delta rho A : ℝ}
    {fine : TubeFamily delta} {coarse : TubeFamily rho}
    (P : DilatedTubeCover A fine coarse)
    (j : Fin coarse.card) :
    0 < P.toFactoring.fiberCount j := by
  rcases P.parent_surjective j with ⟨i, hi⟩
  change (0 : ENNReal) <
    ((Finset.univ.filter fun x : Fin fine.card => P.parent x = j).card :
      ENNReal)
  exact_mod_cast Finset.card_pos.mpr ⟨i, by simp [hi]⟩

/-- Every finite assigned cover fiber count is finite. -/
lemma factoringFiberCount_ne_top
    {delta rho A : ℝ}
    {fine : TubeFamily delta} {coarse : TubeFamily rho}
    (P : DilatedTubeCover A fine coarse)
    (j : Fin coarse.card) :
    P.toFactoring.fiberCount j ≠ ⊤ := by
  have hfine_ne_top : fine.enncard ≠ ⊤ := by
    simp [TubeFamily.enncard]
  exact ne_top_of_le_ne_top hfine_ne_top
    (P.toFactoring.fiberCount_le_enncard j)

/-- A nonempty coarse family has one minimum selected fiber. -/
lemma exists_minFactoringFiber
    {delta rho A : ℝ}
    {fine : TubeFamily delta} {coarse : TubeFamily rho}
    (P : DilatedTubeCover A fine coarse)
    (hfine : fine.Nonempty) :
    ∃ j : Fin coarse.card,
      ∀ k : Fin coarse.card,
        P.toFactoring.fiberCount j ≤ P.toFactoring.fiberCount k := by
  classical
  have hcoarse := P.coarse_nonempty hfine
  let j₀ : Fin coarse.card := ⟨0, hcoarse⟩
  let fibers : Finset ENNReal :=
    Finset.univ.image P.toFactoring.fiberCount
  have hfibers : fibers.Nonempty :=
    ⟨P.toFactoring.fiberCount j₀,
      Finset.mem_image.mpr ⟨j₀, Finset.mem_univ _, rfl⟩⟩
  let m := fibers.min' hfibers
  have hmmem : m ∈ fibers := fibers.min'_mem hfibers
  rcases Finset.mem_image.mp hmmem with
    ⟨j, _hj, hj⟩
  refine ⟨j, ?_⟩
  intro k
  rw [hj]
  exact fibers.min'_le _ <|
    Finset.mem_image.mpr ⟨k, Finset.mem_univ _, rfl⟩

/--
The fine preimage proportion of a parent set is at most `C` times its parent
proportion, in cross-multiplied form.
-/
lemma factoringFiberIndicesOver_card_mul_coarseCard_le
    {delta rho A : ℝ}
    {fine : TubeFamily delta} {coarse : TubeFamily rho}
    (P : DilatedTubeCover A fine coarse)
    (hfine : fine.Nonempty)
    {C : ENNReal} (huniform : P.toFactoring.FibersAreCUniform C)
    (I : Finset (Fin coarse.card)) :
    ((P.toFactoring.fiberIndicesOver I).card : ENNReal) *
        (coarse.card : ENNReal) ≤
      C * (I.card : ENNReal) * fine.enncard := by
  rcases P.exists_minFactoringFiber hfine with ⟨jmin, hjmin⟩
  have hover :
      ((P.toFactoring.fiberIndicesOver I).card : ENNReal) ≤
        (I.card : ENNReal) * (C * P.toFactoring.fiberCount jmin) := by
    rw [P.toFactoring.fiberIndicesOver_card I]
    calc
      ∑ j ∈ I, P.toFactoring.fiberCount j
          ≤ ∑ _j ∈ I, C * P.toFactoring.fiberCount jmin := by
        apply Finset.sum_le_sum
        intro j _hj
        exact huniform.2 j jmin
      _ = (I.card : ENNReal) * (C * P.toFactoring.fiberCount jmin) := by
        simp [Finset.sum_const, nsmul_eq_mul]
  have htotal :
      (coarse.card : ENNReal) * P.toFactoring.fiberCount jmin ≤ fine.enncard := by
    rw [← P.sum_factoringFiberCount]
    calc
      (coarse.card : ENNReal) * P.toFactoring.fiberCount jmin
          = ∑ _j : Fin coarse.card, P.toFactoring.fiberCount jmin := by
            simp [nsmul_eq_mul]
      _ ≤ ∑ j : Fin coarse.card, P.toFactoring.fiberCount j := by
        exact Finset.sum_le_sum fun j _ => hjmin j
  calc
    ((P.toFactoring.fiberIndicesOver I).card : ENNReal) *
          (coarse.card : ENNReal)
        ≤ ((I.card : ENNReal) * (C * P.toFactoring.fiberCount jmin)) *
            (coarse.card : ENNReal) := by
          exact mul_le_mul_right' hover _
    _ = C * (I.card : ENNReal) *
          ((coarse.card : ENNReal) * P.toFactoring.fiberCount jmin) := by
        ring
    _ ≤ C * (I.card : ENNReal) * fine.enncard := by
      exact mul_le_mul_left' htotal _

/--
An arbitrary fine-index set has normalized size at most `C` times the
normalized size of its parent image.
-/
lemma fineIndexSet_card_mul_coarseCard_le
    {delta rho A : ℝ}
    {fine : TubeFamily delta} {coarse : TubeFamily rho}
    (P : DilatedTubeCover A fine coarse)
    (hfine : fine.Nonempty)
    {C : ENNReal} (huniform : P.toFactoring.FibersAreCUniform C)
    (X : Finset (Fin fine.card)) :
    (X.card : ENNReal) * (coarse.card : ENNReal) ≤
      C * ((X.image P.parent).card : ENNReal) * fine.enncard := by
  have hsubset :
      X ⊆ P.toFactoring.fiberIndicesOver (X.image P.parent) := by
    intro i hi
    change i ∈ Finset.univ.filter fun x : Fin fine.card =>
      P.parent x ∈ X.image P.parent
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ i, ?_⟩
    exact Finset.mem_image.mpr ⟨i, hi, rfl⟩
  have hcard :
      (X.card : ENNReal) ≤
        ((P.toFactoring.fiberIndicesOver
          (X.image P.parent)).card : ENNReal) := by
    exact_mod_cast Finset.card_le_card hsubset
  calc
    (X.card : ENNReal) * (coarse.card : ENNReal)
        ≤ ((P.toFactoring.fiberIndicesOver
              (X.image P.parent)).card : ENNReal) *
            (coarse.card : ENNReal) := by
          exact mul_le_mul_right' hcard _
    _ ≤ C * ((X.image P.parent).card : ENNReal) * fine.enncard :=
      P.factoringFiberIndicesOver_card_mul_coarseCard_le
        hfine huniform (X.image P.parent)

/--
Comparing parent proportions across two independent uniform covers costs the
product of the two uniformity constants.
-/
lemma parentCard_mul_leftCard_le_twoUniformity_mul_rightCard_mul_imageCard
    {delta rho sigma A B : ℝ}
    {fine : TubeFamily delta}
    {left : TubeFamily rho} {right : TubeFamily sigma}
    (P : DilatedTubeCover A fine left)
    (Q : DilatedTubeCover B fine right)
    (hfine : fine.Nonempty)
    {CP CQ : ENNReal}
    (hP : P.toFactoring.FibersAreCUniform CP)
    (hQ : Q.toFactoring.FibersAreCUniform CQ)
    (I : Finset (Fin right.card)) :
    (I.card : ENNReal) * (left.card : ENNReal) ≤
      CQ * CP * (right.card : ENNReal) *
        (((Q.toFactoring.fiberIndicesOver I).image
          P.parent).card : ENNReal) := by
  let X := Q.toFactoring.fiberIndicesOver I
  let J := X.image P.parent
  have hq :
      (I.card : ENNReal) * fine.enncard ≤
        CQ * (right.card : ENNReal) * (X.card : ENNReal) :=
    Q.toFactoring
      |>.parentCard_mul_fineCard_le_uniformity_mul_coarseCard_mul_overCard
      hQ I
  have hp :
      (X.card : ENNReal) * (left.card : ENNReal) ≤
        CP * (J.card : ENNReal) * fine.enncard :=
    P.fineIndexSet_card_mul_coarseCard_le hfine hP X
  have hfine_zero : fine.enncard ≠ 0 := by
    simp [TubeFamily.enncard, Nat.ne_of_gt hfine]
  have hfine_top : fine.enncard ≠ ⊤ := by
    simp [TubeFamily.enncard]
  apply
    (ENNReal.mul_le_mul_iff_left hfine_zero hfine_top).mp
  calc
    (I.card : ENNReal) * (left.card : ENNReal) * fine.enncard
        = ((I.card : ENNReal) * fine.enncard) *
            (left.card : ENNReal) := by ring
    _ ≤ (CQ * (right.card : ENNReal) * (X.card : ENNReal)) *
          (left.card : ENNReal) := by
      exact mul_le_mul_right' hq _
    _ = CQ * (right.card : ENNReal) *
          ((X.card : ENNReal) * (left.card : ENNReal)) := by ring
    _ ≤ CQ * (right.card : ENNReal) *
          (CP * (J.card : ENNReal) * fine.enncard) := by
      exact mul_le_mul_left' hp _
    _ = (CQ * CP * (right.card : ENNReal) *
          (J.card : ENNReal)) * fine.enncard := by ring

end DilatedTubeCover

end Kakeya.Streamlined
