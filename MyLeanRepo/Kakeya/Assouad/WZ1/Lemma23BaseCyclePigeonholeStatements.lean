import MyLeanRepo.Kakeya.Assouad.WZ1.Lemma23SnappedTripartiteFiberStatements

/-!
# Fix the base height and global bin in WZ1 Lemma 23

After counting snapped four-cycles, the paper pigeonholes the first cube by
its exact base height and its global scalar `rho`-bin.  This produces the
filtered cycle family consumed by the bounded tripartite-fiber theorem.
-/

namespace Kakeya.Assouad

noncomputable section

/-- The Step 4 base key of one snapped four-cycle. -/
def wz1Lemma23BaseCycleKey
    (rho : ℝ) (f : ℝ → ℝ)
    (path :
      (ℤ × ℤ × ℤ) ×
        (ℤ × ℤ × ℤ) ×
        (ℤ × ℤ × ℤ) ×
        (ℤ × ℤ × ℤ)) : ℤ × ℤ :=
  (wz1Lemma23SnappedHeight path.1,
    wz1Lemma23SnappedGlobalBin rho f path.1)

/--
If the first-cube base key takes at most `keyBound` values, then one actual
base-height/global-bin fiber retains its proportional share of the snapped
four-cycles.
-/
def WZ1Lemma23BaseCyclePigeonholeStatement : Prop :=
  ∀ (rho : ℝ) (f g : ℝ → ℝ)
    (cells : Finset (ℤ × ℤ × ℤ))
    (keyBound : ℕ),
    let cycles :=
      wz1Lemma23SnappedFourCycles rho f g cells
    let keys :=
      cycles.image (wz1Lemma23BaseCycleKey rho f)
    keys.card ≤ keyBound →
      ∃ baseHeightIndex baseGlobalBin : ℤ,
        keyBound *
            (wz1Lemma23SnappedBaseCycles
              rho f g cells
              baseHeightIndex baseGlobalBin).card ≥
          cycles.card

end

end Kakeya.Assouad
