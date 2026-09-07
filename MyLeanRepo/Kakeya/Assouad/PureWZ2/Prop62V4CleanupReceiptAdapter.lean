import MyLeanRepo.Kakeya.Assouad.PureWZ2.Prop62CleanupReceipt

/-!
# Proposition 6.2 external cleanup receipt adapter

This module exposes a statement-independent interface for importing the six
outputs of an external one-pass tree cleanup.  It deliberately does not run
the canonical cleanup producer.
-/

namespace Kakeya.Assouad

structure PureWZ2Prop62CleanupOracleData
    {Leaf Node : Type}
    [Fintype Leaf] [DecidableEq Leaf]
    [Fintype Node] [DecidableEq Node]
    {depth : ℕ}
    (tree : PureWZ2Prop62FiniteTree Leaf Node depth)
    (selected : Finset Leaf) where
  core : Finset Leaf
  core_subset : core ⊆ selected
  global_retention :
    selected.card ≤ 2 ^ depth * core.card
  node_density :
    ∀ level, level ≤ depth →
      ∀ node,
        (core ∩ tree.fiber level node).Nonempty →
          selected.card * (tree.fiber level node).card ≤
            2 ^ depth *
              (core ∩ tree.fiber level node).card *
              Fintype.card Leaf
  weighted_retention :
    ∀ (weight : Leaf → ENNReal) (weightLevel : ENNReal),
      (∀ leaf ∈ selected, weightLevel ≤ weight leaf) →
      (∀ leaf ∈ selected, weight leaf ≤ 2 * weightLevel) →
        ∑ leaf ∈ selected, weight leaf ≤
          2 ^ (depth + 1) * ∑ leaf ∈ core, weight leaf
  local_cwa_transfer :
    ∀ level, level ≤ depth →
      ∀ node,
        (core ∩ tree.fiber level node).Nonempty →
        ∀ (constant volumeFactor : ENNReal),
          ∀ count : Finset Leaf → ENNReal,
            (∀ first second, first ⊆ second →
              count first ≤ count second) →
            count (tree.fiber level node) ≤
                constant * volumeFactor *
                  (tree.fiber level node).card →
              count (core ∩ tree.fiber level node) ≤
                (constant * (2 ^ depth : ENNReal) *
                    (Fintype.card Leaf : ENNReal) *
                    (selected.card : ENNReal)⁻¹) *
                  volumeFactor *
                  ((core ∩ tree.fiber level node).card : ENNReal)

def pureWZ2Prop62CleanupOracleDataOfFields
    {Leaf Node : Type}
    [Fintype Leaf] [DecidableEq Leaf]
    [Fintype Node] [DecidableEq Node]
    {depth : ℕ}
    (tree : PureWZ2Prop62FiniteTree Leaf Node depth)
    (selected core : Finset Leaf)
    (coreSubset : core ⊆ selected)
    (globalRetention :
      selected.card ≤ 2 ^ depth * core.card)
    (nodeDensity :
      ∀ level, level ≤ depth →
        ∀ node,
          (core ∩ tree.fiber level node).Nonempty →
            selected.card * (tree.fiber level node).card ≤
              2 ^ depth *
                (core ∩ tree.fiber level node).card *
                Fintype.card Leaf)
    (weightedRetention :
      ∀ (weight : Leaf → ENNReal) (weightLevel : ENNReal),
        (∀ leaf ∈ selected, weightLevel ≤ weight leaf) →
        (∀ leaf ∈ selected, weight leaf ≤ 2 * weightLevel) →
          ∑ leaf ∈ selected, weight leaf ≤
            2 ^ (depth + 1) * ∑ leaf ∈ core, weight leaf)
    (localCWATransfer :
      ∀ level, level ≤ depth →
        ∀ node,
          (core ∩ tree.fiber level node).Nonempty →
          ∀ (constant volumeFactor : ENNReal),
            ∀ count : Finset Leaf → ENNReal,
              (∀ first second, first ⊆ second →
                count first ≤ count second) →
              count (tree.fiber level node) ≤
                  constant * volumeFactor *
                    (tree.fiber level node).card →
                count (core ∩ tree.fiber level node) ≤
                  (constant * (2 ^ depth : ENNReal) *
                      (Fintype.card Leaf : ENNReal) *
                      (selected.card : ENNReal)⁻¹) *
                    volumeFactor *
                    ((core ∩ tree.fiber level node).card : ENNReal)) :
    PureWZ2Prop62CleanupOracleData tree selected where
  core := core
  core_subset := coreSubset
  global_retention := globalRetention
  node_density := nodeDensity
  weighted_retention := weightedRetention
  local_cwa_transfer := localCWATransfer

def PureWZ2Prop62CleanupOracleData.toReceipt
    {Leaf Node : Type}
    [Fintype Leaf] [DecidableEq Leaf]
    [Fintype Node] [DecidableEq Node]
    {depth : ℕ}
    {tree : PureWZ2Prop62FiniteTree Leaf Node depth}
    {selected : Finset Leaf}
    (oracle : PureWZ2Prop62CleanupOracleData tree selected) :
    PureWZ2Prop62CleanupReceipt tree selected where
  core := oracle.core
  core_subset := oracle.core_subset
  global_retention := oracle.global_retention
  node_density := oracle.node_density
  weighted_retention := oracle.weighted_retention
  local_cwa_transfer := oracle.local_cwa_transfer

def PureWZ2Prop62CleanupOracle : Prop :=
  ∀ (Leaf Node : Type),
    ∀ [Fintype Leaf] [DecidableEq Leaf],
      ∀ [Fintype Node] [DecidableEq Node],
        ∀ (depth : ℕ),
          ∀ (tree : PureWZ2Prop62FiniteTree Leaf Node depth),
            ∀ (selected : Finset Leaf),
              selected.Nonempty →
                Nonempty (PureWZ2Prop62CleanupReceipt tree selected)

def pureWZ2Prop62CleanupOracleOfData
    (provide :
      ∀ (Leaf Node : Type),
        ∀ [Fintype Leaf] [DecidableEq Leaf],
          ∀ [Fintype Node] [DecidableEq Node],
            ∀ (depth : ℕ),
              ∀ (tree : PureWZ2Prop62FiniteTree Leaf Node depth),
                ∀ (selected : Finset Leaf),
                  selected.Nonempty →
                    Nonempty
                      (PureWZ2Prop62CleanupOracleData tree selected)) :
    PureWZ2Prop62CleanupOracle := by
  intro Leaf Node _ _ _ _ depth tree selected selectedNonempty
  exact
    Nonempty.map
      PureWZ2Prop62CleanupOracleData.toReceipt
      (provide Leaf Node depth tree selected selectedNonempty)

def pureWZ2Prop62CleanupReceiptOfFields
    {Leaf Node : Type}
    [Fintype Leaf] [DecidableEq Leaf]
    [Fintype Node] [DecidableEq Node]
    {depth : ℕ}
    (tree : PureWZ2Prop62FiniteTree Leaf Node depth)
    (selected core : Finset Leaf)
    (coreSubset : core ⊆ selected)
    (globalRetention :
      selected.card ≤ 2 ^ depth * core.card)
    (nodeDensity :
      ∀ level, level ≤ depth →
        ∀ node,
          (core ∩ tree.fiber level node).Nonempty →
            selected.card * (tree.fiber level node).card ≤
              2 ^ depth *
                (core ∩ tree.fiber level node).card *
                Fintype.card Leaf)
    (weightedRetention :
      ∀ (weight : Leaf → ENNReal) (weightLevel : ENNReal),
        (∀ leaf ∈ selected, weightLevel ≤ weight leaf) →
        (∀ leaf ∈ selected, weight leaf ≤ 2 * weightLevel) →
          ∑ leaf ∈ selected, weight leaf ≤
            2 ^ (depth + 1) * ∑ leaf ∈ core, weight leaf)
    (localCWATransfer :
      ∀ level, level ≤ depth →
        ∀ node,
          (core ∩ tree.fiber level node).Nonempty →
          ∀ (constant volumeFactor : ENNReal),
            ∀ count : Finset Leaf → ENNReal,
              (∀ first second, first ⊆ second →
                count first ≤ count second) →
              count (tree.fiber level node) ≤
                  constant * volumeFactor *
                    (tree.fiber level node).card →
                count (core ∩ tree.fiber level node) ≤
                  (constant * (2 ^ depth : ENNReal) *
                      (Fintype.card Leaf : ENNReal) *
                      (selected.card : ENNReal)⁻¹) *
                    volumeFactor *
                    ((core ∩ tree.fiber level node).card : ENNReal)) :
    PureWZ2Prop62CleanupReceipt tree selected :=
  (pureWZ2Prop62CleanupOracleDataOfFields
    tree selected core coreSubset globalRetention nodeDensity
      weightedRetention localCWATransfer).toReceipt

end Kakeya.Assouad
