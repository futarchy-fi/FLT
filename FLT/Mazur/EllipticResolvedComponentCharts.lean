/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.EllipticResolvedIdentityPoints
public import FLT.Mazur.EllipticResolvedRetainedSmoothCharts
public import FLT.Mazur.EllipticResolvedTerminalSmoothCharts

/-!
# One family of component charts in the original resolved smooth fiber

Identity, retained and terminal tori all have the same actual target and
residue-field structure. The index records precisely the allowed depth and
parity conditions; it does not assume coverage or any group-law comparison.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory IsLocalRing
open scoped LaurentPolynomial
namespace FLT.Mazur.WeierstrassDividedDepth
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u

/-- The existing original torus charts, indexed by their actual depth and branch. -/
inductive ResolvedComponentIndex (depth : ℕ) where
  /-- The original smooth residue cubic. -/
  | identity
  /-- A positive puncture retained from an earlier depth. -/
  | retainedPositive (j : ℕ) (hj0 : 0 < j) (hj : j < depth / 2)
  /-- A negative puncture retained from an earlier depth. -/
  | retainedNegative (j : ℕ) (hj0 : 0 < j) (hj : j < depth / 2)
  /-- The positive puncture at positive odd final depth. -/
  | terminalPositive (hk0 : 0 < depth / 2) (hp : 2 * (depth / 2) < depth)
  /-- The negative puncture at positive odd final depth. -/
  | terminalNegative (hk0 : 0 < depth / 2) (hp : 2 * (depth / 2) < depth)
  /-- The middle component at positive even final depth. -/
  | terminalMiddle (hk0 : 0 < depth / 2) (hm : 2 * (depth / 2) = depth)

variable {K : Type u} [Field K] (A : ValuationSubring K)
  {W : WeierstrassCurve A} {π : A} {depth : ℕ} (D : SplitNodeDepth W π depth)
  (r : (ResidueField A)ˣ)
local notation "F" => ResidueField A
local notation "p" => resolvedSplitStructure A D

/-- Every original torus chart as a map into the same actual resolved smooth open. -/
def resolvedComponentChart (i : ResolvedComponentIndex depth) :
    Spec (.of F[T;T⁻¹]) ⟶ (p).smoothLocus.toScheme :=
  match i with
  | .identity => resolvedIdentitySmoothChart A D
  | .retainedPositive j hj0 hj => resolvedRetainedPositiveSmoothChart A D r j hj0 hj
  | .retainedNegative j hj0 hj => resolvedRetainedNegativeSmoothChart A D r j hj0 hj
  | .terminalPositive hk0 hp => resolvedTerminalPositiveSmoothChart A D r hk0 hp
  | .terminalNegative hk0 hp => resolvedTerminalNegativeSmoothChart A D r hk0 hp
  | .terminalMiddle hk0 hm => resolvedTerminalMiddleSmoothChart A D r hk0 hm

instance resolvedComponentChart_isOpenImmersion (i : ResolvedComponentIndex depth) :
    IsOpenImmersion (resolvedComponentChart A D r i) := by
  cases i <;> dsimp only [resolvedComponentChart] <;> infer_instance

/-- Each component chart preserves the actual original residue coefficient map. -/
@[reassoc] theorem resolvedComponentChart_structure (i : ResolvedComponentIndex depth) :
    resolvedComponentChart A D r i ≫ (p).smoothLocus.ι ≫ p =
      (MultiplicativeGroupScheme.gm F).hom := by
  cases i with
  | identity =>
    rw [resolvedComponentChart, resolvedIdentitySmoothChart_inclusion_assoc,
      resolvedIdentityChart_structure]
  | retainedPositive j hj0 hj =>
    rw [resolvedComponentChart, resolvedRetainedPositiveSmoothChart_inclusion_assoc,
      resolvedRetainedPositiveChart_structure]
  | retainedNegative j hj0 hj =>
    rw [resolvedComponentChart, resolvedRetainedNegativeSmoothChart_inclusion_assoc,
      resolvedRetainedNegativeChart_structure]
  | terminalPositive hk0 hp =>
    rw [resolvedComponentChart, resolvedTerminalPositiveSmoothChart_inclusion_assoc,
      resolvedTerminalPositiveChart_structure]
  | terminalNegative hk0 hp =>
    rw [resolvedComponentChart, resolvedTerminalNegativeSmoothChart_inclusion_assoc,
      resolvedTerminalNegativeChart_structure]
  | terminalMiddle hk0 hm =>
    rw [resolvedComponentChart, resolvedTerminalMiddleSmoothChart_inclusion_assoc,
      resolvedTerminalMiddleChart_structure]

/-- All component charts are morphisms over the same original residue spectrum. -/
def resolvedComponentChartOver (i : ResolvedComponentIndex depth) :
    MultiplicativeGroupScheme.gm F ⟶ Over.mk ((p).smoothLocus.ι ≫ p) :=
  Over.homMk (resolvedComponentChart A D r i) (resolvedComponentChart_structure A D r i)

end FLT.Mazur.WeierstrassDividedDepth
