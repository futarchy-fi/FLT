/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassSuccessiveXTerminalConicCover
public import FLT.Mazur.PolygonCyclicNormalizationRanges

/-!
# Original terminal punctures in the complete affine node branches

The conic punctures become the reciprocal projective overlap maps into the
ordered terminal branches, with the parameter inversion retained explicitly.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits IsLocalRing
open scoped LaurentPolynomial
namespace FLT.Mazur.WeierstrassSuccessiveX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] [IsDomain R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} {n : ℕ} (D : SplitNodeDepth W π n)
  (k : ℕ) (hk : 2 * (k + 1) ≤ n) (b3 b4 b6 : R)
  (h3 : W.a₃ = π ^ (k + 1) * b3) (h4 : W.a₄ = π ^ (k + 1) * b4)
  (h6 : W.a₆ = (π ^ (k + 1)) ^ 2 * b6) (hp : 2 * (k + 1) < n)
local notation "K" => ResidueField R
local notation "W₀" => W.map (residue R)
local notation "c" => residue R b6
local notation "ψ" => residueNodeConicMap D k hk b3 b4 b6 h3 h4 h6 hp
local notation "s" => Spec.map (CommRingCat.ofHom (AlgHom.toRingHom ψ))
local notation "ha" => D.a₁_unit.map (residue R)
local notation "hc" => Iff.mpr (residue_eq_zero_iff _)
  (WeierstrassDilatation.divided_constant_mem D (k + 1) hp b6 h6)
local notation "s₁" => Spec.map
  (CommRingCat.ofHom (AlgHom.toRingHom (conicBoundaryFirst W₀ c ha hc)))
local notation "s₂" => Spec.map
  (CommRingCat.ofHom (AlgHom.toRingHom (conicBoundarySecond W₀ c ha hc)))
local notation "I" => Scheme.Spec.mapIso
  (Iso.op (RingEquiv.toCommRingCatIso
    (AlgEquiv.toRingEquiv (LaurentPolynomial.invert (R := K)))))

local notation "ι" => Iso.hom I
local notation "p" => ProjectiveLine.overlapLeft K

/-- The first original puncture uses the second node branch with reciprocal coordinate. -/
@[reassoc] theorem residueNodeConicFirstPuncture_branch :
    s₁ ≫ s = ProjectiveLine.overlapRight K ≫ PolygonCyclicAtlas.secondBranch K := by
  rw [residueNodeConicFirst_spec, ← PolygonCyclicAtlas.overlap_secondBranch]
  rfl

/-- The opposite puncture uses the first node branch with the same reciprocal coordinate. -/
@[reassoc] theorem residueNodeConicSecondPuncture_branch :
    s₂ ≫ s = ProjectiveLine.overlapRight K ≫ PolygonCyclicAtlas.firstBranch K := by
  rw [residueNodeConicSecond_spec, ← PolygonCyclicAtlas.overlap_firstBranch]
  rfl

end FLT.Mazur.WeierstrassSuccessiveX
