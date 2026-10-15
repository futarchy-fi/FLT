/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedZeroExteriorSmoothCoordinates
public import FLT.Mazur.EllipticResolvedOrientedAtlas
public import FLT.Mazur.WeierstrassDividedZeroEqualityCycle

/-!
# The reciprocal arithmetic identity chart in the original closed cycle

The natural label zero agrees with the complete exterior component torus,
for both parity cases and also at depth two. Only stage equality is transported.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory IsLocalRing
namespace FLT.Mazur.WeierstrassDividedDepth
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {K : Type u} [Field K] (A : ValuationSubring K)
  {W : WeierstrassCurve A} {π : A} {depth : ℕ} (D : SplitNodeDepth W π depth)
  (s : ℕ) (he : depth / 2 = s + 1)
local notation "F" => ResidueField A
local notation "hπ" => SplitNodeDepth.uniformizer_ne_zero D
local notation "data" => splitResolutionData A D
local notation "p" => resolvedSplitStructure A D
local notation "t" => eqToHom (finiteGlobalTensorModel_index_congr hπ data F
  (le_refl _) (by omega) he)
local notation "torus" => Over.Hom.left (PolygonPinching.torusToComponent F)

/-- The original reciprocal identity parameter is the full punctured exterior parameter. -/
@[reassoc] theorem resolvedReciprocalIdentitySmoothChart_exterior :
    resolvedReciprocalIdentitySmoothChart A D ≫ (p).smoothLocus.ι ≫ t =
      torus ≫ finalZeroExteriorComponent hπ data D s (by omega) rfl (by omega) := by
  rw [resolvedReciprocalIdentitySmoothChart_inclusion_assoc,
    resolvedIdentityChart_eq_infinity, finalZeroExteriorComponent_torus,
    ← infinityLaurentChart_eq_smooth_embedding]
  simp only [infinityLaurentChart, Category.assoc]
  rw [finiteInfinityTensorChart_index_transport hπ data _ (by omega) he]

/-- The odd closed cycle uses exactly the original reciprocal identity chart. -/
@[reassoc] theorem resolvedReciprocalIdentitySmoothChart_odd_cyclic
    (hp : 2 * (s + 1) < depth) :
    resolvedReciprocalIdentitySmoothChart A D ≫ (p).smoothLocus.ι ≫ t =
      torus ≫ (zeroSplitCycleComponent hπ data D s (by omega) rfl
        (by omega) (by omega) 0).left := by
  rw [zeroSplitCycleComponent_exterior]
  exact resolvedReciprocalIdentitySmoothChart_exterior A D s he

/-- The even closed cycle retains the same identity coordinate, including depth two. -/
@[reassoc] theorem resolvedReciprocalIdentitySmoothChart_even_cyclic
    (hp : 2 * (s + 1) = depth) :
    resolvedReciprocalIdentitySmoothChart A D ≫ (p).smoothLocus.ι ≫ t =
      torus ≫ (zeroEqualityCycleComponent hπ data D s (by omega) rfl
        (by omega) (by omega) 0).left := by
  rw [zeroEqualityCycleComponent_exterior]
  exact resolvedReciprocalIdentitySmoothChart_exterior A D s he

variable (r : (ResidueField A)ˣ)

/-- Natural arithmetic label zero needs no scalar correction in the odd cycle. -/
@[reassoc] theorem resolvedOrientedComponentChart_odd_zero
    (hp : 2 * (s + 1) < depth) :
    resolvedOrientedComponentChart A D r ⟨0, D.depth_pos⟩ ≫ (p).smoothLocus.ι ≫ t =
      torus ≫ (zeroSplitCycleComponent hπ data D s (by omega) rfl
        (by omega) (by omega) 0).left := by
  rw [resolvedOrientedComponentChart_zero]
  exact resolvedReciprocalIdentitySmoothChart_odd_cyclic A D s he hp

/-- Natural arithmetic label zero needs no scalar correction in the even cycle. -/
@[reassoc] theorem resolvedOrientedComponentChart_even_zero
    (hp : 2 * (s + 1) = depth) :
    resolvedOrientedComponentChart A D r ⟨0, D.depth_pos⟩ ≫ (p).smoothLocus.ι ≫ t =
      torus ≫ (zeroEqualityCycleComponent hπ data D s (by omega) rfl
        (by omega) (by omega) 0).left := by
  rw [resolvedOrientedComponentChart_zero]
  exact resolvedReciprocalIdentitySmoothChart_even_cyclic A D s he hp

end FLT.Mazur.WeierstrassDividedDepth
