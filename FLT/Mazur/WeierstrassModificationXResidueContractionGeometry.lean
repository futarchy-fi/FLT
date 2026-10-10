/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassModificationXResidueContraction
public import FLT.Mazur.WeierstrassModificationXResidueNodeGeometry

/-!
# The full residue normal form retains the original contraction

The algebraic contraction functions define exactly the original tensor
projection followed by the original cubic contraction, transported through
the existing residue equivalence. This comparison retains c at middle depth.
-/

@[expose] public noncomputable section

open IsLocalRing AlgebraicGeometry CategoryTheory

namespace FLT.Mazur.WeierstrassModificationX

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u
variable {R : Type u} [CommRing R] [IsDomain R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} {n : ℕ} (D : SplitNodeDepth W π n)
  (k : ℕ) (hk0 : 0 < k) (hk : 2 * k ≤ n) (b3 b4 b6 : R)
  (h3 : W.a₃ = π ^ k * b3) (h4 : W.a₄ = π ^ k * b4)
  (h6 : W.a₆ = (π ^ k) ^ 2 * b6)

local notation "K" => ResidueField R
local notation "F" => FiberCoordinate (residue R W.a₁) (residue R b6)
local notation "T" => ScalarExtension W (π ^ k) b3 b4 b6 K

/-- The existing full normal form identifies the actual tensor residue fiber scheme. -/
def residueFiberIso : Spec (.of F) ≅ Spec (.of T) :=
  Scheme.Spec.mapIso
    (residueFiberEquiv D k hk0 hk b3 b4 b6 h3 h4).toRingEquiv.toCommRingCatIso.op

/-- The original x/y functions give a contraction from the full residual normal form. -/
def residueFullContraction : Spec (.of F) ⟶ WeierstrassIntegralChart.integralCurve W :=
  Spec.map (CommRingCat.ofHom
    (residueOriginalCoordinateMap D k hk0 hk b3 b4 b6 h3 h4 h6).toRingHom) ≫
      WeierstrassIntegralChart.integralCurveChart W 2

/-- The normal-form chart map is precisely the original tensor projection. -/
@[reassoc] theorem residueFiberIso_projection :
    (residueFiberIso D k hk0 hk b3 b4 b6 h3 h4).hom ≫
        residueChartProjection k b3 b4 b6 =
      Spec.map (CommRingCat.ofHom
        (residueNormalMap D k hk0 hk b3 b4 b6 h3 h4).toRingHom) := by
  change Spec.map _ ≫ Spec.map _ = _
  rw [← Spec.map_comp]
  rfl

/-- The full algebraic contraction agrees with the actual original tensor contraction. -/
@[reassoc] theorem residueFiberIso_contraction :
    (residueFiberIso D k hk0 hk b3 b4 b6 h3 h4).hom ≫
        residueChartContraction k b3 b4 b6 h3 h4 h6 =
      residueFullContraction D k hk0 hk b3 b4 b6 h3 h4 h6 := by
  rw [residueChartContraction, ← Category.assoc, residueFiberIso_projection]
  change Spec.map _ ≫ (Spec.map _ ≫ _) = Spec.map _ ≫ _
  rw [← Category.assoc, ← Spec.map_comp]
  rfl

/-- The transported contraction remains a morphism over the original coefficient ring. -/
@[reassoc] theorem residueFullContraction_structure :
    residueFullContraction D k hk0 hk b3 b4 b6 h3 h4 h6 ≫
        WeierstrassIntegralChart.integralCurveStructure W =
      Spec.map (CommRingCat.ofHom (algebraMap R F)) := by
  rw [residueFullContraction, Category.assoc,
    WeierstrassIntegralChart.integralCurveChart_structure]
  change Spec.map _ ≫ Spec.map _ = _
  rw [← Spec.map_comp]
  congr 1
  ext r
  exact (residueOriginalCoordinateMap D k hk0 hk b3 b4 b6 h3 h4 h6).commutes r

end FLT.Mazur.WeierstrassModificationX
