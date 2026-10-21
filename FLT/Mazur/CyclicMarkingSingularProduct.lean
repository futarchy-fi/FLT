/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CyclicMarkingSingularCriterion
public import FLT.Mazur.FiniteFlatAffineLocalFree

/-!
# The full finite flat product for singular cyclic orbit equations

Smoothness of the group alone makes the actual orbit carrier and its product
finite flat. These are the original schemes on which the equation is imposed.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory MonObj
namespace FLT.Mazur.GeneralizedEllipticCurve
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {S : Scheme} (E : GeneralizedEllipticCurve S) {n : ℕ}
  (φ : Multiplicative (ZMod n) →* (𝟙_ (Over S) ⟶ E.group))

/-- The actual full orbit carrier in the smooth group of the possibly singular curve. -/
def singularOrbitCarrier : Over S :=
  ClosedGroupIdeal.carrier E.group (E.cyclicMarkingGroupIdeal φ)

/-- The entire product carrying the multiplication equation. -/
def singularOrbitProduct : Over S := E.singularOrbitCarrier φ ⊗ E.singularOrbitCarrier φ

/-- The full obstruction ideal, with its nilpotent structure. -/
def singularOrbitMultiplicationIdeal : (E.singularOrbitProduct φ).left.IdealSheafData :=
  (E.cyclicMarkingGroupIdeal φ).comap
    (ClosedGroupIdeal.productMap E.group (E.cyclicMarkingGroupIdeal φ)).left

/-- The module equation vanishes precisely when its full image ideal vanishes. -/
theorem singularOrbitMultiplication_iff_ideal :
    ClosedGroupIdeal.multiplicationEquation E.group (E.cyclicMarkingGroupIdeal φ) = 0 ↔
      E.singularOrbitMultiplicationIdeal φ = ⊥ :=
  FCurve.idealModulePullbackι_eq_zero_iff_comap _ _

variable [SmoothOfRelativeDimension 1 E.group.hom]

instance singularOrbitCarrier_isFinite : IsFinite (E.singularOrbitCarrier φ).hom :=
  (E.cyclicMarkingGroupIdeal_degree φ).1

instance singularOrbitCarrier_flat : Flat (E.singularOrbitCarrier φ).hom :=
  (E.cyclicMarkingGroupIdeal_degree φ).2.1

instance singularOrbitCarrier_locallyOfFinitePresentation :
    LocallyOfFinitePresentation (E.singularOrbitCarrier φ).hom :=
  (E.cyclicMarkingGroupIdeal_degree φ).2.2.1

instance singularOrbitProduct_isFinite : IsFinite (E.singularOrbitProduct φ).hom := by
  change IsFinite (pullback.fst (E.singularOrbitCarrier φ).hom (E.singularOrbitCarrier φ).hom ≫
    (E.singularOrbitCarrier φ).hom)
  infer_instance

instance singularOrbitProduct_flat : Flat (E.singularOrbitProduct φ).hom := by
  change Flat (pullback.fst (E.singularOrbitCarrier φ).hom (E.singularOrbitCarrier φ).hom ≫
    (E.singularOrbitCarrier φ).hom)
  infer_instance

instance singularOrbitProduct_locallyOfFinitePresentation :
    LocallyOfFinitePresentation (E.singularOrbitProduct φ).hom := by
  change LocallyOfFinitePresentation
    (pullback.fst (E.singularOrbitCarrier φ).hom (E.singularOrbitCarrier φ).hom ≫
      (E.singularOrbitCarrier φ).hom)
  infer_instance

/-- Every affine base chart gives a projective algebra for coefficient extraction. -/
theorem singularOrbitProduct_app_projective (U : S.affineOpens) :
    let _ := ((E.singularOrbitProduct φ).hom.app U.1).hom.toAlgebra
    Module.Projective Γ(S, U.1)
      Γ((E.singularOrbitProduct φ).left, (E.singularOrbitProduct φ).hom ⁻¹ᵁ U.1) :=
  FCurve.finiteFlat_app_projective (E.singularOrbitProduct φ).hom U

end FLT.Mazur.GeneralizedEllipticCurve
