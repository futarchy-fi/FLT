/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.GeneralizedCurveGraph

/-!
# Relative generalized elliptic curves

This is DR II.1.12: a classified genus-one family, its smooth commutative
group, an action extending multiplication, and geometric graph rotations.
The group is presented with an isomorphism to the actual relative smooth open.
These are the defining geometric data, not a moduli or arithmetic conclusion.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory MonObj
namespace FLT.Mazur

/-- The actual relative smooth open, viewed over the same base. -/
abbrev curveSmoothOpen {S : Scheme} (X : Over S) [LocallyOfFinitePresentation X.hom] :
    Over S := Over.mk (X.hom.smoothLocus.ι ≫ X.hom)

/-- The inclusion of the relative smooth open. -/
def curveSmoothInclusion {S : Scheme} (X : Over S) [LocallyOfFinitePresentation X.hom] :
    curveSmoothOpen X ⟶ X := Over.homMk X.hom.smoothLocus.ι rfl

/-- A generalized elliptic curve over a scheme, in the sense of DR II.1.12. -/
structure GeneralizedEllipticCurve (S : Scheme) where
  /-- The curve over the base. -/
  curve : Over S
  /-- Proper flat classified geometric genus-one fibers. -/
  family : FCurve.ClassifiedGenusOneFamily curve.hom
  /-- The group presenting the smooth open. -/
  group : Over S
  /-- Its commutative group scheme structure. -/
  [commGroup : CommGrpObj group]
  /-- Identification with the actual relative smooth locus. -/
  smoothIso : letI := family.family.2.2; group ≅ curveSmoothOpen curve
  /-- The whole-curve action morphism. -/
  act : group ⊗ curve ⟶ curve
  /-- Identity acts trivially. -/
  unit_act : η[group] ▷ curve ≫ act = (λ_ curve).hom
  /-- Multiplication acts associatively. -/
  assoc_act : μ[group] ▷ curve ≫ act =
    (α_ group group curve).hom ≫ group ◁ act ≫ act
  /-- Restriction to the smooth open is the group multiplication. -/
  restriction : letI := family.family.2.2
    group ◁ (smoothIso.hom ≫ curveSmoothInclusion curve) ≫ act =
      μ[group] ≫ smoothIso.hom ≫ curveSmoothInclusion curve
  /-- Every geometric translation rotates the actual singular-fiber graph. -/
  rotations : letI := family.family.2.2; GeneralizedCurveGraph.GeometricRotations act

attribute [instance] GeneralizedEllipticCurve.commGroup

namespace GeneralizedEllipticCurve
variable {S : Scheme} (E : GeneralizedEllipticCurve S)

instance : LocallyOfFinitePresentation E.curve.hom := E.family.family.2.2

/-- The smooth group inclusion in the curve. -/
def inclusion : E.group ⟶ E.curve := E.smoothIso.hom ≫ curveSmoothInclusion E.curve

/-- Restriction of the whole-curve action to the smooth group. -/
theorem action_inclusion : E.group ◁ E.inclusion ≫ E.act = μ[E.group] ≫ E.inclusion :=
  E.restriction

/-- The identity section of the generalized curve. -/
def identitySection : 𝟙_ (Over S) ⟶ E.curve := η[E.group] ≫ E.inclusion

end GeneralizedEllipticCurve
end FLT.Mazur
