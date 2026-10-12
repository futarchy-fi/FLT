/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.RelativeGenusOneProjectiveSections
public import FLT.Mazur.SectionPoleCanonicalCoefficient

/-!
# The original homogeneous coordinates along the marking

The order-two and canonical-cube sections restrict to zero in the retained
marking frame. The normalized order-three section restricts to one, giving
exactly the homogeneous tuple [0, 1, 0] over the original base ring.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Scheme.Modules MonoidalCategory
namespace FLT.Mazur.FCurve
open ModuleLineBundleTensorPullback
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] divisorLineBundle sectionPoleMultiplicativeCoordinates

variable {S : Scheme.{0}} [IsAffine S] [IsNoetherianRing Γ(S, ⊤)]
  (G : Over S) [GrpObj G] [IsProper G.hom]
  [SmoothOfRelativeDimension 1 G.hom] [GeometricallyIntegral G.hom]
  (hg : CurveFiberHypotheses.NodalGenusOneGeometricFibers G.hom)
  (s : 𝟙_ (Over S) ⟶ G) (hI : EffectiveCartier s.left.ker)
  (e : (pullback s.left).obj (divisorLineBundle s.left.ker hI) ≅ structureModule S)

local notation "L" => divisorLineBundle s.left.ker hI
local notation "T" => relativePointProjectiveSections G hg s hI e
/-- The included order-two coordinate vanishes along the original marking. -/
theorem relativePointProjectiveX_coefficient :
    sectionPoleCoefficient s.left hI e 3 (relativePointProjectiveX G hg s hI e) = 0 :=
  sectionPoleCoefficient_step G.hom s.left s.w hI e 2
    (relativePointFramedLift G hg s hI e 1 (by decide))

/-- The actual order-three coordinate equals one in the retained marking frame. -/
theorem relativePointProjectiveY_coefficient :
    sectionPoleCoefficient s.left hI e 3 (relativePointProjectiveY G hg s hI e) = 1 :=
  relativePointFramedLift_coefficient G hg s hI e 2 (by decide)

omit [IsAffine S] [IsNoetherianRing Γ(S, ⊤)] [GrpObj G]
  [SmoothOfRelativeDimension 1 G.hom] [GeometricallyIntegral G.hom] in
/-- The canonical degree-three coordinate vanishes along the original marking. -/
theorem relativePointProjectiveZ_coefficient :
    sectionPoleCoefficient s.left hI e 3 (relativePointProjectiveZ G s hI) = 0 :=
  sectionPoleCoefficient_canonical G.hom s.left s.w hI e 2

/-- The full original coordinate triple restricts to [0, 1, 0] over the actual base. -/
theorem relativePointProjectiveSections_coefficient (i : Fin 3) :
    sectionPoleCoefficient s.left hI e 3 (T i) = (![0, 1, 0] : Fin 3 → Γ(S, ⊤)) i := by
  fin_cases i
  · exact relativePointProjectiveX_coefficient G hg s hI e
  · exact relativePointProjectiveY_coefficient G hg s hI e
  · exact relativePointProjectiveZ_coefficient G s hI e

end FLT.Mazur.FCurve
