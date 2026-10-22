/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.GeneralizedCurveMarkingProjectiveSections
public import FLT.Mazur.SectionPoleCanonicalCoefficient

/-!
# The original homogeneous coordinates along the marking

The order-two and canonical-cube sections restrict to zero in the retained
marking frame. The normalized order-three section restricts to one, giving
exactly the homogeneous tuple [0, 1, 0] over the original base ring.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Scheme.Modules MonoidalCategory
namespace FLT.Mazur.GeneralizedEllipticCurve
open FCurve ModuleLineBundleTensorPullback
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] divisorLineBundle sectionPoleMultiplicativeCoordinates
  Scheme.Modules.pullback ModuleSheafTensor.tensor

variable {S : Scheme.{0}} [IsAffine S] [IsNoetherianRing Γ(S, ⊤)]
  (E : GeneralizedEllipticCurve S) (s : 𝟙_ (Over S) ⟶ E.group)

local notation "t" => s ≫ E.inclusion
local notation "hI" => And.left (smoothMarking_relativeCartier E s)

local instance generalizedCurveMarkingMarkedCoordinatesProper :
    IsProper E.curve.hom := E.family.family.1

variable (e : (pullback (s ≫ E.inclusion).left).obj
  (divisorLineBundle (s ≫ E.inclusion).left.ker
    (smoothMarking_relativeCartier E s).1) ≅ structureModule S)

local notation "L" => divisorLineBundle (Scheme.Hom.ker (Over.Hom.left (t))) (hI)
local notation "T" => smoothMarkingProjectiveSections E s e
/-- The included order-two coordinate vanishes along the original marking. -/
theorem smoothMarkingProjectiveX_coefficient :
    sectionPoleCoefficient (t).left (hI) e 3 (smoothMarkingProjectiveX E s e) = 0 :=
  sectionPoleCoefficient_step E.curve.hom (t).left (t).w (hI) e 2
    (smoothMarkingFramedLift E s e 1 (by decide))

/-- The actual order-three coordinate equals one in the retained marking frame. -/
theorem smoothMarkingProjectiveY_coefficient :
    sectionPoleCoefficient (t).left (hI) e 3 (smoothMarkingProjectiveY E s e) = 1 :=
  smoothMarkingFramedLift_coefficient E s e 2 (by decide)

omit [IsAffine S] [IsNoetherianRing Γ(S, ⊤)] in
/-- The canonical degree-three coordinate vanishes along the original marking. -/
theorem smoothMarkingProjectiveZ_coefficient :
    sectionPoleCoefficient (t).left (hI) e 3 (smoothMarkingProjectiveZ E s) = 0 :=
  sectionPoleCoefficient_canonical E.curve.hom (t).left (t).w (hI) e 2

/-- The full original coordinate triple restricts to [0, 1, 0] over the actual base. -/
theorem smoothMarkingProjectiveSections_coefficient (i : Fin 3) :
    sectionPoleCoefficient (t).left (hI) e 3 (T i) = (![0, 1, 0] : Fin 3 → Γ(S, ⊤)) i := by
  fin_cases i
  · exact smoothMarkingProjectiveX_coefficient E s e
  · exact smoothMarkingProjectiveY_coefficient E s e
  · exact smoothMarkingProjectiveZ_coefficient E s e

end FLT.Mazur.GeneralizedEllipticCurve
