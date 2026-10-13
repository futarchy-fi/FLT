/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.GeneralizedCurveRelativePointFrames
public import FLT.Mazur.RelativeGenusOneUnrestrictedPointFrames
public import FLT.Mazur.RelativeGenusOneUnrestrictedPointVanishing

/-!
# Exact pole frames and vanishing on arbitrary original smooth generalized curves

The original smooth curve and section supply the Cartier pole line. Its actual
positive powers have exact-rank frames on any base and vanish in positive
cohomology over any affine base, including nonnoetherian bases.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry MonoidalCategory
open Scheme.Modules
namespace FLT.Mazur.GeneralizedEllipticCurve
open FCurve ModuleLineBundleTensorPullback
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {S : Scheme} (E : GeneralizedEllipticCurve S)
  [SmoothOfRelativeDimension 1 E.curve.hom] [GeometricallyIntegral E.curve.hom]

/-- The actual positive pole direct image has an exact-rank frame on every original base. -/
theorem smoothPointPower_frame_unrestricted
    (s : 𝟙_ (Over S) ⟶ E.curve) (m : ℕ) (hm : 0 < m) (x : S) :
    ∃ U : S.Opens, x ∈ U ∧ Nonempty
      (((pushforward E.curve.hom).obj (smoothPointPower E s m)).restrict U.ι ≅
        SheafOfModules.free (Fin m)) := by
  let _ : IsProper E.curve.hom := E.family.family.1
  let _ : Smooth E.curve.hom := SmoothOfRelativeDimension.smooth 1 E.curve.hom
  let _ : GrpObj E.curve := GrpObj.ofIso (asIso E.inclusion)
  exact relative_pointPower_frame_unrestricted E.curve E.family.genus s
    (smoothPoint_cartier E s) m hm x

/-- Every positive pole power is acyclic over an arbitrary original affine base. -/
theorem smoothPointPower_acyclic_unrestricted [IsAffine S]
    (s : 𝟙_ (Over S) ⟶ E.curve) (m : ℕ) (hm : 0 < m) (n : ℕ) :
    Subsingleton (ModuleH (smoothPointPower E s m) (n + 1)) := by
  let _ : IsProper E.curve.hom := E.family.family.1
  let _ : Smooth E.curve.hom := SmoothOfRelativeDimension.smooth 1 E.curve.hom
  let _ : GrpObj E.curve := GrpObj.ofIso (asIso E.inclusion)
  exact relative_pointPower_acyclic_unrestricted E.curve E.family.genus s
    (smoothPoint_cartier E s) m hm n

/-- The original identity yields the exact pole frames without any base finiteness assumption. -/
theorem identityPointPower_frame_unrestricted (m : ℕ) (hm : 0 < m) (x : S) :
    ∃ U : S.Opens, x ∈ U ∧ Nonempty
      (((pushforward E.curve.hom).obj (smoothPointPower E E.identitySection m)).restrict U.ι ≅
        SheafOfModules.free (Fin m)) :=
  smoothPointPower_frame_unrestricted E E.identitySection m hm x

end FLT.Mazur.GeneralizedEllipticCurve
