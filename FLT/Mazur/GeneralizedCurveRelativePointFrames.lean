/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.RelativeGenusOnePointFrames
public import FLT.Mazur.SmoothGeneralizedCurveGroupIso

/-!
# Relative point-power frames on original smooth generalized curves

The actual smooth inclusion supplies the group object, and the given family
supplies the geometric genus. Its original section cuts out a Cartier divisor.
All positive pole powers then have exact-rank frames and canonical affine
base change, without assuming coordinates or a cohomology witness.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry MonoidalCategory
open Scheme.Modules
namespace FLT.Mazur.GeneralizedEllipticCurve
open FCurve ModuleLineBundleTensorPullback
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable {S : Scheme} (E : GeneralizedEllipticCurve S)
  [SmoothOfRelativeDimension 1 E.curve.hom]

/-- The original section is Cartier on the relative smooth total curve. -/
theorem smoothPoint_cartier (s : 𝟙_ (Over S) ⟶ E.curve) : EffectiveCartier s.left.ker := by
  let _ : IsProper E.curve.hom := E.family.family.1
  exact (smoothSectionCartier E.curve.hom s.left inferInstance inferInstance s.w).1

/-- The actual positive pole-power coefficient of the original section. -/
def smoothPointPower (s : 𝟙_ (Over S) ⟶ E.curve) (m : ℕ) : E.curve.left.Modules :=
  tensorPower (divisorLineBundle s.left.ker (smoothPoint_cartier E s)) m

variable [IsAffine S] [IsNoetherianRing Γ(S, ⊤)] [GeometricallyIntegral E.curve.hom]

/-- The original relative pole spaces admit exact-rank local frames. -/
theorem smoothPointPower_frame (s : 𝟙_ (Over S) ⟶ E.curve) (m : ℕ) (hm : 0 < m) (x : S) :
    ∃ U : S.Opens, x ∈ U ∧ Nonempty
      (((pushforward E.curve.hom).obj (smoothPointPower E s m)).restrict U.ι ≅
        SheafOfModules.free (Fin m)) := by
  let _ : IsProper E.curve.hom := E.family.family.1
  let _ : Smooth E.curve.hom := SmoothOfRelativeDimension.smooth 1 E.curve.hom
  let _ : GrpObj E.curve := GrpObj.ofIso (asIso E.inclusion)
  exact relative_pointPower_frame E.curve E.family.genus s (smoothPoint_cartier E s) m hm x

/-- Every positive pole power on the original family is acyclic over the affine base. -/
theorem smoothPointPower_acyclic (s : 𝟙_ (Over S) ⟶ E.curve) (m : ℕ) (hm : 0 < m) (n : ℕ) :
    Subsingleton (ModuleH (smoothPointPower E s m) (n + 1)) := by
  let _ : IsProper E.curve.hom := E.family.family.1
  let _ : Smooth E.curve.hom := SmoothOfRelativeDimension.smooth 1 E.curve.hom
  let _ : GrpObj E.curve := GrpObj.ofIso (asIso E.inclusion)
  exact relative_pointPower_acyclic E.curve E.family.genus s (smoothPoint_cartier E s) m hm n

/-- The constructed relative point-power direct image commutes with affine base change. -/
def smoothPointPowerPushforwardIso (s : 𝟙_ (Over S) ⟶ E.curve) (m : ℕ) (hm : 0 < m)
    {P T : Scheme} [IsAffine T] {p : P ⟶ E.curve.left} {q : P ⟶ T} {g : T ⟶ S}
    (h : IsPullback p q E.curve.hom g) :
    (pullback g).obj ((pushforward E.curve.hom).obj (smoothPointPower E s m)) ≅
      (pushforward q).obj ((pullback p).obj (smoothPointPower E s m)) := by
  letI : IsProper E.curve.hom := E.family.family.1
  letI : Smooth E.curve.hom := SmoothOfRelativeDimension.smooth 1 E.curve.hom
  letI : GrpObj E.curve := GrpObj.ofIso (asIso E.inclusion)
  exact relativePointPowerPushforwardIso E.curve E.family.genus s
    (smoothPoint_cartier E s) m hm h

/-- In particular the original identity supplies all the required positive pole frames. -/
theorem identityPointPower_frame (m : ℕ) (hm : 0 < m) (x : S) :
    ∃ U : S.Opens, x ∈ U ∧ Nonempty
      (((pushforward E.curve.hom).obj (smoothPointPower E E.identitySection m)).restrict U.ι ≅
        SheafOfModules.free (Fin m)) :=
  smoothPointPower_frame E E.identitySection m hm x

end FLT.Mazur.GeneralizedEllipticCurve
