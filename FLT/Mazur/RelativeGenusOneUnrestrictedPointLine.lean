/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.RelativeGenusOnePointFibers
public import FLT.Mazur.SmoothGeometricAcyclicRankOne

/-!
# The actual degree-one pole direct image over unrestricted bases

The original genus-one fiber calculation and smooth line-sheaf approximation
construct the actual direct-image line. No Noetherian or affine condition is
imposed on the original base.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry MonoidalCategory
open Scheme.Modules
namespace FLT.Mazur.FCurve
open ModuleLineBundleTensorPullback CartierAbel LineSectionBaseChange ModuleSheafTensor
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {S : Scheme} (G : Over S) [GrpObj G] [IsProper G.hom]
  [SmoothOfRelativeDimension 1 G.hom] [GeometricallyIntegral G.hom]
  (hg : CurveFiberHypotheses.NodalGenusOneGeometricFibers G.hom)
  (s : 𝟙_ (Over S) ⟶ G) (hI : EffectiveCartier s.left.ker)

include hg in
/-- The actual degree-one pole line has acyclic rank-one fibers over every original base. -/
theorem relative_pointOne_geometricAcyclicRankOne :
    GeometricAcyclicRankOne G.hom (tensorPower (divisorLineBundle s.left.ker hI) 1) := by
  intro x
  exact ⟨fun n ↦ relative_pointPower_field_acyclic G hg s hI
    (S.fromSpecResidueField x) 1 (by decide) n,
    relative_pointPower_field_h0 G hg s hI (S.fromSpecResidueField x) 1 (by decide)⟩

include hg in
/-- The actual degree-one direct image is a line without restrictions on the base. -/
theorem relative_pointOne_pushforward_rankOne_unrestricted :
    LocallyFreeRankOne ((pushforward G.hom).obj
      (tensorPower (divisorLineBundle s.left.ker hI) 1)) := by
  let _ := SmoothOfRelativeDimension.smooth 1 G.hom
  exact ((smooth_geometricAcyclicRankOne_iff_actual G.hom _
    (hI.divisorLineBundle_locallyFreeRankOne.tensorPower 1)).mp
      (relative_pointOne_geometricAcyclicRankOne G hg s hI)).2

include hg in
/-- Removing the tensor unitor retains the original divisor line's actual direct image. -/
theorem relative_pointLine_pushforward_rankOne_unrestricted :
    LocallyFreeRankOne ((pushforward G.hom).obj (divisorLineBundle s.left.ker hI)) :=
  (relative_pointOne_pushforward_rankOne_unrestricted G hg s hI).of_iso
    ((pushforward G.hom).mapIso (rightUnitor (divisorLineBundle s.left.ker hI)))

end FLT.Mazur.FCurve
