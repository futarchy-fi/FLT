/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.RelativeGenusOnePointFibers
public import FLT.Mazur.SmoothGeometricAcyclicFiniteFree

/-!
# Higher pole direct images over unrestricted original genus-one bases

Positive pole orders on the original section have locally finite free actual
direct images. This includes the second, third and sixth pole spaces without
assuming the original base is affine, reduced or Noetherian.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry MonoidalCategory
open Scheme.Modules
namespace FLT.Mazur.FCurve
open ModuleLineBundleTensorPullback LineSectionBaseChange
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {S : Scheme} (G : Over S) [GrpObj G] [IsProper G.hom]
  [SmoothOfRelativeDimension 1 G.hom] [GeometricallyIntegral G.hom]
  (hg : CurveFiberHypotheses.NodalGenusOneGeometricFibers G.hom)
  (s : 𝟙_ (Over S) ⟶ G) (hI : EffectiveCartier s.left.ker)
  (m : ℕ) (hm : 0 < m)

include hg hm in
/-- Every positive pole power has acyclic actual residue fibers on an unrestricted base. -/
theorem relative_pointPower_geometric_acyclic_unrestricted (x : S) (n : ℕ) :
    Subsingleton (ModuleH ((pullback (G.hom.fiberι x)).obj
      (tensorPower (divisorLineBundle s.left.ker hI) m)) (n + 1)) :=
  relative_pointPower_field_acyclic G hg s hI (S.fromSpecResidueField x) m hm n

include hg hm in
/-- Every higher positive pole direct image admits finite frames on the original base. -/
theorem relative_pointPower_pushforward_locallyFiniteFree_unrestricted :
    LocallyFiniteFree ((pushforward G.hom).obj
      (tensorPower (divisorLineBundle s.left.ker hI) m)) := by
  let _ := SmoothOfRelativeDimension.smooth 1 G.hom
  exact smooth_geometricAcyclic_locallyFiniteFree G.hom _
    (hI.divisorLineBundle_locallyFreeRankOne.tensorPower m)
    (relative_pointPower_geometric_acyclic_unrestricted G hg s hI m hm)

end FLT.Mazur.FCurve
