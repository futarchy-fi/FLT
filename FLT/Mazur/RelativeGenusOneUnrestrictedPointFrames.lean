/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.RelativeGenusOneUnrestrictedPointPowers
public import FLT.Mazur.SmoothGeometricAcyclicExactFrames

/-!
# Exact higher pole frames on arbitrary original genus-one bases

The actual O(ms) direct image has precisely m local basis sections for every
positive m, including the pole orders two, three and six of cubic coordinates.
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
/-- The original higher pole direct image has exactly m local basis sections on every base. -/
theorem relative_pointPower_frame_unrestricted (x : S) :
    ∃ U : S.Opens, x ∈ U ∧ Nonempty
      (((pushforward G.hom).obj (tensorPower (divisorLineBundle s.left.ker hI) m)).restrict U.ι
        ≅ SheafOfModules.free (Fin m)) := by
  let _ := SmoothOfRelativeDimension.smooth 1 G.hom
  exact smooth_geometricAcyclic_exactRank_frame G.hom _
    (hI.divisorLineBundle_locallyFreeRankOne.tensorPower m)
    (relative_pointPower_geometric_acyclic_unrestricted G hg s hI m hm) x m
    (relative_pointPower_field_h0 G hg s hI (S.fromSpecResidueField x) m hm)

end FLT.Mazur.FCurve
