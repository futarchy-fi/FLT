/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OneGonSmoothingRelativeGroup
public import FLT.Mazur.WeierstrassSmoothCoefficientGroupIso
public import FLT.Mazur.WeierstrassSplitNodalSmoothGroupComparison

/-!
# The complete smoothing's actual closed smooth group is the torus

The coefficient comparison retains the full smooth group, including singular
fibers. Specializing the complete smoothing identifies its actual closed group
with the multiplicative group, using the proved split-nodal group law.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry
namespace FLT.Mazur.OneGonSmoothing
open WeierstrassIntegralChart WeierstrassDividedDepth
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {R : Type} [CommRing R] (S : Type) [CommRing S] [Algebra R S] (t : R)

/-- The actual smooth group comparison over an arbitrary coefficient algebra. -/
irreducible_def relativeCoefficientGroupIso :
    relativeGroup (algebraMap R S t) ≅
      relativeTestGroup t (Spec.map (CommRingCat.ofHom (algebraMap R S))) :=
  eqToIso (congrArg integralSmoothGroup (equation_map t (algebraMap R S)).symm) ≪≫
    originalSmoothCoefficientGroupIso S (equation t)

/-- At parameter zero the original smooth group is the multiplicative group. -/
def zeroRelativeGroupTorusIso :
    relativeGroup (0 : R) ≅ CommGrp.mk (MultiplicativeGroupScheme.gm R) :=
  integralSmoothSplitNodalTorusIso (-1 : Rˣ)

/-- The original closed coefficient map kills the smoothing parameter as a curve equation. -/
theorem completeClosed_equation (K : Type) [Field K] :
    (equation (PowerSeries.X : PowerSeries K)).map PowerSeries.constantCoeff =
      splitNodalEquation (-1 : Kˣ) := by
  rw [equation_map, PowerSeries.constantCoeff_X]
  rfl

/-- The actual constant-coefficient fiber of the complete smooth group is the torus. -/
irreducible_def completeClosedGroupTorusIso (K : Type) [Field K] :
    relativeTestGroup (PowerSeries.X : PowerSeries K)
      (Spec.map (CommRingCat.ofHom (PowerSeries.constantCoeff (R := K)))) ≅
        CommGrp.mk (MultiplicativeGroupScheme.gm K) := by
  letI := (PowerSeries.constantCoeff (R := K)).toAlgebra
  exact (originalSmoothCoefficientGroupIso K (equation (PowerSeries.X : PowerSeries K))).symm ≪≫
    eqToIso (congrArg integralSmoothGroup (completeClosed_equation K)) ≪≫
      integralSmoothSplitNodalTorusIso (-1 : Kˣ)

/-- The group comparison also retains the original closed smooth scheme over its residue base. -/
def completeClosedGroupTorusOverIso (K : Type) [Field K] :
    (relativeTestGroup (PowerSeries.X : PowerSeries K)
      (Spec.map (CommRingCat.ofHom (PowerSeries.constantCoeff (R := K))))).X ≅
        MultiplicativeGroupScheme.gm K :=
  (CommGrp.forget (Over (Spec (.of K)))).mapIso (completeClosedGroupTorusIso K)

end FLT.Mazur.OneGonSmoothing
