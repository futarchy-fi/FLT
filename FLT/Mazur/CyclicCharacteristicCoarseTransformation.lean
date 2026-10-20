/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CyclicCharacteristicOrbitSchemeDescent
public import FLT.Mazur.CyclicCharacteristicDisjointQuotientReduction
public import FLT.Mazur.CyclicCharacteristicUnmarkedSchemeDescent

/-!
# The coarse transformation on normalized unmarked parameters

The original orbit projection descends to the actual fppf parameter sheaf.
This construction concerns the normalized parameter scope; coverage of all
generalized elliptic curves, including the boundary, is a separate question.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.CyclicCharacteristicOrbit
open CyclicCharacteristicAtlas
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable (n : ℕ) [NeZero n]

/-- The original characteristic charts map to the constructed orbit scheme. -/
def normalizedCoarseChart (b : Bool) : normalizedLocus n b ⟶ invariantOrbitScheme n :=
  normalizedDisjointInclusion n b ≫ invariantOrbitSchemeProjection n

/-- The coarse charts respect every actual unmarked comparison. -/
theorem normalizedCoarseChart_invariant : UnmarkedInvariant n (normalizedCoarseChart n) :=
  (disjointComparison_invariant_iff n (invariantOrbitSchemeProjection n)).mp
    (invariantOrbitSchemeProjection_condition n)

/-- The natural coarse map on the actual normalized unmarked parameter sheaf. -/
def normalizedCoarseTransformation : unmarkedParameterSheaf n ⟶
    Scheme.fppfTopology.uliftYoneda.{1}.obj (invariantOrbitScheme n) :=
  unmarkedSchemeDesc n (normalizedCoarseChart n) (normalizedCoarseChart_invariant n)

/-- Its pullback to the original parameter presheaf is the original projection. -/
theorem normalizedCoarseTransformation_parameters :
    unmarkedParameterSheafMap n ≫ (normalizedCoarseTransformation n).hom =
      schemeParameterMap n (normalizedCoarseChart n) :=
  unmarkedParameterSheafMap_desc n _ _

/-- Every original normalized parameter retains its prescribed orbit morphism. -/
theorem normalizedCoarseTransformation_evaluation {T : Scheme} (b : Bool)
    (q : T ⟶ normalizedLocus n b) :
    (normalizedCoarseTransformation n).hom.app (Opposite.op T)
      ((unmarkedParameterSheafMap n).app (Opposite.op T) ⟨b, ULift.up q⟩) =
        ULift.up (q ≫ normalizedCoarseChart n b) :=
  unmarkedSchemeDesc_evaluation n _ _ b q

/-- The chart equations uniquely characterize this actual sheaf morphism. -/
theorem normalizedCoarseTransformation_unique
    (d : unmarkedParameterSheaf n ⟶
      Scheme.fppfTopology.uliftYoneda.{1}.obj (invariantOrbitScheme n))
    (hd : unmarkedParameterSheafMap n ≫ d.hom =
      schemeParameterMap n (normalizedCoarseChart n)) :
    d = normalizedCoarseTransformation n :=
  unmarkedSheaf_hom_ext n (hd.trans (normalizedCoarseTransformation_parameters n).symm)

end FLT.Mazur.CyclicCharacteristicOrbit
