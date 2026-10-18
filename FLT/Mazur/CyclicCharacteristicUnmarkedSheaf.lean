/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CyclicCharacteristicUnmarkedQuotientUniversal
public import FLT.Mazur.SchemeFppfFamilyCover
public import Mathlib.CategoryTheory.Sites.LocallyBijective

/-!
# The fppf sheaf quotient of the actual unmarked parameters

Sheafification adds descent to the pointwise quotient. Its universal map
retains every original normalized parameter and is locally surjective.
Maps to any fppf sheaf are exactly natural full unmarked invariants.
No scheme representation of this sheaf is asserted.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.CyclicCharacteristicAtlas
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable (n : ℕ) [NeZero n]

/-- The fppf sheafification of the actual full unmarked quotient presheaf. -/
def unmarkedParameterSheaf : Sheaf Scheme.fppfTopology (Type 1) :=
  (presheafToSheaf Scheme.fppfTopology (Type 1)).obj (unmarkedParameterClassPresheaf n)

/-- Every original unmarked class has its canonical sheaf quotient image. -/
def unmarkedClassToSheaf :
    unmarkedParameterClassPresheaf n ⟶ (unmarkedParameterSheaf n).obj :=
  toSheafify Scheme.fppfTopology (unmarkedParameterClassPresheaf n)

/-- The canonical actual parameter map into the fppf quotient. -/
def unmarkedParameterSheafMap :
    normalizedParameterPresheaf n ⟶ (unmarkedParameterSheaf n).obj :=
  unmarkedParameterProjection n ≫ unmarkedClassToSheaf n

/-- The pointwise quotient projection is locally surjective for the fppf topology. -/
instance unmarkedParameterProjection_isLocallySurjective :
    Presheaf.IsLocallySurjective Scheme.fppfTopology (unmarkedParameterProjection n) :=
  Presheaf.isLocallySurjective_of_surjective _ _ (unmarkedParameterProjection_surjective n)

/-- Every sheaf section locally comes from an original unmarked parameter class. -/
instance unmarkedClassToSheaf_isLocallySurjective :
    Presheaf.IsLocallySurjective Scheme.fppfTopology (unmarkedClassToSheaf n) :=
  inferInstanceAs (Presheaf.IsLocallySurjective Scheme.fppfTopology (toSheafify _ _))

/-- Actual normalized parameters locally cover every section of the sheaf quotient. -/
instance unmarkedParameterSheafMap_isLocallySurjective :
    Presheaf.IsLocallySurjective Scheme.fppfTopology (unmarkedParameterSheafMap n) :=
  inferInstanceAs (Presheaf.IsLocallySurjective _
    (unmarkedParameterProjection n ≫ unmarkedClassToSheaf n))

variable {F : Sheaf Scheme.fppfTopology (Type 1)}
  (v : normalizedParameterPresheaf n ⟶ F.obj) (hv : ParameterInvariant n v)

/-- Descend a proved full unmarked invariant to the actual fppf quotient. -/
def unmarkedSheafDesc : unmarkedParameterSheaf n ⟶ F :=
  ⟨sheafifyLift Scheme.fppfTopology (unmarkedParameterDesc n v hv) F.property⟩

/-- Sheaf descent retains the supplied natural invariant on every original parameter. -/
theorem unmarkedParameterSheafMap_desc :
    unmarkedParameterSheafMap n ≫ (unmarkedSheafDesc n v hv).hom = v := by
  change (unmarkedParameterProjection n ≫ toSheafify _ _) ≫ sheafifyLift _ _ _ = v
  rw [Category.assoc, toSheafify_sheafifyLift, unmarkedParameterProjection_desc]

/-- The original normalized parameters detect morphisms out of the actual sheaf quotient. -/
theorem unmarkedSheaf_hom_ext {a b : unmarkedParameterSheaf n ⟶ F}
    (h : unmarkedParameterSheafMap n ≫ a.hom =
      unmarkedParameterSheafMap n ≫ b.hom) : a = b := by
  apply Sheaf.hom_ext
  apply sheafify_hom_ext Scheme.fppfTopology _ _ F.property
  apply unmarkedParameter_hom_ext n
  simpa only [unmarkedParameterSheafMap, unmarkedClassToSheaf, Category.assoc] using h

include hv in
/-- Every full natural invariant has a unique extension to the constructed fppf sheaf. -/
theorem unmarkedSheaf_desc_existsUnique :
    ∃! d : unmarkedParameterSheaf n ⟶ F, unmarkedParameterSheafMap n ≫ d.hom = v := by
  refine ⟨unmarkedSheafDesc n v hv, unmarkedParameterSheafMap_desc n v hv, ?_⟩
  intro d hd
  exact unmarkedSheaf_hom_ext n (hd.trans (unmarkedParameterSheafMap_desc n v hv).symm)

end FLT.Mazur.CyclicCharacteristicAtlas
