/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.GeneralizedCurveMarkingGluedProper
public import FLT.Mazur.GeneralizedCurveMarkingPointedCubic

/-!
# The original marking is the global infinity section

The image of the original section recovers the actual integral infinity
section on every affine frame. Properness makes this global section closed.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry MonoidalCategory
namespace FLT.Mazur.GeneralizedEllipticCurve
open GroupSectionBaseChange WeierstrassIntegralChart
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {S : Scheme} [IsLocallyNoetherian S] (E : GeneralizedEllipticCurve S)
  (s : 𝟙_ (Over S) ⟶ E.group)

local instance gluedSectionNoetherian (i : SmoothMarkingAffineChart E s) :
    IsNoetherianRing Γ(i.base.1.toScheme, ⊤) :=
  IsLocallyNoetherian.component_noetherian ⟨⊤, isAffineOpen_top _⟩

/-- The global infinity section is the image of the actual original marking. -/
def smoothMarkingGluedZero : S ⟶ smoothMarkingGluedCubic E s :=
  (s ≫ E.inclusion).left ≫ smoothMarkingToGluedCubic E s

/-- The marking image is a section over the original base. -/
@[reassoc] theorem smoothMarkingGluedZero_over :
    smoothMarkingGluedZero E s ≫ smoothMarkingGluedBase E s = 𝟙 S := by
  rw [smoothMarkingGluedZero, Category.assoc, smoothMarkingToGluedCubic_over]
  exact (s ≫ E.inclusion).w

/-- Every actual affine frame recovers its integral infinity section. -/
@[reassoc] theorem smoothMarkingGluedZero_chart (i : SmoothMarkingAffineChart E s) :
    i.base.1.ι ≫ smoothMarkingGluedZero E s =
      i.base.1.toScheme.toSpecΓ ≫ integralCurveZero (smoothMarkingAffineEquation E s i) ≫
        smoothMarkingGluedChart E s i := by
  rw [smoothMarkingGluedZero, ← Category.assoc, ← section_fst i.base.1.ι,
    pullSection_smoothMarking, Category.assoc, smoothMarkingToGluedCubic_chart,
    smoothMarkingLocalToGlued, ← Category.assoc,
    smoothMarkingToIntegralCubic_marking (E.baseChange i.base.1.ι)
      (pullSection i.base.1.ι s) i.frame, Category.assoc]
  rfl

/-- The local infinity sections determine the global marking image uniquely. -/
theorem smoothMarkingGluedZero_unique (z : S ⟶ smoothMarkingGluedCubic E s)
    (hz : ∀ i : SmoothMarkingAffineChart E s, i.base.1.ι ≫ z =
      i.base.1.toScheme.toSpecΓ ≫ integralCurveZero (smoothMarkingAffineEquation E s i) ≫
        smoothMarkingGluedChart E s i) : z = smoothMarkingGluedZero E s := by
  apply Scheme.Cover.hom_ext (smoothMarkingFrameCover E s)
  intro i
  exact (hz i).trans (smoothMarkingGluedZero_chart E s i).symm

/-- The constructed infinity section is a closed immersion, including over nilpotent bases. -/
instance smoothMarkingGluedZero_isClosedImmersion :
    IsClosedImmersion (smoothMarkingGluedZero E s) := by
  have : IsClosedImmersion (smoothMarkingGluedZero E s ≫ smoothMarkingGluedBase E s) := by
    rw [smoothMarkingGluedZero_over]
    infer_instance
  exact IsClosedImmersion.of_comp (smoothMarkingGluedZero E s) (smoothMarkingGluedBase E s)

end FLT.Mazur.GeneralizedEllipticCurve
