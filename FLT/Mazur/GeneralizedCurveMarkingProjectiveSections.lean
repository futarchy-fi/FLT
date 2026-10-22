/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.GeneralizedCurveMarkingFramedProducts
public import FLT.Mazur.SectionPoleGeneratorCover
public import FLT.Mazur.ModuleSectionProjectiveOver

/-!
# The original relative projective coordinate sections

The normalized order-three lift generates along the marking, while the
canonical divisor cube generates its complement. The actual three sections
therefore define a projective morphism on the entire original family.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Scheme.Modules MonoidalCategory
namespace FLT.Mazur.GeneralizedEllipticCurve
open FCurve ModuleLineBundleTensorPullback
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] divisorLineBundle sectionPoleMultiplicativeCoordinates
  Scheme.Modules.pullback ModuleSheafTensor.tensor

variable {S : Scheme} [IsAffine S] [IsNoetherianRing Γ(S, ⊤)]
  (E : GeneralizedEllipticCurve S) (s : 𝟙_ (Over S) ⟶ E.group)

local notation "t" => s ≫ E.inclusion
local notation "hI" => And.left (smoothMarking_relativeCartier E s)

local instance generalizedCurveMarkingProjectiveSectionsProper :
    IsProper E.curve.hom := E.family.family.1

variable (e : (pullback (s ≫ E.inclusion).left).obj
  (divisorLineBundle (s ≫ E.inclusion).left.ker
    (smoothMarking_relativeCartier E s).1) ≅ structureModule S)

local notation "L" => divisorLineBundle (Scheme.Hom.ker (Over.Hom.left (t))) (hI)

/-- The actual order-two section, included into the common degree-three line. -/
def smoothMarkingProjectiveX : Γ(tensorPower (L) 3, ⊤) :=
  moduleH0Equiv _ (divisorPowerRingStep E.curve.hom.appTop.hom (hI) 2
    (smoothMarkingFramedLift E s e 1 (by decide)))

/-- The normalized order-three section in the common projective line. -/
def smoothMarkingProjectiveY : Γ(tensorPower (L) 3, ⊤) :=
  moduleH0Equiv _ (smoothMarkingFramedLift E s e 2 (by decide))

/-- The third homogeneous coordinate is the canonical divisor cube. -/
def smoothMarkingProjectiveZ : Γ(tensorPower (L) 3, ⊤) :=
  tensorPowerSection _ ⊤ (divisorSection (hI) ⊤) 3

/-- The original triple, in the Weierstrass order X, Y, Z. -/
def smoothMarkingProjectiveSections : Fin 3 → Γ(tensorPower (L) 3, ⊤) :=
  ![smoothMarkingProjectiveX E s e, smoothMarkingProjectiveY E s e,
    smoothMarkingProjectiveZ E s]

/-- The last two original coordinate sections already cover the total space. -/
theorem smoothMarkingProjectiveSections_cover :
    ⨆ i, sectionGeneratorOpen (tensorPower (L) 3)
      (smoothMarkingProjectiveSections E s e i) = ⊤ := by
  apply top_unique
  rw [← sectionPoleGenerator_sup (t).left (hI) e 3
    (smoothMarkingProjectiveY E s e) E.curve.hom (t).w (by decide)
    (smoothMarkingFramedLift_coefficient E s e 2 (by decide))]
  apply sup_le
  · exact le_iSup_of_le 2 le_rfl
  · exact le_iSup_of_le 1 le_rfl

/-- The globally defined projective map of the original normalized pole sections. -/
def smoothMarkingToProjectiveSpace : E.curve.left ⟶ ProjectiveSpace.space Γ(S, ⊤) (Fin 3) :=
  sectionProjectiveMorphism (tensorPower (L) 3) 2
    (smoothMarkingProjectiveSections E s e)
    (smoothMarkingProjectiveSections_cover E s e) E.curve.hom.appTop.hom

/-- Its affine Z chart is exactly the original marked-point complement. -/
theorem smoothMarkingToProjectiveSpace_preimage_z :
    smoothMarkingToProjectiveSpace E s e ⁻¹ᵁ
      ProjectiveSpace.chart Γ(S, ⊤) (Fin 3) 2 = (t).left.ker.support.compl := by
  rw [smoothMarkingToProjectiveSpace, sectionProjectiveMorphism_preimage_chart]
  change sectionGeneratorOpen (tensorPower (L) 3)
    (tensorPowerSection _ ⊤ (divisorSection (hI) ⊤) 3) = _
  rw [tensorPowerSection_generatorOpen (hI).divisorLineBundle_locallyFreeRankOne _ (by decide),
    divisorSection_generatorOpen]

/-- The global projective coordinate map retains the actual original base morphism. -/
theorem smoothMarkingToProjectiveSpace_over :
    smoothMarkingToProjectiveSpace E s e ≫
      ProjectiveSpace.baseProjection Γ(S, ⊤) (Fin 3) = E.curve.hom ≫ S.toSpecΓ := by
  have ha := sectionProjectiveMorphism_baseProjection (tensorPower (L) 3) 2
    (smoothMarkingProjectiveSections E s e)
    (smoothMarkingProjectiveSections_cover E s e) (E.curve.hom ≫ S.toSpecΓ)
  have hr : (E.curve.hom ≫ S.toSpecΓ).appTop.hom.comp
      (Scheme.ΓSpecIso (.of Γ(S, ⊤))).inv.hom = E.curve.hom.appTop.hom := by
    change ((Scheme.ΓSpecIso (.of Γ(S, ⊤))).inv ≫ (E.curve.hom ≫ S.toSpecΓ).appTop).hom = _
    rw [Scheme.Hom.comp_appTop, Scheme.toSpecΓ_appTop]
    erw [Iso.inv_hom_id_assoc]
  rw [hr] at ha
  exact ha

end FLT.Mazur.GeneralizedEllipticCurve
