/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.RelativeGenusOneFramedProducts
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
namespace FLT.Mazur.FCurve
open ModuleLineBundleTensorPullback
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] divisorLineBundle sectionPoleMultiplicativeCoordinates

variable {S : Scheme} [IsAffine S] [IsNoetherianRing Γ(S, ⊤)]
  (G : Over S) [GrpObj G] [IsProper G.hom]
  [SmoothOfRelativeDimension 1 G.hom] [GeometricallyIntegral G.hom]
  (hg : CurveFiberHypotheses.NodalGenusOneGeometricFibers G.hom)
  (s : 𝟙_ (Over S) ⟶ G) (hI : EffectiveCartier s.left.ker)
  (e : (pullback s.left).obj (divisorLineBundle s.left.ker hI) ≅ structureModule S)

local notation "L" => divisorLineBundle s.left.ker hI

/-- The actual order-two section, included into the common degree-three line. -/
def relativePointProjectiveX : Γ(tensorPower (L) 3, ⊤) :=
  moduleH0Equiv _ (divisorPowerRingStep G.hom.appTop.hom hI 2
    (relativePointFramedLift G hg s hI e 1 (by decide)))

/-- The normalized order-three section in the common projective line. -/
def relativePointProjectiveY : Γ(tensorPower (L) 3, ⊤) :=
  moduleH0Equiv _ (relativePointFramedLift G hg s hI e 2 (by decide))

/-- The third homogeneous coordinate is the canonical divisor cube. -/
def relativePointProjectiveZ : Γ(tensorPower (L) 3, ⊤) :=
  tensorPowerSection _ ⊤ (divisorSection hI ⊤) 3

/-- The original triple, in the Weierstrass order X, Y, Z. -/
def relativePointProjectiveSections : Fin 3 → Γ(tensorPower (L) 3, ⊤) :=
  ![relativePointProjectiveX G hg s hI e, relativePointProjectiveY G hg s hI e,
    relativePointProjectiveZ G s hI]

/-- The last two original coordinate sections already cover the total space. -/
theorem relativePointProjectiveSections_cover :
    ⨆ i, sectionGeneratorOpen (tensorPower (L) 3)
      (relativePointProjectiveSections G hg s hI e i) = ⊤ := by
  apply top_unique
  rw [← sectionPoleGenerator_sup s.left hI e 3
    (relativePointProjectiveY G hg s hI e) G.hom s.w (by decide)
    (relativePointFramedLift_coefficient G hg s hI e 2 (by decide))]
  apply sup_le
  · exact le_iSup_of_le 2 le_rfl
  · exact le_iSup_of_le 1 le_rfl

/-- The globally defined projective map of the original normalized pole sections. -/
def relativePointToProjectiveSpace : G.left ⟶ ProjectiveSpace.space Γ(S, ⊤) (Fin 3) :=
  sectionProjectiveMorphism (tensorPower (L) 3) 2
    (relativePointProjectiveSections G hg s hI e)
    (relativePointProjectiveSections_cover G hg s hI e) G.hom.appTop.hom

/-- Its affine Z chart is exactly the original marked-point complement. -/
theorem relativePointToProjectiveSpace_preimage_z :
    relativePointToProjectiveSpace G hg s hI e ⁻¹ᵁ
      ProjectiveSpace.chart Γ(S, ⊤) (Fin 3) 2 = s.left.ker.support.compl := by
  rw [relativePointToProjectiveSpace, sectionProjectiveMorphism_preimage_chart]
  change sectionGeneratorOpen (tensorPower (L) 3)
    (tensorPowerSection _ ⊤ (divisorSection hI ⊤) 3) = _
  rw [tensorPowerSection_generatorOpen hI.divisorLineBundle_locallyFreeRankOne _ (by decide),
    divisorSection_generatorOpen]

/-- The global projective coordinate map retains the actual original base morphism. -/
theorem relativePointToProjectiveSpace_over :
    relativePointToProjectiveSpace G hg s hI e ≫
      ProjectiveSpace.baseProjection Γ(S, ⊤) (Fin 3) = G.hom ≫ S.toSpecΓ := by
  have ha := sectionProjectiveMorphism_baseProjection (tensorPower (L) 3) 2
    (relativePointProjectiveSections G hg s hI e)
    (relativePointProjectiveSections_cover G hg s hI e) (G.hom ≫ S.toSpecΓ)
  have hr : (G.hom ≫ S.toSpecΓ).appTop.hom.comp
      (Scheme.ΓSpecIso (.of Γ(S, ⊤))).inv.hom = G.hom.appTop.hom := by
    change ((Scheme.ΓSpecIso (.of Γ(S, ⊤))).inv ≫ (G.hom ≫ S.toSpecΓ).appTop).hom = _
    rw [Scheme.Hom.comp_appTop, Scheme.toSpecΓ_appTop]
    erw [Iso.inv_hom_id_assoc]
  rw [hr] at ha
  exact ha

end FLT.Mazur.FCurve
