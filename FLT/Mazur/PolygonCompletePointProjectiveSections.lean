/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompletePointPoleProducts
public import FLT.Mazur.SectionPoleGeneratorCover
public import FLT.Mazur.ModuleSectionProjectiveOver

/-!
# Original complete-base projective pole sections

The canonical divisor cube and the integral unit-leading order-three lift
cover the actual total space and define its degree-three projective morphism.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Scheme.Modules
namespace FLT.Mazur.PolygonInfinitesimalStages
open FCurve FCurve.ModuleLineBundleTensorPullback
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase
  divisorLineBundle ModuleSheafTensor.tensor

variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n] (i : Fin n)
local notation "S" => Spec (CommRingCat.of (PowerSeries K))
local notation "f" => exactVeroneseProjToBase K n h
local notation "s" => completeBaseMarking K n h i
local notation "hI" => And.left (completeBaseMarking_relativeCartier K n h i)

local notation "L" => completePointLine K n h i

/-- The actual order-two section, included into the common degree-three line. -/
def completePointProjectiveX : Γ(tensorPower (L) 3, ⊤) :=
  moduleH0Equiv _ (divisorPowerRingStep (f).appTop.hom hI 2
    (completePointPoleLift K n h i 0))

/-- The normalized order-three section in the common projective line. -/
def completePointProjectiveY : Γ(tensorPower (L) 3, ⊤) :=
  moduleH0Equiv _ (completePointPoleLift K n h i 1)

/-- The third homogeneous coordinate is the canonical divisor cube. -/
def completePointProjectiveZ : Γ(tensorPower (L) 3, ⊤) :=
  tensorPowerSection _ ⊤ (divisorSection hI ⊤) 3

/-- The original triple, in the Weierstrass order X, Y, Z. -/
def completePointProjectiveSections : Fin 3 → Γ(tensorPower (L) 3, ⊤) :=
  ![completePointProjectiveX K n h i, completePointProjectiveY K n h i,
    completePointProjectiveZ K n h i]

/-- The last two original coordinate sections already cover the total space. -/
theorem completePointProjectiveSections_cover :
    ⨆ j, sectionGeneratorOpen (tensorPower (L) 3)
      (completePointProjectiveSections K n h i j) = ⊤ := by
  let _ := exactVeroneseProjToBase_isProper K n h
  apply top_unique
  rw [← sectionPoleGenerator_sup s hI (completePointSectionFrame K n h i) 3
    (completePointProjectiveY K n h i) f (completeBaseMarking_toBase K n h i) (by decide)
    (completePointPoleLift_coefficient K n h i 1)]
  apply sup_le
  · exact le_iSup_of_le 2 le_rfl
  · exact le_iSup_of_le 1 le_rfl

/-- The globally defined projective map of the original normalized pole sections. -/
def completePointToProjectiveSpace :
    exactVeroneseProj K n h ⟶ ProjectiveSpace.space Γ(S, ⊤) (Fin 3) :=
  sectionProjectiveMorphism (tensorPower (L) 3) 2
    (completePointProjectiveSections K n h i)
    (completePointProjectiveSections_cover K n h i) (f).appTop.hom

/-- Its affine Z chart is exactly the original marked-point complement. -/
theorem completePointToProjectiveSpace_preimage_z :
    completePointToProjectiveSpace K n h i ⁻¹ᵁ
      ProjectiveSpace.chart Γ(S, ⊤) (Fin 3) 2 = (s).ker.support.compl := by
  rw [completePointToProjectiveSpace, sectionProjectiveMorphism_preimage_chart]
  change sectionGeneratorOpen (tensorPower (L) 3)
    (tensorPowerSection _ ⊤ (divisorSection hI ⊤) 3) = _
  erw [tensorPowerSection_generatorOpen (hI).divisorLineBundle_locallyFreeRankOne _ (by decide),
    divisorSection_generatorOpen]

/-- The global projective coordinate map retains the actual original base morphism. -/
theorem completePointToProjectiveSpace_over :
    completePointToProjectiveSpace K n h i ≫
      ProjectiveSpace.baseProjection Γ(S, ⊤) (Fin 3) = f ≫ (S).toSpecΓ := by
  have ha := sectionProjectiveMorphism_baseProjection (tensorPower (L) 3) 2
    (completePointProjectiveSections K n h i)
    (completePointProjectiveSections_cover K n h i) (f ≫ (S).toSpecΓ)
  have hr : (f ≫ (S).toSpecΓ).appTop.hom.comp
      (Scheme.ΓSpecIso (.of Γ(S, ⊤))).inv.hom = (f).appTop.hom := by
    change ((Scheme.ΓSpecIso (.of Γ(S, ⊤))).inv ≫ (f ≫ (S).toSpecΓ).appTop).hom = _
    rw [Scheme.Hom.comp_appTop, Scheme.toSpecΓ_appTop]
    erw [Iso.inv_hom_id_assoc]
  erw [hr] at ha
  exact ha

end FLT.Mazur.PolygonInfinitesimalStages
