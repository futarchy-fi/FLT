/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PrincipalIdealScalarImage
public import FLT.Mazur.StructureIdealPowerQuotient

/-!
# A regular principal quotient is the actual closed structure sheaf

The principal image comparison is an isomorphism when its scalar is
regular. Passing to cokernels preserves the original geometric restriction.
-/

@[expose] public noncomputable section

open CategoryTheory Limits AlgebraicGeometry

namespace FLT.Mazur.RegularPrincipalStructureQuotient

open FCurve GlobalIdealPower IdealPowerScalarLift PrincipalIdealScalarImage

universe u

set_option backward.isDefEq.respectTransparency false

variable {X : Scheme.{u}} [IsLocallyNoetherian X]
  (I : X.IdealSheafData) (M : X.Modules) [M.IsFinitePresentation]
  (r : Γ(X, ⊤))
  (hI : ∀ U : X.affineOpens, I.ideal U =
    Ideal.span {X.presheaf.map U.1.leTop.op r})
  [Mono (scalarEnd M r)]

/-- A regular principal scalar identifies the original module with its ideal image. -/
def principalImageIso : M ≅ multiple I M := by
  have : Mono (ontoPrincipal I M r hI) :=
    mono_of_mono_fac (ontoPrincipal_inclusion I M r hI)
  have := isIso_of_mono_of_epi (ontoPrincipal I M r hI)
  exact asIso (ontoPrincipal I M r hI)

/-- The image comparison retains actual multiplication by the original scalar. -/
@[reassoc] theorem principalImageIso_inclusion :
    (principalImageIso I M r hI).hom ≫ inclusion I M = scalarEnd M r :=
  ontoPrincipal_inclusion I M r hI

/-- Taking the principal scalar cokernel is the actual ideal-image quotient. -/
def cokernelIso : cokernel (scalarEnd M r) ≅ cokernel (inclusion I M) :=
  cokernel.mapIso _ _ (principalImageIso I M r hI) (Iso.refl _) (by
    simpa using (principalImageIso_inclusion I M r hI).symm)

/-- The cokernel comparison preserves the projection of the original module. -/
@[reassoc] theorem cokernelIso_projection :
    cokernel.π (scalarEnd M r) ≫ (cokernelIso I M r hI).hom =
      cokernel.π (inclusion I M) := by
  unfold cokernelIso
  exact cokernel.π_desc _ _ _


/-- The scalar quotient of functions is the structure sheaf of the actual closed subscheme. -/
def structureCokernelIso [Mono (scalarEnd (structureModule X) r)] :
    cokernel (scalarEnd (structureModule X) r) ≅
      (Scheme.Modules.pushforward I.subschemeι).obj (structureModule I.subscheme) := by
  let _ := CoherentIdealIntersection.structureModule_coherent (X := X)
  exact cokernelIso I (structureModule X) r hI ≪≫
    cokernel.mapIso _ _ (StructureIdealPowerQuotient.multipleIso I) (Iso.refl _) (by
      simpa using (StructureIdealPowerQuotient.multipleIso_inclusion I).symm) ≪≫
        IdealAdicQuotient.idealQuotientCokernelIso I

/-- The scalar-quotient comparison retains the actual restriction to the closed subscheme. -/
@[reassoc] theorem structureCokernelIso_projection
    [Mono (scalarEnd (structureModule X) r)] :
    cokernel.π (scalarEnd (structureModule X) r) ≫ (structureCokernelIso I r hI).hom =
      idealQuotientMap I := by
  let _ := CoherentIdealIntersection.structureModule_coherent (X := X)
  dsimp only [structureCokernelIso, Iso.trans_hom]
  rw [cokernelIso_projection_assoc]
  rw [← Category.assoc]
  erw [cokernel.π_desc]
  exact IdealAdicQuotient.idealQuotientCokernelIso_projection I

end FLT.Mazur.RegularPrincipalStructureQuotient
