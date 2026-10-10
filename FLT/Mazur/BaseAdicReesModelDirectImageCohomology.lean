/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.BaseAdicReesModelScalarRestriction
public import FLT.Mazur.AffinePushforwardCohomology

/-!
# Comparing cohomology with the proper Rees model

The actual affine source projection preserves cohomology in every degree.
Naturality retains multiplication by the named global Rees scalars used
by proper coherent finiteness, expressed through the actual pushforward maps.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry
open Scheme.Modules FLT.Mazur.FCurve FLT.Mazur.IdealPowerScalarLift

namespace FLT.Mazur.BaseAdicRees

variable {R : CommRingCat.{0}} [IsNoetherianRing R]
  {X : Scheme.{0}} [X.IsSeparated] (f : X ⟶ Spec R) (J : Ideal R)
  [IsLocallyNoetherian X] (M : X.Modules) [M.IsFinitePresentation]

/-- The actual direct image has the same cohomology as the original global model. -/
def modelDirectImageCohomologyEquiv (q : ℕ) :
    ModuleH (modelPushforward f J M) q ≃+ ModuleH (globalModelSheaf f J M) q := by
  let _ := Module.compHom (ModuleH (globalModelSheaf f J M) q)
    (modelSourceProjection f J).appTop.hom
  exact (affinePushforwardModuleHEquiv (modelSourceProjection f J)
    (globalModelSheaf f J M) q).toAddEquiv

/-- The comparison retains multiplication by the named proper-model Rees scalar. -/
lemma modelDirectImageCohomologyEquiv_reesEnd (q : ℕ) (a : reesAlgebra J)
    (s : ModuleH (modelPushforward f J M) q) :
    modelDirectImageCohomologyEquiv f J M q (moduleHMap (modelReesEnd f J M a) q s) =
      a • (show ModuleRingH (modelCohomologyScalars f J) (globalModelSheaf f J M) q from
        modelDirectImageCohomologyEquiv f J M q s) := by
  have h := affinePushforwardModuleHEquiv_naturality (modelSourceProjection f J)
    (globalModelSheaf f J M)
    (scalarEnd (globalModelSheaf f J M) (modelCohomologyScalars f J a)) q s
  rw [scalarEnd_cohomology] at h
  exact h

/-- A chosen source base-ring action is retained in every cohomological degree as well. -/
def modelDirectImageRingCohomologyEquiv {A : Type} [CommRing A]
    (ρ : A →+* Γ(X, ⊤)) (q : ℕ) :
    ModuleRingH ρ (modelPushforward f J M) q ≃ₗ[A]
      ModuleRingH ((modelSourceProjection f J).appTop.hom.comp ρ)
        (globalModelSheaf f J M) q :=
  affinePushforwardRingHEquiv (modelSourceProjection f J) (globalModelSheaf f J M) ρ q

end FLT.Mazur.BaseAdicRees
