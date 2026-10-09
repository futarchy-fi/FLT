/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineResidueSectionCoefficients
public import FLT.Mazur.ArtinianRelativeSectionCriterion
public import FLT.Mazur.ProperRelativeEvaluationLocus

/-!
# Semilinear coordinates for actual section evaluation

The identity on global functions changes the structural section-ring scalars
to the original affine base ring. Evaluation becomes the relative augmentation.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.Approximation
open Chow Chow.AffineBase FCurve ArtinianRelativeSectionCriterion

variable {R : CommRingCat.{0}} {X : Scheme.{0}} (f : X ⟶ Spec R)

local instance : RingHomInvPair (affineSectionRingEquiv R).toRingHom
    (affineSectionRingEquiv R).symm.toRingHom :=
  RingHomInvPair.of_ringEquiv (affineSectionRingEquiv R)

local instance : RingHomInvPair (affineSectionRingEquiv R).symm.toRingHom
    (affineSectionRingEquiv R).toRingHom :=
  RingHomInvPair.of_ringEquiv_symm (affineSectionRingEquiv R)

/-- Actual global functions have semilinear coordinates over the original affine ring. -/
def affineSectionsSemilinearEquiv :
    let _ := (baseCohomologyScalars f).toAlgebra
    baseSections (structureModule X) f.appTop.hom ⊤
      ≃ₛₗ[(affineSectionRingEquiv R).toRingHom] Γ(X, ⊤) :=
  let _ := (baseCohomologyScalars f).toAlgebra
  { (AddEquiv.refl Γ(X, ⊤)) with
    map_smul' := fun r a ↦ by
      change X.presheaf.map (𝟙 _) (f.appTop r) * (show Γ(X, ⊤) from a) =
        f.appTop ((Scheme.ΓSpecIso R).inv ((Scheme.ΓSpecIso R).hom r)) * (show Γ(X, ⊤) from a)
      simp only [X.presheaf.map_id, ConcreteCategory.id_apply, Iso.hom_inv_id_apply] }

/-- Section coordinates leave the underlying global function unchanged. -/
lemma affineSectionsSemilinearEquiv_apply (a : Γ(X, ⊤)) :
    affineSectionsSemilinearEquiv f a = a := rfl

/-- In affine coordinates the actual linear evaluation is the relative augmentation. -/
lemma affineSectionsSemilinearEquiv_evaluation (s : Spec R ⟶ X)
    (hs : s ≫ f = 𝟙 _) (a : baseSections (structureModule X) f.appTop.hom ⊤) :
    affineSectionRingEquiv R (evaluation f s hs a) =
      relativeSectionAugmentation f s hs (affineSectionsSemilinearEquiv f a) := rfl

end FLT.Mazur.Approximation
