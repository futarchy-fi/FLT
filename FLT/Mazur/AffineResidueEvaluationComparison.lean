/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineSectionEvaluationCoordinates
public import FLT.Mazur.TensorEvaluationSemilinear

/-!
# Actual residue coefficients and the finite relative evaluation locus

All three semilinear coordinate changes identify injectivity of actual
residue-spectrum tensor evaluation with the ideal-residue-field condition.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.Approximation
open Chow.AffineBase ArtinianRelativeSectionCriterion

variable {R : CommRingCat.{0}} {X : Scheme.{0}} (f : X ⟶ Spec R)
  (s : Spec R ⟶ X) (hs : s ≫ f = 𝟙 _) (b : Spec R)

local instance : RingHomInvPair (affineSectionRingEquiv R).toRingHom
    (affineSectionRingEquiv R).symm.toRingHom :=
  RingHomInvPair.of_ringEquiv (affineSectionRingEquiv R)

local instance : RingHomInvPair (affineSectionRingEquiv R).symm.toRingHom
    (affineSectionRingEquiv R).toRingHom :=
  RingHomInvPair.of_ringEquiv_symm (affineSectionRingEquiv R)

/-- Actual residue-spectrum coefficients give exactly the relative evaluation condition. -/
theorem residueSectionEvaluation_injective_iff :
    let _ := (baseCohomologyScalars f).toAlgebra
    let _ : Algebra Γ(Spec R, ⊤) Γ(Spec ((Spec R).residueField b), ⊤) :=
      ((Spec R).fromSpecResidueField b).appTop.hom.toAlgebra
    Function.Injective ((evaluation f s hs).lTensor Γ(Spec ((Spec R).residueField b), ⊤)) ↔
      Function.Injective
        ((relativeSectionAugmentation f s hs).toLinearMap.lTensor b.asIdeal.ResidueField) := by
  let _ := (baseCohomologyScalars f).toAlgebra
  let _ : Algebra Γ(Spec R, ⊤) Γ(Spec ((Spec R).residueField b), ⊤) :=
    ((Spec R).fromSpecResidueField b).appTop.hom.toAlgebra
  exact tensorEvaluation_injective_iff_semilinear (residueSectionSemilinearEquiv R b)
    (affineSectionsSemilinearEquiv f) (affineSectionRingEquiv R).toSemilinearEquiv
    (evaluation f s hs) (relativeSectionAugmentation f s hs).toLinearMap
    (affineSectionsSemilinearEquiv_evaluation f s hs)

/-- Actual residue-spectrum tensor evaluations have an open injectivity locus. -/
theorem isOpen_actualResidueTensorEvaluationLocus [IsNoetherianRing R] [IsProper f] :
    IsOpen {b : Spec R |
      let _ : Algebra Γ(Spec R, ⊤) Γ(Spec ((Spec R).residueField b), ⊤) :=
        ((Spec R).fromSpecResidueField b).appTop.hom.toAlgebra
      Function.Injective
        ((evaluation f s hs).lTensor Γ(Spec ((Spec R).residueField b), ⊤))} := by
  let _ := (baseCohomologyScalars f).toAlgebra
  have he : {b : Spec R |
      let _ : Algebra Γ(Spec R, ⊤) Γ(Spec ((Spec R).residueField b), ⊤) :=
        ((Spec R).fromSpecResidueField b).appTop.hom.toAlgebra
      Function.Injective ((evaluation f s hs).lTensor Γ(Spec ((Spec R).residueField b), ⊤))} =
      {b : Spec R | Function.Injective
        ((relativeSectionAugmentation f s hs).toLinearMap.lTensor b.asIdeal.ResidueField)} := by
    ext b
    exact residueSectionEvaluation_injective_iff f s hs b
  rw [he]
  exact isOpen_proper_relativeEvaluationLocus f s hs

end FLT.Mazur.Approximation
