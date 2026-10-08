/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineBasisModuleMorphism
public import FLT.Mazur.IdealAdicGradedComponentRestriction
public import FLT.Mazur.IdealAdicRelativeRecoveryScalars

/-!
# Homogeneous retracts of the actual descended pushforward

The original ideal-adic quotient sheaves are retracts of the actual
pushforward, with its geometric structure-sheaf action unchanged.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry
open Scheme.Modules FLT.Mazur.IdealAdicQuotient FLT.Mazur.IdealAdicGradedSections

universe u

namespace FLT.Mazur.IdealAdicGradedPullback

variable {X Y : Scheme.{u}} [IsLocallyNoetherian X] [IsLocallyNoetherian Y] [IsAffine Y]
variable (J : Y.IdealSheafData) (f : X ⟶ Y)

attribute [local irreducible] relativeDescendedCoefficientPushforward
attribute [local irreducible] relativePushforwardCoefficientSectionsIso

/-- Original homogeneous insertion into actual pushforward sections, on the affine basis. -/
def relativeHomogeneousInclusionBasis (n : ℕ) :
    AffineBasisModuleMorphism.basis (idealGraded (J.comap f) n) ⟶
      AffineBasisModuleMorphism.basis (relativeDescendedCoefficientPushforward J f) :=
  ⟨{ app := fun U ↦ AddCommGrpCat.ofHom
        (((relativePushforwardCoefficientLinearEquiv J f U.unop).symm.toLinearMap.comp
          (of (J.comap f) U.unop.1 n)).toAddMonoidHom)
     naturality := fun U V i ↦ by
       apply ConcreteCategory.hom_ext
       intro s
       let k : V.unop.1 ⟶ U.unop.1 := homOfLE i.unop.le
       apply (ConcreteCategory.bijective_of_isIso
         (relativePushforwardCoefficientSectionsIso J f V.unop).hom).injective
       change (relativePushforwardCoefficientSectionsIso J f V.unop).hom
         ((relativePushforwardCoefficientSectionsIso J f V.unop).inv
           (of (J.comap f) V.unop.1 n ((idealGraded (J.comap f) n).presheaf.map
             k.op s))) =
         (relativePushforwardCoefficientSectionsIso J f V.unop).hom
           ((relativeDescendedCoefficientPushforward J f).presheaf.map
             k.op
               ((relativePushforwardCoefficientSectionsIso J f U.unop).inv
                 (of (J.comap f) U.unop.1 n s)))
       have h := ConcreteCategory.congr_hom
         (relativePushforwardCoefficientSectionsIso_naturality J f k)
         ((relativePushforwardCoefficientSectionsIso J f U.unop).inv
           (of (J.comap f) U.unop.1 n s))
       simp only [ConcreteCategory.comp_apply] at h
       rw [h, Iso.inv_hom_id_apply, Iso.inv_hom_id_apply]
       exact (restrict_of (J.comap f) V.unop.1 k n s).symm }⟩

/-- Original homogeneous extraction from actual pushforward sections, on the affine basis. -/
def relativeHomogeneousProjectionBasis (n : ℕ) :
    AffineBasisModuleMorphism.basis (relativeDescendedCoefficientPushforward J f) ⟶
      AffineBasisModuleMorphism.basis (idealGraded (J.comap f) n) :=
  ⟨{ app := fun U ↦ AddCommGrpCat.ofHom
        (((component (J.comap f) U.unop.1 n).comp
          (relativePushforwardCoefficientLinearEquiv J f U.unop).toLinearMap).toAddMonoidHom)
     naturality := fun U V i ↦ by
       apply ConcreteCategory.hom_ext
       intro s
       let k : V.unop.1 ⟶ U.unop.1 := homOfLE i.unop.le
       change component (J.comap f) V.unop.1 n
         ((relativePushforwardCoefficientSectionsIso J f V.unop).hom
           ((relativeDescendedCoefficientPushforward J f).presheaf.map
             k.op s)) =
         (idealGraded (J.comap f) n).presheaf.map k.op
           (component (J.comap f) U.unop.1 n
             ((relativePushforwardCoefficientSectionsIso J f U.unop).hom s))
       have h := ConcreteCategory.congr_hom
         (relativePushforwardCoefficientSectionsIso_naturality J f k) s
       simp only [ConcreteCategory.comp_apply] at h
       rw [h]
       exact component_restrict (J.comap f) k n _ }⟩

/-- Inclusion of the original graded quotient into the actual pushforward as an O_X-module. -/
def relativeHomogeneousInclusion (n : ℕ) :
    idealGraded (J.comap f) n ⟶ relativeDescendedCoefficientPushforward J f :=
  AffineBasisModuleMorphism.extend _ _ (relativeHomogeneousInclusionBasis J f n)
    (fun U r s ↦ ((relativePushforwardCoefficientLinearEquiv J f U).symm.toLinearMap.comp
      (of (J.comap f) U.1 n)).map_smul r s)

/-- Projection onto the original graded quotient as an O_X-module. -/
def relativeHomogeneousProjection (n : ℕ) :
    relativeDescendedCoefficientPushforward J f ⟶ idealGraded (J.comap f) n :=
  AffineBasisModuleMorphism.extend _ _ (relativeHomogeneousProjectionBasis J f n)
    (fun U r s ↦ ((component (J.comap f) U.1 n).comp
      (relativePushforwardCoefficientLinearEquiv J f U).toLinearMap).map_smul r s)

/-- Affine sections of the global inclusion are the original homogeneous insertion. -/
lemma relativeHomogeneousInclusion_app (n : ℕ) (U : X.affineOpens) :
    (relativeHomogeneousInclusion J f n).app U.1 =
      AddCommGrpCat.ofHom
        (((relativePushforwardCoefficientLinearEquiv J f U).symm.toLinearMap.comp
          (of (J.comap f) U.1 n)).toAddMonoidHom) :=
  AffineBasisModuleMorphism.extend_app _ _ _ _ U

/-- Affine sections of the global projection extract the original homogeneous coefficient. -/
lemma relativeHomogeneousProjection_app (n : ℕ) (U : X.affineOpens) :
    (relativeHomogeneousProjection J f n).app U.1 =
      AddCommGrpCat.ofHom
        (((component (J.comap f) U.1 n).comp
          (relativePushforwardCoefficientLinearEquiv J f U).toLinearMap).toAddMonoidHom) :=
  AffineBasisModuleMorphism.extend_app _ _ _ _ U

attribute [local irreducible] relativeHomogeneousInclusion relativeHomogeneousProjection

/-- The homogeneous quotient is a retract for the original geometric O_X action. -/
@[reassoc]
lemma relativeHomogeneousInclusion_projection (n : ℕ) :
    relativeHomogeneousInclusion J f n ≫ relativeHomogeneousProjection J f n =
      𝟙 (idealGraded (J.comap f) n) := by
  apply AffineBasisModuleMorphism.hom_ext
  intro U
  rw [Hom.comp_app, Hom.id_app]
  rw [relativeHomogeneousInclusion_app, relativeHomogeneousProjection_app]
  apply ConcreteCategory.hom_ext
  intro s
  change component (J.comap f) U.1 n
    ((relativePushforwardCoefficientLinearEquiv J f U)
      ((relativePushforwardCoefficientLinearEquiv J f U).symm
        (of (J.comap f) U.1 n s))) = s
  rw [LinearEquiv.apply_symm_apply, component_of]

end FLT.Mazur.IdealAdicGradedPullback
