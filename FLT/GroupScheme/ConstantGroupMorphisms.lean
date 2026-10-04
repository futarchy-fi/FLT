/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.ConstantGroupPoints
public import FLT.GroupScheme.EtaleGenericMorphismExtension

/-! # Integral morphisms of constant groups with their prescribed point maps -/

@[expose] public noncomputable section
namespace ThreeAdicPlan
variable (R K : Type) [CommRing R] [IsDomain R] [IsLocalRing R]
  [Field K] [Algebra R K] [PerfectField K] [IsFractionRing R K]
  {A B : Type} [AddCommGroup A] [Finite A] [AddCommGroup B] [Finite B]

/-- A constant group homomorphism on the actual generic points. -/
def constantGroupGenericHom (f : A →+ B) :
    GenericGaloisHom (constantGroupModel R K A) (constantGroupModel R K B) where
  toAddMonoidHom := (constantGroupPointEquiv R K B).toAddMonoidHom.comp
    (f.comp (constantGroupPointEquiv R K A).symm.toAddMonoidHom)
  map_smul' g x := by simp only [constantGroupModel_smul]

/-- The generic map has the specified value on every original group element. -/
@[simp] theorem constantGroupGenericHom_point (f : A →+ B) (a : A) :
    constantGroupGenericHom R K f (constantGroupPointEquiv R K A a) =
      constantGroupPointEquiv R K B (f a) := by
  change constantGroupPointEquiv R K B (f ((constantGroupPointEquiv R K A).symm
    (constantGroupPointEquiv R K A a))) = _
  rw [AddEquiv.symm_apply_apply]

/-- Extend the prescribed constant map over the integral base using etaleness. -/
def constantGroupHom [IsIntegrallyClosed R] (f : A →+ B) :
    ModelHom (constantGroupModel R K A) (constantGroupModel R K B) := by
  let : Algebra.Etale R (constantGroupModel R K A).CoordinateRing :=
    Algebra.Etale.of_equiv (constantGroupCoordinates R K A).symm
  exact (extend_generic_morphism_of_etale_perfectField _ _
    (constantGroupGenericHom R K f)).exists.choose

/-- The integral extension retains exactly the prescribed generic map. -/
@[simp] theorem genericHom_constantGroupHom [IsIntegrallyClosed R] (f : A →+ B) :
    genericHom (constantGroupHom R K f) = constantGroupGenericHom R K f := by
  let : Algebra.Etale R (constantGroupModel R K A).CoordinateRing :=
    Algebra.Etale.of_equiv (constantGroupCoordinates R K A).symm
  exact (extend_generic_morphism_of_etale_perfectField _ _
    (constantGroupGenericHom R K f)).exists.choose_spec

/-- Injective constant maps remain injective on geometric points. -/
theorem constantGroupGenericHom_injective (f : A →+ B) (hf : Function.Injective f) :
    Function.Injective (constantGroupGenericHom R K f) :=
  (constantGroupPointEquiv R K B).injective.comp
    (hf.comp (constantGroupPointEquiv R K A).symm.injective)

/-- Surjective constant maps remain surjective on geometric points. -/
theorem constantGroupGenericHom_surjective (f : A →+ B) (hf : Function.Surjective f) :
    Function.Surjective (constantGroupGenericHom R K f) :=
  (constantGroupPointEquiv R K B).surjective.comp
    (hf.comp (constantGroupPointEquiv R K A).symm.surjective)

end ThreeAdicPlan
