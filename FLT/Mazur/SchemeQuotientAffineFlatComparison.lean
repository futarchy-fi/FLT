/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeQuotientAffineBaseCoordinates

/-!
# Flat quotient comparisons over actual affine bases

The constructed tensor model of an actual affine base morphism is equivariant
for the genuine pullback action. Under flatness, its actual invariant-spectrum
quotient is the new affine base, with the quotient morphism identified with
the base projection. The group order need not be invertible.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory Limits AlgebraicGeometry TensorProduct
open FLT.Mazur.SchemeCoordinateAction FLT.Mazur.FiniteGroupQuotient

namespace FLT.Mazur.SchemeQuotientAffineBase

universe u
variable {G : Type u} [Group G] {X S : Scheme.{u}} [IsAffine X] [IsAffine S]
variable (ρ : G →* Aut X) (f : S ⟶ SchemeFiniteGroupQuotient.quotient ρ)

attribute [local instance] tensorAction

/-- The affine tensor model intertwines the actual pullback action, with coordinate inverse. -/
@[reassoc]
lemma iso_equivariant (g : G) :
    let _ := coordinateAlgebra ρ f
    let _ := coordinateAction ρ
    actionMap G (Γ(S, ⊤) ⊗[SchemeFiniteGroupQuotient.invariantCoordinates ρ] Γ(X, ⊤)) g ≫
      (iso ρ f).hom = (iso ρ f).hom ≫
        (FiniteGroupPullback.action ρ _ (SchemeFiniteGroupQuotient.quotientMap_invariant ρ)
          f g⁻¹).hom := by
  let _ := coordinateAlgebra ρ f
  let _ := coordinateAction ρ
  apply FiniteGroupPullback.isoPullback_equivariant _ _ _ _ (isPullback ρ f)
  · exact SchemeQuotientTensor.toSource_equivariant ρ Γ(S, ⊤) g
  · change _ ≫ (SchemeQuotientTensor.toBase ρ Γ(S, ⊤) ≫ S.isoSpec.inv) = _
    rw [SchemeQuotientTensor.toBase_invariant_assoc]
    rfl

variable [Finite G] [Flat f]

/-- The quotient of the tensor model is isomorphic to the actual affine new base. -/
def quotientIso :
    let _ := coordinateAlgebra ρ f
    let _ := coordinateAction ρ
    affineQuotient G (Γ(S, ⊤) ⊗[SchemeFiniteGroupQuotient.invariantCoordinates ρ] Γ(X, ⊤)) ≅
      S := by
  let _ := coordinateAlgebra ρ f
  let _ := coordinateAction ρ
  let _ : Module.Flat (SchemeFiniteGroupQuotient.invariantCoordinates ρ) Γ(S, ⊤) :=
    coordinate_flat ρ f
  exact flatQuotientIso G Γ(X, ⊤) Γ(S, ⊤) ≪≫ S.isoSpec.symm

omit [IsAffine X] in
/-- The flat comparison identifies the quotient morphism with the actual base projection. -/
@[reassoc]
lemma quotientMap_quotientIso_hom :
    let _ := coordinateAlgebra ρ f
    let _ := coordinateAction ρ
    quotientMap G (Γ(S, ⊤) ⊗[SchemeFiniteGroupQuotient.invariantCoordinates ρ] Γ(X, ⊤)) ≫
      (quotientIso ρ f).hom = toBase ρ f := by
  let _ := coordinateAlgebra ρ f
  let _ := coordinateAction ρ
  let _ : Module.Flat (SchemeFiniteGroupQuotient.invariantCoordinates ρ) Γ(S, ⊤) :=
    coordinate_flat ρ f
  change _ ≫ ((flatQuotientIso G Γ(X, ⊤) Γ(S, ⊤)).hom ≫ S.isoSpec.inv) = _
  rw [quotientMap_flatQuotientIso_hom_assoc]
  rfl

/-- The actual affine-base flat quotient comparison retains the entire cartesian square. -/
theorem quotient_isPullback :
    let _ := coordinateAlgebra ρ f
    let _ := coordinateAction ρ
    IsPullback (toSource ρ f)
      (quotientMap G (Γ(S, ⊤) ⊗[SchemeFiniteGroupQuotient.invariantCoordinates ρ] Γ(X, ⊤)) ≫
        (quotientIso ρ f).hom) (SchemeFiniteGroupQuotient.quotientMap ρ) f := by
  let _ := coordinateAlgebra ρ f
  let _ := coordinateAction ρ
  dsimp only
  rw [quotientMap_quotientIso_hom]
  exact isPullback ρ f

end FLT.Mazur.SchemeQuotientAffineBase
