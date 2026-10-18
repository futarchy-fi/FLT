/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FiniteGroupFreeTensorInvariants
public import FLT.Mazur.SchemeQuotientAffineBaseCoordinates
public import FLT.Mazur.SchemeFiniteGroupFreeBoundary

/-!
# Free quotient comparison over every affine coefficient scheme

The quotient of the original tensor chart is the entire new affine base.
Freeness replaces the earlier flatness condition on the coefficient map;
arbitrary original primes and nilpotents are preserved.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TensorProduct
open FLT.Mazur.SchemeCoordinateAction FLT.Mazur.FiniteGroupQuotient
namespace FLT.Mazur.SchemeQuotientAffineBase
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {G : Type u} [Group G] [Finite G] {X S : Scheme.{u}} [IsAffine X] [IsAffine S]
  (ρ : G →* Aut X) (f : S ⟶ SchemeFiniteGroupQuotient.quotient ρ)
  (hfree : ∀ (K : Type u) [Field K] (a : Spec (.of K) ⟶ X) (g : G),
    a ≫ (ρ g).hom = a → g = 1)
attribute [local instance] tensorAction

/-- The tensor chart quotient is the full original affine coefficient scheme. -/
def freeQuotientIso :
    let _ := coordinateAlgebra ρ f
    let _ := coordinateAction ρ
    affineQuotient G (Γ(S, ⊤) ⊗[SchemeFiniteGroupQuotient.invariantCoordinates ρ] Γ(X, ⊤)) ≅
      S := by
  let _ := coordinateAlgebra ρ f
  let _ := coordinateAction ρ
  exact Scheme.Spec.mapIso (freeTensorInvariantEquiv G Γ(X, ⊤) Γ(S, ⊤)
    (SchemeFiniteGroupQuotient.coordinate_fixedPointIdeal_eq_top ρ hfree)).toCommRingCatIso.op ≪≫
      S.isoSpec.symm

/-- The quotient comparison keeps the actual original coefficient projection. -/
@[reassoc]
theorem quotientMap_freeQuotientIso_hom :
    let _ := coordinateAlgebra ρ f
    let _ := coordinateAction ρ
    quotientMap G (Γ(S, ⊤) ⊗[SchemeFiniteGroupQuotient.invariantCoordinates ρ] Γ(X, ⊤)) ≫
      (freeQuotientIso ρ f hfree).hom = toBase ρ f := by
  let _ := coordinateAlgebra ρ f
  let _ := coordinateAction ρ
  change Spec.map (CommRingCat.ofHom (inclusion G _)) ≫
    (Spec.map (CommRingCat.ofHom (tensorInvariantMap G Γ(X, ⊤) Γ(S, ⊤))) ≫ S.isoSpec.inv) = _
  rw [← Category.assoc, ← Spec.map_comp]
  rfl

/-- The actual arbitrary coefficient quotient square is cartesian as a square of schemes. -/
theorem freeQuotient_isPullback :
    let _ := coordinateAlgebra ρ f
    let _ := coordinateAction ρ
    IsPullback (toSource ρ f)
      (quotientMap G (Γ(S, ⊤) ⊗[SchemeFiniteGroupQuotient.invariantCoordinates ρ] Γ(X, ⊤)) ≫
        (freeQuotientIso ρ f hfree).hom) (SchemeFiniteGroupQuotient.quotientMap ρ) f := by
  let _ := coordinateAlgebra ρ f
  let _ := coordinateAction ρ
  dsimp only
  rw [quotientMap_freeQuotientIso_hom]
  exact isPullback ρ f

end FLT.Mazur.SchemeQuotientAffineBase
