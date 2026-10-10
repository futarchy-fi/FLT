/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedDepthBoundary
public import FLT.Mazur.WeierstrassSuccessiveXDepthTensorOverlap

/-!
# The integral depth transition in boundary coordinates

The parameter identification used to attach the actual divided boundary
agrees with the localization transport used before tensor base change.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassDividedDepth
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type*} [CommRing R] {W : WeierstrassCurve R} {π : R} {k : ℕ}
open WeierstrassSuccessiveX

/-- Parameter congruence agrees with transport of the actual principal localization. -/
theorem horizontalParameterEquiv_eq_transport (s t b3 b4 b6 : R) (h : s = t) :
    (WeierstrassDilatation.horizontalParameterEquiv W t s b3 b4 b6 b3 b4 b6
      h.symm rfl rfl rfl).symm =
      PrincipalOpenTransport.equiv
        (WeierstrassDilatation.parameterEquiv W s t b3 b4 b6 b3 b4 b6 h rfl rfl rfl)
        _ _ (WeierstrassDilatation.parameterEquiv_x W s t b3 b4 b6 b3 b4 b6
          h rfl rfl rfl) := by
  subst t
  apply AlgEquiv.coe_toAlgHom_injective
  apply IsLocalization.algHom_ext (Submonoid.powers (WeierstrassDilatation.x W s b3 b4 b6))
  apply AlgHom.ext
  intro z
  exact (PrincipalOpenTransport.equiv_base
    (WeierstrassDilatation.parameterEquiv W s s b3 b4 b6 b3 b4 b6 rfl rfl rfl rfl)
    _ _ rfl z).symm

/-- The inverse atlas boundary identification is the actual depth localization transport. -/
theorem nextBoundaryIso_inv (e : Data W π (k + 1)) :
    (nextBoundaryIso e).inv = Spec.map (CommRingCat.ofHom
      (depthDividedOpenEquiv W π k e.b3 e.b4 e.b6).toRingHom) := by
  change Spec.map (CommRingCat.ofHom
    (WeierstrassDilatation.horizontalParameterEquiv W (π ^ k * π) (π ^ (k + 1))
      e.b3 e.b4 e.b6 e.b3 e.b4 e.b6 (pow_succ π k).symm rfl rfl rfl).symm.toRingHom) = _
  rw [horizontalParameterEquiv_eq_transport]
  rfl

/-- The full integral transition converts the boundary attachment into the x-open inclusion. -/
@[reassoc] theorem depthOverlap_nextToX (e : Data W π (k + 1)) :
    Spec.map (CommRingCat.ofHom (depthOverlapEquiv W π k e.b3 e.b4 e.b6).toRingHom) ≫
      nextToX e = xOpenInclusion W (π ^ k) π e.b3 e.b4 e.b6 := by
  have h : Spec.map (CommRingCat.ofHom
      (depthOverlapEquiv W π k e.b3 e.b4 e.b6).toRingHom) =
        (overlapIso W (π ^ k) π e.b3 e.b4 e.b6).hom ≫ (nextBoundaryIso e).inv := by
    rw [nextBoundaryIso_inv]
    change Spec.map _ = Spec.map _ ≫ Spec.map _
    rw [← Spec.map_comp]
    rfl
  rw [h, nextToX]
  simp only [Category.assoc, Iso.inv_hom_id_assoc, Iso.hom_inv_id_assoc]

end FLT.Mazur.WeierstrassDividedDepth
