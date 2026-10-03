/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.LaurentTensor
public import FLT.Mazur.ProjectiveActionFieldExtension
public import FLT.Mazur.ProjectiveLineActionPoints

/-!
# Multiplicative-group coordinates after field extension

The Laurent tensor equivalence identifies the actual pullback with the
multiplicative group over the new field. Its projections retain coefficient
change, including arbitrary units of the extension field.
-/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped LaurentPolynomial TensorProduct
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
namespace FLT.Mazur.MultiplicativeGroupFieldExtension
open ProjectiveLineProductCharts ProjectiveActionFieldExtension
variable (K L : Type u) [Field K] [Field L] [Algebra K L]

/-- Laurent tensor coordinates on the actual pullback of the multiplicative group. -/
def schemeIso : (MultiplicativeGroupScheme.gm L).left ≅
    pullback (parameterToBase K L) (MultiplicativeGroupScheme.gm K).hom :=
  Scheme.Spec.mapIso (LaurentTensor.equivalence K L).toRingEquiv.toCommRingCatIso.op ≪≫
    (pullbackSpecIso K L K[T;T⁻¹]).symm

@[reassoc (attr := simp)] theorem schemeIso_fst :
    (schemeIso K L).hom ≫ pullback.fst _ _ = (MultiplicativeGroupScheme.gm L).hom := by
  simp only [schemeIso, Iso.trans_hom, Iso.symm_hom, Category.assoc]
  erw [pullbackSpecIso_inv_fst']
  change Spec.map (CommRingCat.ofHom (LaurentTensor.equivalence K L).toRingHom) ≫
    Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeft : L →ₐ[K] L ⊗[K] K[T;T⁻¹]).toRingHom) = _
  rw [← Spec.map_comp]
  apply congrArg Spec.map
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro r
  exact LaurentTensor.equivalence_left K L r

@[reassoc (attr := simp)] theorem schemeIso_snd :
    (schemeIso K L).hom ≫ pullback.snd _ _ = gmCoeff K L := by
  simp only [schemeIso, Iso.trans_hom, Iso.symm_hom, Category.assoc]
  erw [pullbackSpecIso_inv_snd]
  change Spec.map (CommRingCat.ofHom (LaurentTensor.equivalence K L).toRingHom) ≫
    Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight : K[T;T⁻¹] →ₐ[K] L ⊗[K] K[T;T⁻¹]).toRingHom) = _
  rw [← Spec.map_comp]
  apply congrArg Spec.map
  apply CommRingCat.hom_ext
  apply RingHom.ext
  exact LaurentTensor.equivalence_right K L

/-- The actual pulled-back multiplicative group in extension-field coordinates. -/
def equivalence : MultiplicativeGroupScheme.gm L ≅
    (Over.pullback (parameterToBase K L)).obj (MultiplicativeGroupScheme.gm K) :=
  Over.isoMk (schemeIso K L ≪≫ pullbackSymmetry _ _) (by
    change (schemeIso K L).hom ≫ (pullbackSymmetry _ _).hom ≫ pullback.snd _ _ = _
    rw [pullbackSymmetry_hom_comp_snd]
    exact schemeIso_fst K L)

@[reassoc (attr := simp)] theorem hom_fst :
    (equivalence K L).hom.left ≫
      pullback.fst (MultiplicativeGroupScheme.gm K).hom (parameterToBase K L) = gmCoeff K L := by
  change (schemeIso K L).hom ≫ (pullbackSymmetry _ _).hom ≫ _ = _
  rw [pullbackSymmetry_hom_comp_fst]
  exact schemeIso_snd K L

@[reassoc] theorem unitPoint_coeff (a : Lˣ) :
    ProjectiveLineActionSpecialization.unitPoint L a ≫ gmCoeff K L =
      ProjectiveLineActionPoints.groupPoint K L a := by
  change Spec.map _ ≫ Spec.map _ = Spec.map _
  rw [← Spec.map_comp]
  apply congrArg Spec.map
  apply CommRingCat.hom_ext
  apply PolygonScalingNaturality.ringHom_ext
  · intro r
    simp [LaurentUnitPoints.evalUnit]
  · simp [LaurentUnitPoints.evalUnit]
  · simp [LaurentUnitPoints.evalUnit]
end FLT.Mazur.MultiplicativeGroupFieldExtension
