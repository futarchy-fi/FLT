/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.DiagonalizableProductAlgebra
public import FLT.Mazur.CharacterGroupBaseChange
public import FLT.Mazur.WeierstrassSmoothSurjectiveKernel

/-!
# The original character cofaces are the scheme group operations

The product-character spectrum is the actual categorical product. The two
cofaces are its projections and the diagonal coface is Hopf multiplication.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory

namespace FLT.Mazur.DiagonalizableCobar

open CharacterSchemeBaseChange WeierstrassIntegralChart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

attribute [local irreducible] productEquiv

universe u
variable (R G : Type u) [CommRing R] [AddCommMonoid G]

/-- The full product-character spectrum is the original scheme fiber product. -/
def productSchemeIso : (model R (G × G)).left ≅
    pullback (model R G).hom (model R G).hom :=
  Scheme.Spec.mapIso (productEquiv R G).toRingEquiv.toCommRingCatIso.op ≪≫
    (pullbackSpecIso R (AddMonoidAlgebra R G) (AddMonoidAlgebra R G)).symm

/-- The first projection is the specified original first character coface. -/
@[reassoc] theorem productSchemeIso_fst :
    (productSchemeIso R G).hom ≫ pullback.fst _ _ =
      Spec.map (CommRingCat.ofHom (firstMap R G).toRingHom) := by
  simp only [productSchemeIso, Iso.trans_hom, Iso.symm_hom, Category.assoc]
  erw [pullbackSpecIso_inv_fst']
  change Spec.map (CommRingCat.ofHom (productEquiv R G).toRingHom) ≫ Spec.map _ = _
  rw [← Spec.map_comp]
  exact congrArg (fun f : AddMonoidAlgebra R G →ₐ[R] AddMonoidAlgebra R (G × G) =>
    Spec.map (CommRingCat.ofHom f.toRingHom)) (productEquiv_includeLeft R G)

/-- The second projection is the specified original second character coface. -/
@[reassoc] theorem productSchemeIso_snd :
    (productSchemeIso R G).hom ≫ pullback.snd _ _ =
      Spec.map (CommRingCat.ofHom (secondMap R G).toRingHom) := by
  simp only [productSchemeIso, Iso.trans_hom, Iso.symm_hom, Category.assoc]
  erw [pullbackSpecIso_inv_snd]
  change Spec.map (CommRingCat.ofHom (productEquiv R G).toRingHom) ≫ Spec.map _ = _
  rw [← Spec.map_comp]
  exact congrArg (fun f : AddMonoidAlgebra R G →ₐ[R] AddMonoidAlgebra R (G × G) =>
    Spec.map (CommRingCat.ofHom f.toRingHom)) (productEquiv_includeRight R G)

/-- The same comparison is an isomorphism over the original coefficient base. -/
def productOverIso : model R (G × G) ≅ model R G ⊗ model R G :=
  Over.isoMk (productSchemeIso R G) (by
    change (productSchemeIso R G).hom ≫ pullback.fst _ _ ≫ (model R G).hom = _
    rw [productSchemeIso_fst_assoc]
    exact (smoothAlgebraTestMap (firstMap R G)).w)

/-- The first cartesian projection is exactly the original algebra test map. -/
@[reassoc] theorem productOverIso_fst :
    (productOverIso R G).hom ≫ CartesianMonoidalCategory.fst _ _ =
      smoothAlgebraTestMap (firstMap R G) := by
  apply Over.OverMorphism.ext
  exact productSchemeIso_fst R G

/-- The second cartesian projection is exactly the original algebra test map. -/
@[reassoc] theorem productOverIso_snd :
    (productOverIso R G).hom ≫ CartesianMonoidalCategory.snd _ _ =
      smoothAlgebraTestMap (secondMap R G) := by
  apply Over.OverMorphism.ext
  exact productSchemeIso_snd R G

/-- The diagonal coface is multiplication of the original character monoid scheme. -/
@[reassoc] theorem productOverIso_mul :
    (productOverIso R G).hom ≫ MonObj.mul (X := model R G) =
      smoothAlgebraTestMap (diagonalMap R G) := by
  apply Over.OverMorphism.ext
  rw [Over.comp_left]
  change (productSchemeIso R G).hom ≫
    (MonObj.mul (X := (Spec (.of (AddMonoidAlgebra R G))).asOver (Spec (.of R)))).left = _
  rw [mul_spec_asOver_spec_left]
  simp only [productSchemeIso, Iso.trans_hom, Iso.symm_hom, Category.assoc,
    Iso.inv_hom_id_assoc]
  change Spec.map (CommRingCat.ofHom (productEquiv R G).toRingHom) ≫ Spec.map _ = _
  rw [← Spec.map_comp]
  exact congrArg (fun f : AddMonoidAlgebra R G →ₐ[R] AddMonoidAlgebra R (G × G) =>
    Spec.map (CommRingCat.ofHom f.toRingHom)) (productEquiv_comul R G)

end FLT.Mazur.DiagonalizableCobar
