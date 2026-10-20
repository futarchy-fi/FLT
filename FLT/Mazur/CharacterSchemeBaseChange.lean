/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CharacterAlgebraScalarExtension
public import Mathlib.AlgebraicGeometry.Pullbacks

/-!
# Character coordinates on actual arithmetic scheme pullbacks

The scalar tensor equivalence identifies the spectrum over the extended ring
with the actual scheme pullback. Both projection formulas are retained explicitly.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped TensorProduct

namespace FLT.Mazur.CharacterSchemeBaseChange

open CharacterAlgebraScalarExtension

universe u
variable (R A M : Type u) [CommRing R] [CommRing A] [Algebra R A] [AddCommMonoid M]

/-- The original character spectrum over its coefficient base. -/
abbrev model : Over (Spec (.of R)) :=
  Over.mk (Spec.map (CommRingCat.ofHom (algebraMap R (AddMonoidAlgebra R M))))

/-- The specified map of coefficient spectra. -/
abbrev baseMap : Spec (.of A) ⟶ Spec (.of R) :=
  Spec.map (CommRingCat.ofHom (algebraMap R A))

/-- Changing character coefficients gives exactly the geometric scalar pullback. -/
def schemeIso : Spec (.of (AddMonoidAlgebra A M)) ≅
    pullback (baseMap R A) (model R M).hom :=
  Scheme.Spec.mapIso (equivalence R A M).toRingEquiv.toCommRingCatIso.op ≪≫
    (pullbackSpecIso R A (AddMonoidAlgebra R M)).symm

/-- The first projection is precisely the extended coefficient structure map. -/
@[reassoc] theorem schemeIso_fst :
    (schemeIso R A M).hom ≫ pullback.fst _ _ = (model A M).hom := by
  simp only [schemeIso, Iso.trans_hom, Iso.symm_hom, Category.assoc]
  erw [pullbackSpecIso_inv_fst']
  change Spec.map (CommRingCat.ofHom (equivalence R A M).toRingHom) ≫
    Spec.map (CommRingCat.ofHom
      (Algebra.TensorProduct.includeLeft :
        A →ₐ[R] A ⊗[R] AddMonoidAlgebra R M).toRingHom) = _
  rw [← Spec.map_comp]
  apply congrArg Spec.map
  apply CommRingCat.hom_ext
  apply RingHom.ext
  exact equivalence_left R A M

/-- The second projection is exactly the coefficient-change map on the original characters. -/
@[reassoc] theorem schemeIso_snd :
    (schemeIso R A M).hom ≫ pullback.snd _ _ =
      Spec.map (CommRingCat.ofHom (coeff R A M).toRingHom) := by
  simp only [schemeIso, Iso.trans_hom, Iso.symm_hom, Category.assoc]
  erw [pullbackSpecIso_inv_snd]
  change Spec.map (CommRingCat.ofHom (equivalence R A M).toRingHom) ≫
    Spec.map (CommRingCat.ofHom
      (Algebra.TensorProduct.includeRight :
        AddMonoidAlgebra R M →ₐ[R] A ⊗[R] AddMonoidAlgebra R M).toRingHom) = _
  rw [← Spec.map_comp]
  apply congrArg Spec.map
  apply CommRingCat.hom_ext
  apply RingHom.ext
  exact equivalence_right R A M

/-- The character scheme over the new ring is isomorphic to the actual categorical pullback. -/
def overIso : model A M ≅ (Over.pullback (baseMap R A)).obj (model R M) :=
  Over.isoMk (schemeIso R A M ≪≫ pullbackSymmetry _ _) (by
    change (schemeIso R A M).hom ≫ (pullbackSymmetry _ _).hom ≫ pullback.snd _ _ = _
    rw [pullbackSymmetry_hom_comp_snd]
    exact schemeIso_fst R A M)

/-- The over-scheme comparison retains the actual map back to the original character scheme. -/
@[reassoc] theorem overIso_fst :
    (overIso R A M).hom.left ≫ pullback.fst (model R M).hom (baseMap R A) =
      Spec.map (CommRingCat.ofHom (coeff R A M).toRingHom) := by
  change (schemeIso R A M).hom ≫ (pullbackSymmetry _ _).hom ≫ _ = _
  rw [pullbackSymmetry_hom_comp_fst]
  exact schemeIso_snd R A M

end FLT.Mazur.CharacterSchemeBaseChange
