/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassCoefficientShearGluing
public import FLT.Mazur.WeierstrassDividedGlobalCoefficientCartesian

/-!
# The original smooth action domain on the full sheared equation gluing

The parameter is the independently constructed smooth locus of the original
coefficient curve. Both projections of its product with the sheared gluing
are preserved by the comparison with the existing coefficient action domain.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassIntegralChart
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] [IsDomain R] [IsBezout R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (S : Type u) [CommRing S] [Algebra R S] (r : S) (j : ℕ) (hj : j ≤ n)
local notation "V" => W.map (algebraMap R S)
local notation "f" => integralSmoothStructure V
local notation "g" => coefficientShearGluedStructure hπ data S r j hj
local notation "q" => Spec.map (CommRingCat.ofHom (algebraMap R S))
local notation "base" => finiteGlobalStructure hπ data j hj
local notation "p" => pullback.fst q base
local notation "E" => coefficientShearGluedIso hπ data S r j hj

/-- The actual smooth parameter and full sheared model form the original two-input domain. -/
def coefficientShearActionDomain : Scheme := pullback f g

/-- Reconstruction on the domain leaves the smooth parameter unchanged. -/
def coefficientShearActionDomainMap :
    coefficientShearActionDomain hπ data S r j hj ⟶ pullback f p :=
  pullback.lift (pullback.fst f g) (pullback.snd f g ≫ (E).hom)
    (by simpa only [Category.assoc, coefficientShearGluedStructure] using
      (show pullback.fst f g ≫ f = pullback.snd f g ≫ g from pullback.condition))

/-- The domain comparison retains the entire independently constructed smooth parameter. -/
@[reassoc] theorem coefficientShearActionDomainMap_parameter :
    coefficientShearActionDomainMap hπ data S r j hj ≫ pullback.fst f p =
      pullback.fst f g := pullback.lift_fst _ _ _

/-- Its second projection is exactly the full tensor reconstruction of the model input. -/
@[reassoc] theorem coefficientShearActionDomainMap_model :
    coefficientShearActionDomainMap hπ data S r j hj ≫ pullback.snd f p =
      pullback.snd f g ≫ (E).hom := pullback.lift_snd _ _ _

/-- The inverse domain map uses the actual inverse gluing comparison. -/
def coefficientShearActionDomainInv :
    pullback f p ⟶ coefficientShearActionDomain hπ data S r j hj :=
  pullback.lift (pullback.fst f p) (pullback.snd f p ≫ (E).inv)
    (by simp only [Category.assoc, coefficientShearGluedStructure, Iso.inv_hom_id_assoc,
      pullback.condition])

/-- The two complete action domains agree, including all nilpotent and coefficient data. -/
def coefficientShearActionDomainIso :
    coefficientShearActionDomain hπ data S r j hj ≅ pullback f p where
  hom := coefficientShearActionDomainMap hπ data S r j hj
  inv := coefficientShearActionDomainInv hπ data S r j hj
  hom_inv_id := by
    apply pullback.hom_ext
    · simp only [coefficientShearActionDomainInv, Category.assoc, pullback.lift_fst,
        coefficientShearActionDomainMap_parameter, Category.id_comp]
    · simp only [coefficientShearActionDomainInv, Category.assoc, pullback.lift_snd,
        coefficientShearActionDomainMap_model_assoc, Iso.hom_inv_id, Category.comp_id,
        Category.id_comp]
  inv_hom_id := by
    apply pullback.hom_ext
    · simp only [Category.assoc, coefficientShearActionDomainMap_parameter,
        coefficientShearActionDomainInv, pullback.lift_fst, Category.id_comp]
    · simp only [Category.assoc, coefficientShearActionDomainMap_model,
        coefficientShearActionDomainInv, pullback.lift_snd_assoc,
        Iso.inv_hom_id, Category.comp_id, Category.id_comp]

/-- The domain comparison is cartesian over its full original model input. -/
theorem coefficientShearActionDomain_isPullback :
    IsPullback (coefficientShearActionDomainMap hπ data S r j hj)
      (pullback.snd f g) (pullback.snd f p) (E).hom := by
  let _ : IsIso (coefficientShearActionDomainMap hπ data S r j hj) :=
    (coefficientShearActionDomainIso hπ data S r j hj).isIso_hom
  exact IsPullback.of_horiz_isIso ⟨coefficientShearActionDomainMap_model hπ data S r j hj⟩

/-- Forgetting coefficients on the sheared domain retains both original integral inputs. -/
def coefficientShearOriginalActionProduct :
    coefficientShearActionDomain hπ data S r j hj ⟶ finiteGlobalActionProduct hπ data j hj :=
  coefficientShearActionDomainMap hπ data S r j hj ≫
    finiteGlobalCoefficientActionProduct hπ data j hj S

/-- The original smooth parameter projection is unchanged by the entire reconstruction. -/
@[reassoc] theorem coefficientShearOriginalActionProduct_parameter :
    coefficientShearOriginalActionProduct hπ data S r j hj ≫
        pullback.fst (integralSmoothStructure W) base =
      pullback.fst f g ≫ originalSmoothCoefficientMap S W := by
  rw [coefficientShearOriginalActionProduct, Category.assoc,
    finiteGlobalCoefficientActionProduct_fst, coefficientShearActionDomainMap_parameter_assoc]

/-- The original model projection is unchanged by the entire reconstruction. -/
@[reassoc] theorem coefficientShearOriginalActionProduct_model :
    coefficientShearOriginalActionProduct hπ data S r j hj ≫
        pullback.snd (integralSmoothStructure W) base =
      pullback.snd f g ≫ coefficientShearGluedProjection hπ data S r j hj := by
  rw [coefficientShearOriginalActionProduct, Category.assoc,
    finiteGlobalCoefficientActionProduct_snd, coefficientShearActionDomainMap_model_assoc]
  rfl

/-- The full domain is the original integral action domain pulled back along the model map. -/
theorem coefficientShearOriginalActionProduct_isPullback :
    IsPullback (coefficientShearOriginalActionProduct hπ data S r j hj)
      (pullback.snd f g) (pullback.snd (integralSmoothStructure W) base)
      (coefficientShearGluedProjection hπ data S r j hj) :=
  (coefficientShearActionDomain_isPullback hπ data S r j hj).paste_horiz
    (finiteGlobalCoefficientActionProduct_isPullback hπ data j hj S)

end FLT.Mazur.WeierstrassDividedDepth
