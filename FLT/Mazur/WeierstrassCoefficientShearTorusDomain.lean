/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassCoefficientShearAction
public import FLT.Mazur.WeierstrassRootShearSmoothParameter

/-!
# The actual root-split torus action domain on the sheared model

The torus is compared with the full original smooth parameter through the
proper cubic shear. This gives an isomorphism of complete action domains,
retaining both original inputs and the independently constructed action.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassIntegralChart
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type} [CommRing R] [IsDomain R] [IsBezout R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (S : Type) [CommRing S] [Algebra R S] (r : S) (j : ℕ) (hj : j ≤ n)
local notation "V" => W.map (algebraMap R S)
local notation "f" => integralSmoothStructure V
local notation "g" => coefficientShearGluedStructure hπ data S r j hj
local notation "q" => Spec.map (CommRingCat.ofHom (algebraMap R S))
local notation "base" => finiteGlobalStructure hπ data j hj
local notation "p" => pullback.fst q base
local notation "E" => coefficientShearGluedIso hπ data S r j hj

variable (a : Sˣ) (ha : (a : S) = (W.map (algebraMap R S)).a₁ + 2 * r)
  (hr : r ^ 2 + (W.map (algebraMap R S)).a₁ * r - (W.map (algebraMap R S)).a₂ = 0)
  (h3 : (W.map (algebraMap R S)).a₃ = 0)
  (h4 : (W.map (algebraMap R S)).a₄ = 0)
  (h6 : (W.map (algebraMap R S)).a₆ = 0)
local notation "I" => rootShearTorusSmoothIso V r a ha hr h3 h4 h6
local notation "t" => Over.hom (MultiplicativeGroupScheme.gm S)

/-- The actual torus parameter maps to the original smooth input, with the model fixed. -/
def coefficientShearTorusDomainMap : pullback t g ⟶
    coefficientShearActionDomain hπ data S r j hj :=
  pullback.lift (pullback.fst t g ≫ (I).hom) (pullback.snd t g)
    (by rw [Category.assoc, rootShearTorusSmoothIso_structure, pullback.condition])

/-- The first projection is the original smooth parameter through the actual cubic shear. -/
@[reassoc] theorem coefficientShearTorusDomainMap_parameter :
    coefficientShearTorusDomainMap hπ data S r j hj a ha hr h3 h4 h6 ≫ pullback.fst f g =
      pullback.fst t g ≫ (I).hom := pullback.lift_fst _ _ _

/-- The complete model input is unchanged by the torus comparison. -/
@[reassoc] theorem coefficientShearTorusDomainMap_model :
    coefficientShearTorusDomainMap hπ data S r j hj a ha hr h3 h4 h6 ≫ pullback.snd f g =
      pullback.snd t g := pullback.lift_snd _ _ _

/-- The full original smooth domain maps back through the inverse actual parameter comparison. -/
def coefficientShearTorusDomainInv : coefficientShearActionDomain hπ data S r j hj ⟶
    pullback t g :=
  pullback.lift (pullback.fst f g ≫ (I).inv) (pullback.snd f g) (by
    rw [Category.assoc, ← rootShearTorusSmoothIso_structure V r a ha hr h3 h4 h6,
      Iso.inv_hom_id_assoc, pullback.condition])

/-- The torus product is the whole independently constructed smooth action domain. -/
def coefficientShearTorusDomainIso : pullback t g ≅
    coefficientShearActionDomain hπ data S r j hj where
  hom := coefficientShearTorusDomainMap hπ data S r j hj a ha hr h3 h4 h6
  inv := coefficientShearTorusDomainInv hπ data S r j hj a ha hr h3 h4 h6
  hom_inv_id := by
    apply pullback.hom_ext
    · simp only [Category.assoc, coefficientShearTorusDomainInv, pullback.lift_fst,
        coefficientShearTorusDomainMap_parameter_assoc, Iso.hom_inv_id,
        Category.comp_id, Category.id_comp]
    · simp only [Category.assoc, coefficientShearTorusDomainInv, pullback.lift_snd,
        coefficientShearTorusDomainMap_model, Category.id_comp]
  inv_hom_id := by
    apply pullback.hom_ext
    · simp only [Category.assoc, coefficientShearTorusDomainMap_parameter,
        coefficientShearTorusDomainInv, pullback.lift_fst_assoc,
        Iso.inv_hom_id, Category.comp_id, Category.id_comp]
    · simp only [Category.assoc, coefficientShearTorusDomainMap_model,
        coefficientShearTorusDomainInv, pullback.lift_snd, Category.id_comp]

/-- The existing original action written on its actual full torus parameter domain. -/
def coefficientShearTorusAction : pullback t g ⟶ coefficientShearGlued hπ data S r j hj :=
  (coefficientShearTorusDomainIso hπ data S r j hj a ha hr h3 h4 h6).hom ≫
    coefficientShearAction hπ data S r j hj

/-- The original action output agrees on the complete tensor reconstruction. -/
@[reassoc] theorem coefficientShearTorusAction_reconstruction :
    coefficientShearTorusAction hπ data S r j hj a ha hr h3 h4 h6 ≫ (E).hom =
      (coefficientShearTorusDomainIso hπ data S r j hj a ha hr h3 h4 h6).hom ≫
        coefficientShearActionDomainMap hπ data S r j hj ≫
          finiteGlobalCoefficientAction hπ data j hj S := by
  rw [coefficientShearTorusAction, Category.assoc, coefficientShearAction_reconstruction]

/-- The full torus parameter remains the original smooth input after forgetting coefficients. -/
@[reassoc] theorem coefficientShearTorusDomain_originalParameter :
    (coefficientShearTorusDomainIso hπ data S r j hj a ha hr h3 h4 h6).hom ≫
        coefficientShearOriginalActionProduct hπ data S r j hj ≫
          pullback.fst (integralSmoothStructure W) base =
      pullback.fst t g ≫ (I).hom ≫ originalSmoothCoefficientMap S W := by
  rw [coefficientShearOriginalActionProduct_parameter]
  exact coefficientShearTorusDomainMap_parameter_assoc
    hπ data S r j hj a ha hr h3 h4 h6 _

end FLT.Mazur.WeierstrassDividedDepth
