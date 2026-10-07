/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassInfinityIdentityChart
public import FLT.Mazur.WeierstrassInfinityAdditionScheme

/-!
# Concrete open neighborhoods of the two Y-chart identity sections

Pull the two infinity-domain localizations back along either zero section.
The resulting spectrum is open in the Y chart and maps to the original
infinity addition domain. Its normalized addition map is its original input.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

namespace FLT.Mazur.WeierstrassIntegralChart

variable {R : Type*} [CommRing R] (W : WeierstrassCurve R)

/-- Choose which factor of the Y-chart product is the zero section. -/
def infinityIdentityInput (b : Bool) : ChartProduct W 1 1 →ₐ[R] Coordinate W 1 :=
  if b then chartProductAtLeftInfinity W 1 else chartProductAtRightInfinity W 1

/-- The pulled-back denominator of the regular divided difference. -/
def infinityIdentityDen (b : Bool) : Coordinate W 1 :=
  infinityIdentityInput W b (infinityDen W (AlgHom.id R _))

/-- Pull the slope domain back to the chosen identity section. -/
abbrev InfinityIdentitySlopeOpen (b : Bool) := Localization.Away (infinityIdentityDen W b)

/-- The first localization map from the Y chart. -/
def infinityIdentitySlopeRestriction (b : Bool) :
    Coordinate W 1 →ₐ[R] InfinityIdentitySlopeOpen W b :=
  IsScalarTower.toAlgHom R (Coordinate W 1) (InfinityIdentitySlopeOpen W b)

/-- The pulled-back slope domain maps to the original two-input slope domain. -/
def infinityIdentitySlopeMap (b : Bool) :
    InfinitySlopeOpen W →ₐ[R] InfinityIdentitySlopeOpen W b :=
  IsLocalization.Away.liftAlgHom (infinityDen W (AlgHom.id R _))
    (show IsUnit (((infinityIdentitySlopeRestriction W b).comp
      (infinityIdentityInput W b)) (infinityDen W (AlgHom.id R _))) from
      IsLocalization.Away.algebraMap_isUnit (infinityIdentityDen W b))

/-- Both slope-domain maps retain the original input pair. -/
theorem infinityIdentitySlopeMap_inputs (b : Bool) :
    (infinityIdentitySlopeMap W b).comp (infinitySlopeRestriction W) =
      (infinityIdentitySlopeRestriction W b).comp (infinityIdentityInput W b) := by
  apply AlgHom.ext
  intro a
  change infinityIdentitySlopeMap W b (algebraMap _ _ a) = _
  simp only [infinityIdentitySlopeMap, IsLocalization.Away.liftAlgHom_apply,
    IsLocalization.Away.lift_eq, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom]

/-- The pulled-back homogeneous output Y coordinate. -/
def infinityIdentityOutputY (b : Bool) : InfinityIdentitySlopeOpen W b :=
  infinityIdentitySlopeMap W b (infinityOutputCoordinates W 1)

/-- The full identity neighborhood, including normalized output. -/
abbrev InfinityIdentityOpen (b : Bool) := Localization.Away (infinityIdentityOutputY W b)

/-- The second localization, retaining the output normalization. -/
def infinityIdentityOutputRestriction (b : Bool) :
    InfinityIdentitySlopeOpen W b →ₐ[R] InfinityIdentityOpen W b :=
  IsScalarTower.toAlgHom R (InfinityIdentitySlopeOpen W b) (InfinityIdentityOpen W b)

/-- Restrict the original Y chart to the full identity neighborhood. -/
def infinityIdentityRestriction (b : Bool) :
    Coordinate W 1 →ₐ[R] InfinityIdentityOpen W b :=
  (infinityIdentityOutputRestriction W b).comp (infinityIdentitySlopeRestriction W b)

/-- The identity neighborhood maps into the existing infinity addition domain. -/
def infinityIdentityMap (b : Bool) : InfinityAdditionOpen W →ₐ[R] InfinityIdentityOpen W b :=
  IsLocalization.Away.liftAlgHom (infinityOutputCoordinates W 1)
    (show IsUnit (((infinityIdentityOutputRestriction W b).comp
      (infinityIdentitySlopeMap W b)) (infinityOutputCoordinates W 1)) from
      IsLocalization.Away.algebraMap_isUnit (infinityIdentityOutputY W b))

/-- The final map retains the chosen slope-domain map. -/
theorem infinityIdentityMap_output (b : Bool) :
    (infinityIdentityMap W b).comp (infinityOutputRestriction W) =
      (infinityIdentityOutputRestriction W b).comp (infinityIdentitySlopeMap W b) := by
  apply AlgHom.ext
  intro a
  change infinityIdentityMap W b (algebraMap _ _ a) = _
  simp only [infinityIdentityMap, IsLocalization.Away.liftAlgHom_apply,
    IsLocalization.Away.lift_eq, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom]

/-- The full domain square commutes as algebra homomorphisms. -/
theorem infinityIdentityMap_inputs (b : Bool) :
    (infinityIdentityMap W b).comp (infinityAdditionRestriction W) =
      (infinityIdentityRestriction W b).comp (infinityIdentityInput W b) := by
  rw [infinityAdditionRestriction, ← AlgHom.comp_assoc, infinityIdentityMap_output,
    AlgHom.comp_assoc, infinityIdentitySlopeMap_inputs, ← AlgHom.comp_assoc]
  rfl

/-- On this entire neighborhood, normalized addition returns the original input. -/
theorem infinityIdentityMap_addition (b : Bool) :
    (infinityIdentityMap W b).comp (infinityAdditionChart W) =
      infinityIdentityRestriction W b := by
  cases b
  · exact infinityAdditionChart_right_identity W _ _ (infinityIdentityMap_inputs W false)
  · exact infinityAdditionChart_left_identity W _ _ (infinityIdentityMap_inputs W true)

/-- Inclusion of the concrete identity neighborhood in the Y chart. -/
def infinityIdentityInclusion (b : Bool) :
    Spec (.of (InfinityIdentityOpen W b)) ⟶ Spec (.of (Coordinate W 1)) :=
  Spec.map (CommRingCat.ofHom (infinityIdentityRestriction W b).toRingHom)

/-- Both localizations are actual open immersions, as is their composite. -/
instance infinityIdentityInclusion_isOpenImmersion (b : Bool) :
    IsOpenImmersion (infinityIdentityInclusion W b) := by
  change IsOpenImmersion (Spec.map (CommRingCat.ofHom
    ((infinityIdentityOutputRestriction W b).toRingHom.comp
      (infinityIdentitySlopeRestriction W b).toRingHom)))
  rw [CommRingCat.ofHom_comp, Spec.map_comp]
  have : IsOpenImmersion (Spec.map
      (CommRingCat.ofHom (infinityIdentitySlopeRestriction W b).toRingHom)) :=
    IsOpenImmersion.of_isLocalization (infinityIdentityDen W b)
  have : IsOpenImmersion (Spec.map
      (CommRingCat.ofHom (infinityIdentityOutputRestriction W b).toRingHom)) :=
    IsOpenImmersion.of_isLocalization (infinityIdentityOutputY W b)
  infer_instance

/-- The neighborhood maps to the original addition domain with the prescribed inputs. -/
theorem infinityIdentitySpec_inputs (b : Bool) :
    Spec.map (CommRingCat.ofHom (infinityIdentityMap W b).toRingHom) ≫
        infinityAdditionInclusion W =
      infinityIdentityInclusion W b ≫
        Spec.map (CommRingCat.ofHom (infinityIdentityInput W b).toRingHom) := by
  change Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
  rw [← Spec.map_comp, ← Spec.map_comp]
  exact congrArg (fun f => Spec.map (CommRingCat.ofHom f.toRingHom))
    (infinityIdentityMap_inputs W b)

/-- Addition on the neighborhood is the original Y-chart inclusion as a scheme morphism. -/
theorem infinityIdentitySpec_addition (b : Bool) :
    Spec.map (CommRingCat.ofHom (infinityIdentityMap W b).toRingHom) ≫
      infinityAdditionSpec W = infinityIdentityInclusion W b := by
  change Spec.map _ ≫ Spec.map _ = Spec.map _
  rw [← Spec.map_comp]
  exact congrArg (fun f => Spec.map (CommRingCat.ofHom f.toRingHom))
    (infinityIdentityMap_addition W b)

end FLT.Mazur.WeierstrassIntegralChart
