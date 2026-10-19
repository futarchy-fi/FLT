/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CyclicCharacteristicInvariantLocalization
public import FLT.Mazur.CyclicCharacteristicInvariantAffineComparison

/-!
# Principal open subschemes of the invariant affine targets

The proved localization of actual invariant sections makes each principal
restriction an open immersion between the affine targets. Its image is exactly
the expected spectrum basic open. This does not assert that the orbit-to-affine
comparison is an isomorphism.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Opposite TopologicalSpace
namespace FLT.Mazur.CyclicCharacteristicOrbit
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable (n : ℕ) [NeZero n] (W : Opens (Orbit n))
  (s : (invariantSheaf n).obj.obj (op W))
local notation "D" => invariantPrincipal n W s

/-- The actual principal section ring is canonically the localized invariant section ring. -/
def invariantPrincipalSectionEquiv :
    let _ := (principalRestriction n W s).toAlgebra
    Localization.Away s ≃ₐ[((invariantSheaf n).obj.obj (op W))]
      ((invariantSheaf n).obj.obj (op D)) := by
  let _ := (principalRestriction n W s).toAlgebra
  let _ := principalRestriction_isLocalization n W s
  exact IsLocalization.algEquiv (.powers s) _ _

/-- This identification sends original coefficients to their actual sheaf restrictions. -/
theorem invariantPrincipalSectionEquiv_algebraMap (a : ((invariantSheaf n).obj.obj (op W))) :
    invariantPrincipalSectionEquiv n W s
      (algebraMap ((invariantSheaf n).obj.obj (op W)) (Localization.Away s) a) =
      principalRestriction n W s a := by
  let _ := (principalRestriction n W s).toAlgebra
  exact (invariantPrincipalSectionEquiv n W s).commutes a

/-- Principal restriction gives a scheme morphism between the constructed affine targets. -/
def invariantAffinePrincipalMap :
    invariantAffineTarget n D ⟶ invariantAffineTarget n W :=
  Spec.map (CommRingCat.ofHom (principalRestriction n W s))

/-- The actual target restriction is an open immersion, by invariant localization. -/
instance invariantAffinePrincipalMap_isOpenImmersion :
    IsOpenImmersion (invariantAffinePrincipalMap n W s) := by
  let _ := (principalRestriction n W s).toAlgebra
  let _ := principalRestriction_isLocalization n W s
  exact IsOpenImmersion.of_isLocalization s

/-- The spectrum basic open of the original invariant coefficient. -/
def invariantAffineBasicOpen : (invariantAffineTarget n W).Opens :=
  PrimeSpectrum.basicOpen s

/-- The image is exactly the basic open of the original invariant function. -/
theorem invariantAffinePrincipalMap_range :
    Set.range (invariantAffinePrincipalMap n W s) = (invariantAffineBasicOpen n W s : Set _) := by
  let _ := (principalRestriction n W s).toAlgebra
  let _ := principalRestriction_isLocalization n W s
  exact PrimeSpectrum.localization_away_comap_range ((invariantSheaf n).obj.obj (op D)) s

/-- The principal affine target is the corresponding actual open subscheme. -/
def invariantAffinePrincipalIso :
    invariantAffineTarget n D ≅ (invariantAffineBasicOpen n W s).toScheme :=
  IsOpenImmersion.isoOfRangeEq (invariantAffinePrincipalMap n W s)
    (invariantAffineBasicOpen n W s).ι (by
      rw [invariantAffinePrincipalMap_range, Scheme.Opens.range_ι])

/-- The open-subscheme identification retains the original invariant restriction morphism. -/
@[reassoc] theorem invariantAffinePrincipalIso_inclusion :
    (invariantAffinePrincipalIso n W s).hom ≫
      (invariantAffineBasicOpen n W s).ι =
        invariantAffinePrincipalMap n W s :=
  IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _

end FLT.Mazur.CyclicCharacteristicOrbit
