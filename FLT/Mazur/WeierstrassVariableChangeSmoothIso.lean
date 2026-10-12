/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassVariableChangeIntegralIso
public import FLT.Mazur.WeierstrassRelativeSmoothOpen

/-!
# Variable changes on the entire original relative smooth locus

The actual proper cubic isomorphism restricts to the full relative smooth
opens. No discriminant invertibility is assumed, so the comparison also
applies to the nodal residue equation after a tangent-root shear.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits WeierstrassCurve
namespace FLT.Mazur.WeierstrassIntegralChart
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type} [CommRing R] (W V : WeierstrassCurve R)
  (C : VariableChange R) (h : C • W = V)
local notation "E" => integralVariableChangeIso W V C h
local notation "U" => integralSmoothOpen W
local notation "T" => integralSmoothOpen V

/-- The actual variable change has exactly the full original smooth locus as its preimage. -/
theorem integralVariableChange_preimage_smooth : (E).hom ⁻¹ᵁ U = T := by
  change (E).hom ⁻¹ᵁ (integralCurveStructure W).smoothLocus =
    (integralCurveStructure V).smoothLocus
  rw [Scheme.Hom.preimage_smoothLocus_eq]
  congr 1
  exact integralVariableChangeTo_structure W V C h

/-- Restriction of the original proper cubic isomorphism to the actual smooth parameter. -/
def integralVariableChangeSmoothMap : (T).toScheme ⟶ (U).toScheme :=
  IsOpenImmersion.lift (U).ι ((T).ι ≫ (E).hom) (by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨x, rfl⟩
    have hx : (T).ι x ∈ (E).hom ⁻¹ᵁ U := by
      rw [integralVariableChange_preimage_smooth]
      exact x.property
    exact hx)

/-- The smooth comparison retains every original cubic function. -/
@[reassoc] theorem integralVariableChangeSmoothMap_inclusion :
    integralVariableChangeSmoothMap W V C h ≫ (U).ι = (T).ι ≫ (E).hom :=
  IsOpenImmersion.lift_fac _ _ _

instance integralVariableChangeSmoothMap_isOpenImmersion :
    IsOpenImmersion (integralVariableChangeSmoothMap W V C h) :=
  inferInstanceAs (IsOpenImmersion (IsOpenImmersion.lift _ _ _))

/-- The full smooth restriction square is cartesian in the original proper cubics. -/
theorem integralVariableChangeSmoothMap_isPullback :
    IsPullback (integralVariableChangeSmoothMap W V C h) (T).ι (U).ι (E).hom := by
  apply IsOpenImmersion.isPullback
  · exact (integralVariableChangeSmoothMap_inclusion W V C h).symm
  · simpa only [Scheme.Opens.opensRange_ι] using
      integralVariableChange_preimage_smooth W V C h

instance integralVariableChangeSmoothMap_isIso :
    IsIso (integralVariableChangeSmoothMap W V C h) :=
  (integralVariableChangeSmoothMap_isPullback W V C h).isIso_fst_of_isIso

/-- Variable change identifies the whole original smooth schemes, including bad fibers. -/
def integralVariableChangeSmoothIso : (T).toScheme ≅ (U).toScheme :=
  asIso (integralVariableChangeSmoothMap W V C h)

/-- The full smooth comparison preserves the coefficient morphism. -/
@[reassoc] theorem integralVariableChangeSmoothMap_structure :
    integralVariableChangeSmoothMap W V C h ≫ integralSmoothStructure W =
      integralSmoothStructure V := by
  change integralVariableChangeSmoothMap W V C h ≫ (U).ι ≫ integralCurveStructure W = _
  rw [integralVariableChangeSmoothMap_inclusion_assoc]
  change (T).ι ≫ integralVariableChangeTo W V C h ≫ integralCurveStructure W = _
  rw [integralVariableChangeTo_structure]

/-- The geometric comparison is an isomorphism of the actual smooth schemes over the base. -/
def integralVariableChangeSmoothOverIso :
    Over.mk (integralSmoothStructure V) ≅ Over.mk (integralSmoothStructure W) :=
  Over.isoMk (integralVariableChangeSmoothIso W V C h)
    (integralVariableChangeSmoothMap_structure W V C h)

end FLT.Mazur.WeierstrassIntegralChart
