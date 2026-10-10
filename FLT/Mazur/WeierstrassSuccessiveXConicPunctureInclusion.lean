/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassSuccessiveXConicPunctureCompatibility

/-!
# Original punctures factor their full ordered conic parameter charts

The factorization is an equality of scheme maps, and the full ordered charts
are disjoint whenever the divided conic constant vanishes.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
namespace FLT.Mazur.WeierstrassSuccessiveX
open WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type*} [CommRing R] (W : WeierstrassCurve R) (c : R)
  (ha : IsUnit W.a₁) (hc : c = 0)
local notation "C₀" => ConicCoordinate W.a₁ c
local notation "i" => Spec.map (CommRingCat.ofHom (algebraMap C₀ (MiddleConicOpen W c)))
local notation "p" => Spec.map (CommRingCat.ofHom (AlgHom.toRingHom (conicZeroPuncture c hc)))
local notation "s₁" =>
  Spec.map (CommRingCat.ofHom (AlgHom.toRingHom (conicBoundaryFirst W c ha hc)))
local notation "s₂" =>
  Spec.map (CommRingCat.ofHom (AlgHom.toRingHom (conicBoundarySecond W c ha hc)))
local notation "P₁" =>
  Iso.inv (conicFirstParameterIso (WeierstrassCurve.a₁ W) c ha) ≫
    conicFirstOpenImmersion (WeierstrassCurve.a₁ W) c
local notation "P₂" =>
  Iso.inv (conicSecondParameterIso (WeierstrassCurve.a₁ W) c ha) ≫
    conicSecondOpenImmersion (WeierstrassCurve.a₁ W) c

/-- The first actual boundary puncture is the puncture of the entire first parameter chart. -/
@[reassoc] theorem conicBoundaryFirst_inclusion : s₁ ≫ i = p ≫ P₁ := by
  calc
    _ = Spec.map (CommRingCat.ofHom (conicPuncturedFirst W c hc).toRingHom) := by
      rw [← Spec.map_comp]
      congr 1
      apply CommRingCat.hom_ext
      exact RingHom.ext (conicBoundaryFirst_base W c ha hc)
    _ = _ := conicPuncturedFirst_spec c hc W ha

/-- The second actual boundary puncture retains the entire opposite parameter chart. -/
@[reassoc] theorem conicBoundarySecond_inclusion : s₂ ≫ i = p ≫ P₂ := by
  calc
    _ = Spec.map (CommRingCat.ofHom (conicPuncturedSecond W c hc).toRingHom) := by
      rw [← Spec.map_comp]
      congr 1
      apply CommRingCat.hom_ext
      exact RingHom.ext (conicBoundarySecond_base W c ha hc)
    _ = _ := conicPuncturedSecond_spec c hc W ha

include hc in
/-- Vanishing divided constant separates the full original ordered conic parameter charts. -/
theorem conicParameters_disjoint_of_zero : Disjoint (Set.range P₁) (Set.range P₂) := by
  subst c
  exact conicZeroParameters_disjoint W.a₁ ha

end FLT.Mazur.WeierstrassSuccessiveX
