/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassSuccessiveZeroConicShearComparison

/-!
# Both actual conic punctures agree with the signed sheared punctures

The equality compares complete tensor restrictions and complete scheme
maps; the coefficient transport is discharged using its coordinate identities.
-/

@[expose] public noncomputable section
open IsLocalRing AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassSuccessiveX
open WeierstrassModificationX WeierstrassDividedDepth
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] [IsDomain R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} {k depth : ℕ}
  (D : SplitNodeDepth W π depth) (hk0 : k = 0) (hk : 2 * (k + 1) ≤ depth)
  (d : Data W π (k + 1))
local notation "K" => ResidueField R
local notation "V" => W.map (residue R)
local notation "U" => rootShearCurve V 0
local notation "c" => residue R d.b6
variable (hs : algebraMap R (ResidueField R) (π ^ k) = 1) (hp : algebraMap R (ResidueField R) π = 0)
  (h3 : algebraMap R (ResidueField R) d.b3 = 0) (h4 : algebraMap R (ResidueField R) d.b4 = 0)
  (hr : (0 : ResidueField R) ^ 2 + algebraMap R (ResidueField R) W.a₁ * 0 -
    algebraMap R (ResidueField R) W.a₂ = 0)
local notation "E" => conicCoefficientTransport c (rootShearZero_tangent V)
local notation "F" => tensorShearScaleOneConicMap W (π ^ k) π
  d.b3 d.b4 d.b6 K 0 hs hp h3 h4 hr

variable (hc : residue R d.b6 = 0)

/-- The actual first tensor puncture equals the root-zero sheared first puncture. -/
theorem zeroResidueConicFirst_eq_shear :
    (conicPuncturedFirst V c hc).comp (zeroResidueConicMap D hk0 hk d) =
      (conicPuncturedFirst U c hc).comp F := by
  rw [zeroResidueConicMap_eq_shear D hk0 hk d hs hp h3 h4 hr,
    ← AlgHom.comp_assoc, conicPuncturedFirst_coefficientTransport]

/-- The opposite tensor puncture retains its original negative slope. -/
theorem zeroResidueConicSecond_eq_shear :
    (conicPuncturedSecond V c hc).comp (zeroResidueConicMap D hk0 hk d) =
      (conicPuncturedSecond U c hc).comp F := by
  rw [zeroResidueConicMap_eq_shear D hk0 hk d hs hp h3 h4 hr,
    ← AlgHom.comp_assoc, conicPuncturedSecond_coefficientTransport]

local notation "Z" => zeroResidueConicImmersion D k hk0 hk
  d.b3 d.b4 d.b6 d.factor3 d.factor4
local notation "G" => tensorShearScaleOneConicImmersion W (π ^ k) π
  d.b3 d.b4 d.b6 K 0 hs hp h3 h4 hr

/-- Equality of the whole first puncture in the original tensor chart. -/
theorem zeroResidueConicFirst_spec_eq_shear :
    Spec.map (CommRingCat.ofHom (conicPuncturedFirst V c hc).toRingHom) ≫ Z =
      Spec.map (CommRingCat.ofHom (conicPuncturedFirst U c hc).toRingHom) ≫ G := by
  rw [← zeroResidueConicMap_spec, tensorShearScaleOneConicImmersion_eq_spec,
    ← Spec.map_comp, ← Spec.map_comp]
  exact congrArg (fun f => Spec.map (CommRingCat.ofHom (AlgHom.toRingHom f)))
    (zeroResidueConicFirst_eq_shear D hk0 hk d hs hp h3 h4 hr hc)

/-- Equality of the whole opposite puncture in the same original tensor chart. -/
theorem zeroResidueConicSecond_spec_eq_shear :
    Spec.map (CommRingCat.ofHom (conicPuncturedSecond V c hc).toRingHom) ≫ Z =
      Spec.map (CommRingCat.ofHom (conicPuncturedSecond U c hc).toRingHom) ≫ G := by
  rw [← zeroResidueConicMap_spec, tensorShearScaleOneConicImmersion_eq_spec,
    ← Spec.map_comp, ← Spec.map_comp]
  exact congrArg (fun f => Spec.map (CommRingCat.ofHom (AlgHom.toRingHom f)))
    (zeroResidueConicSecond_eq_shear D hk0 hk d hs hp h3 h4 hr hc)

end FLT.Mazur.WeierstrassSuccessiveX
