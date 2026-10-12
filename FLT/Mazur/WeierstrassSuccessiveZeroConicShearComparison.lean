/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassConicCoefficientTransport
public import FLT.Mazur.WeierstrassSuccessiveZeroConicMap
public import FLT.Mazur.WeierstrassSuccessiveShearScaleOneConicBoundary

/-!
# The actual split residue conic is the root-zero sheared conic

Compare the full algebra restrictions, keeping the coefficient transport
explicit. Taking spectra identifies the independently constructed immersions.
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

/-- All original tensor functions agree after the explicit conic equation transport. -/
theorem zeroResidueConicMap_eq_shear :
    zeroResidueConicMap D hk0 hk d = (E).toAlgHom.comp F := by
  apply Algebra.TensorProduct.ext_ring
  apply WeierstrassSuccessiveX.hom_ext
  intro i
  change zeroResidueConicMap D hk0 hk d
      (tensorCoord W (π ^ k) π d.b3 d.b4 d.b6 K i) =
    E (F (tensorCoord W (π ^ k) π d.b3 d.b4 d.b6 K i))
  rw [tensorShearScaleOneConicMap_coord]
  fin_cases i
  · exact (zeroResidueConicMap_t D hk0 hk d).trans
      (conicCoefficientTransport_t c (rootShearZero_tangent V)).symm
  · change _ = E (conicV (U).a₁ c + algebraMap K _ 0)
    rw [map_zero, add_zero, conicCoefficientTransport_v]
    exact zeroResidueConicMap_v D hk0 hk d
  · change _ = E 0
    rw [map_zero]
    exact zeroResidueConicMap_u D hk0 hk d

/-- The whole original conic immersion is the sheared immersion after equation transport. -/
theorem zeroResidueConicImmersion_eq_shear :
    zeroResidueConicImmersion D k hk0 hk d.b3 d.b4 d.b6 d.factor3 d.factor4 =
      Spec.map (CommRingCat.ofHom (E).toAlgHom.toRingHom) ≫
        tensorShearScaleOneConicImmersion W (π ^ k) π
          d.b3 d.b4 d.b6 K 0 hs hp h3 h4 hr := by
  rw [← zeroResidueConicMap_spec, zeroResidueConicMap_eq_shear D hk0 hk d hs hp h3 h4 hr,
    tensorShearScaleOneConicImmersion_eq_spec, ← Spec.map_comp]
  rfl

end FLT.Mazur.WeierstrassSuccessiveX
