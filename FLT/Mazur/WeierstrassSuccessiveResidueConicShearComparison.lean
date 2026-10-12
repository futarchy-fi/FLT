/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassSuccessiveResidueLineShearComparison
public import FLT.Mazur.WeierstrassSuccessiveShearConicBoundary
public import FLT.Mazur.WeierstrassSuccessiveShearScaleOneConicBoundary
public import FLT.Mazur.WeierstrassSuccessiveZeroConicMap

/-!
# Full original conic restrictions agree with root-zero shear

The positive-scale and scale-one equations are compared separately on every
original tensor generator. Equal-tangent transport keeps the entire conic.
-/

@[expose] public noncomputable section
open IsLocalRing AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassSuccessiveX
open WeierstrassModificationX WeierstrassDividedDepth
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option quotPrecheck false
universe u
variable {R : Type u} [CommRing R] [IsDomain R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} {k depth : ℕ}
  (D : SplitNodeDepth W π depth) (hk : 2 * (k + 1) ≤ depth)
  (d : Data W π (k + 1))
local notation "K" => ResidueField R
local notation "V" => W.map (residue R)
local notation "U" => rootShearCurve V 0
local notation "c" => residue R d.b6
variable (hp : algebraMap R (ResidueField R) π = 0)
  (h3 : algebraMap R (ResidueField R) d.b3 = 0) (h4 : algebraMap R (ResidueField R) d.b4 = 0)
  (hr : (0 : ResidueField R) ^ 2 + algebraMap R (ResidueField R) W.a₁ * 0 -
    algebraMap R (ResidueField R) W.a₂ = 0)
local notation "H" => conicCoefficientTransport c (Eq.symm (rootShearZero_tangent V))

section Positive
variable (hk0 : 0 < k) (hs : algebraMap R (ResidueField R) (π ^ k) = 0)
local notation "E" => residueRetainedFiberEquiv D k hk0 hk d.b3 d.b4 d.b6 d.factor3 d.factor4
local notation "M" => middleConicMap V c ((residue_eq_zero_iff _).mpr D.a₂_mem)
local notation "F" => tensorShearConicMap W (π ^ k) π d.b3 d.b4 d.b6 K 0 hs hp h3 h4 hr

/-- Root-zero shear agrees with restriction of every original positive-scale tensor function. -/
theorem residueSuccessiveConicMap_eq_shear :
    (H).toAlgHom.comp ((M).comp (E).toAlgHom) = F := by
  apply Algebra.TensorProduct.ext_ring
  apply hom_ext
  intro i
  change H (M (E (tensorCoord W (π ^ k) π d.b3 d.b4 d.b6 K i))) =
    F (tensorCoord W (π ^ k) π d.b3 d.b4 d.b6 K i)
  rw [residueRetainedFiberEquiv_coord, middleConicMap_coord, tensorShearConicMap_coord]
  fin_cases i
  · exact conicCoefficientTransport_t c _
  · change H (conicV (V).a₁ c) = conicV (U).a₁ c + algebraMap K _ 0
    rw [map_zero, add_zero]
    exact conicCoefficientTransport_v c
      (Eq.symm (rootShearZero_tangent V))
  · exact map_zero _

/-- The entire positive-scale conic immersion reconstructs the original tensor immersion. -/
theorem residueSuccessiveConicImmersion_eq_shear :
    Spec.map (CommRingCat.ofHom (H).toAlgHom.toRingHom) ≫
        residueSuccessiveConicImmersion D k hk0 hk d.b3 d.b4 d.b6 d.factor3 d.factor4 =
      tensorShearConicImmersion W (π ^ k) π d.b3 d.b4 d.b6 K 0 hs hp h3 h4 hr := by
  rw [tensorShearConicImmersion_eq_spec]
  unfold residueSuccessiveConicImmersion middleConicImmersion residueRetainedIso
  change Spec.map _ ≫ Spec.map _ ≫ Spec.map _ = _
  rw [← Spec.map_comp, ← Spec.map_comp]
  exact congrArg (fun f => Spec.map (CommRingCat.ofHom (AlgHom.toRingHom f)))
    (residueSuccessiveConicMap_eq_shear D hk d hp h3 h4 hr hk0 hs)
end Positive

section ScaleOne
variable (hk0 : k = 0) (hs : algebraMap R (ResidueField R) (π ^ k) = 1)
local notation "F" => tensorShearScaleOneConicMap W (π ^ k) π d.b3 d.b4 d.b6
  K 0 hs hp h3 h4 hr

/-- The separate scale-one restriction preserves all three original tensor generators. -/
theorem zeroResidueConicMap_transport_eq_shear :
    (H).toAlgHom.comp (zeroResidueConicMap D hk0 hk d) = F := by
  apply Algebra.TensorProduct.ext_ring
  apply hom_ext
  intro i
  change H (zeroResidueConicMap D hk0 hk d
      (tensorCoord W (π ^ k) π d.b3 d.b4 d.b6 K i)) =
    F (tensorCoord W (π ^ k) π d.b3 d.b4 d.b6 K i)
  rw [tensorShearScaleOneConicMap_coord]
  fin_cases i
  · erw [zeroResidueConicMap_t]
    exact conicCoefficientTransport_t c _
  · erw [zeroResidueConicMap_v]
    change H (conicV (V).a₁ c) = conicV (U).a₁ c + algebraMap K _ 0
    rw [map_zero, add_zero]
    exact conicCoefficientTransport_v c
      (Eq.symm (rootShearZero_tangent V))
  · erw [zeroResidueConicMap_u]
    exact map_zero _

/-- The complete scale-one conic keeps its original geometric immersion. -/
theorem zeroResidueConicImmersion_transport_eq_shear :
    Spec.map (CommRingCat.ofHom (H).toAlgHom.toRingHom) ≫
        zeroResidueConicImmersion D k hk0 hk d.b3 d.b4 d.b6 d.factor3 d.factor4 =
      tensorShearScaleOneConicImmersion W (π ^ k) π d.b3 d.b4 d.b6
        K 0 hs hp h3 h4 hr := by
  rw [← zeroResidueConicMap_spec D hk0 hk d, tensorShearScaleOneConicImmersion_eq_spec,
    ← Spec.map_comp]
  exact congrArg (fun f => Spec.map (CommRingCat.ofHom (AlgHom.toRingHom f)))
    (zeroResidueConicMap_transport_eq_shear D hk d hp h3 h4 hr hk0 hs)
end ScaleOne

end FLT.Mazur.WeierstrassSuccessiveX
