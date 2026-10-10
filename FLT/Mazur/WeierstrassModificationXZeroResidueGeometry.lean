/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassModificationXZeroResidue
public import FLT.Mazur.WeierstrassModificationXMorphism

/-!
# The full start-zero slope scheme with its original contraction

The slope localization is isomorphic to the entire original tensor chart.
Its cubic map retains every original function, including the ordered x/y formulas.
-/

@[expose] public noncomputable section
open IsLocalRing AlgebraicGeometry CategoryTheory
open scoped TensorProduct
namespace FLT.Mazur.WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] [IsDomain R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} {depth : ℕ} (D : SplitNodeDepth W π depth)
  (hdepth : 0 < depth) (k : ℕ) (hk : k = 0) (b3 b4 b6 : R)
  (h3 : W.a₃ = π ^ k * b3) (h4 : W.a₄ = π ^ k * b4)
  (h6 : W.a₆ = (π ^ k) ^ 2 * b6)
local notation "K" => ResidueField R
local notation "a" => residue R W.a₁
local notation "P" => SlopeOpen a
local notation "T" => ScalarExtension W (π ^ k) b3 b4 b6 K
local notation "e" => zeroResidueSlopeEquiv D hdepth k hk b3 b4 b6 h3 h4 h6

/-- The full localized slope line is the original start-zero tensor residue scheme. -/
def zeroResidueSlopeIso : Spec (.of P) ≅ Spec (.of T) :=
  Scheme.Spec.mapIso (e).toRingEquiv.toCommRingCatIso.op

/-- The comparison transports all original horizontal chart functions. -/
def zeroResidueSlopeMap : Coordinate W (π ^ k) b3 b4 b6 →ₐ[R] P :=
  ((e).toAlgHom.restrictScalars R).comp Algebra.TensorProduct.includeRight

/-- The original function map is exactly evaluation on its pure tensor. -/
theorem zeroResidueSlopeMap_apply (z : Coordinate W (π ^ k) b3 b4 b6) :
    zeroResidueSlopeMap D hdepth k hk b3 b4 b6 h3 h4 h6 z = e ((1 : K) ⊗ₜ[R] z) := rfl

/-- The full original affine cubic coordinate map into the slope localization. -/
def zeroResidueOriginalMap : WeierstrassIntegralChart.Coordinate W 2 →ₐ[R] P :=
  (zeroResidueSlopeMap D hdepth k hk b3 b4 b6 h3 h4 h6).comp
    (fromOriginal W (π ^ k) b3 b4 b6 h3 h4 h6)

/-- The original cubic horizontal coordinate is the ordered tangent product. -/
theorem zeroResidueOriginalMap_x :
    zeroResidueOriginalMap D hdepth k hk b3 b4 b6 h3 h4 h6
      (WeierstrassIntegralChart.coord W 2 0) =
        slopeZ a * (slopeZ a + algebraMap K P a) := by
  rw [zeroResidueOriginalMap, AlgHom.comp_apply, fromOriginal_x,
    zeroResidueSlopeMap_apply, zeroResidueSlopeEquiv_x]

/-- The original cubic vertical coordinate is the same product times the original slope. -/
theorem zeroResidueOriginalMap_y :
    zeroResidueOriginalMap D hdepth k hk b3 b4 b6 h3 h4 h6
      (WeierstrassIntegralChart.coord W 2 1) =
        (slopeZ a * (slopeZ a + algebraMap K P a)) * slopeZ a := by
  rw [zeroResidueOriginalMap, AlgHom.comp_apply, fromOriginal_y,
    zeroResidueSlopeMap_apply, zeroResidueSlopeEquiv_y]

/-- The full start-zero slope chart contracts to the original projective cubic. -/
def zeroResidueSlopeContraction : Spec (.of P) ⟶
    WeierstrassIntegralChart.integralCurve W :=
  Spec.map (CommRingCat.ofHom
    (zeroResidueOriginalMap D hdepth k hk b3 b4 b6 h3 h4 h6).toRingHom) ≫
      WeierstrassIntegralChart.integralCurveChart W 2

/-- The contraction is exactly the original tensor projection and cubic chart map. -/
@[reassoc] theorem zeroResidueSlopeIso_contraction :
    (zeroResidueSlopeIso D hdepth k hk b3 b4 b6 h3 h4 h6).hom ≫
      Spec.map (CommRingCat.ofHom
        (show Coordinate W (π ^ k) b3 b4 b6 →ₐ[R] T from
          Algebra.TensorProduct.includeRight).toRingHom) ≫
        toCurve W (π ^ k) b3 b4 b6 h3 h4 h6 =
      zeroResidueSlopeContraction D hdepth k hk b3 b4 b6 h3 h4 h6 := by
  change Spec.map _ ≫ Spec.map _ ≫ (Spec.map _ ≫ _) = Spec.map _ ≫ _
  rw [← Category.assoc, ← Spec.map_comp, ← Category.assoc, ← Spec.map_comp]
  rfl

/-- The entire slope comparison retains the residue coefficient structure. -/
@[reassoc] theorem zeroResidueSlopeIso_structure :
    (zeroResidueSlopeIso D hdepth k hk b3 b4 b6 h3 h4 h6).hom ≫
      Spec.map (CommRingCat.ofHom (algebraMap K T)) =
        Spec.map (CommRingCat.ofHom (algebraMap K P)) := by
  change Spec.map _ ≫ Spec.map _ = _
  rw [← Spec.map_comp]
  congr 1
  ext r
  exact (e).commutes r

end FLT.Mazur.WeierstrassModificationX
