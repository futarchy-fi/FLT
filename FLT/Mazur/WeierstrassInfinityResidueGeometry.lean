/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassInfinityResidueTensor
public import FLT.Mazur.WeierstrassSplitNodalTorus
public import FLT.Mazur.TensorOpenChart

/-!
# The whole original residue infinity chart as a smooth torus

The scheme isomorphism preserves every original cubic function and the
residue structure map. Smoothness holds on the entire tensor chart.
-/

@[expose] public noncomputable section
open IsLocalRing AlgebraicGeometry CategoryTheory
open scoped TensorProduct LaurentPolynomial
namespace FLT.Mazur.WeierstrassIntegralChart
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] [IsDomain R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} {depth : ℕ} (D : SplitNodeDepth W π depth)
  (hdepth : 0 < depth)
local notation "K" => ResidueField R
local notation "e" => infinityResidueEquiv D hdepth

/-- The Laurent spectrum identifies the entire original tensor infinity chart. -/
def infinityResidueIso : Spec (.of K[T;T⁻¹]) ≅ Spec (.of (K ⊗[R] Coordinate W 1)) :=
  Scheme.Spec.mapIso (e).toRingEquiv.toCommRingCatIso.op

/-- The full comparison retains the actual residue coefficient structure. -/
@[reassoc] theorem infinityResidueIso_structure :
    (infinityResidueIso D hdepth).hom ≫
      Spec.map (CommRingCat.ofHom (algebraMap K (K ⊗[R] Coordinate W 1))) =
        (MultiplicativeGroupScheme.gm K).hom := by
  change Spec.map _ ≫ Spec.map _ = Spec.map _
  rw [← Spec.map_comp]
  congr 1
  exact CommRingCat.hom_ext (RingHom.ext (e).commutes)

/-- All original integral infinity functions in Laurent coordinates. -/
def infinityResidueOriginalMap : Coordinate W 1 →ₐ[R] K[T;T⁻¹] :=
  ((e).toAlgHom.restrictScalars R).comp Algebra.TensorProduct.includeRight

/-- The original projective coordinates retain their ordered Laurent formulas. -/
theorem infinityResidueOriginalMap_coord (i : Fin 3) :
    infinityResidueOriginalMap D hdepth (coord W 1 i) =
      ![splitNodalLaurentX (WeierstrassDilatation.residueTangentUnit D), 1,
        splitNodalLaurentZ (WeierstrassDilatation.residueTangentUnit D)] i :=
  infinityResidueEquiv_coord D hdepth i

/-- The comparison projects to the original integral chart on every function. -/
@[reassoc] theorem infinityResidueIso_projection :
    (infinityResidueIso D hdepth).hom ≫ TensorOpenChart.projection =
      Spec.map (CommRingCat.ofHom (infinityResidueOriginalMap D hdepth).toRingHom) := by
  change Spec.map _ ≫ Spec.map _ = Spec.map _
  rw [← Spec.map_comp]
  rfl

/-- The full Laurent chart retains the original projective cubic contraction. -/
def infinityResidueContraction : Spec (.of K[T;T⁻¹]) ⟶ integralCurve W :=
  Spec.map (CommRingCat.ofHom (infinityResidueOriginalMap D hdepth).toRingHom) ≫
    integralCurveChart W 1

/-- No original cubic function is lost in the full infinity normalization. -/
@[reassoc] theorem infinityResidueIso_contraction :
    (infinityResidueIso D hdepth).hom ≫ TensorOpenChart.projection ≫
      integralCurveChart W 1 = infinityResidueContraction D hdepth := by
  rw [infinityResidueIso_projection_assoc]
  rfl

include D hdepth
/-- The entire original tensor infinity algebra is smooth over the residue field. -/
theorem infinityResidueTensor_smooth : Algebra.Smooth K (ChartScalarExtension K W 1) := by
  let _ := MultiplicativeGroupScheme.smooth_laurent K
  exact Algebra.Smooth.of_equiv (e).symm

/-- Smoothness of the actual residue structure morphism, without restricting its source. -/
theorem infinityResidueTensor_structure_smooth : Smooth
    (Spec.map (CommRingCat.ofHom (algebraMap K (K ⊗[R] Coordinate W 1)))) := by
  apply (HasRingHomProperty.Spec_iff (P := @Smooth)).mpr
  exact RingHom.smooth_algebraMap.mpr (infinityResidueTensor_smooth D hdepth)

end FLT.Mazur.WeierstrassIntegralChart
