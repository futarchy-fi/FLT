/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassInfinityResidueGeometry
public import FLT.Mazur.WeierstrassInfinityTensorBoundary
public import FLT.Mazur.PrincipalOpenNormalization

/-!
# The entire original Y-boundary in Laurent infinity coordinates

The original tensor Y/Z overlap is the full localization of the Laurent
algebra at its original Z/Y function. The original inclusion, transition,
coefficient structure and cubic contraction are all preserved.
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
local notation "tz" => infinityTensorCoord (W := W) 2

/-- The boundary parameter is the original Z/Y, with its full Laurent formula. -/
def infinityResidueBoundaryFunction : K[T;T⁻¹] := (e) tz

/-- The original boundary function retains its exact normalized cubic expression. -/
theorem infinityResidueBoundaryFunction_eq :
    infinityResidueBoundaryFunction D hdepth =
      splitNodalLaurentZ (WeierstrassDilatation.residueTangentUnit D) :=
  infinityResidueEquiv_coord D hdepth 2

/-- The complete normalized principal open, with no component removed. -/
abbrev InfinityResidueBoundary := Localization.Away (infinityResidueBoundaryFunction D hdepth)

/-- The full original overlap tensor algebra is the normalized Laurent principal open. -/
def infinityResidueBoundaryEquiv : K ⊗[R] Overlap W 2 1 ≃ₐ[K]
    InfinityResidueBoundary D hdepth :=
  (infinityTensorBoundaryEquiv W K).trans (PrincipalOpenNormalization.equiv e tz)

/-- Its spectrum comparison retains the whole original affine Y-boundary. -/
def infinityResidueBoundaryIso : Spec (.of (InfinityResidueBoundary D hdepth)) ≅
    Spec (.of (K ⊗[R] Overlap W 2 1)) :=
  PrincipalOpenNormalization.specIso e tz ≪≫ infinityTensorBoundaryIso W K

/-- The normalized boundary inclusion in the full Laurent infinity chart. -/
def infinityResidueBoundaryInclusion : Spec (.of (InfinityResidueBoundary D hdepth)) ⟶
    Spec (.of K[T;T⁻¹]) :=
  Spec.map (CommRingCat.ofHom (algebraMap K[T;T⁻¹] (InfinityResidueBoundary D hdepth)))

instance infinityResidueBoundaryInclusion_isOpenImmersion :
    IsOpenImmersion (infinityResidueBoundaryInclusion D hdepth) :=
  IsOpenImmersion.of_isLocalization (infinityResidueBoundaryFunction D hdepth)

/-- The actual original Y/Z transition is the full normalized principal inclusion. -/
@[reassoc] theorem infinityResidueBoundaryIso_inclusion :
    (infinityResidueBoundaryIso D hdepth).hom ≫
      WeierstrassDividedDepth.tensorBoundaryToInfinity (W := W) K =
        infinityResidueBoundaryInclusion D hdepth ≫ (infinityResidueIso D hdepth).hom := by
  change (_ ≫ _) ≫ _ = _
  rw [Category.assoc, infinityTensorBoundaryIso_inclusion]
  exact PrincipalOpenNormalization.specIso_inclusion e tz

/-- The entire boundary retains every original projective cubic function. -/
@[reassoc] theorem infinityResidueBoundaryIso_contraction :
    (infinityResidueBoundaryIso D hdepth).hom ≫ TensorOpenChart.projection ≫
      affineBoundaryToY W ≫ integralCurveChart W 1 =
        infinityResidueBoundaryInclusion D hdepth ≫ infinityResidueContraction D hdepth := by
  rw [← WeierstrassDividedDepth.tensorBoundaryToInfinity_projection_assoc,
    infinityResidueBoundaryIso_inclusion_assoc, infinityResidueIso_contraction]

/-- All residue coefficients retain their original restrictions to the whole boundary. -/
@[reassoc] theorem infinityResidueBoundaryIso_structure :
    (infinityResidueBoundaryIso D hdepth).hom ≫
      Spec.map (CommRingCat.ofHom (algebraMap K (K ⊗[R] Overlap W 2 1))) =
        Spec.map (CommRingCat.ofHom (algebraMap K (InfinityResidueBoundary D hdepth))) := by
  rw [← WeierstrassDividedDepth.tensorBoundaryToInfinity_structure (W := W) K,
    infinityResidueBoundaryIso_inclusion_assoc, infinityResidueIso_structure]
  change Spec.map _ ≫ Spec.map _ = Spec.map _
  rw [← Spec.map_comp]
  congr 1

end FLT.Mazur.WeierstrassIntegralChart
