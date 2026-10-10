/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassInfinityResidueTensor
public import FLT.Mazur.PrincipalOpenNormalization

/-!
# Original nodal residue charts and their entire principal overlaps

The actual tensor chart and its whole localized overlap are the chart and
overlap of the split nodal equation. Every original coordinate is retained.
-/

@[expose] public noncomputable section
open IsLocalRing AlgebraicGeometry CategoryTheory
open scoped TensorProduct
namespace FLT.Mazur.WeierstrassIntegralChart
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] [IsDomain R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} {depth : ℕ} (D : SplitNodeDepth W π depth)
  (hdepth : 0 < depth)
local notation "K" => ResidueField R
local notation "N" => splitNodalEquation (WeierstrassDilatation.residueTangentUnit D)

/-- The entire original tensor chart is the corresponding nodal chart. -/
def nodalResidueChartEquiv (j : Fin 3) : (K ⊗[R] Coordinate W j) ≃ₐ[K] Coordinate N j :=
  (chartBaseChangeEquiv K W j).trans
    (equationChartEquiv (splitDepth_residue_equation D hdepth) j)

/-- Normalization retains every original projective coordinate. -/
theorem nodalResidueChartEquiv_coord (j i : Fin 3) :
    nodalResidueChartEquiv D hdepth j ((1 : K) ⊗ₜ[R] coord W j i) = coord N j i := by
  exact (congrArg (equationChartEquiv (splitDepth_residue_equation D hdepth) j)
    (chartBaseChangeEquiv_coord K W j i)).trans
      (equationChartEquiv_coord (splitDepth_residue_equation D hdepth) j i)

/-- Localization at an original tensor coordinate gives the whole nodal overlap. -/
def nodalResidueLocalizationEquiv (j k : Fin 3) :
    Localization.Away ((1 : K) ⊗ₜ[R] coord W j k) ≃ₐ[K] Overlap N j k :=
  IsLocalization.algEquivOfAlgEquiv _ _
    (M := Submonoid.powers ((1 : K) ⊗ₜ[R] coord W j k))
    (T := Submonoid.powers (coord N j k)) (nodalResidueChartEquiv D hdepth j)
    (by rw [Submonoid.map_powers, nodalResidueChartEquiv_coord])

/-- The entire original tensor overlap, including all its functions, is nodal. -/
def nodalResidueBoundaryEquiv (j k : Fin 3) : K ⊗[R] Overlap W j k ≃ₐ[K] Overlap N j k :=
  (PrincipalOpenTensor.equiv K (coord W j k)).trans
    (nodalResidueLocalizationEquiv D hdepth j k)

/-- All original overlap coordinates survive in the full nodal boundary. -/
theorem nodalResidueBoundaryEquiv_coord (j k i : Fin 3) :
    nodalResidueBoundaryEquiv D hdepth j k ((1 : K) ⊗ₜ[R] overlapCoord W j k i) =
      overlapCoord N j k i := by
  change nodalResidueLocalizationEquiv D hdepth j k
    (PrincipalOpenTensor.equiv K (coord W j k)
      ((1 : K) ⊗ₜ[R] algebraMap _ _ (coord W j i))) = _
  rw [PrincipalOpenTensor.equiv_tmul, one_smul, PrincipalOpenTensor.coefficient_base,
    nodalResidueLocalizationEquiv, IsLocalization.algEquivOfAlgEquiv_eq,
    nodalResidueChartEquiv_coord]
  rfl

/-- The whole nodal boundary is isomorphic to the original tensor overlap. -/
def nodalResidueBoundaryIso (j k : Fin 3) :
    overlapScheme N j k ≅ Spec (.of (K ⊗[R] Overlap W j k)) :=
  Scheme.Spec.mapIso (nodalResidueBoundaryEquiv D hdepth j k).toRingEquiv.toCommRingCatIso.op

/-- The original chart and its nodal normalization are isomorphic on spectra. -/
def nodalResidueChartIso (j : Fin 3) :
    chartScheme N j ≅ Spec (.of ((K ⊗[R] Coordinate W j))) :=
  Scheme.Spec.mapIso (nodalResidueChartEquiv D hdepth j).toRingEquiv.toCommRingCatIso.op

/-- The full boundary comparison preserves the actual residue coefficients. -/
@[reassoc] theorem nodalResidueBoundaryIso_structure (j k : Fin 3) :
    (nodalResidueBoundaryIso D hdepth j k).hom ≫
      Spec.map (CommRingCat.ofHom (algebraMap K (K ⊗[R] Overlap W j k))) =
        Spec.map (CommRingCat.ofHom (algebraMap K (Overlap N j k))) := by
  change Spec.map _ ≫ Spec.map _ = Spec.map _
  rw [← Spec.map_comp]
  congr 1
  exact CommRingCat.hom_ext (RingHom.ext (nodalResidueBoundaryEquiv D hdepth j k).commutes)

end FLT.Mazur.WeierstrassIntegralChart
