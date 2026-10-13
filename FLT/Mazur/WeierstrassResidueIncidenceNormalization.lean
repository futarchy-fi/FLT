/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassIncidenceShearLineContraction
public import FLT.Mazur.WeierstrassDividedResidueFiniteNormalization
public import FLT.Mazur.WeierstrassResidueTangentComponentData

/-!
# The incidence restriction is the original nonsplit residue normalization

Compare all original cubic functions, including the unsheared vertical coordinate.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory IsLocalRing
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassModificationX WeierstrassIntegralChart
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option quotPrecheck false
variable {R : Type} [CommRing R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} {k : ℕ} (d : Data W π k)
  (hk : 0 < k) (hres : residue R π = 0)
local notation "V" => W.map (residue R)
local notation "Q" => AdjoinRoot (nodeTangentPolynomial V)
local notation "r" => AdjoinRoot.root (nodeTangentPolynomial V)
variable (hs : algebraMap R (AdjoinRoot (nodeTangentPolynomial (W.map (residue R))))
    (π ^ k) = 0)
  (h3 : algebraMap R (AdjoinRoot (nodeTangentPolynomial (W.map (residue R)))) d.b3 = 0)
  (h4 : algebraMap R (AdjoinRoot (nodeTangentPolynomial (W.map (residue R)))) d.b4 = 0)
local notation "hr" => residueTangentEquation_root W
local notation "N" => originalShearIncidenceNormalization W (π ^ k) d.b3 d.b4 d.b6
  Q r hs h3 h4 hr d.factor3 d.factor4 d.factor6
local notation "h" => originalResidue_normalization_coefficients d hk hres
local notation "T" => nodeTangentNormalizationChart V (h).1 (h).2.1 (h).2.2

/-- Every original cubic function agrees with the proper lift's actual affine normalization. -/
theorem originalShearIncidenceNormalization_eq_residue :
    (N).toRingHom = originalResidueNormalization d hk hres := by
  let g : WeierstrassIntegralChart.Coordinate W 2 →ₐ[R] Polynomial Q :=
    { __ := originalResidueNormalization d hk hres
      commutes' := by
        intro z
        change T (chartCoefficientMap (S := ResidueField R) W 2
          (algebraMap R _ z)) = algebraMap R (Polynomial Q) z
        rw [AlgHom.commutes]
        exact (T).commutes ((residue R) z) }
  have he : N = g := by
    apply WeierstrassIntegralChart.hom_ext
    intro i
    change N (coord W 2 i) = originalResidueNormalization d hk hres (coord W 2 i)
    fin_cases i
    · change N (coord W 2 0) = originalResidueNormalization d hk hres (coord W 2 0)
      rw [originalShearIncidenceNormalization_x, originalResidueNormalization_coord]
      rfl
    · change N (coord W 2 1) = originalResidueNormalization d hk hres (coord W 2 1)
      rw [originalShearIncidenceNormalization_y, originalResidueNormalization_coord]
      rfl
    · change N (coord W 2 2) = originalResidueNormalization d hk hres (coord W 2 2)
      rw [coord_self, map_one, map_one]
  exact congrArg AlgHom.toRingHom he

end FLT.Mazur.WeierstrassDividedDepth
