/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassSuccessiveShearScaleOneIncidence
public import FLT.Mazur.WeierstrassIncidenceShearLineContraction
public import FLT.Mazur.WeierstrassSmoothSuccessiveIntegralCubicMaps
public import FLT.Mazur.WeierstrassResidueIncidenceNormalization

/-!
# The scale-one incidence line is the original cubic normalization

The original modification contraction preserves the whole polynomial slope.
At start zero this identifies the retained incidence with the same actual
residue normalization used by the proper exterior lift.
-/

@[expose] public noncomputable section
open Polynomial IsLocalRing
namespace FLT.Mazur.WeierstrassSuccessiveX
open WeierstrassDividedDepth WeierstrassModificationX WeierstrassIntegralChart
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option quotPrecheck false
universe u
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R) (s π b3 b4 b6 : R)
  (S : Type u) [CommRing S] [Algebra R S] (r : S)
  (hs : algebraMap R S s = 1) (hp : algebraMap R S π = 0)
  (h3 : algebraMap R S b3 = 0) (h4 : algebraMap R S b4 = 0)
  (hr : r ^ 2 + algebraMap R S W.a₁ * r - algebraMap R S W.a₂ = 0)
local notation "L" => originalShearScaleOneIncidenceMap W s π b3 b4 b6 S r hs hp h3 h4 hr
local notation "hz" => show algebraMap R S (s * π) = 0 from by rw [map_mul, hp, mul_zero]

/-- Every original modification function restricts to the same complete incidence line. -/
theorem originalShearScaleOneIncidenceMap_modification :
    (L).comp (modificationMap W s π b3 b4 b6) =
      originalShearInitialLineMap W (s * π) b3 b4 b6 S r hz h3 h4 hr := by
  apply WeierstrassModificationX.hom_ext
  · rw [AlgHom.comp_apply, modificationMap_t,
      originalShearScaleOneIncidenceMap_coord, originalShearInitialLineMap_t]
    rfl
  · rw [AlgHom.comp_apply, modificationMap_v,
      originalShearScaleOneIncidenceMap_coord, originalShearInitialLineMap_v]
    rfl

end FLT.Mazur.WeierstrassSuccessiveX
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassSuccessiveX WeierstrassModificationX WeierstrassIntegralChart
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option quotPrecheck false
variable {R : Type} [CommRing R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} (d : Data W π (0 + 1))
  (hres : residue R π = 0)
local notation "V" => W.map (residue R)
local notation "Q" => AdjoinRoot (nodeTangentPolynomial V)
local notation "r" => AdjoinRoot.root (nodeTangentPolynomial V)
variable (h3 : algebraMap R (AdjoinRoot (nodeTangentPolynomial (W.map (residue R)))) d.b3 = 0)
  (h4 : algebraMap R (AdjoinRoot (nodeTangentPolynomial (W.map (residue R)))) d.b4 = 0)
local notation "hp" => residueTangentEquation_zero W π ((residue_eq_zero_iff π).mp hres)
local notation "hs" => show algebraMap R Q (π ^ 0) = 1 from by simp
local notation "hr" => residueTangentEquation_root W
local notation "L" => originalShearScaleOneIncidenceMap W (π ^ 0) π
  d.b3 d.b4 d.b6 Q r hs hp h3 h4 hr
local notation "hz" => show algebraMap R Q (π ^ (0 + 1)) = 0 from by simp [hp]

/-- The complete original cubic contraction of the scale-one line is its residue normalization. -/
theorem originalShearScaleOneIncidenceMap_eq_residue :
    ((L).comp (successiveIntegralCubicMap d)).toRingHom =
      originalResidueNormalization d (by decide) hres := by
  let O := originalShearIncidenceNormalization W (π ^ (0 + 1))
    d.b3 d.b4 d.b6 Q r hz h3 h4 hr d.factor3 d.factor4 d.factor6
  have H : (L).comp (successiveIntegralCubicMap d) = O := by
    apply WeierstrassIntegralChart.hom_ext
    intro i
    fin_cases i
    · change L (modificationMap W (π ^ 0) π d.b3 d.b4 d.b6
        (fromOriginal W (π ^ 0 * π) d.b3 d.b4 d.b6
          (by simpa using d.factor3) (by simpa using d.factor4)
          (by simpa using d.factor6) (coord W 2 0))) = _
      rw [fromOriginal_x, modificationMap_x, map_mul, AlgHom.commutes,
        originalShearScaleOneIncidenceMap_coord]
      change _ = originalShearIncidenceNormalization W (π ^ (0 + 1))
        d.b3 d.b4 d.b6 Q r hz h3 h4 hr d.factor3 d.factor4 d.factor6 (coord W 2 0)
      rw [originalShearIncidenceNormalization_x]
      simp
    · change L (modificationMap W (π ^ 0) π d.b3 d.b4 d.b6
        (fromOriginal W (π ^ 0 * π) d.b3 d.b4 d.b6
          (by simpa using d.factor3) (by simpa using d.factor4)
          (by simpa using d.factor6) (coord W 2 1))) = _
      rw [fromOriginal_y, WeierstrassModificationX.y, map_mul, modificationMap_x,
        modificationMap_v, map_mul, map_mul, AlgHom.commutes,
        originalShearScaleOneIncidenceMap_coord, originalShearScaleOneIncidenceMap_coord]
      change _ = originalShearIncidenceNormalization W (π ^ (0 + 1))
        d.b3 d.b4 d.b6 Q r hz h3 h4 hr d.factor3 d.factor4 d.factor6 (coord W 2 1)
      rw [originalShearIncidenceNormalization_y]
      simp [mul_comm]
    · change ((L).comp (successiveIntegralCubicMap d)) (coord W 2 2) = O (coord W 2 2)
      rw [coord_self, map_one, map_one]
  exact (congrArg AlgHom.toRingHom H).trans
    (originalShearIncidenceNormalization_eq_residue d (by decide) hres hz h3 h4)

end FLT.Mazur.WeierstrassDividedDepth
