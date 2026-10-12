/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AuxiliaryLevelFieldMarking
public import FLT.Mazur.GeometricPointCoverCriterion
public import FLT.Mazur.UniversalWeierstrassAuxiliaryLevel
public import FLT.Mazur.WeierstrassGeometricFourBasis
public import FLT.Mazur.WeierstrassGeometricFourTorsion

/-!
# Auxiliary markings cover every smooth original Weierstrass family

The explicit geometric four-torsion basis gives points of the actual faithful
marking open for any smooth equation with two invertible. Thus this open is
surjective over the original coefficient ring, without choosing a new equation.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.WeierstrassAuxiliaryFieldCover
open WeierstrassIntegralChart UniversalWeierstrass AuxiliaryLevel
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type} [CommRing R] (W : WeierstrassCurve R) (hΔ : IsUnit W.Δ)

local notation "G" => integralCurveGroup W hΔ
local instance : IsSeparated (G).X.hom := inferInstanceAs (IsSeparated (integralCurveStructure W))

/-- The auxiliary marking open on the original smooth cubic over its coefficient ring. -/
def scheme : Over (Spec (.of R)) := faithfulScheme (G).X (Labels 4)

/-- Every geometric coefficient field has a faithful marking on the original cubic. -/
theorem geometric_marking (h2 : IsUnit (2 : R)) (K : Type) [Field K] [IsSepClosed K]
    [Algebra R K] :
    ∃ φ : Labels 4 →* integralGroupFieldPoints (K := K) W hΔ, Function.Injective φ := by
  classical
  let _ : W.IsElliptic := ⟨hΔ⟩
  have hk : (2 : K) ≠ 0 := by
    have hu := h2.map (algebraMap R K)
    simpa only [map_ofNat, isUnit_iff_ne_zero] using hu
  obtain ⟨φ, hφ⟩ := WeierstrassGeometricFourBasis.exists_injective_marking
    (W.map (algebraMap R K)) hk
  let e := integralAffinePointAddEquiv (K := K) W hΔ
  exact ⟨(e.toAddMonoidHom.comp φ).toMultiplicativeLeft,
    fun _ _ he ↦ hφ (e.injective (congrArg Additive.ofMul he))⟩

/-- Every geometric point of the original coefficient base lifts to the actual marking open. -/
theorem geometric_lift (h2 : IsUnit (2 : R)) (K : Type) [Field K] [IsAlgClosed K]
    (g : Spec (.of K) ⟶ Spec (.of R)) :
    ∃ f : Spec (.of K) ⟶ (scheme W hΔ).left, f ≫ (scheme W hΔ).hom = g := by
  obtain ⟨r, hr⟩ := Spec.map_surjective g
  let _ := r.hom.toAlgebra
  obtain ⟨φ, hφ⟩ := geometric_marking W hΔ h2 K
  let f := fieldFaithfulLift (G).X (Labels 4)
    (Spec.map (CommRingCat.ofHom (algebraMap R K))) φ hφ
  exact ⟨f.left, f.w.trans hr⟩

/-- Auxiliary bases exist locally over every point of the original coefficient base. -/
theorem surjective (h2 : IsUnit (2 : R)) : Surjective (scheme W hΔ).hom := by
  constructor
  intro s
  obtain ⟨_, y, hy⟩ := GeometricPointCoverCriterion.covers
    (fun _ : Unit ↦ (scheme W hΔ).hom) (fun K _ _ g ↦ by
      obtain ⟨f, hf⟩ := geometric_lift W hΔ h2 K g
      exact ⟨(), f, hf⟩) s
  exact ⟨y, hy⟩

end FLT.Mazur.WeierstrassAuxiliaryFieldCover
