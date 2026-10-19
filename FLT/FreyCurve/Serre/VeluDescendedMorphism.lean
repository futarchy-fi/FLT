/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.FreyCurve.Serre.VeluCoefficientInvariantDescent
public import FLT.FreyCurve.Serre.VeluGlobalGaloisInvariant

/-!
# The actual descended Vélu morphism on the original base-field cubic

Descent uses the full proved kernel-pair compatibility. The resulting morphism
recovers the original global map on the exact target equation, in a Cartesian
square with the original source and target coefficient projections.
-/

@[expose] public noncomputable section

open CategoryTheory Limits AlgebraicGeometry
open FLT.Mazur.WeierstrassIntegralChart

namespace WeierstrassCurve.Velu

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {K L : Type} [Field K] [Field L] [Algebra K L]
  [CharZero K] [CharZero L] [Algebra.IsAlgebraic K L] [IsAlgClosed L] [DecidableEq L]
  (E : WeierstrassCurve K) [E.IsElliptic]
  (G : AddSubgroup (E.map (algebraMap K L)).toAffine.Point) [Fintype G]
  (hodd : ∀ Q : G, Q ≠ 0 → Q ≠ -Q)
  (V : WeierstrassCurve K)
  (hV : V.map (algebraMap K L) = curve (E.map (algebraMap K L)) G)
  (hG : ∀ (g : L ≃ₐ[K] L) P, P ∈ G →
    Affine.Point.map (W' := E.toAffine) g.toAlgHom P ∈ G)

local notation "EL" => E.map (algebraMap K L)
local notation "VL" => V.map (algebraMap K L)

/-- The original Vélu map descends to the original cubic and exact base-field target. -/
def veluDescendedMorphism : integralCurve E ⟶ integralCurve V :=
  coefficientInvariantDesc E (integralCurveStructure V) (integralCurveStructure E)
    (veluGlobalToBaseTarget E G hodd V hV)
    (by rw [veluGlobalToBaseTarget_base, integralCoefficientMorphism_structure])
    (veluGlobalToBaseTarget_galois E G hodd V hV hG)

/-- The constructed map recovers the entire original geometric map to the base target. -/
@[reassoc] theorem veluDescendedMorphism_fac :
    integralCoefficientMorphism E ≫ veluDescendedMorphism E G hodd V hV hG =
      veluGlobalToBaseTarget E G hodd V hV := coefficientInvariantDesc_fac ..

/-- The descended morphism is over the original base field. -/
@[reassoc] theorem veluDescendedMorphism_base :
    veluDescendedMorphism E G hodd V hV hG ≫ integralCurveStructure V =
      integralCurveStructure E := coefficientInvariantDesc_base ..

/-- The original geometric Vélu morphism is exactly the base change of the descended map. -/
theorem veluDescendedMorphism_isPullback :
    IsPullback (integralCoefficientMorphism E)
      (veluGlobalToEquation EL G hodd VL hV)
      (veluDescendedMorphism E G hodd V hV hG) (integralCoefficientMorphism V) := by
  have H : IsPullback
      (veluGlobalToEquation EL G hodd VL hV ≫ integralCurveStructure VL)
      (integralCoefficientMorphism E)
      (Spec.map (CommRingCat.ofHom (algebraMap K L)))
      (veluDescendedMorphism E G hodd V hV hG ≫ integralCurveStructure V) := by
    rw [veluGlobalToEquation_base, veluDescendedMorphism_base]
    exact (integralCoefficient_isPullback E).flip
  apply (H.of_right ?_ (integralCoefficient_isPullback V).flip).flip
  exact (veluDescendedMorphism_fac E G hodd V hV hG).symm

/-- The original identity section is retained by descent. -/
@[reassoc] theorem veluDescendedMorphism_zero :
    integralCurveZero E ≫ veluDescendedMorphism E G hodd V hV hG =
      integralCurveZero V := by
  have H := (flat_and_surjective_SpecMap_iff
    (CommRingCat.ofHom (algebraMap K L))).mpr
      (RingHom.faithfullyFlat_algebraMap_iff.mpr inferInstance)
  let _ := H.1
  let _ := H.2
  let _ := Flat.epi_of_flat_of_surjective (Spec.map (CommRingCat.ofHom (algebraMap K L)))
  apply (cancel_epi (Spec.map (CommRingCat.ofHom (algebraMap K L)))).mp
  rw [← integralCoefficientMorphism_zero_assoc, veluDescendedMorphism_fac,
    veluGlobalToBaseTarget_zero]

/-- The original geometric map determines the rational morphism uniquely. -/
theorem veluDescendedMorphism_unique (f : integralCurve E ⟶ integralCurve V)
    (h : integralCoefficientMorphism E ≫ f = veluGlobalToBaseTarget E G hodd V hV) :
    f = veluDescendedMorphism E G hodd V hV hG := by
  apply (cancel_epi (integralCoefficientMorphism (S := L) E)).mp
  rw [veluDescendedMorphism_fac, h]

end WeierstrassCurve.Velu
