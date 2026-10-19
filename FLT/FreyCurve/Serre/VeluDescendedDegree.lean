/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.FreyCurve.Serre.VeluDescendedMorphism
public import FLT.Mazur.FiniteFiberSurjectiveDescent

/-!
# Finite locally free degree of the actual descended Vélu map

Properness and the finite geometric fibers give finiteness on the original
base-field cubics. Dominance and smooth target stalks give flatness. The
actual Cartesian coefficient square then transfers the geometric degree.
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
local notation "φ" => veluDescendedMorphism E G hodd V hV hG

include hV hodd in
omit [CharZero K] [Algebra.IsAlgebraic K L] in
/-- The exact base-field target equation is elliptic. -/
theorem veluDescendedTarget_isElliptic : V.IsElliptic := by
  have hv : (VL).Δ ≠ 0 := by
    rw [hV]
    exact curve_discr_ne_zero EL G hodd
  refine ⟨isUnit_iff_ne_zero.mpr fun h ↦ hv ?_⟩
  rw [map_Δ, h, map_zero]

/-- The descended original morphism is proper. -/
instance veluDescendedMorphism_proper : IsProper φ := by
  have H : IsProper (φ ≫ integralCurveStructure V) := by
    rw [veluDescendedMorphism_base]
    infer_instance
  let _ := H
  exact IsProper.of_comp φ (integralCurveStructure V)

/-- The entire original target is covered by the descended morphism. -/
instance veluDescendedMorphism_surjective : Surjective φ := by
  let _ : Surjective (veluGlobalToEquation EL G hodd VL hV) := by
    unfold veluGlobalToEquation
    infer_instance
  have H : Surjective (integralCoefficientMorphism (S := L) E ≫ φ) := by
    rw [veluDescendedMorphism_fac, veluGlobalToBaseTarget]
    infer_instance
  let _ := H
  exact Surjective.of_comp (integralCoefficientMorphism (S := L) E) φ

/-- Finiteness of the whole geometric map gives finiteness on the original cubics. -/
instance veluDescendedMorphism_finite : IsFinite φ :=
  FLT.Mazur.FiniteFiberSurjectiveDescent.isFinite
    (veluDescendedMorphism_isPullback E G hodd V hV hG)

/-- The actual map is flat over the smooth original target. -/
instance veluDescendedMorphism_flat : Flat φ := by
  let _ := integralCurveStructure_smooth_dimension V
    (veluDescendedTarget_isElliptic E G hodd V hV).isUnit
  exact FLT.Mazur.FCurve.dominantIntegral_smoothCurve_flat φ (integralCurveStructure V)

/-- Finite presentation holds over the original Noetherian target. -/
instance veluDescendedMorphism_lfp : LocallyOfFinitePresentation φ := by
  let _ := LocallyOfFiniteType.isLocallyNoetherian (integralCurveStructure V)
  infer_instance

/-- Every original target fiber has the original subgroup order as its rank. -/
theorem veluDescendedMorphism_rank (y : integralCurve V) : (φ).finrank y = Nat.card G := by
  obtain ⟨z, rfl⟩ := (integralCoefficientMorphism (S := L) V).surjective y
  rw [← Scheme.Hom.finrank_of_isPullback _ _ _ _
    (veluDescendedMorphism_isPullback E G hodd V hV hG)]
  exact (veluGlobalToEquation_degree EL G hodd VL hV).2.2.2 z

/-- The descended map has the same finite locally free degree as the original global map. -/
theorem veluDescendedMorphism_degree :
    FLT.Mazur.FCurve.FiniteLocallyFreeDegree φ (Nat.card G) :=
  ⟨inferInstance, inferInstance, inferInstance, veluDescendedMorphism_rank E G hodd V hV hG⟩

end WeierstrassCurve.Velu
