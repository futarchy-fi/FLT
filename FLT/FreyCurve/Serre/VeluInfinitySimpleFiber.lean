/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.FreyCurve.Serre.VeluInfinitySimpleFiberIdeal
public import FLT.FreyCurve.Serre.VeluInfinityRegularMorphism
public import FLT.Mazur.EvaluationKernelPullback

/-!
# The original Vélu identity fiber on an explicit scheme neighborhood

The exact ideal computation gives a Cartesian square of actual schemes.
Thus the local identity fiber is Spec K, with its reduced scheme structure.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry FLT.Mazur.WeierstrassIntegralChart

namespace WeierstrassCurve.Velu

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {K : Type} [Field K] [CharZero K] [DecidableEq K]
  (E : WeierstrassCurve K) (G : AddSubgroup E.toAffine.Point) [Fintype G]

/-- The additional principal restriction of the original infinity neighborhood. -/
def veluSimpleRestriction : Spec (.of (InfinitySimpleRing E G)) ⟶
    Spec (.of (InfinityTargetRing E G)) :=
  Spec.map (CommRingCat.ofHom (algebraMap (InfinityTargetRing E G) (InfinitySimpleRing E G)))

/-- The extra restriction is an actual open immersion. -/
instance veluSimpleRestriction_isOpenImmersion : IsOpenImmersion (veluSimpleRestriction E G) :=
  IsOpenImmersion.of_isLocalization (infinityTargetXFactor E G)

/-- The simple neighborhood embedded in the original source cubic. -/
def veluSimpleOpenImmersion : Spec (.of (InfinitySimpleRing E G)) ⟶ integralCurve E :=
  veluSimpleRestriction E G ≫ veluInfinityOpenImmersion E G

/-- The source embedding is open before any completion or passage to reduced schemes. -/
instance veluSimpleOpenImmersion_isOpenImmersion :
    IsOpenImmersion (veluSimpleOpenImmersion E G) :=
  inferInstanceAs (IsOpenImmersion (veluSimpleRestriction E G ≫ veluInfinityOpenImmersion E G))

/-- The original identity lifted to the smaller actual neighborhood. -/
def veluSimplePointLift : Spec (.of K) ⟶ Spec (.of (InfinitySimpleRing E G)) :=
  Spec.map (CommRingCat.ofHom (infinitySimpleEvaluation E G).toRingHom)

/-- The extra localization keeps the original infinity lift. -/
@[reassoc] theorem veluSimplePointLift_restriction :
    veluSimplePointLift E G ≫ veluSimpleRestriction E G = veluInfinityPointLift E G := by
  rw [veluSimplePointLift, veluSimpleRestriction, ← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  exact infinitySimpleEvaluation_algebraMap E G

variable (hodd : ∀ Q : G, Q ≠ 0 → Q ≠ -Q)

/-- The same original regular morphism on the smaller source neighborhood. -/
def veluSimpleRegularMorphism :
    Spec (.of (InfinitySimpleRing E G)) ⟶ integralCurve (curve E G) :=
  Spec.map (CommRingCat.ofHom (infinitySimpleChart E G hodd).toRingHom) ≫
    integralCurveChart (curve E G) 1

/-- Restriction retains the exact original infinity morphism. -/
@[reassoc] theorem veluSimpleRegularMorphism_restriction :
    veluSimpleRestriction E G ≫ veluInfinityRegularMorphism E G hodd =
      veluSimpleRegularMorphism E G hodd := by
  rw [veluSimpleRestriction, veluInfinityRegularMorphism, ← Spec.map_comp_assoc]
  rfl

/-- The local identity fiber is exactly the original reduced base-field point. -/
theorem veluSimpleRegularMorphism_identityFiber :
    IsPullback (veluSimplePointLift E G) (𝟙 (Spec (.of K)))
      (veluSimpleRegularMorphism E G hodd)
      (Spec.map (CommRingCat.ofHom (infinityEvaluation (curve E G)).toRingHom) ≫
        integralCurveChart (curve E G) 1) := by
  have h := FLT.Mazur.EvaluationKernelPullback.isPullback
    (infinitySimpleChart E G hodd) (infinityEvaluation (curve E G))
    (infinitySimpleEvaluation E G) (infinitySimpleChart_evaluation E G hodd)
    (infinitySimpleChart_fiber_ideal E G hodd)
  have h' : IsPullback
      (Spec.map (CommRingCat.ofHom (infinityEvaluation (curve E G)).toRingHom))
      (𝟙 (Spec (.of K))) (integralCurveChart (curve E G) 1)
      (Spec.map (CommRingCat.ofHom (infinityEvaluation (curve E G)).toRingHom) ≫
        integralCurveChart (curve E G) 1) :=
    IsPullback.of_vert_isIso_mono ⟨by simp⟩
  simpa only [Category.id_comp, veluSimplePointLift, veluSimpleRegularMorphism] using
    h.paste_vert h'

end WeierstrassCurve.Velu
