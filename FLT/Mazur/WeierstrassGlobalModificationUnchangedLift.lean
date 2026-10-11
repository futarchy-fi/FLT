/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassGlobalModificationXOpen

/-!
# Uniqueness of lifts over unchanged output opens

The full pullback squares force every lift above an original unchanged open
into its prescribed copy in the modification. This applies to arbitrary
source schemes, including the actual intersections of action-cover members.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

namespace FLT.Mazur.WeierstrassGlobalModification

open WeierstrassIntegralChart
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u

/-- An identity pullback determines every map above its unchanged base open. -/
theorem lift_eq_of_identity_pullback {U X Y T : Scheme.{u}}
    {e : U ⟶ X} {j : U ⟶ Y} {c : X ⟶ Y}
    (h : IsPullback (𝟙 U) e j c) (p : T ⟶ U) (f : T ⟶ X)
    (hf : p ≫ j = f ≫ c) : f = p ≫ e := by
  have hp : h.lift p f hf = p := by simpa using h.lift_fst p f hf
  rw [← hp]
  exact (h.lift_snd p f hf).symm

variable {R : Type u} [CommRing R] [IsDomain R] [IsBezout R]
  (W : WeierstrassCurve R) (s b3 b4 b6 : R)
  (h3 : W.a₃ = s * b3) (h4 : W.a₄ = s * b4) (h6 : W.a₆ = s ^ 2 * b6) (hs : s ≠ 0)
  {T : Scheme.{u}}

/-- Every lift above an original infinity output is the unchanged infinity lift. -/
theorem lift_eq_infinity (p : T ⟶ chartScheme W 1)
    (f : T ⟶ model W s b3 b4 b6 h3 h4 h6 hs)
    (hf : f ≫ contraction W s b3 b4 b6 h3 h4 h6 hs = p ≫ integralCurveChart W 1) :
    f = p ≫ infinityChart W s b3 b4 b6 h3 h4 h6 hs :=
  lift_eq_of_identity_pullback (infinity_isPullback W s b3 b4 b6 h3 h4 h6 hs) p f hf.symm

/-- Every lift above an original center principal open is its prescribed unchanged lift. -/
theorem lift_eq_originalOpen (a : Coordinate W 2)
    (ha : a ∈ WeierstrassDilatation.modificationCenter W s)
    (p : T ⟶ Spec (.of (Localization.Away a)))
    (f : T ⟶ model W s b3 b4 b6 h3 h4 h6 hs)
    (hf : f ≫ contraction W s b3 b4 b6 h3 h4 h6 hs =
      p ≫ PrincipalAffineRefinement.inclusion a ≫ integralCurveChart W 2) :
    f = p ≫ originalOpen W s b3 b4 b6 h3 h4 h6 hs a ha :=
  lift_eq_of_identity_pullback
    (originalOpen_isPullback W s b3 b4 b6 h3 h4 h6 hs a ha) p f hf.symm

/-- Every lift above the original X-chart is its unchanged lift, for any source scheme. -/
theorem lift_eq_originalX (p : T ⟶ chartScheme W 0)
    (f : T ⟶ model W s b3 b4 b6 h3 h4 h6 hs)
    (hf : f ≫ contraction W s b3 b4 b6 h3 h4 h6 hs = p ≫ integralCurveChart W 0) :
    f = p ≫ originalXChart W s b3 b4 b6 h3 h4 h6 hs := by
  unfold originalXChart
  rw [← Category.assoc, ← Category.assoc]
  apply lift_eq_originalOpen
  rw [hf, Category.assoc, Category.assoc]
  change p ≫ integralCurveChart W 0 = p ≫ inv (overlapInclusion W 0 2) ≫
    chartTransition W 0 2 ≫ overlapInclusion W 2 0 ≫ integralCurveChart W 2
  rw [integralCurveChart_compatibility, IsIso.inv_hom_id_assoc]

end FLT.Mazur.WeierstrassGlobalModification
