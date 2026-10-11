/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonSinglePointMatchingCoordinates

/-!
# The single-point polygon kernel is the marked equal-endpoint kernel

Restrict a matched component family to its marked H0 class. The remaining
components have uniquely determined constant values, so this map is a linear
equivalence. The inverse uses the proved component-coordinate equivalence.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace FLT.Mazur.PolygonSinglePointLoopKernel

open FCurve PolygonPinching PolygonSinglePointLineNormalization
open PolygonSinglePointScalarMatching PolygonSinglePointMatchingCoordinates

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable (K : Type) [Field K] (n : ℕ) [NeZero n] (hn : 0 < n)
  {C : Over (Spec (.of K))} (p : components K n ⟶ C) (q : nodes K n ⟶ C)
  (h : IsPushout (toComponents K n hn) (toNodes K n) p q)
  (a : Kˣ) (j : Fin n) (m : ℕ)

/-- The marked restriction of an actual matched component family. -/
def restriction :
    LinearMap.ker (PolygonComponentHZeroMatching.difference K n hn p q h
      (pointPower K n hn p q h a j m)) →ₗ[K]
        LinearMap.ker (ProjectiveLinePointLoopMatching.difference K a m) where
  toFun v := ⟨(familyCoordinates K n hn p q h a j m v.val).1,
    ((matching_iff K n hn p q h a j m v.val).mp v.property).1⟩
  map_add' v w := Subtype.ext
    (congrArg Prod.fst ((familyCoordinates K n hn p q h a j m).map_add v.val w.val))
  map_smul' r v := Subtype.ext
    (congrArg Prod.fst ((familyCoordinates K n hn p q h a j m).map_smul r v.val))

/-- The marked class uniquely determines every matched unmarked component. -/
theorem restriction_injective : Function.Injective (restriction K n hn p q h a j m) := by
  intro v w he
  apply Subtype.ext
  apply (familyCoordinates K n hn p q h a j m).injective
  apply Prod.ext
  · exact congrArg Subtype.val he
  · funext i
    have hv := ((matching_iff K n hn p q h a j m v.val).mp v.property).2 i
    have hw := ((matching_iff K n hn p q h a j m w.val).mp w.property).2 i
    have hx : (familyCoordinates K n hn p q h a j m v.val).1 =
        (familyCoordinates K n hn p q h a j m w.val).1 := congrArg Subtype.val he
    exact hv.trans ((congrArg (fun x ↦
      (ProjectiveLineMarkedHZero.polynomialEquiv K a m x).val.coeff m) hx).trans hw.symm)

/-- Any actual marked class with equal endpoints extends to a matched component family. -/
theorem restriction_surjective : Function.Surjective (restriction K n hn p q h a j m) := by
  intro x
  let e := familyCoordinates K n hn p q h a j m
  let c := (ProjectiveLineMarkedHZero.polynomialEquiv K a m x.val).val.coeff m
  let v := e.symm (x.val, fun _ ↦ c)
  have hv : e v = (x.val, fun _ ↦ c) := e.apply_symm_apply _
  have hm : v ∈ LinearMap.ker (PolygonComponentHZeroMatching.difference K n hn p q h
      (pointPower K n hn p q h a j m)) := by
    rw [matching_iff]
    change (e v).1 ∈ _ ∧ ∀ i, (e v).2 i = _
    rw [hv]
    exact ⟨x.property, fun _ ↦ rfl⟩
  refine ⟨⟨v, hm⟩, Subtype.ext ?_⟩
  exact congrArg Prod.fst hv

/-- The actual single-point component matching kernel is the P1 equal-endpoint kernel. -/
def equiv :
    LinearMap.ker (PolygonComponentHZeroMatching.difference K n hn p q h
      (pointPower K n hn p q h a j m)) ≃ₗ[K]
        LinearMap.ker (ProjectiveLinePointLoopMatching.difference K a m) :=
  LinearEquiv.ofBijective (restriction K n hn p q h a j m)
    ⟨restriction_injective K n hn p q h a j m, restriction_surjective K n hn p q h a j m⟩

/-- The equivalence is the original marked coordinate, with no chosen cohomology basis. -/
theorem equiv_val (v : LinearMap.ker (PolygonComponentHZeroMatching.difference K n hn p q h
    (pointPower K n hn p q h a j m))) :
    (equiv K n hn p q h a j m v).val =
      (familyCoordinates K n hn p q h a j m v.val).1 := rfl

end FLT.Mazur.PolygonSinglePointLoopKernel
