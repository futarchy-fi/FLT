/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonSinglePointNodeFrame
public import FLT.Mazur.PolygonComponentHZeroMatching
public import FLT.Mazur.PolygonSingleExceptionalMatching

/-!
# Single-point matching as actual scalar endpoint equations

Express the common-node equations in the canonical frames. Only the marked
component can have different endpoint scalars. Cyclic propagation therefore
forces every scalar to equal its marked infinity value.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.Scheme.Modules

namespace FLT.Mazur.PolygonSinglePointScalarMatching

open FCurve PolygonPinching PolygonSinglePointLineNormalization
open PolygonNormalizationLinearSections PolygonSinglePointHZeroCoordinates
open PolygonSinglePointEndpointScalars PolygonSinglePointNodeFrame LinePullbackRestriction
open PolygonComponentHZeroEndpoints

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

attribute [local irreducible] h0Along

variable (K : Type) [Field K] (n : ℕ) [NeZero n] (hn : 0 < n)
  {C : Over (Spec (.of K))} (p : components K n ⟶ C) (q : nodes K n ⟶ C)
  (h : IsPushout (toComponents K n hn) (toNodes K n) p q)
  (a : Kˣ) (j : Fin n) (m : ℕ)

/-- The actual family of component classes for the original single-point power. -/
abbrev Family := ∀ i : Fin n, ModuleScalarH (component K).hom
  (componentLine K n p (pointPower K n hn p q h a j m) i) 0

/-- The scalar at the zero endpoint, in the original canonical frame. -/
def zeroScalar (v : Family K n hn p q h a j m) (i : Fin n) : K :=
  if hi : i = j then
    (ProjectiveLineMarkedHZero.polynomialEquiv K a m
      (ownEquiv K n hn p q h a j m (hi ▸ v i))).val.eval 0 / (-(a : K)) ^ m
  else otherEquiv K n hn p q h a j m ⟨i, hi⟩ (v i)

/-- The scalar at infinity, in the same original canonical frame. -/
def infinityScalar (v : Family K n hn p q h a j m) (i : Fin n) : K :=
  if hi : i = j then
    (ProjectiveLineMarkedHZero.polynomialEquiv K a m
      (ownEquiv K n hn p q h a j m (hi ▸ v i))).val.coeff m
  else otherEquiv K n hn p q h a j m ⟨i, hi⟩ (v i)

/-- The marked zero scalar is its normalized polynomial value. -/
theorem zeroScalar_self (v : Family K n hn p q h a j m) :
    zeroScalar K n hn p q h a j m v j =
      (ProjectiveLineMarkedHZero.polynomialEquiv K a m
        (ownEquiv K n hn p q h a j m (v j))).val.eval 0 / (-(a : K)) ^ m :=
  dite_eq_left rfl

/-- The marked infinity scalar is its leading coefficient. -/
theorem infinityScalar_self (v : Family K n hn p q h a j m) :
    infinityScalar K n hn p q h a j m v j =
      (ProjectiveLineMarkedHZero.polynomialEquiv K a m
        (ownEquiv K n hn p q h a j m (v j))).val.coeff m :=
  dite_eq_left rfl

/-- The unmarked zero scalar is its constant coordinate. -/
theorem zeroScalar_other (v : Family K n hn p q h a j m) (i : Fin n) (hi : i ≠ j) :
    zeroScalar K n hn p q h a j m v i = otherEquiv K n hn p q h a j m ⟨i, hi⟩ (v i) :=
  dite_eq_right hi

/-- The unmarked infinity scalar is the same constant coordinate. -/
theorem infinityScalar_other (v : Family K n hn p q h a j m) (i : Fin n) (hi : i ≠ j) :
    infinityScalar K n hn p q h a j m v i = otherEquiv K n hn p q h a j m ⟨i, hi⟩ (v i) :=
  dite_eq_right hi

/-- Every unmarked component has equal endpoint scalars. -/
theorem off_eq (v : Family K n hn p q h a j m) (i : Fin n) (hi : i ≠ j) :
    zeroScalar K n hn p q h a j m v i = infinityScalar K n hn p q h a j m v i := by
  rw [zeroScalar_other K n hn p q h a j m v i hi,
    infinityScalar_other K n hn p q h a j m v i hi]

/-- The scalar formula at zero lands in the original target line. -/
theorem zero_value (v : Family K n hn p q h a j m) (i : Fin n) (t : point K ⟶ C)
    (w : ProjectiveLine.zeroSection K ≫ (componentι K n i ≫ p) = t) :
    moduleScalarH0Equiv (point K).hom _
        (h0Along (ProjectiveLine.zeroSection K) (componentι K n i ≫ p) t w _ (v i)) =
      (Scheme.ΓSpecIso (.of K)).inv (zeroScalar K n hn p q h a j m v i) •
        pullGlobal t.left _ (canonicalSection K n hn p q h a j m) := by
  by_cases hi : i = j
  · subst i
    rw [zeroScalar_self]
    exact own_zero K n hn p q h a j m t w (v j)
  · rw [zeroScalar_other K n hn p q h a j m v i hi]
    have he := other_endpoint K n hn p q h a j m ⟨i, hi⟩
      (ProjectiveLine.zeroSection K) t w (v i)
    exact he

/-- The scalar formula at infinity lands in the same original target line. -/
theorem infinity_value (v : Family K n hn p q h a j m) (i : Fin n) (t : point K ⟶ C)
    (w : ProjectiveLine.infinitySection K ≫ (componentι K n i ≫ p) = t) :
    moduleScalarH0Equiv (point K).hom _
        (h0Along (ProjectiveLine.infinitySection K) (componentι K n i ≫ p) t w _ (v i)) =
      (Scheme.ΓSpecIso (.of K)).inv (infinityScalar K n hn p q h a j m v i) •
        pullGlobal t.left _ (canonicalSection K n hn p q h a j m) := by
  by_cases hi : i = j
  · subst i
    rw [infinityScalar_self]
    exact own_infinity K n hn p q h a j m t w (v j)
  · rw [infinityScalar_other K n hn p q h a j m v i hi]
    have he := other_endpoint K n hn p q h a j m ⟨i, hi⟩
      (ProjectiveLine.infinitySection K) t w (v i)
    exact he

/-- The actual component gluing kernel is exactly the cyclic scalar matching condition. -/
theorem mem_kernel_iff (v : Family K n hn p q h a j m) :
    v ∈ LinearMap.ker (PolygonComponentHZeroMatching.difference K n hn p q h
      (pointPower K n hn p q h a j m)) ↔
      ∀ i, zeroScalar K n hn p q h a j m v i =
        infinityScalar K n hn p q h a j m v (next hn i) := by
  rw [PolygonComponentHZeroMatching.mem_kernel_iff]
  apply forall_congr'
  intro i
  rw [← (moduleScalarH0Equiv (point K).hom
    (nodeLine K n q (pointPower K n hn p q h a j m) i)).injective.eq_iff]
  change moduleScalarH0Equiv _ _ (h0Along _ _ _ _ _ _) =
    moduleScalarH0Equiv _ _ (h0Along _ _ _ _ _ _) ↔ _
  rw [zero_value, infinity_value, (scalar_cancel K n hn p q h a j m i).eq_iff]

/-- Matching forces all canonical endpoint scalars to the marked infinity value. -/
theorem matching_constants (v : Family K n hn p q h a j m)
    (hv : v ∈ LinearMap.ker (PolygonComponentHZeroMatching.difference K n hn p q h
      (pointPower K n hn p q h a j m))) (i : Fin n) :
    zeroScalar K n hn p q h a j m v i = infinityScalar K n hn p q h a j m v j ∧
      infinityScalar K n hn p q h a j m v i = infinityScalar K n hn p q h a j m v j :=
  PolygonSingleExceptionalMatching.all_eq hn j _ _
    (off_eq K n hn p q h a j m v) ((mem_kernel_iff K n hn p q h a j m v).mp hv) i

end FLT.Mazur.PolygonSinglePointScalarMatching
