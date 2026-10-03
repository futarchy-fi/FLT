/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonLineNormalization
public import FLT.Mazur.ModuleCohomologyExact
public import FLT.Mazur.DivisorLineBundleSheaf
/-!
# Line-valued matching and actual polygon H0

Degree-zero cohomology of a polygon line is the kernel of the actual
normalization branch difference. This intrinsic kernel uses a common node
line; identifying it with a weighted polynomial kernel is a separate step.
-/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme.Modules
@[expose] public noncomputable section
universe u
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
namespace FLT.Mazur.PolygonLineHZero
open FCurve PolygonPinching PolygonLineNormalization
variable (K : Type u) [Field K] (n : ℕ) [NeZero n] (hn : 0 < n)
  {C : Over (Spec (.of K))} (p : components K n ⟶ C) (q : nodes K n ⟶ C)
  (h : IsPushout (toComponents K n hn) (toNodes K n) p q)
  (L : C.left.Modules) (hL : LocallyFreeRankOne L)
/-- The line normalization sequence remains short exact as abelian sheaves. -/
lemma abelian_shortExact :
    (moduleAbelianComplex (complex K n hn p q h L hL)).ShortExact :=
  CoherentDevissage.moduleToSheaf_shortExact (shortExact K n hn p q h L hL)
/-- Actual degree-zero cohomology is exact at the normalization term. -/
lemma exact : Function.Exact
    (moduleScalarHMap C.hom (complex K n hn p q h L hL).f 0)
    (moduleScalarHMap C.hom (complex K n hn p q h L hL).g 0) :=
  moduleScalarH_exact₂ _ (abelian_shortExact K n hn p q h L hL) C.hom 0
/-- Normalization pullback is injective on actual H0. -/
lemma inclusion_injective : Function.Injective
    (moduleScalarHMap C.hom (complex K n hn p q h L hL).f 0) :=
  moduleScalarHMap_zero_injective _ (abelian_shortExact K n hn p q h L hL) C.hom

/-- Actual H0 identifies linearly with the kernel of the node difference. -/
def kernelEquiv : ModuleScalarH C.hom L 0 ≃ₗ[K]
    LinearMap.ker (moduleScalarHMap C.hom (complex K n hn p q h L hL).g 0) :=
  (LinearEquiv.ofInjective _ (inclusion_injective K n hn p q h L hL)).trans
    (LinearEquiv.ofEq _ _ (exact K n hn p q h L hL).linearMap_ker_eq.symm)
/-- The kernel equivalence sends a class to its actual normalization pullback. -/
lemma kernelEquiv_val (x : ModuleScalarH C.hom L 0) :
    (kernelEquiv K n hn p q h L hL x).val =
      moduleScalarHMap C.hom ((pullbackPushforwardAdjunction p.left).unit.app L) 0 x := by
  change moduleScalarHMap C.hom (complex K n hn p q h L hL).f 0 x = _
  rw [inclusion_eq_unit]
  rfl
omit [NeZero n] in
/-- Membership in the intrinsic kernel means equality of the two node-line values. -/
lemma matching_iff (x : ModuleScalarH C.hom
    ((pushforward p.left).obj ((Scheme.Modules.pullback p.left).obj L)) 0) :
    moduleScalarHMap C.hom (complex K n hn p q h L hL).g 0 x = 0 ↔
      moduleScalarHMap C.hom (branch K n hn p q h L hL false) 0 x =
        moduleScalarHMap C.hom (branch K n hn p q h L hL true) 0 x := by
  have he : moduleScalarHMap C.hom (complex K n hn p q h L hL).g 0 x =
      moduleScalarHMap C.hom (branch K n hn p q h L hL false) 0 x -
        moduleScalarHMap C.hom (branch K n hn p q h L hL true) 0 x := by
    apply (moduleH0Equiv _).injective
    rw [map_sub]
    change moduleH0Equiv _ (moduleHMap _ 0 x) =
      moduleH0Equiv _ (moduleHMap _ 0 x) - moduleH0Equiv _ (moduleHMap _ 0 x)
    rw [moduleH0Equiv_naturality, moduleH0Equiv_naturality, moduleH0Equiv_naturality,
      difference_eq_branches]
    rfl
  rw [he, sub_eq_zero]

/-- Apply the intrinsic H0 kernel description to the actual sheaf of a divisor power. -/
def divisorPowerKernelEquiv (I : C.left.IdealSheafData) (hI : EffectiveCartier I) (m : ℕ) :
    ModuleScalarH C.hom (divisorLineBundle (I ^ m) (hI.pow m)) 0 ≃ₗ[K]
      LinearMap.ker (moduleScalarHMap C.hom
        (complex K n hn p q h (divisorLineBundle (I ^ m) (hI.pow m))
          (hI.pow m).divisorLineBundle_locallyFreeRankOne).g 0) :=
  kernelEquiv K n hn p q h _ (hI.pow m).divisorLineBundle_locallyFreeRankOne
end FLT.Mazur.PolygonLineHZero
