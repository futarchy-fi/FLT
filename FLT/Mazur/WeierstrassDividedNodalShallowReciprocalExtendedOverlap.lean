/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedNodalShallowTangentExtendedOverlap
public import FLT.Mazur.WeierstrassDividedNodalShallowReciprocalOverlap
public import FLT.Mazur.WeierstrassDividedReciprocalExtendedAddition

/-!
# Shallow compatibility on a whole previously glued domain

Pull back the existing constituent cover and apply the actual overlap
comparisons on each member. This preserves the full shallow common source.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassDilatation WeierstrassIntegralChart
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] finiteGlobalModel finiteGlobalStructure rootShearCurve
  nodalSecondShear nodalSecondQuotient
variable {R S : Type} [CommRing R] [CommRing S] [Algebra R S] [IsDomain R]
  [IsBezout R] [IsLocalRing R] [IsNoetherianRing R] [Module.Flat R S]
  {W : WeierstrassCurve R} {π : R} {n k m : ℕ} (D : SplitNodeDepth W π m)
  (hdepth : 2 * k ≤ m) (hm : m ≤ 3 * k)
  (data : (i : Fin (n + 1)) → Data W π (0 + i.val)) (hr : m - 2 * k ≤ n)
  (d : Data W π k) (a c : Coordinate W (π ^ k) d.b3 d.b4 d.b6 →ₐ[R] S)
  (j : ℕ) (hj : j ≤ n) (hkj : k ≤ j) (hrj : m - 2 * k ≤ j)
local notation "hπ" => D.uniformizer_ne_zero
local notation "base" => finiteGlobalStructure hπ data j hj
local notation "U" => (base).smoothLocus
local notation "t" => (U).ι ≫ base
local notation "O" => nodalShallowAdditionOpen D hdepth hm data hr d a c
local notation "P" => suppliedDividedSmoothInputOpen d a c

local notation "V" => nodalShallowSmoothSourceOpen D hdepth hm data hr d a c
local notation "pair" => nodalShallowCommonInput D hdepth hm data hr d a c j hj hkj
local notation "Old" => finiteResolvedReciprocalExtendedOpen hπ data j hj
local notation "i" => finiteResolvedReciprocalExtendedInput hπ data j hj

/-- The whole reciprocalextended law agrees on every flat shallow-common-source overlap. -/
theorem nodalShallowCommonOutput_reciprocalExtendedOverlap {X : Scheme}
    (p : X ⟶ (Old).toScheme) (q : X ⟶ (V).toScheme) [Flat q]
    (hpq : p ≫ (Old).ι = q ≫ pair) :
    p ≫ finiteResolvedReciprocalExtendedPartialAddition hπ data j hj =
      q ≫ nodalShallowCommonOutput D hdepth hm data hr d a c j hj hrj := by
  apply Scheme.Cover.hom_ext ((openImageUnionCover i).pullback₁ p)
  intro b
  change Bool at b
  let f := pullback.fst p (openImageUnionMap i b)
  let g := pullback.snd p (openImageUnionMap i b)
  have hp : f ≫ p = g ≫ openImageUnionMap i b := pullback.condition
  have he : g ≫ i b = (f ≫ q) ≫ pair := by
    symm
    rw [Category.assoc, ← hpq, ← Category.assoc, hp, Category.assoc]
    exact congrArg (g ≫ ·) (openImageUnionMap_fac i b)
  cases b
  · have h := nodalShallowCommonOutput_tangentExtendedOverlap
      D hdepth hm data hr d a c j hj hkj hrj g (f ≫ q) he
    rw [← finiteResolvedReciprocalExtendedPartialAddition_old hπ data j hj,
      ← Category.assoc, ← hp, Category.assoc] at h
    exact h
  · have h := nodalShallowCommonOutput_reciprocalOverlap
      D hdepth hm data hr d a c j hj hkj hrj g (f ≫ q) he
    rw [← finiteResolvedReciprocalExtendedPartialAddition_reciprocal hπ data j hj,
      ← Category.assoc, ← hp, Category.assoc] at h
    exact h

end FLT.Mazur.WeierstrassDividedDepth
