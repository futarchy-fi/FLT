/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AdditiveComplexDirectSum
public import FLT.Mazur.ProjectiveTwistCechCohomologySumHomology
public import Mathlib.Algebra.Homology.ShortComplex.Ab

/-!
# Homology of the original additive direct-sum complex

The integral module structure on abelian groups lets the existing
finite-support kernel and quotient construction compute this sum's homology.
No exactness or cohomology-commutation hypothesis is required.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory
open scoped DirectSum

namespace FLT.Mazur.AdditiveComplexDirectSum

open ProjectiveSpace.TwistCechCohomology

/-- An additive short complex with its canonical integral linear structure. -/
def integralShort (S : ShortComplex AddCommGrpCat.{0}) : ShortComplex (ModuleCat ℤ) where
  X₁ := ModuleCat.of ℤ S.X₁
  X₂ := ModuleCat.of ℤ S.X₂
  X₃ := ModuleCat.of ℤ S.X₃
  f := ModuleCat.ofHom S.f.hom.toIntLinearMap
  g := ModuleCat.ofHom S.g.hom.toIntLinearMap
  zero := by
    apply ConcreteCategory.hom_ext
    intro x
    exact S.ab_zero_apply x

/-- Additive and integral module homology have the same original cycles and boundaries. -/
def integralHomologyEquiv (S : ShortComplex AddCommGrpCat.{0}) :
    S.homology ≃+ (integralShort S).homology :=
  S.abHomologyIso.addCommGroupIsoToAddEquiv.trans
    (((forget₂ (ModuleCat ℤ) AddCommGrpCat).mapIso
      (integralShort S).moduleCatHomologyIso.symm).addCommGroupIsoToAddEquiv)

variable (K : ℕ → CochainComplex AddCommGrpCat.{0} ℕ)

/-- The actual short complex of the additive sum has the original componentwise module maps. -/
def sumIntegralShortIso (q : ℕ) :
    integralShort ((complex K).sc q) ≅
      exponentShortSum ℤ (fun n ↦ integralShort ((K n).sc q)) :=
  ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _) (by
    apply ConcreteCategory.hom_ext
    intro x
    rfl) (by
    apply ConcreteCategory.hom_ext
    intro x
    rfl)

/-- Homology of the actual additive sum is the sum of the original component homologies. -/
def homologyEquiv (q : ℕ) :
    (complex K).homology q ≃+ ⨁ n, (K n).homology q := by
  let e := ((forget₂ (ModuleCat ℤ) AddCommGrpCat).mapIso
    (ShortComplex.homologyMapIso (sumIntegralShortIso K q))).addCommGroupIsoToAddEquiv
  let e' := ((forget₂ (ModuleCat ℤ) AddCommGrpCat).mapIso
    (shortSumHomologyIso ℤ (fun n ↦ integralShort ((K n).sc q)))).addCommGroupIsoToAddEquiv
  exact (integralHomologyEquiv ((complex K).sc q)).trans
    (e.trans (e'.trans (DFinsupp.mapRange.addEquiv fun n ↦
      (integralHomologyEquiv ((K n).sc q)).symm)))

end FLT.Mazur.AdditiveComplexDirectSum
