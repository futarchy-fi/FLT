/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.NoetherianSumCechTerms
public import FLT.Mazur.AdditiveComplexDirectSum

/-!
# The original Cech complex is the sum of the original degree complexes

The finite-cover term exchange commutes with every actual differential,
by naturality of the original degree inclusions. This constructs a genuine
complex isomorphism, without presuming any cohomology comparison.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry
open Scheme.Modules FLT.Mazur.FCurve FLT.Mazur.CechSheafHZero
open scoped DirectSum

universe u

namespace FLT.Mazur.NoetherianModuleSum

variable {X : Scheme.{u}} [TopologicalSpace.NoetherianSpace X]
  (M : ℕ → X.Modules) {ι : Type u} [Fintype ι] (U : ι → X.Opens)

/-- Inverse coordinates of one original degree are induced by the actual sheaf inclusion. -/
lemma cechTermEquiv_symm_of (q n : ℕ) (x : (C U (moduleAbelianSheaf (M n))).X q) :
    (cechTermEquiv M U q).symm
      (DirectSum.of (fun k ↦ (C U (moduleAbelianSheaf (M k))).X q) n x) =
      (((cechComplexFunctor U).map
        ((SheafOfModules.toSheaf X.ringCatSheaf).map (inclusion M n)).hom).f q x) := by
  apply (cechTermEquiv M U q).injective
  rw [AddEquiv.apply_symm_apply, cechTermEquiv_inclusion]

/-- The original coordinate exchange intertwines all Cech differentials. -/
lemma cechTermEquiv_symm_d (p q : ℕ)
    (x : ⨁ n, (C U (moduleAbelianSheaf (M n))).X p) :
    (cechTermEquiv M U q).symm
        ((AdditiveComplexDirectSum.complex (fun n ↦ C U (moduleAbelianSheaf (M n)))).d p q x) =
      (C U (moduleAbelianSheaf (sum M))).d p q ((cechTermEquiv M U p).symm x) := by
  induction x using DirectSum.induction_on with
  | zero => simp only [map_zero]
  | add x y hx hy => simp only [map_add, hx, hy]
  | of n x =>
    rw [AdditiveComplexDirectSum.d_of, cechTermEquiv_symm_of, cechTermEquiv_symm_of]
    exact (ConcreteCategory.congr_hom
      (((cechComplexFunctor U).map
        ((SheafOfModules.toSheaf X.ringCatSheaf).map (inclusion M n)).hom).comm p q) x).symm

/-- The actual finite-cover complex of the sheaf sum is the sum of the actual degree complexes. -/
def cechSumIso :
    AdditiveComplexDirectSum.complex (fun n ↦ C U (moduleAbelianSheaf (M n))) ≅
      C U (moduleAbelianSheaf (sum M)) :=
  HomologicalComplex.Hom.isoOfComponents
    (fun q ↦ (cechTermEquiv M U q).symm.toAddCommGrpIso) (by
      intro p q _
      apply ConcreteCategory.hom_ext
      intro x
      exact (cechTermEquiv_symm_d M U p q x).symm)

/-- The complex comparison retains the actual degree inclusions. -/
lemma inclusion_cechSumIso (n : ℕ) :
    AdditiveComplexDirectSum.inclusion (fun k ↦ C U (moduleAbelianSheaf (M k))) n ≫
        (cechSumIso M U).hom =
      (cechComplexFunctor U).map
        ((SheafOfModules.toSheaf X.ringCatSheaf).map (inclusion M n)).hom := by
  ext q : 1
  apply ConcreteCategory.hom_ext
  intro x
  exact cechTermEquiv_symm_of M U q n x

end FLT.Mazur.NoetherianModuleSum
