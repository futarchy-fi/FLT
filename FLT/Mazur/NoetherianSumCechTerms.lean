/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FiniteProductDirectSum
public import FLT.Mazur.NoetherianModuleSumInclusions
public import FLT.Mazur.CechSortingMaps

/-!
# Finite Cech terms of the original module-sheaf sum

For a finite cover, the original categorical Cech term of the sectionwise
sum has the original finite-support degree coordinates. This is a termwise
comparison; cohomology and scalar compatibility are subsequent constructions.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry Opposite
open Scheme.Modules FLT.Mazur.FCurve FLT.Mazur.CechSheafHZero
open scoped DirectSum

universe u

namespace FLT.Mazur.NoetherianModuleSum

variable {X : Scheme.{u}} [TopologicalSpace.NoetherianSpace X]
  (M : ℕ → X.Modules) {ι : Type u} [Fintype ι] (U : ι → X.Opens)

/-- Original categorical Cech coordinates of a sectionwise sum are finitely supported in degree. -/
def cechTermEquiv (q : ℕ) :
    (C U (moduleAbelianSheaf (sum M))).X q ≃+
      ⨁ n, (C U (moduleAbelianSheaf (M n))).X q :=
  (termEquiv U (moduleAbelianSheaf (sum M)) q).trans
    ((FiniteProductDirectSum.equiv ℤ (fun n a ↦ Γ(M n, V U q a))).symm.toAddEquiv.trans
      (DFinsupp.mapRange.addEquiv fun n ↦ (termEquiv U (moduleAbelianSheaf (M n)) q).symm))

/-- Every exchanged coordinate is precisely the original degree of the original section. -/
lemma cechTermEquiv_coordinate (q : ℕ) (x : (C U (moduleAbelianSheaf (sum M))).X q)
    (n : ℕ) (a : Fin (q + 1) → ι) :
    termEquiv U (moduleAbelianSheaf (M n)) q (cechTermEquiv M U q x n) a =
      DFinsupp.toFun (show ⨁ k, Γ(M k, V U q a) from
        termEquiv U (moduleAbelianSheaf (sum M)) q x a) n := by
  change termEquiv U (moduleAbelianSheaf (M n)) q
    ((termEquiv U (moduleAbelianSheaf (M n)) q).symm _) a = _
  rw [AddEquiv.apply_symm_apply]
  exact FiniteProductDirectSum.equiv_symm_apply ℤ _ _ n a

/-- A genuine degree inclusion has exactly its own categorical Cech coordinate. -/
lemma cechTermEquiv_inclusion (q n : ℕ) (x : (C U (moduleAbelianSheaf (M n))).X q) :
    cechTermEquiv M U q
      (((cechComplexFunctor U).map
        ((SheafOfModules.toSheaf X.ringCatSheaf).map (inclusion M n)).hom).f q x) =
      DirectSum.of (fun k ↦ (C U (moduleAbelianSheaf (M k))).X q) n x := by
  apply DFinsupp.ext
  intro k
  apply (termEquiv U (moduleAbelianSheaf (M k)) q).injective
  funext a
  rw [cechTermEquiv_coordinate, CechSortingMaps.termEquiv_naturality]
  change (DirectSum.of (fun k ↦ Γ(M k, V U q a)) n
    (termEquiv U (moduleAbelianSheaf (M n)) q x a)) k = _
  by_cases h : n = k
  · subst k
    rw [DirectSum.of_eq_same, DirectSum.of_eq_same]
  · rw [DirectSum.of_eq_of_ne _ _ _ (Ne.symm h),
      DirectSum.of_eq_of_ne _ _ _ (Ne.symm h), map_zero]
    rfl

end FLT.Mazur.NoetherianModuleSum
