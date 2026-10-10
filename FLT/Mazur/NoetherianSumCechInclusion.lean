/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.NoetherianSumCechCohomology
public import FLT.Mazur.AdditiveComplexSumHomologyInclusion

/-!
# Original sheaf inclusions in the all-degree cohomology comparison

The chain-level inclusion identity passes through direct-sum homology and
the natural affine-cover comparison. Each summand keeps its original map.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry
open Scheme.Modules FLT.Mazur.FCurve FLT.Mazur.CechSheafHZero
open scoped DirectSum

namespace FLT.Mazur.NoetherianModuleSum

variable {X : Scheme.{0}} [TopologicalSpace.NoetherianSpace X]
  (M : ℕ → X.Modules) {ι : Type} [Fintype ι] (U : ι → X.Opens)

attribute [local irreducible] cechSumIso AdditiveComplexDirectSum.homologyEquiv

/-- The original degree inclusion is retained on Cech cohomology in every degree. -/
lemma cechCohomologyEquiv_inclusion (q n : ℕ)
    (x : CH U (moduleAbelianSheaf (M n)) q) :
    cechCohomologyEquiv M U q
        (CHmap U ((SheafOfModules.toSheaf X.ringCatSheaf).map (inclusion M n)) q x) =
      DirectSum.of (fun k ↦ CH U (moduleAbelianSheaf (M k)) q) n x := by
  let φ := (cechComplexFunctor U).map
    ((SheafOfModules.toSheaf X.ringCatSheaf).map (inclusion M n)).hom
  have hi : φ ≫
        (cechSumIso M U).inv =
      AdditiveComplexDirectSum.inclusion (fun k ↦ C U (moduleAbelianSheaf (M k))) n := by
    dsimp only [φ]
    rw [← inclusion_cechSumIso, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  change AdditiveComplexDirectSum.homologyEquiv
    (fun k ↦ C U (moduleAbelianSheaf (M k))) q
    (HomologicalComplex.homologyMap (cechSumIso M U).inv q
      (HomologicalComplex.homologyMap φ q x)) = _
  rw [← ConcreteCategory.comp_apply
    (HomologicalComplex.homologyMap φ q)
    (HomologicalComplex.homologyMap (cechSumIso M U).inv q),
    ← HomologicalComplex.homologyMap_comp, hi]
  exact AdditiveComplexDirectSum.homologyEquiv_inclusion
    (fun k ↦ C U (moduleAbelianSheaf (M k))) q n x

variable [X.IsSeparated] [∀ n, (M n).IsQuasicoherent] [(sum M).IsQuasicoherent]
  (hU : ∀ i, IsAffineOpen (U i)) (hCover : iSup U = ⊤)

/-- Every original sheaf inclusion is retained by the actual all-degree cohomology equivalence. -/
lemma cohomologyEquiv_inclusion (q n : ℕ) (x : ModuleH (M n) q) :
    cohomologyEquiv M U hU hCover q (moduleHMap (inclusion M n) q x) =
      DirectSum.of (fun k ↦ ModuleH (M k) q) n x := by
  obtain ⟨x, rfl⟩ := (affineCoverCechEquiv (M n) U hU hCover q).surjective x
  rw [← affineCoverCechEquiv_naturality (M n) U hU hCover (inclusion M n)]
  change (DFinsupp.mapRange.addEquiv fun k ↦
    (affineCoverCechEquiv (M k) U hU hCover q).toAddEquiv)
      (cechCohomologyEquiv M U q
        ((affineCoverCechEquiv (sum M) U hU hCover q).symm
          ((affineCoverCechEquiv (sum M) U hU hCover q) _))) = _
  rw [LinearEquiv.symm_apply_apply, cechCohomologyEquiv_inclusion]
  exact DirectSum.map_of
    (fun k ↦ (affineCoverCechEquiv (M k) U hU hCover q).toAddEquiv.toAddMonoidHom) n x

end FLT.Mazur.NoetherianModuleSum
