/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.EquivalenceRelationFrameRebaseGeometric

/-!
# Relabeling complete geometric frames

Relabeling changes only the finite enumeration of the original fiber. The actual
geometric coordinate morphisms are retained, so completeness is preserved.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.EquivalenceRelationOrderedFrames
open RelativeOrderedTuples
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {A : Scheme.{0}} (E : Over A) [IsSeparated E.hom]
  (I : Type) [Fintype I] {T : Scheme.{0}} {b : T ⟶ A}

/-- Relabel an actual distinct frame without changing its displayed base. -/
def frameRelabel (t : Over.mk b ⟶ distinctScheme E I) (σ : Equiv.Perm I) :
    Over.mk b ⟶ distinctScheme E I :=
  Over.homMk (t.left ≫ (distinctAction E I σ).hom) (by
    rw [Category.assoc, distinctAction_base]
    exact t.w)

/-- Every original relation coordinate is retained under its new label. -/
@[reassoc] theorem frameRelabel_coordinate
    (t : Over.mk b ⟶ distinctScheme E I) (σ : Equiv.Perm I) (i : I) :
    (frameRelabel E I t σ ≫ distinctCoordinate E I i).left =
      (t ≫ distinctCoordinate E I (σ.symm i)).left := by
  change (t.left ≫ (distinctAction E I σ).hom) ≫ _ = _
  rw [Category.assoc, distinctAction_coordinate]
  rfl

variable {K : Type} [Field K] {b : Spec (.of K) ⟶ A}
  (t : Over.mk b ⟶ distinctScheme E I) (σ : Equiv.Perm I)

/-- Relabeling also retains the entire morphism into the original geometric fiber. -/
theorem frameRelabel_geometric (i : I) :
    geometricCoordinate E I (frameRelabel E I t σ) i =
      geometricCoordinate E I t (σ.symm i) := by
  apply pullback.hom_ext
  · rw [geometricCoordinate_fst, geometricCoordinate_fst, frameRelabel_coordinate]
  · rw [geometricCoordinate_snd, geometricCoordinate_snd]

/-- A permutation preserves completeness of the full original geometric fiber. -/
theorem frameRelabel_complete
    (ht : Function.Bijective (fun i ↦ geometricCoordinate E I t i default)) :
    Function.Bijective (fun i ↦ geometricCoordinate E I (frameRelabel E I t σ) i default) := by
  simpa only [frameRelabel_geometric, Function.comp_def] using ht.comp σ.symm.bijective

end FLT.Mazur.EquivalenceRelationOrderedFrames
