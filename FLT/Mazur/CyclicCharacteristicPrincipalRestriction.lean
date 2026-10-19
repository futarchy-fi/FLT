/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CyclicCharacteristicInvariantPrincipal
public import FLT.Mazur.CyclicCharacteristicComparisonNoetherian
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated

/-!
# Principal restriction on the original source and quotient

The actual source section ring on an invariant principal open is a
localization. Restrictions of invariant functions retain the original source
restriction and the defining function becomes a unit.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Opposite TopologicalSpace
namespace FLT.Mazur.CyclicCharacteristicOrbit
open CyclicCharacteristicAtlas
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable (n : ℕ) [NeZero n]
local notation "U" => normalizedDisjointSource n
local notation "A" => disjointComparisonArrows n
local notation "src" => disjointComparisonSource n
variable (W : Opens (Orbit n))
  (s : (invariantSheaf n).obj.obj (op W))
local notation "D" => invariantPrincipal n W s
local notation "j" => homOfLE (invariantPrincipal_le n W s)

/-- Restriction to the actual invariant principal neighborhood. -/
def principalRestriction : (invariantSheaf n).obj.obj (op W) →+*
    (invariantSheaf n).obj.obj (op D) :=
  ((invariantSheaf n).obj.map (j).op).hom

/-- Restriction of original source functions to that same neighborhood. -/
def principalSourceRestriction : (sourceSheaf n).obj.obj (op W) →+*
    (sourceSheaf n).obj.obj (op D) :=
  ((sourceSheaf n).obj.map (j).op).hom

/-- The invariant restriction uses exactly the original source restriction. -/
theorem principalRestriction_inclusion (a : (invariantSheaf n).obj.obj (op W)) :
    (invariantInclusion n).hom.app (op D) (principalRestriction n W s a) =
      principalSourceRestriction n W s ((invariantInclusion n).hom.app (op W) a) :=
  congrArg (fun k ↦ k a) ((invariantInclusion n).hom.naturality (j).op)

/-- The defining function becomes invertible on the principal neighborhood. -/
theorem principalRestriction_isUnit : IsUnit (principalRestriction n W s s) :=
  RingedSpace.isUnit_res_basicOpen (ringedSpace n) s

/-- The source section ring is the localization at the actual original invariant function. -/
theorem principalSourceRestriction_isLocalization :
    @IsLocalization.Away _ _ ((invariantInclusion n).hom.app (op W) s)
      ((sourceSheaf n).obj.obj (op D)) _ (principalSourceRestriction n W s).toAlgebra := by
  suffices H : ∀ (V : (U).Opens) (i : V ⟶ (pullOpen n W).val),
      V = (U).basicOpen ((invariantInclusion n).hom.app (op W) s) →
      @IsLocalization.Away _ _ ((invariantInclusion n).hom.app (op W) s)
        Γ(U, V) _ ((U).presheaf.map i.op).hom.toAlgebra from
    H _ _ (pullOpen_invariantPrincipal n W s)
  intro V i hV
  subst V
  exact isLocalization_basicOpen_of_qcqs (NoetherianSpace.isCompact _)
    (isQuasiSeparated_univ.of_subset (Set.subset_univ _)) _

end FLT.Mazur.CyclicCharacteristicOrbit
