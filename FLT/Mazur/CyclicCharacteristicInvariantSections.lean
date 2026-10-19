/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CyclicCharacteristicInvariantSheaf
public import FLT.Mazur.CyclicCharacteristicOrbitOpens
public import Mathlib.CategoryTheory.Limits.Types.Equalizers

/-!
# Sections of the invariant regular-function sheaf

On every actual orbit open, invariant sections are exactly source regular
functions whose pullbacks along the two original relation projections agree.
The second pullback includes the necessary equality of the open domains.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
namespace FLT.Mazur.CyclicCharacteristicOrbit
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CyclicCharacteristicAtlas
variable (n : ℕ) [NeZero n]
local notation "U" => normalizedDisjointSource n
local notation "A" => disjointComparisonArrows n
local notation "src" => disjointComparisonSource n
local notation "tgt" => disjointComparisonTarget n
variable (W : TopologicalSpace.Opens (Orbit n))

/-- The first sheaf comparison is the original pullback on the invariant source open. -/
theorem firstRestriction_app :
    (firstRestriction n).hom.app (op W) = (src).app (pullOpen n W).val := rfl

/-- The second sheaf comparison is the original pullback with its open domain identified. -/
theorem secondRestriction_app :
    (secondRestriction n).hom.app (op W) = (tgt).app (pullOpen n W).val ≫
      (A).presheaf.map (eqToHom (congrArg op (pullOpen_preimage_eq n W).symm)) := by
  change (tgt).app (pullOpen n W).val ≫
    (TopCat.Presheaf.pushforwardEq (relation_quotientMap n).symm
      (A).presheaf).hom.app (op W) = _
  rw [TopCat.Presheaf.pushforwardEq_hom_app]

/-- Every invariant sheaf section satisfies the actual two pullback equations. -/
theorem invariantSection_condition (s : (invariantSheaf n).obj.obj (op W)) :
    (firstRestriction n).hom.app (op W) ((invariantInclusion n).hom.app (op W) s) =
      (secondRestriction n).hom.app (op W) ((invariantInclusion n).hom.app (op W) s) :=
  congrArg (fun k ↦ k.hom.app (op W) s) (invariantInclusion_condition n)

/-- Every source section satisfying the relation has a unique invariant section above it. -/
theorem invariantSection_existsUnique (s : (sourceSheaf n).obj.obj (op W))
    (hs : (firstRestriction n).hom.app (op W) s =
      (secondRestriction n).hom.app (op W) s) :
    ∃! t : (invariantSheaf n).obj.obj (op W),
      (invariantInclusion n).hom.app (op W) t = s := by
  have h₁ := isLimitForkMapOfIsLimit (TopCat.Sheaf.forget _ _) (equalizer.condition _ _)
    (equalizerIsEqualizer (firstRestriction n) (secondRestriction n))
  have h₂ := isLimitForkMapOfIsLimit ((evaluation _ _).obj (op W)) _ h₁
  have h₃ := isLimitForkMapOfIsLimit (forget CommRingCat) _ h₂
  exact Types.unique_of_type_equalizer _ _ h₃ s hs

/-- Invariant sections are determined by their actual source regular functions. -/
theorem invariantSection_ext {s t : (invariantSheaf n).obj.obj (op W)}
    (h : (invariantInclusion n).hom.app (op W) s =
      (invariantInclusion n).hom.app (op W) t) : s = t := by
  obtain ⟨v, _, hv⟩ := invariantSection_existsUnique n W
    ((invariantInclusion n).hom.app (op W) t) (invariantSection_condition n W t)
  exact (hv s h).trans (hv t rfl).symm

/-- Invariant functions, expressed entirely in original scheme regular-function coordinates. -/
theorem invariantSection_iff (s : Γ(U, (pullOpen n W).val)) :
    (∃! t : (invariantSheaf n).obj.obj (op W),
      (invariantInclusion n).hom.app (op W) t = s) ↔
        (src).app (pullOpen n W).val s =
          (A).presheaf.map
            (eqToHom (congrArg op (pullOpen_preimage_eq n W).symm))
              ((tgt).app (pullOpen n W).val s) := by
  constructor
  · rintro ⟨t, rfl, _⟩
    have h := invariantSection_condition n W t
    rw [firstRestriction_app, secondRestriction_app] at h
    exact h
  · intro hs
    apply invariantSection_existsUnique
    rw [firstRestriction_app, secondRestriction_app]
    exact hs

end FLT.Mazur.CyclicCharacteristicOrbit
