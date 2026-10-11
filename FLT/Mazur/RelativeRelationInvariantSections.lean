/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.RelativeRelationInvariantSheaf
public import FLT.Mazur.RelativeRelationOrbitOpens
public import Mathlib.CategoryTheory.Limits.Types.Equalizers

/-!
# Sections of the invariant regular-function sheaf

On every actual orbit open, invariant sections are exactly source regular
functions whose pullbacks along the two original relation projections agree.
The second pullback includes the necessary equality of the open domains.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
universe u
namespace FLT.Mazur.RelativeRelationOrbit
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {S : Scheme.{u}} {A U : Over S} {p q : A ⟶ U}
  (e : CategoryTheory.EquivalenceRelation p q)
  (W : TopologicalSpace.Opens (Orbit e))

/-- The first sheaf comparison is the original pullback on the invariant source open. -/
theorem firstRestriction_app :
    (firstRestriction e).hom.app (op W) = p.left.app (pullOpen e W).val := rfl

/-- The second sheaf comparison is the original pullback with its open domain identified. -/
theorem secondRestriction_app :
    (secondRestriction e).hom.app (op W) = q.left.app (pullOpen e W).val ≫
      A.left.presheaf.map (eqToHom (congrArg op (pullOpen_preimage_eq e W).symm)) := by
  change q.left.app (pullOpen e W).val ≫
    (TopCat.Presheaf.pushforwardEq (relation_quotientMap e).symm
      A.left.presheaf).hom.app (op W) = _
  rw [TopCat.Presheaf.pushforwardEq_hom_app]

/-- Every invariant sheaf section satisfies the actual two pullback equations. -/
theorem invariantSection_condition (s : (invariantSheaf e).obj.obj (op W)) :
    (firstRestriction e).hom.app (op W) ((invariantInclusion e).hom.app (op W) s) =
      (secondRestriction e).hom.app (op W) ((invariantInclusion e).hom.app (op W) s) :=
  congrArg (fun k ↦ k.hom.app (op W) s) (invariantInclusion_condition e)

/-- Every source section satisfying the relation has a unique invariant section above it. -/
theorem invariantSection_existsUnique (s : (sourceSheaf e).obj.obj (op W))
    (hs : (firstRestriction e).hom.app (op W) s =
      (secondRestriction e).hom.app (op W) s) :
    ∃! t : (invariantSheaf e).obj.obj (op W),
      (invariantInclusion e).hom.app (op W) t = s := by
  have h₁ := isLimitForkMapOfIsLimit (TopCat.Sheaf.forget _ _) (equalizer.condition _ _)
    (equalizerIsEqualizer (firstRestriction e) (secondRestriction e))
  have h₂ := isLimitForkMapOfIsLimit ((evaluation _ _).obj (op W)) _ h₁
  have h₃ := isLimitForkMapOfIsLimit (forget CommRingCat) _ h₂
  exact Types.unique_of_type_equalizer _ _ h₃ s hs

/-- Invariant sections are determined by their actual source regular functions. -/
theorem invariantSection_ext {s t : (invariantSheaf e).obj.obj (op W)}
    (h : (invariantInclusion e).hom.app (op W) s =
      (invariantInclusion e).hom.app (op W) t) : s = t := by
  obtain ⟨v, _, hv⟩ := invariantSection_existsUnique e W
    ((invariantInclusion e).hom.app (op W) t) (invariantSection_condition e W t)
  exact (hv s h).trans (hv t rfl).symm

/-- Invariant functions, expressed entirely in original scheme regular-function coordinates. -/
theorem invariantSection_iff (s : Γ(U.left, (pullOpen e W).val)) :
    (∃! t : (invariantSheaf e).obj.obj (op W),
      (invariantInclusion e).hom.app (op W) t = s) ↔
        p.left.app (pullOpen e W).val s =
          A.left.presheaf.map
            (eqToHom (congrArg op (pullOpen_preimage_eq e W).symm))
              (q.left.app (pullOpen e W).val s) := by
  constructor
  · rintro ⟨t, rfl, _⟩
    have h := invariantSection_condition e W t
    rw [firstRestriction_app, secondRestriction_app] at h
    exact h
  · intro hs
    apply invariantSection_existsUnique
    rw [firstRestriction_app, secondRestriction_app]
    exact hs

end FLT.Mazur.RelativeRelationOrbit
