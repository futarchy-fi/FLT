/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.RelativeRelationInvariantMap
public import FLT.Mazur.RelativeRelationInvariantSections

/-!
# Original regular functions under maps of invariant quotients

The actual descended locally ringed morphism pulls invariant sections back
through its original scheme map. This includes the inverse images of opens
and the entire invariant structure sheaf.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
universe u
namespace FLT.Mazur.RelativeRelationOrbit
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {S S' : Scheme.{u}} {A U : Over S} {A' U' : Over S'}
  {p q : A ⟶ U} {p' q' : A' ⟶ U'}
  (e : CategoryTheory.EquivalenceRelation p q)
  (e' : CategoryTheory.EquivalenceRelation p' q')
  (g : U'.left ⟶ U.left) (r : A'.left ⟶ A.left)
  (hp : r ≫ p.left = p'.left ≫ g) (hq : r ≫ q.left = q'.left ≫ g)
local notation "m" => invariantMap e e' g r hp hq

/-- Forgetting local stalks retains the original regular-function square. -/
theorem invariantMap_ringed_projection :
    toRingedSpace e' ≫ (m).toShHom = g.toShHom ≫ toRingedSpace e := by
  have h := congrArg (fun k ↦ k.toShHom) (invariantMap_projection e e' g r hp hq)
  simpa only [LocallyRingedSpace.comp_toShHom,
    invariantLocallyRingedProjection_toShHom] using h

/-- The actual source inverse image lies in the original scheme inverse image. -/
theorem invariantMap_sourceOpen_le (O : TopologicalSpace.Opens (Orbit e)) :
    (pullOpen e' ((TopologicalSpace.Opens.map (m).base).obj O)).val ≤
      g ⁻¹ᵁ (pullOpen e O).val := by
  intro x hx
  change (m).base (projection e' x) ∈ O at hx
  rw [invariantMap_projection_apply] at hx
  exact hx

/-- The sheaf comparison is pullback of the original invariant source functions. -/
theorem invariantMap_source_app (O : TopologicalSpace.Opens (Orbit e)) :
    (m).c.app (op O) ≫
      (invariantInclusion e').hom.app (op ((TopologicalSpace.Opens.map (m).base).obj O)) =
    (invariantInclusion e).hom.app (op O) ≫
      g.appLE _ _ (invariantMap_sourceOpen_le e e' g r hp hq O) := by
  have h := PresheafedSpace.congr_app
    (congrArg (fun k ↦ k.hom) (invariantMap_ringed_projection e e' g r hp hq)) (op O)
  change (m).c.app (op O) ≫ (invariantInclusion e').hom.app _ =
    (invariantInclusion e).hom.app (op O) ≫
      g.app _ ≫ U'.left.presheaf.map (eqToHom _) at h
  refine h.trans ?_
  dsimp only [Scheme.Hom.appLE]
  congr 2

/-- Evaluation retains every original invariant section, not only stalk residues. -/
theorem invariantMap_source_apply (O : TopologicalSpace.Opens (Orbit e))
    (s : (invariantSheaf e).obj.obj (op O)) :
    (invariantInclusion e').hom.app (op ((TopologicalSpace.Opens.map (m).base).obj O))
        ((m).c.app (op O) s) =
      g.appLE _ _ (invariantMap_sourceOpen_le e e' g r hp hq O)
        ((invariantInclusion e).hom.app (op O) s) :=
  congrArg (fun k ↦ k s) (invariantMap_source_app e e' g r hp hq O)

end FLT.Mazur.RelativeRelationOrbit
