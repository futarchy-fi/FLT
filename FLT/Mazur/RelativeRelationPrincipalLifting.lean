/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.RelativeRelationInvariantLocalization
public import FLT.Mazur.RelativeRelationClosedObstruction
public import FLT.Mazur.PrincipalImageCriterion

/-!
# Local closed lifting by a finite-power correction

An original closed invariant function lifts on a principal quotient neighborhood
exactly when a finite power multiple lifts on the original domain. Equivalently,
the explicitly computed original obstruction of that multiple vanishes.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Opposite TopologicalSpace
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
/-- The original section pullback with its invariant ring codomain made explicit. -/
def invariantSectionPullback (W : Opens (Orbit e)) :
    (invariantSheaf e).obj.obj (op W) →+*
      (invariantSheaf e').obj.obj (op ((Opens.map (m).base).obj W)) :=
  ((m).c.app (op W)).hom

variable (W : Opens (Orbit e)) [IsClosedImmersion g]
  (hW : IsAffineOpen (pullOpen e W).val)
  (hR : IsCompact (p.left ⁻¹ᵁ (pullOpen e W).val : Set A.left))
  (s : (invariantSheaf e).obj.obj (op W))
local notation "D" => invariantPrincipal e W s
local notation "j" => homOfLE (invariantPrincipal_le e W s)
include hW hR

/-- The original closed invariant section lifts locally iff a power multiple lifts originally. -/
theorem invariantMap_principal_lift_iff
    (t : (invariantSheaf e').obj.obj (op ((TopologicalSpace.Opens.map (m).base).obj W))) :
    (∃ a : (invariantSheaf e).obj.obj (op D), (m).c.app (op D) a =
      (invariantSheaf e').obj.map ((Opens.map (m).base).map j).op t) ↔
    ∃ (n : ℕ) (a : (invariantSheaf e).obj.obj (op W)),
      (m).c.app (op W) a = (invariantSectionPullback e e' g r hp hq W s ^ n * t) := by
  apply PrincipalImageCriterion.lift_iff (invariantSectionPullback e e' g r hp hq W)
    (principalRestriction e W s)
    ((invariantSheaf e').obj.map ((Opens.map (m).base).map j).op).hom
    (invariantSectionPullback e e' g r hp hq D)
    (fun x ↦ congrArg (fun k ↦ k x) ((m).c.naturality (j).op)) s
    (principalRestriction_isLocalization e W s hW hR)
  have hT : IsAffineOpen (pullOpen e' ((TopologicalSpace.Opens.map (m).base).obj W)).val := by
    rw [invariantMap_sourceOpen_eq]
    exact hW.preimage g
  intro x hx
  suffices aux : ∀ (Z : Opens (Orbit e')) (i : Z ⟶ ((TopologicalSpace.Opens.map (m).base).obj W)),
      Z = invariantPrincipal e' ((TopologicalSpace.Opens.map (m).base).obj W) ((m).c.app (op W) s) →
      (invariantSheaf e').obj.map i.op x = 0 →
      ∃ n : ℕ, invariantSectionPullback e e' g r hp hq W s ^ n * x = 0 from
    aux ((TopologicalSpace.Opens.map (m).base).obj D) _
      (invariantMap_principal e W s e' g r hp hq) hx
  intro Z i hZ hz
  subst Z
  exact (principalRestriction_eq_zero_iff e' ((TopologicalSpace.Opens.map (m).base).obj W)
    ((m).c.app (op W) s) hT x).mp hz

/-- The local lifting equation is exactly finite-power vanishing of the original obstruction. -/
theorem invariantMap_principal_lift_obstruction_iff
    (t : (invariantSheaf e').obj.obj (op ((TopologicalSpace.Opens.map (m).base).obj W))) :
    (∃ a : (invariantSheaf e).obj.obj (op D), (m).c.app (op D) a =
      (invariantSheaf e').obj.map ((Opens.map (m).base).map j).op t) ↔
    ∃ n : ℕ, closedSectionObstruction e e' g r hp hq W hW
      ((invariantSectionPullback e e' g r hp hq W s ^ n * t)) = 0 := by
  rw [invariantMap_principal_lift_iff e e' g r hp hq W hW hR s]
  exact exists_congr fun n ↦
    (closedSectionObstruction_eq_zero_iff e e' g r hp hq W hW _).symm

end FLT.Mazur.RelativeRelationOrbit
