/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.RelativeRelationLiftLocus

/-!
# Finite principal covers carrying actual closed section lifts

Noetherianity descends to the orbit topology. It makes the constructed lifting
locus a finite union of principal opens with affine source inverse images and
actual boundary lifts, while imposing no finite generation on the invariant ring.
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

/-- The actual orbit topology inherits Noetherianity from its original source. -/
theorem orbit_noetherianSpace [NoetherianSpace U.left] : NoetherianSpace (Orbit e) :=
  noetherianSpace_of_surjective (projection e) (projection_continuous e)
    (projection_surjective e)

variable (e' : CategoryTheory.EquivalenceRelation p' q')
  (g : U'.left ⟶ U.left) (r : A'.left ⟶ A.left)
  (hp : r ≫ p.left = p'.left ≫ g) (hq : r ≫ q.left = q'.left ≫ g)
  (W : Opens (Orbit e))
  (t : (invariantSheaf e').obj.obj
    (op ((Opens.map (invariantMap e e' g r hp hq).base).obj W)))
local notation "m" => invariantMap e e' g r hp hq
local notation "I" => closedLiftIdeal e e' g r hp hq W t
local notation "N" => principalLiftOpen e e' g r hp hq W t

/-- Finitely many actual invariant multipliers cover the entire principal lifting locus. -/
theorem principalLiftOpen_finite_cover [NoetherianSpace U.left] :
    ∃ s : Finset I, (N : Set (Orbit e)) =
      ⋃ a ∈ s, (invariantPrincipal e W a.val : Set (Orbit e)) := by
  let _ : NoetherianSpace (ringedSpace e) := orbit_noetherianSpace e
  exact sectionIdealOpen_finite_cover (ringedSpace e) W I

variable [IsClosedImmersion g]
  (hW : IsAffineOpen (pullOpen e W).val)
  (hR : IsCompact (p.left ⁻¹ᵁ (pullOpen e W).val : Set A.left))
include hW hR

/-- Each member of that finite cover has affine source and an actual lift of the closed section. -/
theorem principalLiftOpen_finite_affine_lifts [NoetherianSpace U.left] :
    ∃ s : Finset I, (N : Set (Orbit e)) =
        ⋃ a ∈ s, (invariantPrincipal e W a.val : Set (Orbit e)) ∧
      ∀ a ∈ s, IsAffineOpen (pullOpen e (invariantPrincipal e W a.val)).val ∧
        ∃ b : (invariantSheaf e).obj.obj (op (invariantPrincipal e W a.val)),
          (m).c.app (op (invariantPrincipal e W a.val)) b =
            (invariantSheaf e').obj.map ((Opens.map (m).base).map
              (homOfLE (invariantPrincipal_le e W a.val))).op t := by
  obtain ⟨s, hs⟩ := principalLiftOpen_finite_cover e e' g r hp hq W t
  refine ⟨s, hs, fun a _ ↦ ⟨invariantPrincipal_source_affine e W hW a.val, ?_⟩⟩
  exact (mem_closedLiftIdeal_radical_iff e e' g r hp hq W t hW hR a.val).mp
    (Ideal.le_radical a.property)

end FLT.Mazur.RelativeRelationOrbit
