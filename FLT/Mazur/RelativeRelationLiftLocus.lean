/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.RelativeRelationPrincipalLifting
public import FLT.Mazur.SectionLiftIdeal
public import FLT.Mazur.LocallyRingedSectionPointIdeal

/-!
# The actual principal lifting locus of a closed invariant section

The original comparison defines a multiplier ideal, hence an actual open of
the orbit quotient. Under affine-source and relation-compactness hypotheses,
this open is exactly the union of principal neighborhoods on which the given
closed section lifts. No principal basis or global lifting is assumed.
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
variable (W : Opens (Orbit e))
  (t : (invariantSheaf e').obj.obj
    (op ((Opens.map (invariantMap e e' g r hp hq).base).obj W)))

/-- The ideal of original invariant multipliers making the closed section lift. -/
def closedLiftIdeal : Ideal ((invariantSheaf e).obj.obj (op W)) :=
  sectionLiftIdeal (invariantSectionPullback e e' g r hp hq W) t

/-- The union of principal neighborhoods supplied by actual lifting multipliers. -/
def principalLiftOpen : Opens (Orbit e) :=
  sectionIdealOpen (ringedSpace e) W (closedLiftIdeal e e' g r hp hq W t)

/-- The principal lifting locus stays in the original section domain. -/
theorem principalLiftOpen_le : principalLiftOpen e e' g r hp hq W t ≤ W :=
  sectionIdealOpen_le _ _ _

variable [IsClosedImmersion g]
  (hW : IsAffineOpen (pullOpen e W).val)
  (hR : IsCompact (p.left ⁻¹ᵁ (pullOpen e W).val : Set A.left))

include hW hR in
/-- A denominator lies in the radical precisely when its actual principal open admits a lift. -/
theorem mem_closedLiftIdeal_radical_iff (s : (invariantSheaf e).obj.obj (op W)) :
    s ∈ (closedLiftIdeal e e' g r hp hq W t).radical ↔
      ∃ a : (invariantSheaf e).obj.obj (op (invariantPrincipal e W s)),
        (m).c.app (op (invariantPrincipal e W s)) a =
          (invariantSheaf e').obj.map ((Opens.map (m).base).map
            (homOfLE (invariantPrincipal_le e W s))).op t := by
  rw [invariantMap_principal_lift_iff e e' g r hp hq W hW hR s]
  exact mem_sectionLiftIdeal_radical _ _ _

include hW hR in
/-- Membership means that some principal neighborhood containing the point admits a lift. -/
theorem mem_principalLiftOpen_iff (x : Orbit e) :
    x ∈ principalLiftOpen e e' g r hp hq W t ↔
      ∃ s : (invariantSheaf e).obj.obj (op W), x ∈ invariantPrincipal e W s ∧
        ∃ a : (invariantSheaf e).obj.obj (op (invariantPrincipal e W s)),
          (m).c.app (op (invariantPrincipal e W s)) a =
            (invariantSheaf e').obj.map ((Opens.map (m).base).map
              (homOfLE (invariantPrincipal_le e W s))).op t := by
  change x ∈ sectionIdealOpen (ringedSpace e) W _ ↔ _
  rw [← sectionIdealOpen_radical, mem_sectionIdealOpen]
  exact exists_congr fun s ↦ by
    rw [mem_closedLiftIdeal_radical_iff e e' g r hp hq W t hW hR s, and_comm]
    rfl

omit [IsClosedImmersion g] in
/-- Failure at an actual quotient point is exactly containment in its actual point prime. -/
theorem notMem_principalLiftOpen_iff (x : W) :
    x.val ∉ principalLiftOpen e e' g r hp hq W t ↔
      closedLiftIdeal e e' g r hp hq W t ≤
        sectionPointIdeal (invariantLocallyRingedSpace e) W x :=
  notMem_sectionIdealOpen_iff (invariantLocallyRingedSpace e) W
    (closedLiftIdeal e e' g r hp hq W t) x

end FLT.Mazur.RelativeRelationOrbit
