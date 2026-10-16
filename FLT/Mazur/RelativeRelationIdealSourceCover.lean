/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.RelativeRelationInvariantPrincipal
public import FLT.Mazur.RingedSpaceIdealLocus

/-!
# Testing invariant ideal coverage on the original affine source

An invariant ideal covers the original orbit domain exactly when its images
generate the unit ideal in the affine SOURCE section ring. This criterion
does not identify the quotient with the spectrum of the invariant ring.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Opposite TopologicalSpace
universe u
namespace FLT.Mazur.RelativeRelationOrbit
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {S : Scheme.{u}} {A U : Over S} {p q : A ⟶ U}
  (e : CategoryTheory.EquivalenceRelation p q) (W : Opens (Orbit e))
  (I : Ideal ((invariantSheaf e).obj.obj (op W)))

/-- The actual original source functions supplied by the invariant ideal. -/
def invariantIdealSourceGenerators : Set Γ(U.left, (pullOpen e W).val) :=
  (invariantInclusion e).hom.app (op W) '' (I : Set _)

/-- The ideal those invariant functions generate in the original source ring. -/
def invariantIdealSource : Ideal Γ(U.left, (pullOpen e W).val) :=
  Ideal.span (invariantIdealSourceGenerators e W I)

/-- The inverse image of the invariant ideal locus is the union of its actual source basics. -/
theorem pullOpen_sectionIdealOpen :
    (pullOpen e (sectionIdealOpen (ringedSpace e) W I)).val =
      ⨆ a : invariantIdealSourceGenerators e W I, U.left.basicOpen a.val := by
  ext x
  change projection e x ∈ sectionIdealOpen (ringedSpace e) W I ↔ _
  rw [mem_sectionIdealOpen]
  have hx (s : (invariantSheaf e).obj.obj (op W)) :
      projection e x ∈ RingedSpace.basicOpen (ringedSpace e) s ↔
        x ∈ U.left.basicOpen ((invariantInclusion e).hom.app (op W) s) := by
    change x ∈ (pullOpen e (invariantPrincipal e W s)).val ↔ _
    rw [pullOpen_invariantPrincipal]
  constructor
  · rintro ⟨s, hs, hxs⟩
    exact Opens.mem_iSup.mpr ⟨⟨_, ⟨s, hs, rfl⟩⟩, (hx s).mp hxs⟩
  · intro h
    obtain ⟨⟨a, s, hs, ha⟩, hxa⟩ := Opens.mem_iSup.mp h
    subst a
    exact ⟨s, hs, (hx s).mpr hxa⟩

/-- On an affine source domain, coverage is exactly the explicit source ideal unit test. -/
theorem sectionIdealOpen_eq_iff_sourceIdeal_top (hW : IsAffineOpen (pullOpen e W).val) :
    sectionIdealOpen (ringedSpace e) W I = W ↔ invariantIdealSource e W I = ⊤ := by
  change _ ↔ Ideal.span (invariantIdealSourceGenerators e W I) = ⊤
  rw [← hW.iSup_basicOpen_eq_self_iff, ← pullOpen_sectionIdealOpen]
  constructor
  · intro h
    rw [h]
  · intro h
    apply (opensOrderIso e).injective
    exact Subtype.ext h

end FLT.Mazur.RelativeRelationOrbit
