/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.RelativeRelationIdealSourceCover

/-!
# Finite coefficient certificates for invariant neighborhood coverage

Coverage of an affine source domain is equivalent to a finite linear
combination of actual invariant ideal elements equaling one in the original
source section ring. The coefficients need not be invariant; this certifies
coverage, not a global invariant lift.
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

/-- The source unit-ideal equation has a finite certificate in actual original functions. -/
theorem invariantIdealSource_eq_top_iff_certificate :
    invariantIdealSource e W I = ⊤ ↔
      ∃ c : I →₀ (sourceSheaf e).obj.obj (op W),
        c.sum (fun a b ↦ b * (invariantInclusion e).hom.app (op W) a.val) = 1 := by
  have h : invariantIdealSourceGenerators e W I =
      Set.range (fun a : I ↦ (invariantInclusion e).hom.app (op W) a.val) := by
    ext a
    simp only [invariantIdealSourceGenerators, Set.mem_image, Set.mem_range,
      Subtype.exists, exists_prop, SetLike.mem_coe]
  rw [invariantIdealSource, h, Ideal.eq_top_iff_one,
    Finsupp.mem_ideal_span_range_iff_exists_finsupp]
  rfl

/-- Enough invariant neighborhoods exist exactly when this finite source identity exists. -/
theorem sectionIdealOpen_eq_iff_sourceCertificate (hW : IsAffineOpen (pullOpen e W).val) :
    sectionIdealOpen (ringedSpace e) W I = W ↔
      ∃ c : I →₀ (sourceSheaf e).obj.obj (op W),
        c.sum (fun a b ↦ b * (invariantInclusion e).hom.app (op W) a.val) = 1 := by
  rw [sectionIdealOpen_eq_iff_sourceIdeal_top e W I hW,
    invariantIdealSource_eq_top_iff_certificate]

end FLT.Mazur.RelativeRelationOrbit
