/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.UnpointedAcyclicDegreeYoneda

/-!
# Actual Hilbert-Picard chart intersections with arbitrary tests

For every original Picard section the constructed degree open maps to the
actual acyclic Hilbert parameter scheme. Its two maps satisfy the full
fiber-product universal property. The projection to the original test is
an open immersion, proving representable openness of the Hilbert Abel chart.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite
namespace FLT.Mazur.HilbertChart
open CartierAbel SchemePicard FCurve
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {R : Type} [CommRing R] [Algebra.FiniteType ℤ R]
  {X : Scheme} (f : X ⟶ Spec (.of R)) [IsProper f] [Flat f] [GeometricallyIntegral f]
  [SmoothOfRelativeDimension 1 f] (d : ℕ) {L : X.Modules} (hL : AmpleLineBundle L)

/-- The original Picard-sheaf class of a map into the actual acyclic Hilbert scheme. -/
def acyclicHilbertPicardPoint (U : Over (Spec (.of R))) (k : U ⟶ acyclicHilbertTest f d) :=
  ((acyclicHilbertPicardIso f d hL).hom.app (op U) (ULift.up k)).val

/-- The Hilbert chart's Picard class is natural on every original test. -/
theorem acyclicHilbertPicardPoint_natural {U V : Over (Spec (.of R))}
    (b : V ⟶ U) (k : U ⟶ acyclicHilbertTest f d) :
    acyclicHilbertPicardPoint f d hL V (b ≫ k) =
      (relativeFppfSheaf f).obj.map b.op (acyclicHilbertPicardPoint f d hL U k) := by
  have h := congrArg (fun a ↦ a (ULift.up k))
    ((acyclicHilbertPicardIso f d hL).hom.naturality b.op)
  exact congrArg Subtype.val h

/-- Equality of the actual Picard classes detects equality of parameter maps. -/
theorem acyclicHilbertPicardPoint_injective (U : Over (Spec (.of R))) :
    Function.Injective (acyclicHilbertPicardPoint f d hL U) := by
  intro k l h
  have he := ((acyclicHilbertPicardIso f d hL).app (op U)).toEquiv.injective
    (Subtype.ext h)
  exact congrArg ULift.down he

variable (T : Over (Spec (.of R))) (s : (relativeFppfSheaf f).obj.obj (op T))

/-- The overlap's canonical map to the actual Hilbert parameter scheme. -/
def acyclicHilbertPicardOverlapToParameter :
    unpointedAcyclicDegreeTest f T s d ⟶ acyclicHilbertTest f d :=
  (((acyclicHilbertPicardIso f d hL).app (op (unpointedAcyclicDegreeTest f T s d))).toEquiv.symm
    ⟨(relativeFppfSheaf f).obj.map (unpointedAcyclicDegreeArrow f T s d).op s,
      unpointedAcyclicDegreeArrow_mem f T s d⟩).down

/-- The two actual overlap maps have precisely the same original Picard class. -/
theorem acyclicHilbertPicardOverlap_class :
    acyclicHilbertPicardPoint f d hL _ (acyclicHilbertPicardOverlapToParameter f d hL T s) =
      (relativeFppfSheaf f).obj.map (unpointedAcyclicDegreeArrow f T s d).op s := by
  exact congrArg Subtype.val
    (((acyclicHilbertPicardIso f d hL).app
      (op (unpointedAcyclicDegreeTest f T s d))).toEquiv.apply_symm_apply _)

/-- The degree open is the actual intersection of an arbitrary test with the Hilbert Abel chart. -/
theorem acyclicHilbertPicardOverlap_lift {U : Over (Spec (.of R))}
    (b : U ⟶ T) (k : U ⟶ acyclicHilbertTest f d)
    (hk : acyclicHilbertPicardPoint f d hL U k = (relativeFppfSheaf f).obj.map b.op s) :
    ∃! l : U ⟶ unpointedAcyclicDegreeTest f T s d,
      l ≫ unpointedAcyclicDegreeArrow f T s d = b ∧
        l ≫ acyclicHilbertPicardOverlapToParameter f d hL T s = k := by
  have hb : (relativeFppfSheaf f).obj.map b.op s ∈
      (acyclicDegreePicardSubfunctor f d).obj (op U) := by
    rw [← hk]
    exact ((acyclicHilbertPicardIso f d hL).hom.app (op U) (ULift.up k)).property
  obtain ⟨l, hl, hu⟩ := (unpointedAcyclicDegreeOpen_represents f T s d b).mp hb
  refine ⟨l, ⟨hl, ?_⟩, fun m hm ↦ hu m hm.1⟩
  apply acyclicHilbertPicardPoint_injective f d hL U
  rw [acyclicHilbertPicardPoint_natural, acyclicHilbertPicardOverlap_class, hk]
  change ((relativeFppfSheaf f).obj.map (unpointedAcyclicDegreeArrow f T s d).op ≫
    (relativeFppfSheaf f).obj.map l.op) s = _
  rw [← Functor.map_comp, ← op_comp, hl]

end FLT.Mazur.HilbertChart
