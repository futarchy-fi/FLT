/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AcyclicHilbertFixedBasePicard

/-!
# Recovering the original Hilbert morphism from the new coefficient model

The inverse scheme comparison and the base-change adjunction give an actual
map to the original Hilbert scheme. Its class formula holds on every test.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
namespace FLT.Mazur.HilbertChart
open FCurve CartierAbel SchemePicard
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {R R' : Type} [CommRing R] [CommRing R']
  [Algebra.FiniteType ℤ R] [Algebra.FiniteType ℤ R']
  {X : Scheme} (f : X ⟶ Spec (.of R)) (a : Spec (.of R') ⟶ Spec (.of R))
  [IsProper f] [Flat f] [GeometricallyIntegral f] [SmoothOfRelativeDimension 1 f]
  {L : X.Modules} (hL : AmpleLineBundle L) (d : ℕ)
local notation "q" => Limits.pullback.snd f a
local instance : SmoothOfRelativeDimension 1 q :=
  MorphismProperty.pullback_snd _ _ inferInstance

/-- The actual morphism from the new-base Hilbert scheme to the original one. -/
def acyclicHilbertFixedBaseProjection :
    (Over.map a).obj (acyclicHilbertTest q d) ⟶ acyclicHilbertTest f d :=
  ((Over.mapPullbackAdj a).homEquiv _ _).symm (acyclicHilbertFixedBaseIso f a hL d).inv

/-- The adjunction recovers the original parameter from each map to the new Hilbert scheme. -/
theorem acyclicHilbertFixedBaseProjection_parameter (T : Over (Spec (.of R')))
    (k : T ⟶ acyclicHilbertTest q d) :
    acyclicHilbertFixedBaseParameter f a hL d T
        ((Over.map a).map k ≫ acyclicHilbertFixedBaseProjection f a hL d) = k := by
  have hn := (Over.mapPullbackAdj a).homEquiv_naturality_left_symm
    k (acyclicHilbertFixedBaseIso f a hL d).inv
  have hp := acyclicHilbertFixedBaseIso_point f a hL d T
    (k ≫ (acyclicHilbertFixedBaseIso f a hL d).inv)
  rw [hn] at hp
  simpa only [acyclicHilbertFixedBaseProjection, Category.assoc, Iso.inv_hom_id,
    Category.comp_id] using hp.symm

/-- The actual projection to the old Hilbert scheme preserves exactly the Picard class. -/
theorem acyclicHilbertFixedBaseProjection_picard (T : Over (Spec (.of R')))
    (k : T ⟶ acyclicHilbertTest q d) :
    (relativeFppfBaseChange f a).hom.hom.app (op T)
        (acyclicHilbertPicardPoint f d hL ((Over.map a).obj T)
          ((Over.map a).map k ≫ acyclicHilbertFixedBaseProjection f a hL d)) =
      acyclicHilbertPicardPoint q d (fixedBaseAmple f a hL) T k := by
  rw [← acyclicHilbertFixedBaseParameter_picard, acyclicHilbertFixedBaseProjection_parameter]

end FLT.Mazur.HilbertChart
