/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.DenseGroundEnvelopeInterior
public import FLT.Mazur.AffineHilbertFullInteriorChart

/-!
# Whole original Hilbert tests lift over the dense coefficient open

For a fixed affine etale translation, its constructed dense coefficient open
works for every original Hilbert source. Tests supported on original full
fibers lift uniquely to the original full-interior chart, preserving their
entire scheme maps, nilpotents, Hilbert parameters and Picard sections.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
namespace FLT.Mazur.HilbertChart.AffineRestriction
open CartierAbel SchemePicard FCurve AffineEtaleDenseFiniteGround
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type} [CommRing R] [IsDomain R] [Algebra.FiniteType ℤ R] {X : Scheme}
  (f : X ⟶ Spec (.of R)) [IsProper f] [Flat f] [GeometricallyIntegral f]
  [SmoothOfRelativeDimension 1 f] {L : X.Modules} (hL : AmpleLineBundle L)
  (d : ℕ) (V : Over (Spec (.of R))) [IsAffine V.left] [Etale V.hom]
  (c : (relativeFppfSheaf f).obj.obj (op V))
  {A : Over (Spec (.of R))} (k : A ⟶ variableHilbertTest f d V)
  [IsOpenImmersion k.left]
local notation "U" => fullEnvelopeInterior f hL d V c k
local notation "i" => fullInteriorSourceMap f hL d V c k
local notation "l" => fullInteriorChart f hL d V c k

/-- One dense coefficient open works for every Hilbert chart with this translation. -/
theorem denseGround_fullEnvelopeInterior_iff (x : A.left)
    (hb : A.hom x ∈ groundOpen R V) :
    x ∈ U ↔ x ∈ fullEnvelopeLocus f hL d V c k :=
  original_interior_iff_over_groundOpen R V A (toEnvelope f hL d V c k).left.opensRange x hb

variable {T : Over (Spec (.of R))} (b : T ⟶ A)
  (hb : Set.range b.left ⊆ fullEnvelopeLocus f hL d V c k)
  (ht : Set.range T.hom ⊆ groundOpen R V)

/-- The whole original test factors through the actual interior, including its nilpotents. -/
def denseGroundFullInteriorLift : T ⟶ fullInteriorSource f hL d V c k := by
  have hr : Set.range b.left ⊆ Set.range (U).ι := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨x, rfl⟩
    apply (denseGround_fullEnvelopeInterior_iff f hL d V c k (b.left x) ?_).mpr
      (hb ⟨x, rfl⟩)
    have hw := congrArg (fun g : T.left ⟶ Spec (.of R) ↦ g x) b.w
    change A.hom (b.left x) = T.hom x at hw
    rw [hw]
    exact ht ⟨x, rfl⟩
  let z := IsOpenImmersion.lift (U).ι b.left hr
  refine Over.homMk z ?_
  change z ≫ (U).ι ≫ A.hom = T.hom
  rw [← Category.assoc, IsOpenImmersion.lift_fac, b.w]

/-- Factorization retains the original whole source map. -/
@[reassoc]
theorem denseGroundFullInteriorLift_comp :
    denseGroundFullInteriorLift f hL d V c k b hb ht ≫ i = b := by
  apply Over.OverMorphism.ext
  exact IsOpenImmersion.lift_fac _ _ _

/-- Factorization retains the original whole Hilbert parameter. -/
@[reassoc]
theorem denseGroundFullInteriorLift_chart :
    denseGroundFullInteriorLift f hL d V c k b hb ht ≫ l = b ≫ k := by
  rw [fullInteriorChart, denseGroundFullInteriorLift_comp_assoc]

/-- The original Picard section is unchanged, also on nonreduced tests. -/
theorem denseGroundFullInteriorLift_section :
    (relativeFppfSheaf f).obj.map (denseGroundFullInteriorLift f hL d V c k b hb ht).op
      (sectionAt f hL d V c l) = (relativeFppfSheaf f).obj.map b.op
        (sectionAt f hL d V c k) := by
  change (relativeFppfSheaf f).obj.map _
    ((relativeFppfSheaf f).obj.map (l).op (variableChartSection f hL d V c)) = _
  rw [← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp,
    denseGroundFullInteriorLift_chart, op_comp, Functor.map_comp]
  rfl

/-- The factorization is unique as a scheme map. -/
theorem denseGroundFullInteriorLift_unique (z : T ⟶ fullInteriorSource f hL d V c k)
    (hz : z ≫ i = b) : z = denseGroundFullInteriorLift f hL d V c k b hb ht := by
  apply Over.OverMorphism.ext
  apply (cancel_mono (U).ι).mp
  exact (congrArg Over.Hom.left hz).trans
    (congrArg Over.Hom.left (denseGroundFullInteriorLift_comp f hL d V c k b hb ht)).symm

end FLT.Mazur.HilbertChart.AffineRestriction
