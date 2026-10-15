/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ArtinianGroundEnvelopeInterior
public import FLT.Mazur.AffineHilbertFullInteriorChart

/-!
# Original Hilbert full interiors over locally Artinian coefficients

Every full original fiber now belongs to the original interior. Any whole
scheme test supported on the full-fiber locus lifts uniquely to the actual
full-interior chart. The factorization retains nilpotents and the original
Picard section, and uses the complete original relation.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
namespace FLT.Mazur.HilbertChart.AffineRestriction
open CartierAbel SchemePicard FCurve
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type} [CommRing R] [Algebra.FiniteType ℤ R]
  [IsLocallyArtinian (Spec (.of R))] {X : Scheme}
  (f : X ⟶ Spec (.of R)) [IsProper f] [Flat f] [GeometricallyIntegral f]
  [SmoothOfRelativeDimension 1 f] {L : X.Modules} (hL : AmpleLineBundle L)
  (d : ℕ) (V : Over (Spec (.of R))) [Etale V.hom] [QuasiCompact V.hom]
  (c : (relativeFppfSheaf f).obj.obj (op V))
  {A : Over (Spec (.of R))} (k : A ⟶ variableHilbertTest f d V)
  [IsOpenImmersion k.left]
local notation "U" => fullEnvelopeInterior f hL d V c k
local notation "i" => fullInteriorSourceMap f hL d V c k
local notation "l" => fullInteriorChart f hL d V c k

/-- Locally Artinian coefficients remove the original full-interior obstruction. -/
theorem artinian_fullEnvelopeInterior_coe :
    (U : Set A.left) = fullEnvelopeLocus f hL d V c k :=
  ArtinianGroundEnvelope.interior_coe A V (toEnvelope f hL d V c k).left.opensRange

variable {T : Over (Spec (.of R))} (b : T ⟶ A)
  (hb : Set.range b.left ⊆ fullEnvelopeLocus f hL d V c k)

/-- The whole original scheme test lifts to the constructed open, including all nilpotents. -/
def artinianFullInteriorLift : T ⟶ fullInteriorSource f hL d V c k := by
  have hr : Set.range b.left ⊆ Set.range (U).ι := by
    rw [Scheme.Opens.range_ι, artinian_fullEnvelopeInterior_coe]
    exact hb
  let z := IsOpenImmersion.lift (U).ι b.left hr
  refine Over.homMk z ?_
  change z ≫ (U).ι ≫ A.hom = T.hom
  rw [← Category.assoc, IsOpenImmersion.lift_fac, b.w]

/-- The source factorization is equality of scheme maps, not just of their points. -/
@[reassoc]
theorem artinianFullInteriorLift_comp :
    artinianFullInteriorLift f hL d V c k b hb ≫ i = b := by
  apply Over.OverMorphism.ext
  exact IsOpenImmersion.lift_fac _ _ _

/-- The Hilbert parameter is the exact original parameter. -/
@[reassoc]
theorem artinianFullInteriorLift_chart :
    artinianFullInteriorLift f hL d V c k b hb ≫ l = b ≫ k := by
  rw [fullInteriorChart, artinianFullInteriorLift_comp_assoc]

/-- Pullback of the constructed chart section recovers the original Picard class on every test. -/
theorem artinianFullInteriorLift_section :
    (relativeFppfSheaf f).obj.map (artinianFullInteriorLift f hL d V c k b hb).op
      (sectionAt f hL d V c l) = (relativeFppfSheaf f).obj.map b.op
        (sectionAt f hL d V c k) := by
  change (relativeFppfSheaf f).obj.map _
    ((relativeFppfSheaf f).obj.map (l).op (variableChartSection f hL d V c)) = _
  rw [← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp,
    artinianFullInteriorLift_chart, op_comp, Functor.map_comp]
  rfl

/-- The lift is unique even for nonreduced source tests. -/
theorem artinianFullInteriorLift_unique (z : T ⟶ fullInteriorSource f hL d V c k)
    (hz : z ≫ i = b) : z = artinianFullInteriorLift f hL d V c k b hb := by
  apply Over.OverMorphism.ext
  apply (cancel_mono (U).ι).mp
  exact (congrArg Over.Hom.left hz).trans
    (congrArg Over.Hom.left (artinianFullInteriorLift_comp f hL d V c k b hb)).symm

end FLT.Mazur.HilbertChart.AffineRestriction
