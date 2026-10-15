/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.HilbertInteriorFiniteEquations
public import FLT.Mazur.EnvelopeInteriorUnitIdealLift

/-!
# Finite equations lift whole original Hilbert tests

The constructed finite equations generate the unit ideal on an affine test
exactly when its whole original parameter factors through the full interior.
The resulting unique lift keeps the coefficient map, Hilbert parameter and
Picard section, also on nonreduced tests. The certificate is not asserted to
hold for arbitrary proper-family classes.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
namespace FLT.Mazur.HilbertChart.AffineRestriction
open CartierAbel SchemePicard FCurve SchemeOpenEnvelope
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type} [CommRing R] [Algebra.FiniteType ℤ R] {X : Scheme}
  (f : X ⟶ Spec (.of R)) [IsProper f] [Flat f] [GeometricallyIntegral f]
  [SmoothOfRelativeDimension 1 f] {L : X.Modules} (hL : AmpleLineBundle L)
  (d : ℕ) (V : Over (Spec (.of R))) [Etale V.hom]
  (c : (relativeFppfSheaf f).obj.obj (op V))
  {A : Over (Spec (.of R))} [IsAffine A.left]
  (k : A ⟶ variableHilbertTest f d V) [IsOpenImmersion k.left]
  {T : Over (Spec (.of R))} [IsAffine T.left] (b : T ⟶ A)
local notation "π" => Over.Hom.left (prod.fst : prod A V ⟶ A)
local notation "O" => Scheme.Hom.opensRange (Over.Hom.left (toEnvelope f hL d V c k))
local notation "U" => fullEnvelopeInterior f hL d V c k
local notation "i" => fullInteriorSourceMap f hL d V c k
local notation "l" => fullInteriorChart f hL d V c k

/-- One finite ideal equality tests the whole original affine scheme morphism. -/
theorem originalInteriorEquations_unit_iff :
    Ideal.span (b.left.appTop.hom ''
      (originalInteriorEquations f hL d V c k : Set Γ(A.left, ⊤))) = ⊤ ↔ Set.range b.left ⊆ U :=
  generator_span_eq_top_iff π O b.left _ (originalInteriorEquations_span f hL d V c k)

/-- Equal original Picard classes give equivalent finite certificates on the whole test. -/
theorem originalInteriorEquations_unit_congr (b' : T ⟶ A)
    (hc : (relativeFppfSheaf f).obj.map b.op (sectionAt f hL d V c k) =
      (relativeFppfSheaf f).obj.map b'.op (sectionAt f hL d V c k)) :
    Ideal.span (b.left.appTop.hom ''
      (originalInteriorEquations f hL d V c k : Set Γ(A.left, ⊤))) = ⊤ ↔
      Ideal.span (b'.left.appTop.hom ''
        (originalInteriorEquations f hL d V c k : Set Γ(A.left, ⊤))) = ⊤ := by
  rw [originalInteriorEquations_unit_iff, originalInteriorEquations_unit_iff,
    Set.range_subset_iff, Set.range_subset_iff]
  obtain ⟨z, hz, _⟩ := lift f hL d V c k b b' hc
  apply forall_congr'
  intro x
  have he := Set.ext_iff.mp
    (congrArg SetLike.coe (fullEnvelopeInterior_invariant f hL d V c k)) (z.left x)
  change (fst f hL d V c k).left (z.left x) ∈ U ↔
    (snd f hL d V c k).left (z.left x) ∈ U at he
  have hp := congrArg (fun u : T ⟶ A ↦ u.left x) hz.1
  have hq := congrArg (fun u : T ⟶ A ↦ u.left x) hz.2
  change (fst f hL d V c k).left (z.left x) = b.left x at hp
  change (snd f hL d V c k).left (z.left x) = b'.left x at hq
  rwa [hp, hq] at he

variable (h : Ideal.span (b.left.appTop.hom ''
      (originalInteriorEquations f hL d V c k : Set Γ(A.left, ⊤))) = ⊤)

/-- The finite certificate constructs a lift over the unchanged original coefficient scheme. -/
def originalEquationTestLift : T ⟶ fullInteriorSource f hL d V c k := by
  have hd : (denominatorIdeal (π).appTop.hom O).map b.left.appTop.hom = ⊤ := by
    rw [← originalInteriorEquations_span f hL d V c k, Ideal.map_span]
    exact h
  let z := unitIdealInteriorLift π O b.left hd
  refine Over.homMk z ?_
  change z ≫ (U).ι ≫ A.hom = T.hom
  exact (Category.assoc z (U).ι A.hom).symm.trans
    ((congrArg (fun g : T.left ⟶ A.left ↦ g ≫ A.hom)
      (unitIdealInteriorLift_comp π O b.left hd)).trans b.w)

/-- Exact recovery of the whole original source map. -/
@[reassoc]
theorem originalEquationTestLift_comp : originalEquationTestLift f hL d V c k b h ≫ i = b := by
  apply Over.OverMorphism.ext
  exact unitIdealInteriorLift_comp π O b.left (by
    rw [← originalInteriorEquations_span f hL d V c k, Ideal.map_span]
    exact h)

/-- Exact recovery of the original Hilbert parameter. -/
@[reassoc]
theorem originalEquationTestLift_chart :
    originalEquationTestLift f hL d V c k b h ≫ l = b ≫ k := by
  rw [fullInteriorChart, originalEquationTestLift_comp_assoc]

/-- The original Picard section is retained on the entire test, not just its geometric points. -/
theorem originalEquationTestLift_section :
    (relativeFppfSheaf f).obj.map (originalEquationTestLift f hL d V c k b h).op
      (sectionAt f hL d V c l) =
        (relativeFppfSheaf f).obj.map b.op (sectionAt f hL d V c k) := by
  change (relativeFppfSheaf f).obj.map _
    ((relativeFppfSheaf f).obj.map (l).op (variableChartSection f hL d V c)) = _
  rw [← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp,
    originalEquationTestLift_chart, op_comp, Functor.map_comp]
  rfl

/-- Uniqueness holds as a morphism over the original coefficient scheme. -/
theorem originalEquationTestLift_unique (z : T ⟶ fullInteriorSource f hL d V c k)
    (hz : z ≫ i = b) : z = originalEquationTestLift f hL d V c k b h := by
  apply Over.OverMorphism.ext
  apply (cancel_mono (U).ι).mp
  exact (congrArg Over.Hom.left hz).trans
    (congrArg Over.Hom.left (originalEquationTestLift_comp f hL d V c k b h)).symm

end FLT.Mazur.HilbertChart.AffineRestriction
