/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.HilbertIdentityGroundOriginalSection
public import FLT.Mazur.OrderedHilbertIdentitySchemeSource
public import FLT.Mazur.RelativePicardCoproductSection

/-!
# Original Picard sections on the constructed scheme cover

Every effective affine component retains its original coefficient map and
Hilbert parameter. The sections assemble on the same scheme coproduct used
for the original invariant quotient cover.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
namespace FLT.Mazur.OrderedHilbertIdentityOriginalSection
open HilbertChart CartierAbel SchemePicard FCurve RelativeRelationOrbit
open OrderedHilbertAffineEtaleTestCover OrderedHilbertFaithfulTestCover AffineRestriction
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type} [CommRing R] [Algebra.FiniteType ℤ R] {X : Scheme}
  (f : X ⟶ Spec (.of R)) [IsProper f] [Flat f] [GeometricallyIntegral f]
  [SmoothOfRelativeDimension 1 f] {L : X.Modules} (hL : AmpleLineBundle L)
local notation "T" => smoothHilbertSource f
local notation "s" => smoothHilbertSourceSection f hL
local notation "E" => fun x ↦ Sigma.fst (Sigma.snd (chartData f hL T s x))
local notation "d" => fun x ↦ Prod.snd (Sigma.fst (chartData f hL T s x))
local notation "c" => fun x ↦ chartClass f hL T s x
local notation "p" => fun x ↦ retainedParameter f hL x
local notation "k" => fun x ↦ AffineParameterNeighborhood.chart f (d x) (E x) (p x)
/-- The effective affine component as a test over the ORIGINAL coefficient spectrum. -/
def test (x : (smoothHilbertSource f).left) : Over (Spec (.of R)) :=
  identityGroundOriginalTest f hL (d x) (E x) (c x) (k x)

/-- This test has exactly the previously constructed affine scheme as its underlying source. -/
theorem test_left (x : (smoothHilbertSource f).left) :
    (test f hL x).left = OrderedHilbertIdentityQuotientCover.source f hL x := rfl

/-- The actual parameter map into the original Hilbert chart. -/
def parameter (x : (smoothHilbertSource f).left) :
    test f hL x ⟶ variableHilbertTest f (d x) (E x) :=
  identityGroundOriginalParameter f hL (d x) (E x) (c x) (k x)

instance parameter_openImmersion (x : (smoothHilbertSource f).left) :
    IsOpenImmersion (parameter f hL x).left :=
  identityGroundOriginalParameter_openImmersion f hL (d x) (E x) (c x) (k x)

/-- The original Picard class on each constructed affine component. -/
def sectionAt (x : (smoothHilbertSource f).left) :
    (relativeFppfSheaf f).obj.obj (op (test f hL x)) :=
  identityGroundOriginalSection f hL (d x) (E x) (c x) (k x)

/-- The component's section is pulled back from its unchanged original chart. -/
theorem sectionAt_eq (x : (smoothHilbertSource f).left) : sectionAt f hL x =
    (relativeFppfSheaf f).obj.map (parameter f hL x).op
      (variableChartSection f hL (d x) (E x) (c x)) := rfl

/-- The original coefficient map on the single constructed scheme source. -/
def sourceTest : Over (Spec (.of R)) := relativeCoproductTest (test f hL)

/-- The section lives on the actual W240 scheme source, not a replacement scheme. -/
theorem sourceTest_left :
    (sourceTest f hL).left = OrderedHilbertIdentitySchemeSource.source f hL := rfl

/-- The unchanged affine component in the original relative site. -/
def component (x : (smoothHilbertSource f).left) : test f hL x ⟶ sourceTest f hL :=
  relativeCoproductArrow (test f hL) x

/-- The ORIGINAL Picard section on the single constructed covering scheme. -/
def sourceSection : (relativeFppfSheaf f).obj.obj (op (sourceTest f hL)) :=
  relativeCoproductSection f (test f hL) (sectionAt f hL)

/-- Restriction recovers every original component section exactly. -/
theorem sourceSection_component (x : (smoothHilbertSource f).left) :
    (relativeFppfSheaf f).obj.map (component f hL x).op (sourceSection f hL) =
      sectionAt f hL x := relativeCoproductSection_map f (test f hL) (sectionAt f hL) x

/-- The constructed section is uniquely determined by its original component data. -/
theorem sourceSection_unique (t : (relativeFppfSheaf f).obj.obj (op (sourceTest f hL)))
    (ht : ∀ x, (relativeFppfSheaf f).obj.map (component f hL x).op t = sectionAt f hL x) :
    t = sourceSection f hL := by
  apply relativeCoproductSection_ext f (test f hL)
  intro x
  exact (ht x).trans (sourceSection_component f hL x).symm

end FLT.Mazur.OrderedHilbertIdentityOriginalSection
