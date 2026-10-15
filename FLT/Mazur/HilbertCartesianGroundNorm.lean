/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CartesianGroundInvariantNorm
public import FLT.Mazur.GroundChartOriginalNormTransport
public import FLT.Mazur.HilbertEnvelopeSourceTransport
public import FLT.Mazur.AffineHilbertNestedRestriction

/-!
# Original Hilbert source norms on Cartesian ground refinements

An actual source coefficient on a full original Hilbert envelope constructs
compatible sections after any full Cartesian translation base change. The
full original relation is used, including arrows with different new grounds.
Existence of such original full-envelope neighborhoods is still separate.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
namespace FLT.Mazur.HilbertChart.AffineRestriction
open FCurve CartierAbel SchemePicard SchemeTranslationNorm Approximation
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] relation fst snd toEnvelope independentTestEnvelope
  independentTestProjection independentTestEnvelopeMap groundOriginalChart
variable {R S : Type} [CommRing R] [CommRing S]
  [Algebra.FiniteType ℤ R] [Algebra.FiniteType ℤ S]
  {X : Scheme} (f : X ⟶ Spec (.of R)) (a : Spec (.of S) ⟶ Spec (.of R))
  [IsProper f] [Flat f] [GeometricallyIntegral f] [SmoothOfRelativeDimension 1 f]
  {L : X.Modules} (hL : AmpleLineBundle L) (d : ℕ)
  (V : Over (Spec (.of R))) (W : Over (Spec (.of S)))
  (t : (Over.map a).obj W ⟶ V) (c : (relativeFppfSheaf f).obj.obj (op V))
  {A : Over (Spec (.of R))} (k : A ⟶ variableHilbertTest f d V)
  [IsIso (toEnvelope f hL d V c k).left]
  {B : Over (Spec (.of S))} (u : (Over.map a).obj B ⟶ A)
  (H : IsPullback t.left W.hom V.hom a) (s : Γ(A.left, ⊤))

/-- Pull the actual original source section to the full changed-ground envelope. -/
def cartesianOriginalSourceSection : Γ((prod B W).left, ⊤) :=
  (fixedBaseEnvelopeMap a V W t u).left.appTop
    (fullEnvelopeSourceSection f hL d V c k s)

local notation "p" => fst f hL d V c k
local notation "q" => snd f hL d V c k
local notation "r" => fst f hL d V c (u ≫ k)
local notation "v" => snd f hL d V c (u ≫ k)
local notation "n" => nestedToFullRelation f hL d V c k u

variable [IsAffine W.left]
/-- The norm requires a basis only for the translation over the new ground. -/
local instance hilbertCartesianTranslationAlgebra : Algebra S Γ(W.left, ⊤) :=
  affineBaseSectionAlgebra W.hom
variable {ι : Type} [Finite ι] (b : Module.Basis ι S Γ(W.left, ⊤))

include H in
omit [Algebra.FiniteType ℤ S] in
/-- Original composition constructs invariance on the full restricted original relation. -/
theorem cartesianOriginalSourceNorm_invariant :
    (r).left.appTop (regularNorm B W b
      (cartesianOriginalSourceSection f a hL d V W t c k u s)) =
    (v).left.appTop (regularNorm B W b
      (cartesianOriginalSourceSection f a hL d V W t c k u s)) := by
  exact regularNorm_cartesianRelation a V B W t H u p q
    (fullEnvelopeSourceSection f hL d V c k s)
    (fullEnvelopeSourceSection_transport f hL d V c k s) b (r).left (v).left (n).left
    (congrArg Over.Hom.left (nestedToFullRelation_fst f hL d V c k u))
    (congrArg Over.Hom.left (nestedToFullRelation_snd f hL d V c k u))

local instance hilbertCartesianChangedSmooth :
    SmoothOfRelativeDimension 1 (pullback.snd f a) :=
  MorphismProperty.pullback_snd _ _ inferInstance
variable (l : B ⟶ variableHilbertTest (pullback.snd f a) d W)
  (hk : u ≫ k = groundOriginalChart f a hL d V W t l)

include H hk in
omit [IsAffine W.left] in
/-- Construct the W306 section-transport obligation from a Cartesian translation square. -/
theorem cartesianOriginalSourceSection_groundTransport :
    groundEnvelopeSectionTransport f a hL d V W t c l
      (cartesianOriginalSourceSection f a hL d V W t c k u s) := by
  unfold groundEnvelopeSectionTransport
  rw [← hk]
  intro i
  let j := (Over.left (relation f hL d V c (u ≫ k))).affineCover.f i
  have hx : (j ≫ (n).left) ≫ (p).left = (j ≫ (r).left) ≫ u.left := by
    have he := congrArg Over.Hom.left (nestedToFullRelation_fst f hL d V c k u)
    simpa only [Category.assoc, Over.comp_left] using congrArg (fun g ↦ j ≫ g) he
  have hy : (j ≫ (n).left) ≫ (q).left = (j ≫ (v).left) ≫ u.left := by
    have he := congrArg Over.Hom.left (nestedToFullRelation_snd f hL d V c k u)
    simpa only [Category.assoc, Over.comp_left] using congrArg (fun g ↦ j ≫ g) he
  let h := originalRelation_ground_eq a B u p q
    (j ≫ (r).left) (j ≫ (v).left) (j ≫ (n).left) hx hy
  refine ⟨cartesianGroundTransport a V B W t.left H _ _ h,
    cartesianGroundTransport_projection a V B W t.left H _ _ h, ?_⟩
  exact cartesianEnvelope_section_transport a V B W t H u p q
    (j ≫ (r).left) (j ≫ (v).left) (j ≫ (n).left) hx hy
    (fullEnvelopeSourceSection f hL d V c k s)
    (fullEnvelopeSourceSection_transport f hL d V c k s)

end FLT.Mazur.HilbertChart.AffineRestriction
