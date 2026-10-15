/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.GroundChartOriginalResidualDescent
public import FLT.Mazur.SchemeRelationNormTransport

/-!
# Cross-ground envelope transport gives original invariant Hilbert norms

The transport obligation is a whole-scheme isomorphism over each affine test
of the full original relation. It must preserve the chosen envelope section.
Under this explicit geometric obligation, the changed-family norm descends
as an actual morphism on the original locally ringed quotient. No existence
of such transports or scheme effectivity of the quotient is asserted here.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
namespace FLT.Mazur.HilbertChart.AffineRestriction
open FCurve CartierAbel SchemePicard RelativeRelationOrbit
open Approximation SchemeTranslationNorm SchemeEffectiveEpiSections
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] relation fst snd invariantLocallyRingedProjection
  variableChartFixedBaseQuotientMap restrictedInvariantQuotientMap
  groundOriginalQuotientMap groundOriginalChart equivalence
  independentTestEnvelope independentTestProjection independentTestEnvelopeMap
variable {R S : Type} [CommRing R] [CommRing S]
  [Algebra.FiniteType ℤ R] [Algebra.FiniteType ℤ S]
  {X : Scheme} (f : X ⟶ Spec (.of R)) (a : Spec (.of S) ⟶ Spec (.of R))
  [IsProper f] [Flat f] [GeometricallyIntegral f] [SmoothOfRelativeDimension 1 f]
  {L : X.Modules} (hL : AmpleLineBundle L) (d : ℕ)
  (V : Over (Spec (.of R))) (W : Over (Spec (.of S)))
  (t : (Over.map a).obj W ⟶ V) (c : (relativeFppfSheaf f).obj.obj (op V))
local instance groundOriginalNormSmooth : SmoothOfRelativeDimension 1 (pullback.snd f a) :=
  MorphismProperty.pullback_snd _ _ inferInstance
variable {B : Over (Spec (.of S))} (l : B ⟶ variableHilbertTest (pullback.snd f a) d W)


local notation "k" => groundOriginalChart f a hL d V W t l
local notation "D" => equivalence f hL d V c k
local notation "p" => fst f hL d V c k
local notation "s" => snd f hL d V c k

local notation "π" => invariantLocallyRingedProjection D

variable [IsAffine W.left]
/-- Keep the actual translation algebra of the changed family. -/
local instance groundOriginalNormAlgebra : Algebra S Γ(W.left, ⊤) :=
  affineBaseSectionAlgebra W.hom
variable {ι : Type} [Finite ι] (b : Module.Basis ι S Γ(W.left, ⊤))
local notation "C" => Scheme.affineCover (Over.left (relation f hL d V c k))

/-- The explicit envelope obligation for the chosen coefficient on every full original arrow. -/
def groundEnvelopeSectionTransport (v : Γ((prod B W).left, ⊤)) : Prop :=
  ∀ i, ∃ e : independentTestEnvelope B W ((C).f i ≫ (p).left) ≅
      independentTestEnvelope B W ((C).f i ≫ (s).left),
    e.hom ≫ independentTestProjection B W ((C).f i ≫ (s).left) =
      independentTestProjection B W ((C).f i ≫ (p).left) ∧
    e.hom.appTop ((independentTestEnvelopeMap B W ((C).f i ≫ (s).left)).appTop v) =
      (independentTestEnvelopeMap B W ((C).f i ≫ (p).left)).appTop v

variable (v : Γ((prod B W).left, ⊤)) (ht : groundEnvelopeSectionTransport f a hL d V W t c l v)
include ht

/-- Whole geometric transport proves full original invariance, including cross-ground arrows. -/
theorem groundOriginalNorm_invariant :
    (p).left.appTop (regularNorm B W b v) =
      (s).left.appTop (regularNorm B W b v) := by
  exact regularNorm_eq_of_affineTransport B W B W b b v v (p).left (s).left C ht

/-- The resulting norm lies in the FULL original compatible-function ring. -/
def groundOriginalInvariantNorm :
    compatibleFunctions (p).left (s).left :=
  ⟨regularNorm B W b v,
    groundOriginalNorm_invariant f a hL d V W t c l b v ht⟩

/-- The original relation preserves the exact nonvanishing open of the transported norm. -/
theorem groundOriginalNorm_open :
    (p).left ⁻¹ᵁ B.left.basicOpen (regularNorm B W b v) =
      (s).left ⁻¹ᵁ B.left.basicOpen (regularNorm B W b v) := by
  exact (Scheme.preimage_basicOpen_top (p).left _).trans
    ((congrArg (relation f hL d V c k).left.basicOpen
      (groundOriginalNorm_invariant f a hL d V W t c l b v ht)).trans
        (Scheme.preimage_basicOpen_top (s).left _).symm)

/-- The full original relation coequalizes the entire representing function morphism. -/
theorem groundOriginalNorm_function_condition :
    (p).left ≫ (functionEquiv B.left).symm
        (regularNorm B W b v) =
      (s).left ≫ (functionEquiv B.left).symm
        (regularNorm B W b v) := by
  apply (functionEquiv _).injective
  have he : functionEquiv ((Over.map a).obj B).left
      ((functionEquiv B.left).symm (regularNorm B W b v)) = regularNorm B W b v :=
    (functionEquiv B.left).apply_symm_apply _
  simpa only [functionEquiv_comp, he] using
    groundOriginalNorm_invariant f a hL d V W t c l b v ht

/-- Descend the norm as an actual morphism on the full original locally ringed quotient. -/
def groundOriginalNormMap :
    invariantLocallyRingedSpace D ⟶ functionScheme.toLocallyRingedSpace :=
  invariantDescend D
    ((functionEquiv B.left).symm (regularNorm B W b v)).toLRSHom
    (by
      simpa only [Scheme.Hom.comp_toLRSHom] using
        congrArg Scheme.Hom.toLRSHom
          (groundOriginalNorm_function_condition f a hL d V W t c l b v ht))

/-- The descended norm retains its entire original source map, including nilpotents. -/
@[reassoc]
theorem groundOriginalNormMap_projection :
    π ≫ groundOriginalNormMap f a hL d V W t c l b v ht =
      ((functionEquiv B.left).symm (regularNorm B W b v)).toLRSHom :=
  invariantDescend_projection D _ _

end FLT.Mazur.HilbertChart.AffineRestriction
