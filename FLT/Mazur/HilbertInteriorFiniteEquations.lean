/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.EnvelopeInteriorFiniteAffineCover
public import FLT.Mazur.EnvelopeBoundaryIdealTransport
public import FLT.Mazur.ValuativeHilbertParameterCriterion
public import FLT.Mazur.AffineHilbertFullInteriorChart

/-!
# Finite original Hilbert equations and their full-relation transport

The original proper-family hypotheses construct a finite affine atlas of
the full interior and finitely many equations for its complement. The
equations detect exactly acyclicity and retention of the original parameter
on all centered valuation tests. Their pulled-back radicals agree along
every affine test of the full original relation, including independent lifts.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite IsLocalRing
namespace FLT.Mazur.HilbertChart.AffineRestriction
open CartierAbel SchemePicard FCurve SchemeOpenEnvelope
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type} [CommRing R] [Algebra.FiniteType ℤ R] {X : Scheme}
  (f : X ⟶ Spec (.of R)) [IsProper f] [Flat f] [GeometricallyIntegral f]
  [SmoothOfRelativeDimension 1 f] {L : X.Modules} (hL : AmpleLineBundle L)
  (d : ℕ) (V : Over (Spec (.of R))) [Etale V.hom] [IsAffine V.left]
  (c : (relativeFppfSheaf f).obj.obj (op V))
  {A : Over (Spec (.of R))} [IsAffine A.left]
  (k : A ⟶ variableHilbertTest f d V) [IsOpenImmersion k.left]
local notation "π" => Over.Hom.left (prod.fst : prod A V ⟶ A)
local notation "O" => Scheme.Hom.opensRange (Over.Hom.left (toEnvelope f hL d V c k))

/-- Actual finite generators in the original parameter ring. -/
def originalInteriorEquations : Finset Γ(A.left, ⊤) := by
  let _ := selectedHilbertSource_isLocallyNoetherian f d V k
  exact interiorGenerators π O

omit [IsAffine V.left] in
/-- The equations generate the exact denominator ideal, not just a smaller test ideal. -/
theorem originalInteriorEquations_span :
    Ideal.span (originalInteriorEquations f hL d V c k : Set Γ(A.left, ⊤)) =
      denominatorIdeal (π).appTop.hom O := by
  let _ := selectedHilbertSource_isLocallyNoetherian f d V k
  exact interiorGenerators_span π O

omit [IsAffine V.left] in
/-- A finite coefficient test detects every point of the original interior. -/
theorem originalInteriorEquations_mem (x : A.left) :
    x ∈ fullEnvelopeInterior f hL d V c k ↔
      ∃ r ∈ originalInteriorEquations f hL d V c k, x ∈ A.left.basicOpen r :=
  interior_iff_generator π O _ (originalInteriorEquations_span f hL d V c k) x

/-- The original interior has a constructed finite affine scheme atlas. -/
def originalInteriorEquationCover : (fullInteriorSource f hL d V c k).left.OpenCover := by
  let _ := selectedHilbertSource_isLocallyNoetherian f d V k
  exact interiorAffineCover π O

instance originalInteriorEquationCover_finite :
    Finite (originalInteriorEquationCover f hL d V c k).I₀ := by
  let _ := selectedHilbertSource_isLocallyNoetherian f d V k
  exact inferInstanceAs (Finite (interiorAffineCover π O).I₀)

instance originalInteriorEquationCover_affine
    (r : (originalInteriorEquationCover f hL d V c k).I₀) :
    IsAffine ((originalInteriorEquationCover f hL d V c k).X r) := by
  let _ := selectedHilbertSource_isLocallyNoetherian f d V k
  exact inferInstanceAs (IsAffine ((interiorAffineCover π O).X r))

local notation "σ" => sectionAt f hL d V c k
local notation "b" D => valuationEnvelopeMap D ≫ prod.fst
local notation "v" D => valuationEnvelopeMap D ≫ prod.snd
local notation "s" D => CategoryTheory.Functor.map
  (ObjectProperty.FullSubcategory.obj (relativeFppfSheaf f)) (Quiver.Hom.op (b D)) σ

/-- Finite scalar nonvanishing is equivalent to the actual original Hilbert valuation tests. -/
theorem originalInteriorEquations_valuation_iff (x : A.left) :
    (∃ r ∈ originalInteriorEquations f hL d V c k, x ∈ A.left.basicOpen r) ↔
      ∀ D : ValuativeCommSq π, D.i₂ (closedPoint D.R) = x →
        ∃ hs : (s D) * (relativeFppfSheaf f).obj.map (v D).op c ∈
            (acyclicDegreePicardSubfunctor f d).obj
              (op (Over.mk (D.i₁ ≫ (prod A V).hom))),
          (acyclicTranslationLift f hL d V c (s D) (v D) hs).left
            (default : Spec (.of D.K)) ∈ Set.range k.left :=
  (originalInteriorEquations_mem f hL d V c k x).symm.trans
    (fullInterior_iff_valuation_parameters f hL d c k x)

omit [IsAffine V.left] in
/-- Boundary ideals agree up to radical on every affine test of the full original relation. -/
theorem originalBoundaryIdeal_relation_radicals {Z : Scheme} [IsAffine Z]
    (z : Z ⟶ (relation f hL d V c k).left) :
    ((denominatorIdeal (π).appTop.hom O).map
      (z ≫ (fst f hL d V c k).left).appTop.hom).radical =
    ((denominatorIdeal (π).appTop.hom O).map
      (z ≫ (snd f hL d V c k).left).appTop.hom).radical := by
  apply radical_map_denominator_eq
  apply SetLike.coe_injective
  exact congrArg (fun U : (relation f hL d V c k).left.Opens ↦ z ⁻¹' (U : Set _))
    (fullEnvelopeInterior_invariant f hL d V c k)

end FLT.Mazur.HilbertChart.AffineRestriction
