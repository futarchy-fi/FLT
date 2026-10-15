/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ValuativeHilbertParameterCriterion
public import FLT.Mazur.FiniteValuativeEnvelopeTest

/-!
# A finite set of original Hilbert coordinates controls all valuation tests

Choose finitely many actual generic points of the excluded original
relation image. Only valuation squares with these generic coordinates need
acyclicity and parameter retention checked. The same finite family works
for every original source point, including all nongeneric coefficient points.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite IsLocalRing
namespace FLT.Mazur.HilbertChart.AffineRestriction
open CartierAbel SchemePicard FCurve SchemeOpenEnvelope
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type} [CommRing R] {A V : Over (Spec (.of R))}
local notation "π" => Over.Hom.left (prod.fst : prod A V ⟶ A)

variable [Algebra.FiniteType ℤ R] {X : Scheme}
  (f : X ⟶ Spec (.of R)) [IsProper f] [Flat f] [GeometricallyIntegral f]
  [SmoothOfRelativeDimension 1 f] {L : X.Modules} (hL : AmpleLineBundle L)
  (d : ℕ) (c : (relativeFppfSheaf f).obj.obj (op V))
  (k : A ⟶ variableHilbertTest f d V) [IsOpenImmersion k.left]
local notation "σ" => sectionAt f hL d V c k
local notation "b" D => valuationEnvelopeMap D ≫ prod.fst
local notation "v" D => valuationEnvelopeMap D ≫ prod.snd
local notation "s" D => CategoryTheory.Functor.map
  (ObjectProperty.FullSubcategory.obj (relativeFppfSheaf f)) (Quiver.Hom.op (b D)) σ

variable [Etale V.hom] [IsAffine V.left] [IsAffine A.left]

/-- Finite original generic coordinates suffice, uniformly over every original source point. -/
theorem exists_finite_valuation_parameter_test :
    ∃ F : Set (prod A V).left, F.Finite ∧
      (∀ e ∈ F, e ∉ (toEnvelope f hL d V c k).left.opensRange) ∧
      ∀ x : A.left, x ∈ fullEnvelopeInterior f hL d V c k ↔
        ∀ D : ValuativeCommSq π, D.i₂ (closedPoint D.R) = x →
          D.i₁ (default : Spec (.of D.K)) ∈ F →
          ∃ hs : (s D) * (relativeFppfSheaf f).obj.map (v D).op c ∈
              (acyclicDegreePicardSubfunctor f d).obj
                (op (Over.mk (D.i₁ ≫ (prod A V).hom))),
            (acyclicTranslationLift f hL d V c (s D) (v D) hs).left
              (default : Spec (.of D.K)) ∈ Set.range k.left := by
  let _ := selectedHilbertSource_isLocallyNoetherian f d V k
  let _ := EnvelopeVerticalGenerizations.original_envelope_noetherian A V
  obtain ⟨F, hF, hFO, ht⟩ := exists_finite_valuation_test π
    (toEnvelope f hL d V c k).left.opensRange
  refine ⟨F, hF, hFO, fun x ↦ ?_⟩
  change x ∈ fullFiberInterior π (toEnvelope f hL d V c k).left.opensRange ↔ _
  rw [ht x]
  exact forall_congr' fun D ↦ imp_congr_right fun _ ↦
    imp_congr_right fun _ ↦ valuation_generic_mem_iff f hL d c k D

end FLT.Mazur.HilbertChart.AffineRestriction
