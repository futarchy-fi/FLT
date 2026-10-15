/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OriginalEnvelopeAcyclicCriterion
public import FLT.Mazur.ValuativeEnvelopeInterior
public import FLT.Mazur.NoetherianEnvelopeGenericInterior
public import FLT.Mazur.VariableHilbertNoetherianSource

/-!
# Exact Hilbert-parameter tests along valuation specializations

The valuation test retains the original independent source and translation
maps. Its generic coordinate belongs to the original relation exactly when
the translated class is acyclic and its constructed Hilbert parameter is
retained. Testing these conditions over all valuation squares centered at
one source point characterizes its ORIGINAL full interior, even over a
nonreduced coefficient ring. No extension of the translation is assumed.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite IsLocalRing
namespace FLT.Mazur.HilbertChart.AffineRestriction
open CartierAbel SchemePicard FCurve SchemeOpenEnvelope
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type} [CommRing R] {A V : Over (Spec (.of R))}
local notation "π" => Over.Hom.left (prod.fst : prod A V ⟶ A)

/-- The whole generic envelope map, over its actual original coefficient map. -/
def valuationEnvelopeMap (D : ValuativeCommSq π) :
    Over.mk (D.i₁ ≫ (prod A V).hom) ⟶ prod A V := Over.homMk D.i₁

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

/-- The actual generic valuation coordinate is retained iff both geometric conditions hold. -/
theorem valuation_generic_mem_iff (D : ValuativeCommSq π) :
    D.i₁ (default : Spec (.of D.K)) ∈ (toEnvelope f hL d V c k).left.opensRange ↔
      ∃ hs : (s D) * (relativeFppfSheaf f).obj.map (v D).op c ∈
          (acyclicDegreePicardSubfunctor f d).obj (op (Over.mk (D.i₁ ≫ (prod A V).hom))),
        (acyclicTranslationLift f hL d V c (s D) (v D) hs).left
          (default : Spec (.of D.K)) ∈ Set.range k.left := by
  have h := original_envelope_geometric_mem_iff f hL d V c k (b D) (v D)
  have he : prod.lift (b D) (v D) = valuationEnvelopeMap D := by
    apply prod.hom_ext
    · exact prod.lift_fst _ _
    · exact prod.lift_snd _ _
  rw [he] at h
  exact h

variable [Etale V.hom] [IsAffine V.left] [IsAffine A.left]

/-- The proper-family problem reduces exactly to actual acyclicity and parameter retention
on valuation generic fibers; neither a changed fiber nor a chosen finite branch suffices. -/
theorem fullInterior_iff_valuation_parameters (x : A.left) :
    x ∈ fullEnvelopeInterior f hL d V c k ↔
      ∀ D : ValuativeCommSq π, D.i₂ (closedPoint D.R) = x →
        ∃ hs : (s D) * (relativeFppfSheaf f).obj.map (v D).op c ∈
            (acyclicDegreePicardSubfunctor f d).obj
              (op (Over.mk (D.i₁ ≫ (prod A V).hom))),
          (acyclicTranslationLift f hL d V c (s D) (v D) hs).left
            (default : Spec (.of D.K)) ∈ Set.range k.left := by
  let _ := selectedHilbertSource_isLocallyNoetherian f d V k
  let _ := EnvelopeVerticalGenerizations.original_envelope_noetherian A V
  change x ∈ fullFiberInterior π (toEnvelope f hL d V c k).left.opensRange ↔ _
  rw [interior_iff_valuation]
  exact forall_congr' fun D ↦ imp_congr_right fun _ ↦ valuation_generic_mem_iff f hL d c k D

end FLT.Mazur.HilbertChart.AffineRestriction
