/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PartialProperEnvelopeInterior
public import FLT.Mazur.AffineBaseSectionFunctor
public import Mathlib.AlgebraicGeometry.Morphisms.Finite

/-!
# Arbitrary envelope opens detected by partial finite translation charts

Finite bases imply proper chart projections. Thus partial charts of the
excluded locus suffice for full-interior neighborhoods of arbitrary opens,
without extending any chosen chart section to the entire envelope.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.SchemeTranslationNorm
open Approximation SchemeOpenEnvelope
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {R : Type} [CommRing R] (B W : Over (Spec (.of R)))
  {I : Type} (T : I → Over (Spec (.of R))) (t : ∀ i, T i ⟶ W)
  [∀ i, IsAffine (T i).left]
/-- Each partial translation chart keeps the algebra of its given structural map. -/
local instance partialFiniteTranslationAlgebra (i : I) : Algebra R Γ((T i).left, ⊤) :=
  affineBaseSectionAlgebra (T i).hom
variable {ι : I → Type} [∀ i, Finite (ι i)]
  (b : ∀ i, Module.Basis (ι i) R Γ((T i).left, ⊤))

include b

/-- A finite basis of the actual section algebra makes the chart structural map finite. -/
theorem partialTranslation_isFinite (i : I) : IsFinite (T i).hom := by
  let _ := Module.Finite.of_basis (b i)
  have h : (T i).left.isoSpec.hom ≫
      Spec.map (CommRingCat.ofHom (algebraMap R Γ((T i).left, ⊤))) = (T i).hom :=
    affineBaseSectionsSpecIso_over R (T i)
  let _ : IsFinite (Spec.map (CommRingCat.ofHom (algebraMap R Γ((T i).left, ⊤)))) :=
    (IsFinite.SpecMap_iff _).mpr (RingHom.finite_algebraMap.mpr inferInstance)
  rw [← h]
  infer_instance

/-- Independent products of the finite translation charts have closed source projections. -/
theorem partialTranslationProjection_isClosedMap (i : I) :
    IsClosedMap (prod.fst : prod B (T i) ⟶ B).left := by
  let _ := partialTranslation_isFinite T b i
  let _ : IsFinite (prod.fst : prod B (T i) ⟶ B).left := MorphismProperty.of_isPullback
    (Over.isPullback_of_binaryFan_isLimit _ (prodIsProd B (T i))).flip
    (inferInstanceAs (IsFinite (T i).hom))
  exact (prod.fst : prod B (T i) ⟶ B).left.isClosedMap

variable [Finite I] (U : (prod B W).left.Opens)
  (ht : ∀ y : (prod B W).left, y ∉ U →
    ∃ i, ∃ z : (T i).left, (t i).left z = (prod.snd : prod B W ⟶ W).left y)
local notation "π" => Over.Hom.left (prod.fst : prod B W ⟶ B)

include ht b

/-- The arbitrary open has an open full-fiber locus using only partial finite translation charts. -/
theorem isOpen_fullFiber_open_of_partialFiniteTranslation : IsOpen (fullFiberLocus π U) := by
  rw [fullFiberLocus_partialTranslationCover B W T t U ht]
  apply isOpen_iInter_of_finite
  intro i
  exact (fullFiberOpen (prod.fst : prod B (T i) ⟶ B).left
    ((prod.map (𝟙 B) (t i)).left ⁻¹ᵁ U)
    (partialTranslationProjection_isClosedMap B T b i)).isOpen

/-- Every actual full fiber belongs to the constructed maximal open. -/
theorem fullInterior_open_eq_of_partialFiniteTranslation :
    (fullFiberInterior π U : Set B.left) = fullFiberLocus π U :=
  (isOpen_fullFiber_open_of_partialFiniteTranslation B W T t b U ht).interior_eq

/-- Partial finite charts construct original source denominators for finite sets of full fibers. -/
theorem exists_denominator_of_partialFiniteTranslation [IsAffine B.left]
    (F : Set B.left) (hF : F.Finite) (hFU : F ⊆ fullFiberLocus π U) :
    ∃ r : Γ(B.left, ⊤), F ⊆ B.left.basicOpen r ∧ r ∈ denominatorIdeal (π).appTop.hom U := by
  apply exists_fullFiberInterior_coefficient π U F hF
  rwa [fullInterior_open_eq_of_partialFiniteTranslation B W T t b U ht]

end FLT.Mazur.SchemeTranslationNorm
