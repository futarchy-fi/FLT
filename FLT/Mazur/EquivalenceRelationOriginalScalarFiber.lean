/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.EquivalenceRelationCompleteSupportedTests
public import FLT.Mazur.ScalarAlgebraicClosureTests

/-!
# Exact equations on the full original scalar fiber

Full invariant-character containment supplies exact equations on the original
relation pulled back along the scalar residue closure. The pullback retains
all nilpotents and every independent second endpoint. No reduction or passage
to a finite complete quotient stage is used.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.EquivalenceRelationNormalizedFrames
open FiniteGroupRestriction SchemeFiniteGroupQuotient ScalarTestLocalization
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] source action restrictedAction
variable {D A : Scheme} {p q : D ⟶ A} [IsSeparated p] [Etale p]
  (e : CategoryTheory.EquivalenceRelation p q) (I : Type) [Fintype I] (o : I)
  (U : (source p q I o).Opens)
  (hU : ∀ g : Equiv.Perm I, (action e I o g).hom ⁻¹ᵁ U = U)
  [IsAffine U.toScheme]
local notation "k" => U.ι ≫ first p q I o
local notation "F" => SchemeRelationRestriction.fst p q k
local notation "H" => SchemeRelationRestriction.snd p q k
local notation "Rel" => SchemeRelationRestriction.doubleDomain p q k
local notation "ρ" => restrictedAction (action e I o) U hU
local notation "J" => completeAffineOrbitIdeal e I o U hU
variable {R : Type} [CommRing R]
  (s : R →+* invariantCoordinates (restrictedAction (action e I o) U hU))
  (P : PrimeSpectrum R)
local notation "K" => AlgebraicClosure P.asIdeal.ResidueField
local notation "b" => Spec.map (CommRingCat.ofHom (algebraMap R K))
local notation "φ" => F ≫ quotientMap ρ ≫ Spec.map (CommRingCat.ofHom s)

/-- The entire original relation fiber, restricting only its first scalar endpoint. -/
abbrev originalScalarRelationFiber : Scheme := pullback φ b

/-- Keep the full original relation arrow and both independently chosen endpoints. -/
abbrev originalScalarRelationFiberMap : originalScalarRelationFiber e I o U hU s P ⟶ Rel :=
  pullback.fst φ b

omit [Etale p] [IsAffine U.toScheme] in
/-- Every point of the constructed full relation fiber has exactly the original scalar prime. -/
theorem originalScalarRelationFiber_center (x : originalScalarRelationFiber e I o U hU s P) :
    PrimeSpectrum.comap s
      ((originalScalarRelationFiberMap e I o U hU s P ≫ F ≫ quotientMap ρ) x) = P := by
  have he := congrArg (fun a ↦ a x) (pullback.condition (f := φ) (g := b))
  change PrimeSpectrum.comap s
    ((originalScalarRelationFiberMap e I o U hU s P ≫ F ≫ quotientMap ρ) x) =
      PrimeSpectrum.comap (algebraMap R K) (pullback.snd φ b x) at he
  rw [Subsingleton.elim (pullback.snd φ b x) (⊥ : PrimeSpectrum K)] at he
  exact he.trans (algebraicClosure_residue_center P)

/-- Character containment controls every point, including nonclosed points of the full fiber. -/
theorem originalScalarRelationFiber_complete (hs : s.FiniteType)
    (hJ : ∀ χ : invariantCoordinates ρ →+* K, χ.comp s = algebraMap R K →
      J ≤ RingHom.ker χ) :
    Set.range (originalScalarRelationFiberMap e I o U hU s P ≫ F ≫ quotientMap ρ) ⊆
      (completeAffineOrbitImage e I o U hU : Set (quotient ρ)) := by
  rw [← completeAffineOrbitIdeal_zeroLocus]
  rintro _ ⟨x, rfl⟩ t ht
  apply (residueGeometricTest_iff_original_fiber s P hs t).mp _ _
    (originalScalarRelationFiber_center e I o U hU s P x)
  exact (residueGeometricTest_iff s P t).mpr (fun χ hχ ↦ hJ χ hχ ht)

/-- The full original fiber satisfies exact equations, including all nilpotent directions. -/
theorem originalScalarRelationFiber_equalizes [IsLocallyNoetherian A] (hs : s.FiniteType)
    (hJ : ∀ χ : invariantCoordinates ρ →+* K, χ.comp s = algebraMap R K →
      J ≤ RingHom.ker χ) (t : invariantCoordinates ρ) :
    (originalScalarRelationFiberMap e I o U hU s P ≫ F).appTop t.val =
      (originalScalarRelationFiberMap e I o U hU s P ≫ H).appTop t.val :=
  completeOrbitSupportedTest_equalizes e I o U hU _
    (originalScalarRelationFiber_complete e I o U hU s P hs hJ) t

end FLT.Mazur.EquivalenceRelationNormalizedFrames
