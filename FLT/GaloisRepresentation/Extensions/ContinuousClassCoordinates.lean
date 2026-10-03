/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GaloisRepresentation.Extensions.ContinuousCocycleCoordinates
public import FLT.GaloisRepresentation.Extensions.CharacterCoefficients

/-!
# Scalar extension of explicit continuous classes in basis coordinates

Every class over a finite extension has prime-field coordinate classes.
Equality is detected coordinatewise, including all changes of splitting.
This is the finite-basis model of scalar extension, before its linear upgrade.
-/

@[expose] public section

namespace GaloisRepresentation.Extensions

variable {G M ι : Type*} [Group G] [TopologicalSpace G]
    [AddCommGroup M] [DistribMulAction G M] [TopologicalSpace M]

/-- The coordinate classes of a continuous product-valued cocycle class. -/
def classCoordinates (x : ContinuousClass G (ι → M)) (i : ι) : ContinuousClass G M :=
  Quotient.map (fun c ↦ cocycleCoordinate c i)
    (fun _ _ h ↦ (splittingEquivalent_coordinates_iff _ _).mp h i) x

/-- Equality of classes is detected by their coordinates. -/
theorem classCoordinates_injective : Function.Injective (classCoordinates (G := G) (M := M)
    (ι := ι)) := by
  intro x y
  induction x using Quotient.inductionOn with | h c =>
    induction y using Quotient.inductionOn with | h d =>
      intro h
      apply Quotient.sound
      apply (splittingEquivalent_coordinates_iff _ _).mpr
      intro i
      exact Quotient.exact (congrFun h i)

/-- Representatives of each coordinate reconstruct every family of classes. -/
theorem classCoordinates_surjective : Function.Surjective (classCoordinates (G := G)
    (M := M) (ι := ι)) := by
  intro x
  classical
  refine ⟨continuousClassMk (cocycleFromCoordinates (fun i ↦ (x i).out)), ?_⟩
  funext i
  change continuousClassMk (x i).out = x i
  exact Quotient.out_eq _

/-- Product coefficients give exactly the product of continuous classes. -/
noncomputable def classCoordinatesEquiv :
    ContinuousClass G (ι → M) ≃ (ι → ContinuousClass G M) :=
  Equiv.ofBijective classCoordinates ⟨classCoordinates_injective, classCoordinates_surjective⟩

variable {F k : Type*} [Field F] [Field k] [Algebra F k]
    (χ : G →* Fˣ) [Fintype ι] (b : Module.Basis ι F k)

/-- Continuous classes of an extended character line in a finite coefficient basis. -/
noncomputable def characterClassCoordinates :
    ContinuousClass G (CharacterModule χ k) ≃ (ι → ContinuousClass G (CharacterModule χ F)) :=
  (coefficientClassEquiv (characterBasisCoordinates χ b).toAddEquiv
    (characterBasisCoordinates_equivariant χ b)).trans classCoordinatesEquiv

/-- The comparison on cocycles computes each actual basis coordinate. -/
theorem characterClassCoordinates_mk (c : ContinuousCocycle G (CharacterModule χ k)) (i : ι) :
    characterClassCoordinates χ b (continuousClassMk c) i =
      continuousClassMk (cocycleCoordinate
        (mapCoefficientCocycle (characterBasisCoordinates χ b).toAddEquiv
          (characterBasisCoordinates_equivariant χ b) c) i) := rfl

end GaloisRepresentation.Extensions
