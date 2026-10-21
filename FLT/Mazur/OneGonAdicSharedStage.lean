/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OneGonAdicIndependentStageNormalForm
public import FLT.Mazur.OneGonAdicIndependentStageRefinement

/-!+# Actual independent stages in a prescribed shared finite ring

Any finite-type subalgebra containing a supplied stage is itself a literal
stage in that support diagram. Its transition refines the supplied smooth map.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.OneGonAdicIndependentModel
open Approximation OneGonSmoothing CharacterSchemeBaseChange OneGonAdicCharacterTower
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type} [CommRing R] (I : Ideal R) [IsAdicComplete I R]
  (t : R) (ht : t ∈ I) (n : ℕ) [NeZero n] (s : Set R)
  (K : Subalgebra ℤ R) [Algebra.FiniteType ℤ K] (hK : base I t ht n s ≤ K)

/-- The prescribed finite ring, viewed as an actual stage of the support diagram. -/
def sharedStage : (CoefficientStage (base I t ht n s))ᵒᵖ :=
  Opposite.op ⟨K, hK, inferInstance⟩

/-- The coefficient algebra is the literal inclusion of the support into the shared ring. -/
@[instance_reducible]
def sharedAlgebra : Algebra (base I t ht n s) K := (Subalgebra.inclusion hK).toAlgebra

/-- The shared stage carries exactly the prescribed ring. -/
theorem sharedStage_base : stageBase I t ht n s (sharedStage I t ht n s K hK) = K := rfl

omit [Algebra.FiniteType ℤ K] in
/-- Its arithmetic parameter is the original element of the ambient adic ring. -/
theorem shared_parameter_eq (u : Set R) (hU : base I t ht n u ≤ K) :
    Subalgebra.inclusion hK (parameter I t ht n s) =
      Subalgebra.inclusion hU (parameter I t ht n u) := by
  apply Subtype.ext
  rfl

/-- Every supplied stage contained in the shared ring has its actual diagram transition. -/
def sharedToStage (i : (CoefficientStage (base I t ht n s))ᵒᵖ)
    (hi : stageBase I t ht n s i ≤ K) : sharedStage I t ht n s K hK ⟶ i :=
  (homOfLE (show i.unop ≤ (sharedStage I t ht n s K hK).unop from hi)).op

/-- The shared curve has the coefficient algebra of the literal support inclusion. -/
theorem sharedStage_curve (hs : complementaryInverse I t ht ∈ s) :
    stageCurve I t ht n s (sharedStage I t ht n s K hK) hs =
      (ArithmeticOneGonGeneralizedCurve.curve (parameter I t ht n s)
        (parameter_complementaryUnit I t ht n s hs)).baseChange
          (@baseMap (base I t ht n s) K _ _ (sharedAlgebra I t ht n s K hK)) :=
  stageCurve_eq I t ht n s (sharedStage I t ht n s K hK) hs

end FLT.Mazur.OneGonAdicIndependentModel
