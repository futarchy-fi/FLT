/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GaloisRepresentation.HardlyRamified.PadicOrderEmbedding
public import FLT.GaloisRepresentation.HardlyRamified.StandardFamilyMember

/-! # A dependent family retaining the actual original member at three -/

@[expose] public noncomputable section
open scoped TensorProduct
namespace GaloisRepresentation
variable (E : Type*) [Field E] [NumberField E]

/-- Insert a specified actual three-adic member, using standard members elsewhere. -/
def threeAdicFamily
    (σ₃ : GaloisRep ℚ (AlgebraicClosure ℚ_[3]) (Fin 2 → AlgebraicClosure ℚ_[3])) :
    GaloisRepFamily ℚ E 2 := fun {p} hp _ ↦ by
  classical
  by_cases h : p = 3
  · subst p
    exact σ₃
  · exact standardFamilyMember p

/-- The member at three is the supplied representation itself. -/
@[simp] theorem threeAdicFamily_three
    (σ₃ : GaloisRep ℚ (AlgebraicClosure ℚ_[3]) (Fin 2 → AlgebraicClosure ℚ_[3]))
    (φ : E →+* AlgebraicClosure ℚ_[3]) :
    threeAdicFamily E σ₃ (inferInstance : Fact (Nat.Prime 3)) φ = σ₃ := by
  simp [threeAdicFamily]

/-- Every other member is the framed scalar extension of the standard lattice. -/
theorem threeAdicFamily_ne_three
    (σ₃ : GaloisRep ℚ (AlgebraicClosure ℚ_[3]) (Fin 2 → AlgebraicClosure ℚ_[3]))
    {p : ℕ} (hp : Fact p.Prime) (φ : E →+* AlgebraicClosure ℚ_[p]) (hp3 : p ≠ 3) :
    threeAdicFamily E σ₃ hp φ = standardFamilyMember p := by
  simp [threeAdicFamily, hp3]

variable {R V : Type*} [CommRing R] [Nontrivial R] [TopologicalSpace R]
  [AddCommGroup V] [Module R V] [Module.Finite R V] [Module.Free R V]
  [Algebra R (AlgebraicClosure ℚ_[3])] [ContinuousSMul R (AlgebraicClosure ℚ_[3])]
  (hV : Module.rank R V = 2) (ρ : GaloisRep ℚ R V)

/-- The chosen embedding and framing retain the original three-adic representation. -/
def originalThreeAdicMember :
    GaloisRep ℚ (AlgebraicClosure ℚ_[3]) (Fin 2 → AlgebraicClosure ℚ_[3]) :=
  (ρ.baseChange (AlgebraicClosure ℚ_[3])).conj
    (rankTwoFrame (AlgebraicClosure ℚ_[3]) hV)

/-- The family containing the actual original representation, including its extension class. -/
def originalThreeAdicFamily : GaloisRepFamily ℚ E 2 :=
  threeAdicFamily E (originalThreeAdicMember hV ρ)

/-- The original-member equivalence is the actual coefficient-extension framing. -/
theorem originalThreeAdicFamily_three (φ : E →+* AlgebraicClosure ℚ_[3]) :
    originalThreeAdicFamily E hV ρ (inferInstance : Fact (Nat.Prime 3)) φ =
      (ρ.baseChange (AlgebraicClosure ℚ_[3])).conj
        (rankTwoFrame (AlgebraicClosure ℚ_[3]) hV) :=
  threeAdicFamily_three E _ φ

end GaloisRepresentation
