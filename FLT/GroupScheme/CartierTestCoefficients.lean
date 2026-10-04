/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.CartierTestNaturality

/-! # Coefficient transport of the original integral Cartier evaluation -/

@[expose] public noncomputable section
namespace HopfAlgebra.CartierDual
variable {R A S T : Type} [CommRing R] [CommRing A] [CommRing S] [CommRing T]
  [Algebra R S] [Algebra R T] [HopfAlgebra R A] [Module.Finite R A] [Module.Free R A]

/-- Evaluation commutes with every map of test algebras, including integral reductions. -/
theorem testEvaluation_coefficients (q : S →ₐ[R] T)
    (ψ : CartierDual R A →ₐ[R] S) (d : A →ₗ[R] S) :
    q (testEvaluation ψ d) = testEvaluation (q.comp ψ) (q.toLinearMap.comp d) := by
  rw [testEvaluation_eq_sum (Module.Free.chooseBasis R A),
    testEvaluation_eq_sum (Module.Free.chooseBasis R A)]
  simp

/-- The finite character commutes with coefficient specialization as an equality of units. -/
theorem testCharacter_coefficients (q : S →ₐ[R] T)
    (ψ : CartierDual R A →ₐ[R] S) (f : A →ₐ[R] S) :
    Units.map q.toMonoidHom (testCharacter ψ (WithConv.toConv f)) =
      testCharacter (q.comp ψ) (WithConv.toConv (q.comp f)) := by
  apply Units.ext
  exact testEvaluation_coefficients q ψ f.toLinearMap

/-- Transposed original morphisms give the same character on every integral test algebra. -/
theorem testCharacter_naturality {B : Type} [CommRing B] [HopfAlgebra R B]
    [Module.Finite R B] [Module.Free R B] (f : A →ₐc[R] B)
    (ψ : CartierDual R A →ₐ[R] S) (x : B →ₐ[R] S) :
    testCharacter (ψ.comp (map f)) (WithConv.toConv x) =
      testCharacter ψ (WithConv.toConv (x.comp f.toAlgHom)) := by
  apply Units.ext
  exact testEvaluation_naturality f ψ x.toLinearMap

end HopfAlgebra.CartierDual
