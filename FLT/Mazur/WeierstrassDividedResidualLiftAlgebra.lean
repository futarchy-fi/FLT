/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.PolygonSmoothingPunctureSpecCalculus
public import FLT.Mazur.WeierstrassDividedResidualLiftTransitionsFirst
public import FLT.Mazur.WeierstrassDividedTerminalResidualAlgebra

/-!
# Full Laurent algebra of the corrected arithmetic closing residual

The actual geometric composition K inverse, D, S inverse corresponds to
S inverse followed by D followed by K inverse on functions. Both incoming
and outgoing retained substitutions keep their entire Laurent support.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
open scoped LaurentPolynomial
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages PolygonSmoothing WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
variable {R : Type} [CommRing R] [IsDomain R] {W : WeierstrassCurve R} {π : R}
  (hπ : π ≠ 0) {n : ℕ} (data : (i : Fin (n + 1)) → Data W π (1 + i.val))
  (H : ArithmeticAtlasCoefficients data) (m j : ℕ) (hj : j + 1 ≤ n)
  (u : Rˣ) (hu : (data ⟨j + 1, Nat.lt_succ_of_le hj⟩).b6 = π * ↑u)
local notation "Q" => Quotient R π m
local notation "A" => arithmeticResidualLiftRetainedPuncture hπ data H m j hj u hu
local notation "S" => arithmeticResidualLiftTerminalPuncture hπ data H m j hj u hu

/-- The full retained substitution in the original inverse edge coordinate. -/
def arithmeticResidualLiftEdgeEquiv (b a : Bool) : Q[T;T⁻¹] ≃ₐ[Q] Q[T;T⁻¹] :=
  (LaurentPolynomial.invert.trans (A b a)).trans LaurentPolynomial.invert

local notation "K" => arithmeticResidualLiftEdgeEquiv hπ data H m j hj u hu

/-- Both full edge substitutions induce exactly the previously constructed geometric edges. -/
theorem arithmeticResidualLiftEdgeEquiv_spec (b a : Bool) :
    punctureSpecIso (K b a) = arithmeticResidualLiftEdgeIso hπ data H m j hj u hu b a := by
  simp only [arithmeticResidualLiftEdgeEquiv, punctureSpecIso_trans,
    punctureSpecIso_invert, arithmeticResidualLiftEdgeIso]
  rfl

/-- The complete new residual, with contravariant order and all inverse terms retained. -/
def arithmeticResidualLiftClosingEquiv (b : Bool) : Q[T;T⁻¹] ≃ₐ[Q] Q[T;T⁻¹] :=
  ((S b).symm.trans (arithmeticTerminalResidualEquiv data H m j hj u hu b)).trans
    (K b true).symm

local notation "E" => arithmeticResidualLiftClosingEquiv hπ data H m j hj u hu

/-- The full algebra residual realizes the actual corrected geometric closing residual. -/
theorem arithmeticResidualLiftClosingEquiv_spec (b : Bool) :
    punctureSpecIso (E b) = arithmeticResidualLiftClosingResidual hπ data H m j hj u hu b := by
  have hd : punctureSpecIso (arithmeticTerminalResidualEquiv data H m j hj u hu b) =
      arithmeticTerminalResidualTwist data H m j hj u hu b := by
    apply Iso.ext
    exact arithmeticTerminalResidualEquiv_spec data H m j hj u hu b
  rw [arithmeticResidualLiftClosingEquiv, punctureSpecIso_trans, punctureSpecIso_trans,
    punctureSpecIso_symm, arithmeticResidualLiftEdgeEquiv_spec, hd]
  rfl

/-- The incoming full algebra transition is identity on the first arithmetic layer. -/
theorem arithmeticResidualLiftEdgeEquiv_incoming_first (b : Bool) :
    arithmeticResidualLiftEdgeEquiv hπ data H 1 j hj u hu b false = AlgEquiv.refl := by
  apply punctureSpecIso_injective
  rw [arithmeticResidualLiftEdgeEquiv_spec, arithmeticResidualLiftEdgeIso_incoming_first,
    punctureSpecIso_refl]
  rfl

/-- The full corrected algebra residual is identity on the first arithmetic layer. -/
theorem arithmeticResidualLiftClosingEquiv_first (b : Bool) :
    arithmeticResidualLiftClosingEquiv hπ data H 1 j hj u hu b = AlgEquiv.refl := by
  apply punctureSpecIso_injective
  rw [arithmeticResidualLiftClosingEquiv_spec, arithmeticResidualLiftClosingResidual_first,
    punctureSpecIso_refl]
  rfl

end FLT.Mazur.WeierstrassDividedDepth
