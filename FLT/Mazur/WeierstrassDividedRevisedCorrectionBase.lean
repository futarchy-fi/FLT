/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedRevisedFirstRetained
public import FLT.Mazur.WeierstrassDividedRevisedInitialBase
public import FLT.Mazur.WeierstrassDividedTerminalParameterStructure

/-!
# Coefficient projections of full first-order closing corrections

Both retained corrections and the single common terminal correction are
algebra equivalences over the original quotient ring.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages PolygonSmoothing WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
variable {R : Type} [CommRing R] {W : WeierstrassCurve R} {π : R} {n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (1 + i.val))
  (H : ArithmeticAtlasCoefficients data)

/-- Every full retained fixed-smoothing normalization preserves the coefficient ring. -/
@[reassoc] theorem arithmeticRetainedFixedSmoothingIso_base (m k : ℕ) (hk : k ≤ n)
    (a : Fin k) :
    (arithmeticRetainedFixedSmoothingIso data H m k hk a).hom ≫
      chartStructure (Quotient R π m)
        (arithmeticInitialMobiusSmoothing W H.a1_unit (π ^ 1) π m) =
      chartStructure (Quotient R π m) (parameter R π m) :=
  retainedFixedSmoothingChart_structure ..

variable [IsDomain R] (hπ : π ≠ 0) (j : ℕ) (hj : j + 1 ≤ n)
  (u : Rˣ) (hu : (data ⟨j + 1, Nat.lt_succ_of_le hj⟩).b6 = π * ↑u)
local notation "Q" => Quotient R π 1
local notation "τ" => arithmeticInitialMobiusSmoothing W H.a1_unit (π ^ 1) π 1
local notation "σ" => arithmeticTerminalChangedSmoothing data H 1 j hj u hu

/-- The complete retained residual factor acts over the original quotient base. -/
@[reassoc] theorem arithmeticFirstResidualRetainedIso_base (b : Bool) :
    (arithmeticFirstResidualRetainedIso hπ data H j hj u hu b).hom ≫
      chartStructure Q τ = chartStructure Q τ :=
  terminalComponent_algebra_structure
    (arithmeticFirstResidualRetainedFactor hπ data H j hj u hu b).toAlgHom

/-- The common terminal correction preserves coefficients on its entire node. -/
@[reassoc] theorem arithmeticFirstResidualTerminalIso_base :
    (arithmeticFirstResidualTerminalIso hπ data H j hj u hu).hom ≫
      chartStructure Q σ = chartStructure Q σ :=
  terminalComponent_algebra_structure
    (arithmeticFirstResidualTerminalFactor hπ data H j hj u hu).symm.toAlgHom

/-- The actual corrected map from every retained source node lies over its original base. -/
@[reassoc] theorem arithmeticFirstOriginalRevisedRetainedMap_base
    (a : Fin (j + 1)) (b : Bool) :
    arithmeticFirstOriginalRevisedRetainedMap hπ data H j hj u hu a b ≫
      arithmeticRevisedPolygonToBase data H 1 j hj u hu =
        chartStructure Q (parameter R π 1) := by
  rw [arithmeticFirstOriginalRevisedRetainedMap]
  simp only [Category.assoc, arithmeticRevisedPolygonRetainedChart_base,
    twistedRetainedOrientation_base]
  split_ifs
  · rw [arithmeticFirstResidualRetainedIso_base, arithmeticRetainedFixedSmoothingIso_base]
  · rw [Iso.refl_hom, Category.id_comp, arithmeticRetainedFixedSmoothingIso_base]

end FLT.Mazur.WeierstrassDividedDepth
