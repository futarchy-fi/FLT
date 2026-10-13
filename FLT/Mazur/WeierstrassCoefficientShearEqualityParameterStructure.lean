/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassCoefficientShearEqualityChartParameters
import all FLT.Mazur.WeierstrassCoefficientShearRetainedFiber

/-!
# Coefficient structures of both entire equality component parameters

Extract the entire conic and divided equation, including both incidence markings.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
open scoped Polynomial
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassSuccessiveX WeierstrassModificationX WeierstrassDilatation
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option quotPrecheck false
universe u
variable {R : Type u} [CommRing R]
  {W : WeierstrassCurve R} {π : R} {start n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (S : Type u) [Field S] [Algebra R S] (r : S) (j : ℕ) (hj : j + 1 ≤ n)
local notation "d" => data (Fin.mk (j + 1) (Nat.lt_succ_of_le hj))
variable (hs : algebraMap R S (π ^ (start + j)) = 0) (hp : algebraMap R S π = 0)
  (h3 : algebraMap R S (data ⟨j + 1, Nat.lt_succ_of_le hj⟩).b3 = 0)
  (h4 : algebraMap R S (data ⟨j + 1, Nat.lt_succ_of_le hj⟩).b4 = 0)
  (hc : IsUnit (algebraMap R S (data ⟨j + 1, Nat.lt_succ_of_le hj⟩).b6))
  (hr : r ^ 2 + algebraMap R S W.a₁ * r - algebraMap R S W.a₂ = 0)
  (a : Sˣ) (ha : (a : S) = (rootShearCurve (W.map (algebraMap R S)) r).a₁)
local notation "U" => rootShearCurve (W.map (algebraMap R S)) r
local notation "c" => algebraMap R S (Data.b6 d)
local notation "hu" => Eq.mp (congrArg IsUnit ha) (Units.isUnit a)
local notation "hsNext" => show algebraMap R S (π ^ (start + (j + 1))) = 0 from by
  rw [← Nat.add_assoc, pow_succ, map_mul, hp, mul_zero]
local notation "P" => WeierstrassSuccessiveShearTerminal.laurentConicComponent
  W π (start + j) (Data.b3 d) (Data.b4 d) (Data.b6 d) S r hs hp h3 h4 hr hc a ha
local notation "l" => WeierstrassSuccessiveShearTerminal.laurentConicComponentConic
  W π (start + j) (Data.b3 d) (Data.b4 d) (Data.b6 d) S r hs hp h3 h4 hr hc a ha
local notation "t" => WeierstrassSuccessiveShearTerminal.laurentConicComponentTorus
  W π (start + j) (Data.b3 d) (Data.b4 d) (Data.b6 d) S r hs hp h3 h4 hr hc a ha
local notation "p" => WeierstrassSuccessiveShearTerminal.laurentConicComponentStructure
  W π (start + j) (Data.b3 d) (Data.b4 d) (Data.b6 d) S r hs hp h3 h4 hr hc a ha
local notation "J" => WeierstrassSuccessiveShearTerminal.laurentConicComponentProjectiveIso
  W π (start + j) (Data.b3 d) (Data.b4 d) (Data.b6 d) S r hs hp h3 h4 hr hc a ha
local notation "q" => coefficientShearEqualityConicParameter
  data S r j hj hs hp h3 h4 hc hr a ha

/-- The whole conic parameter preserves the original coefficient field. -/
@[reassoc] theorem coefficientShearEqualityConicParameter_structure :
    q ≫ ProjectiveLine.toBase S = conicStructure (U).a₁ c := by
  rw [coefficientShearEqualityConicParameter, Category.assoc,
    WeierstrassSuccessiveShearTerminal.laurentConicComponentProjectiveIso_inv_structure,
    WeierstrassSuccessiveShearTerminal.laurentConicComponentConic_structure]

local notation "e" => coefficientShearLaurentEquiv W (π ^ (start + (j + 1)))
  (Data.b3 d) (Data.b4 d) (Data.b6 d) S r hsNext h3 h4 hr a ha hc
local notation "E" => Scheme.Spec.mapIso (e).toRingEquiv.toCommRingCatIso.op
local notation "v" => coefficientShearEqualityDividedParameter
  data S r j hj hp h3 h4 hc hr a ha

/-- The full original divided equation parameter preserves coefficients. -/
@[reassoc] theorem coefficientShearEqualityDividedParameter_structure :
    v ≫ ProjectiveLine.toBase S =
      coefficientShearAtlasStructure data S r (j + 1) hj (.inl 1) := by
  apply (cancel_epi (E).hom).mp
  rw [coefficientShearEqualityDividedParameter_laurent_assoc, ProjectiveLine.left_toBase]
  have hbase : (E).hom ≫ coefficientShearAtlasStructure data S r (j + 1) hj (.inl 1) =
      Spec.map (CommRingCat.ofHom (algebraMap S (LaurentPolynomial S))) :=
    terminalComponent_algebra_structure (e).toAlgHom
  rw [hbase]
  exact terminalComponent_algebra_structure (Polynomial.toLaurentAlg : S[X] →ₐ[S] _)

end FLT.Mazur.WeierstrassDividedDepth
