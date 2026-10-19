/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedOneInfinityNormalizedRetainedSide

/-!
# Original coefficient base of the full retained Laurent correction

All accumulated substitutions are algebra equivalences over the unreduced
quotient ring. Their full composite and its inverse preserve that base.
-/

@[expose] public noncomputable section
open scoped LaurentPolynomial
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages PolygonSmoothing WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] finiteGlobalModel finiteGlobalContraction
  arithmeticOneFiniteInitialIso arithmeticInitialFactorRatioChart arithmeticOneFiniteAtlasIso
/-- A full Laurent algebra equivalence preserves the entire coefficient projection. -/
@[reassoc] theorem fullLaurentIso_structure {K : Type} [CommRing K]
    (e : K[T;T⁻¹] ≃ₐ[K] K[T;T⁻¹]) :
    (Scheme.Spec.mapIso e.toRingEquiv.toCommRingCatIso.op).hom ≫
      Spec.map (CommRingCat.ofHom (algebraMap K K[T;T⁻¹])) =
        Spec.map (CommRingCat.ofHom (algebraMap K K[T;T⁻¹])) := by
  change Spec.map _ ≫ Spec.map _ = Spec.map _
  rw [← Spec.map_comp]
  congr 1
  exact CommRingCat.hom_ext (RingHom.ext e.commutes)

/-- The inverse full Laurent algebra equivalence preserves the same coefficient projection. -/
@[reassoc] theorem fullLaurentIso_inv_structure {K : Type} [CommRing K]
    (e : K[T;T⁻¹] ≃ₐ[K] K[T;T⁻¹]) :
    (Scheme.Spec.mapIso e.toRingEquiv.toCommRingCatIso.op).inv ≫
      Spec.map (CommRingCat.ofHom (algebraMap K K[T;T⁻¹])) =
        Spec.map (CommRingCat.ofHom (algebraMap K K[T;T⁻¹])) := by
  apply (cancel_epi (Scheme.Spec.mapIso e.toRingEquiv.toCommRingCatIso.op).hom).mp
  rw [Iso.hom_inv_id_assoc, fullLaurentIso_structure]

variable {R : Type} [CommRing R] [IsDomain R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (1 + i.val))
  (H : ArithmeticAtlasCoefficients data) (m : ℕ) (hj : 2 ≤ n)
  (u : Rˣ) (hu : (data ⟨2, Nat.lt_succ_of_le hj⟩).b6 = π * ↑u)
local notation "Q" => Quotient R π m
local notation "τ" => arithmeticInitialMobiusSmoothing W H.a1_unit (π ^ 1) π m
local notation "d" => data (Fin.mk 0 (Nat.zero_lt_succ n))
local notation "N" => arithmeticInitialFactorRatioChart π m W (π ^ 1)
  (Data.b3 d) (Data.b4 d) (Data.b6 d) H.a1_unit H.a2_div
    (H.b3_div _) (H.b4_div _) (H.b6_div _)
local notation "P" => arithmeticFactorRatioOverlapParameter π m W (π ^ 1)
  (Data.b3 d) (Data.b4 d) (Data.b6 d) H.a1_unit H.a2_div
    (H.b3_div _) (H.b4_div _) (H.b6_div _)
local notation "E" => arithmeticOneDiagonalInitialTotalOpenIso hπ data H m hj u hu
local notation "T" => arithmeticOneDiagonalInitialTotalNodeIso hπ data H m hj u hu
local notation "F" => arithmeticOneDiagonalInitialFactorRatio hπ data H m hj u hu
local notation "l" => arithmeticOneDiagonalInitialOverlap hπ data H m hj u hu
local notation "i" => arithmeticOneDiagonalOverlapToInfinity hπ data H m hj u hu
local notation "V" => arithmeticOneDiagonalInfinityParameterIso hπ data H m hj u hu
local notation "A" => arithmeticOneFiniteAtlasObject hπ data H m m hj u hu

local notation "f" => arithmeticOneInfinityNormalizedInitial hπ data H m hj u hu
local notation "A₀" => arithmeticOneFiniteInitialTotalPunctureIso hπ data H m hj u hu m
local notation "P₀" => arithmeticOneFiniteInitialPuncture hπ data H m m hj u hu
local notation "M" => arithmeticInitialMobiusParameter π m W (π ^ 1)
  (Data.b3 d) (Data.b4 d) (Data.b6 d) H.a1_unit H.scale_div H.a2_div
    (H.b3_div _) (H.b4_div _) (H.b6_div _)
local notation "L" => arithmeticFactorRatioLaurentIso π m W (π ^ 1)
  (Data.b3 d) (Data.b4 d) (Data.b6 d) H.a1_unit H.scale_div H.a2_div
    (H.b3_div _) (H.b4_div _) (H.b6_div _)
local notation "D" => arithmeticOneDiagonalState hπ data H hj u hu
local notation "s" => PolygonArithmeticRetainedChain.State.initial D m

local notation "K" => arithmeticOneInfinityNormalizedRetainedParameter hπ data H m hj u hu
local notation "p" => Spec.map (CommRingCat.ofHom (algebraMap Q Q[T;T⁻¹]))

/-- Every accumulated initial boundary factor preserves all original quotient coefficients. -/
@[reassoc] theorem arithmeticOneInitialTotalPunctureIso_base (b a : Bool) :
    (A₀ b a).hom ≫ p = p := by
  simp only [arithmeticOneFiniteInitialTotalPunctureIso, Iso.trans_hom, Category.assoc,
    punctureSpecIso, fullLaurentIso_structure]

/-- The whole inverse initial boundary correction also preserves the original base. -/
@[reassoc] theorem arithmeticOneInitialTotalPunctureIso_inv_base (b a : Bool) :
    (A₀ b a).inv ≫ p = p := by
  apply (cancel_epi (A₀ b a).hom).mp
  rw [Iso.hom_inv_id_assoc, arithmeticOneInitialTotalPunctureIso_base]

/-- The true unreduced retained parameter is over the original quotient coefficient scheme. -/
@[reassoc] theorem arithmeticOneInfinityNormalizedRetainedParameter_base (b : Bool) :
    (K b).hom ≫ p = p := by
  have hM : (M).inv ≫ p = p := fullLaurentIso_inv_structure _
  have hL : (L).hom ≫ p = p := fullLaurentIso_structure _
  simp only [arithmeticOneInfinityNormalizedRetainedParameter, Iso.trans_hom, Iso.symm_hom,
    Category.assoc, hL, hM, arithmeticOneInitialTotalPunctureIso_inv_base]

/-- The inverse true retained parameter keeps all quotient coefficients too. -/
@[reassoc] theorem arithmeticOneInfinityNormalizedRetainedParameter_inv_base (b : Bool) :
    (K b).inv ≫ p = p := by
  apply (cancel_epi (K b).hom).mp
  rw [Iso.hom_inv_id_assoc, arithmeticOneInfinityNormalizedRetainedParameter_base]

/-- The entire reparameterized retained-0 side lies over the unchanged coefficient base. -/
@[reassoc] theorem arithmeticOneInfinityNormalizedRetainedSide_base (b : Bool) :
    arithmeticOneInfinityNormalizedRetainedSide hπ data H m hj u hu b ≫
      chartStructure Q ((D).retained m 0 b) = p := by
  simp only [arithmeticOneInfinityNormalizedRetainedSide, Category.assoc,
    rightBranchOpen_base, punctureSpecIso, fullLaurentIso_structure,
    arithmeticOneInfinityNormalizedRetainedParameter_inv_base]

end FLT.Mazur.WeierstrassDividedDepth
