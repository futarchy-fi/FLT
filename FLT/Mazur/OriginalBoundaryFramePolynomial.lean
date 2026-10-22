/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OriginalBoundaryMixedCoefficientEquations
public import FLT.Mazur.FiniteDifferenceProductPolynomial

/-!
# One finite polynomial for the full original boundary comparison

The original rank and equivalence relation construct comaximal coordinate
ideals. On a Noetherian affine test, one original coefficient polynomial
therefore computes the exact comparison kernel and every correction test.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped BigOperators
namespace FLT.Mazur.EquivalenceRelationOrderedFrames
open RelativeOrderedTuples RingPairInvariantFlatScalars SchemeScalarPrincipalNeighborhood
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {D A B : Scheme.{0}} {p q : D ⟶ A} [IsSeparated p] [Etale p]
  [QuasiCompact p] (J : A.IdealSheafData) (hJ : J.comap p = J.comap q)
attribute [local instance] sourceAlgebra targetAlgebra originalBoundaryAlgebra
set_option quotPrecheck false
local notation "R" => invariants p.appTop.hom q.appTop.hom
local notation "f" => scalarMorphism (algebraMap R Γ(J.subscheme, ⊤))
local notation "P" => pullback.snd p J.subschemeι
local notation "Q" => InvariantIdealRelation.snd J p q hJ
local notation "E" => Over.mk P
local notation "c" => originalBoundaryComparison p q J hJ
local instance polynomialEquationBoundaryOver_separated : IsSeparated (E).hom :=
  inferInstanceAs (IsSeparated P)
local instance polynomialEquationBoundaryOver_etale : Etale (E).hom := inferInstanceAs (Etale P)
local instance polynomialEquationBoundaryOver_compact : QuasiCompact (E).hom :=
  inferInstanceAs (QuasiCompact P)
local instance polynomialEquationOriginalOver_separated : IsSeparated (Over.mk p).hom :=
  ‹IsSeparated p›
local instance polynomialEquationOriginalOver_etale : Etale (Over.mk p).hom := ‹Etale p›
local instance polynomialEquationOriginalOver_compact : QuasiCompact (Over.mk p).hom :=
  ‹QuasiCompact p›
variable (t : B ⟶ pullback
    (scalarMorphism (algebraMap (invariants p.appTop.hom q.appTop.hom) Γ(J.subscheme, ⊤)))
    (scalarMorphism (algebraMap (invariants p.appTop.hom q.appTop.hom) Γ(J.subscheme, ⊤))))
  (n : ℕ)
local notation "x" => t ≫ pullback.fst f f
local notation "y" => t ≫ pullback.snd f f
variable (a : Over.mk (t ≫ pullback.fst _ _) ⟶
    distinctScheme (Over.mk (pullback.snd p J.subschemeι)) (Fin n))
  (ht : Set.range (t ≫ pullback.fst _ _ ≫ J.subschemeι) ⊆ exactRank (Over.mk p) n)

variable [IsAffine A] [IsAffine B] [LocallyQuasiFinite p]
  (e : CategoryTheory.EquivalenceRelation p q)
local instance polynomialEquationBoundary_affine : IsAffine J.subscheme :=
  isAffine_of_isAffineHom J.subschemeι
local instance polynomialEquationOriginal_quasiFinite : LocallyQuasiFinite (Over.mk p).hom :=
  ‹LocallyQuasiFinite p›
attribute [local irreducible] scalarMorphism
local notation "s" k:max => testSection E (Fin n) a k

local notation "l" k:max => (s k ≫ pullback.fst P x ≫ Q).appTop.hom
local notation "r" => (y).appTop.hom

omit [Etale p] [QuasiCompact p] [IsAffine A] [IsAffine B] [LocallyQuasiFinite p] in
/-- The frame ideal uses the unchanged second endpoint on every coordinate. -/
theorem originalBoundaryFrameScalarIdeal_difference (k : Fin n) :
    originalBoundaryFrameScalarIdeal J hJ t n a k =
      FiniteCoefficientDifference.differenceIdeal (l k) r := by
  change FiniteCoefficientDifference.differenceIdeal _
    (s k ≫ pullback.snd P x ≫ y).appTop.hom = _
  have hs : s k ≫ pullback.snd P x ≫ y = y := by
    simpa only [Over.mk_hom, Category.id_comp] using! testSection_snd_assoc E (Fin n) a k y
  rw [hs]
  rfl

include ht e in
/-- Original rank finiteness and monicity make the full difference ideals pairwise comaximal. -/
theorem originalBoundary_frame_difference_coprime :
    Pairwise fun i j : Fin n ↦ IsCoprime
      (FiniteCoefficientDifference.differenceIdeal (l i) r)
      (FiniteCoefficientDifference.differenceIdeal (l j) r) := by
  intro i j hij
  let _ := originalBoundary_frameEquation_closedImmersion J hJ t n ht e
  rw [← originalBoundaryFrameScalarIdeal_difference J hJ t n a i,
    ← originalBoundaryFrameScalarIdeal_difference J hJ t n a j]
  have hv : Function.Injective
      (equalizer.ι (pullback.fst P x ≫ Q) (pullback.snd P x ≫ y) ≫ pullback.snd P x) :=
    (IsClosedImmersion.isClosedEmbedding _).injective
  exact frameEquationScalarIdeal_coprime E (Fin n) a Q y
    (by simpa only [Over.mk_hom] using hv) i j hij

variable [IsNoetherianRing Γ(B, ⊤)]

/-- One chosen polynomial in original boundary coefficients encodes every coordinate ideal. -/
def originalBoundaryFramePolynomial : Polynomial Γ(J.subscheme, ⊤) :=
  FiniteCoefficientDifference.commonDifferencePolynomial (fun k ↦ l k) (fun _ ↦ r)

/-- The product polynomial is formed on the entire affine coefficient test. -/
def originalBoundaryFrameProductPolynomial : Polynomial Γ(B, ⊤) :=
  FiniteCoefficientDifference.differenceProductPolynomial (fun k ↦ l k) (fun _ ↦ r)
    (originalBoundaryFramePolynomial J hJ t n a)

include ht e

/-- Finitely many polynomial coefficients generate the exact original comparison kernel. -/
theorem originalBoundary_frame_scalar_kernel_content :
    RingHom.ker (pullback.snd c t).appTop.hom =
      (originalBoundaryFrameProductPolynomial J hJ t n a).contentIdeal := by
  rw [originalBoundary_frame_scalar_kernel_product J hJ t n a ht e]
  change _ = (FiniteCoefficientDifference.differenceProductPolynomial _ _
    (FiniteCoefficientDifference.commonDifferencePolynomial _ _)).contentIdeal
  rw [FiniteCoefficientDifference.common_differenceProduct_content _ _
    (originalBoundary_frame_difference_coprime J hJ t n a ht e)]
  congr 1
  funext k
  exact originalBoundaryFrameScalarIdeal_difference J hJ t n a k

/-- One polynomial equation modulo any correction ideal controls the full comparison ideal. -/
theorem originalBoundary_frame_kernel_le_iff_polynomial (K : Ideal Γ(B, ⊤)) :
    RingHom.ker (pullback.snd c t).appTop.hom ≤ K ↔
      (originalBoundaryFrameProductPolynomial J hJ t n a).map (Ideal.Quotient.mk K) = 0 := by
  rw [originalBoundary_frame_scalar_kernel_content J hJ t n a ht e,
    ← Polynomial.contentIdeal_eq_bot_iff, Polynomial.contentIdeal_map_eq_map_contentIdeal,
    Ideal.map_eq_bot_iff_le_ker, Ideal.mk_ker]

/-- Vanishing of one finite polynomial constructs a unique full original boundary arrow. -/
theorem originalBoundary_frame_lift_iff_polynomial :
    (∃! d : B ⟶ pullback p J.subschemeι, d ≫ c = t) ↔
      originalBoundaryFrameProductPolynomial J hJ t n a = 0 := by
  let _ := originalBoundaryComparison_mono e J hJ
  let _ : IsFinite (pullback.snd p (t ≫ pullback.fst f f ≫ J.subschemeι)) :=
    finite_pullback_of_exactRank (Over.mk p) n _ ht
  let _ := originalBoundary_comparison_test_closedImmersion J hJ t e
  rw [SchemeClosedScalarKernelLift.existsUnique_lift_iff,
    originalBoundary_frame_scalar_kernel_content J hJ t n a ht e,
    Polynomial.contentIdeal_eq_bot_iff]

end FLT.Mazur.EquivalenceRelationOrderedFrames
