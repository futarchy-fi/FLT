/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassModificationXStandardLaurentInverse
public import FLT.Mazur.WeierstrassModificationXSmallIncidenceUniqueness

/-!
# The complete original initial Laurent boundary is the full standard puncture

Both inverse laws retain the original small branch and the corrected incidence.
The standard puncture isomorphism therefore preserves every original node function.
-/

@[expose] public noncomputable section
open Polynomial AlgebraicGeometry CategoryTheory
open scoped LaurentPolynomial
namespace FLT.Mazur.WeierstrassModificationX
variable {R : Type*} [CommRing R] (W : WeierstrassCurve R) (s b3 b4 b6 : R)
  (I : Ideal R) (hI : IsNilpotent I) (ha : IsUnit W.a₁) (hs : s ∈ I)
  (h2 : W.a₂ ∈ I) (h3 : b3 ∈ I) (h4 : b4 ∈ I) (h6 : b6 ∈ I)
local notation "N" => NodalFiber.Coordinate s
local notation "D" => Localization.Away (NodalFiber.p s)
local notation "L" => PolynomialNodeOpen W s
local notation "r₀" => polynomialSlopeRoot W b3 b4 b6 I hI ha h2 h3 h4 h6
local notation "hr₀" => polynomialSlopeRoot_equation W b3 b4 b6 I hI ha h2 h3 h4 h6
local notation "hm₀" => polynomialSlopeRoot_mem W b3 b4 b6 I hI ha h2 h3 h4 h6
local notation "P" => algebraMap N D (NodalFiber.p s)
local notation "Q" => algebraMap N D (NodalFiber.q s)
local notation "hu" => standardInitialPuncture_denominator_unit W s I hI ha hs
local notation "T" => polynomialNodeInverseT b3 r₀ I hI hm₀ h3 W P Q hu

local notation "F" => standardInitialEvaluation W s b3 b4 b6 I hI ha hs h2 h3 h4 h6
local notation "A" => initialNodeStandardPuncture W s I hI ha hs
local notation "F₀" => polynomialNodeForwardBase W s b3 b4 b6 r₀ hr₀ I hI hm₀ h3
local notation "P₀" => algebraMap N L (NodalFiber.p s)
local notation "Q₀" => algebraMap N L (NodalFiber.q s)
local notation "H" => laurentStandardPunctureEvaluation W s b3 b4 b6 I hI ha hs h2 h3 h4 h6

local notation "ht" => standardInitialEvaluation_t_unit W s b3 b4 b6 I hI ha hs h2 h3 h4 h6

local notation "K" => standardInitialLaurentInverse W s b3 b4 b6 I hI ha hs h2 h3 h4 h6
local notation "E" => laurentBranchEvaluation W s b3 b4 b6 I hI ha hs h2 h3 h4 h6 false

/-- The inverse Laurent evaluation reconstructs the entire original small initial branch. -/
theorem standardInitialLaurentInverse_initial : (K).comp E = F := by
  apply smallIncidence_hom_ext W s b3 b4 b6 I hI ha h3
  · change K (E (t W s b3 b4 b6)) = F (t W s b3 b4 b6)
    rw [show E (t W s b3 b4 b6) = LaurentPolynomial.T (-1) from
      laurentSlopeEvaluation_t ..]
    exact standardInitialLaurentInverse_reciprocal W s b3 b4 b6 I hI ha hs h2 h3 h4 h6
  · change IsUnit (K (E (t W s b3 b4 b6)))
    rw [show E (t W s b3 b4 b6) = LaurentPolynomial.T (-1) from
      laurentSlopeEvaluation_t ..]
    exact (LaurentPolynomial.isUnit_T (-1)).map (K).toRingHom
  · have hm : laurentArithmeticIdeal I ≤
        (I.map (algebraMap R D)).comap (K).toRingHom := by
      rw [laurentArithmeticIdeal, Ideal.map_le_iff_le_comap]
      intro a ha'
      change K (algebraMap R R[T;T⁻¹] a) ∈ I.map (algebraMap R D)
      rw [AlgHom.commutes]
      exact Ideal.mem_map_of_mem _ ha'
    change K (E (v W s b3 b4 b6)) ∈ I.map (algebraMap R D)
    rw [show E (v W s b3 b4 b6) =
      nilpotentLaurentSlope W s b3 b4 b6 I hI ha hs h2 h3 h4 h6 from
        laurentSlopeEvaluation_v ..]
    exact hm (nilpotentLaurentSlope_mem W s b3 b4 b6 I hI ha hs h2 h3 h4 h6)
  · exact standardInitialEvaluation_v_mem W s b3 b4 b6 I hI ha hs h2 h3 h4 h6

/-- The inverse also fixes every complete standard puncture function. -/
theorem standardInitialLaurentInverse_evaluation : (K).comp H = AlgHom.id R D := by
  apply IsLocalization.algHom_ext (Submonoid.powers (NodalFiber.p s))
  apply NodalFiber.hom_ext
  · change K (H (algebraMap N D (NodalFiber.p s))) = P
    rw [laurentStandardPunctureEvaluation_p, map_mul,
      standardInitialLaurentInverse_reciprocal]
    have h := DFunLike.congr_fun
      (standardInitialLaurentInverse_initial W s b3 b4 b6 I hI ha hs h2 h3 h4 h6)
      (polynomialOppositeFactor W s b3 b4 b6 r₀)
    change K (E (polynomialOppositeFactor W s b3 b4 b6 r₀)) =
      F (polynomialOppositeFactor W s b3 b4 b6 r₀) at h
    rw [h, ← map_mul, standardInitialEvaluation_first]
  · change K (H (algebraMap N D (NodalFiber.q s))) = Q
    rw [laurentStandardPunctureEvaluation_q]
    have h := DFunLike.congr_fun
      (standardInitialLaurentInverse_initial W s b3 b4 b6 I hI ha hs h2 h3 h4 h6)
      (polynomialSmallFactor W s b3 b4 b6 r₀)
    exact h.trans (standardInitialEvaluation_small W s b3 b4 b6 I hI ha hs h2 h3 h4 h6)

/-- The full standard initial puncture is the original Laurent torus, with all corrections. -/
def initialStandardPunctureEquiv : D ≃ₐ[R] R[T;T⁻¹] :=
  AlgEquiv.ofAlgHom H K
    (laurentStandardPunctureEvaluation_inverse W s b3 b4 b6 I hI ha hs h2 h3 h4 h6)
    (standardInitialLaurentInverse_evaluation W s b3 b4 b6 I hI ha hs h2 h3 h4 h6)

/-- The original initial Laurent torus is isomorphic to the entire standard puncture D(p). -/
def initialStandardPunctureIso : Spec (.of R[T;T⁻¹]) ≅ Spec (.of D) := by
  let e := initialStandardPunctureEquiv W s b3 b4 b6 I hI ha hs h2 h3 h4 h6
  exact Scheme.Spec.mapIso e.toRingEquiv.toCommRingCatIso.op

attribute [local irreducible] laurentStandardPunctureEvaluation
  initialNodeStandardPuncture laurentNodeRestriction

/-- The isomorphism retains the original full map to the initial node neighborhood. -/
@[reassoc] theorem initialStandardPunctureIso_boundary :
    (initialStandardPunctureIso W s b3 b4 b6 I hI ha hs h2 h3 h4 h6).hom ≫
      Spec.map (CommRingCat.ofHom (A).toRingHom) =
    Spec.map (CommRingCat.ofHom
      (laurentNodeRestriction W s b3 b4 b6 I hI ha hs h2 h3 h4 h6).toRingHom) := by
  change Spec.map (CommRingCat.ofHom (H).toRingHom) ≫ Spec.map _ = _
  rw [← Spec.map_comp]
  apply congrArg Spec.map
  apply CommRingCat.hom_ext
  exact congrArg AlgHom.toRingHom
    (laurentStandardPunctureEvaluation_restriction W s b3 b4 b6 I hI ha hs h2 h3 h4 h6)

/-- Its full node inclusion retains every corrected parameter of the original Laurent map. -/
@[reassoc] theorem initialStandardPunctureIso_node :
    (initialStandardPunctureIso W s b3 b4 b6 I hI ha hs h2 h3 h4 h6).hom ≫
      Spec.map (CommRingCat.ofHom (algebraMap N D)) =
    Spec.map (CommRingCat.ofHom
      ((laurentNodeRestriction W s b3 b4 b6 I hI ha hs h2 h3 h4 h6).comp
        (Algebra.algHom R N L)).toRingHom) := by
  change Spec.map (CommRingCat.ofHom (H).toRingHom) ≫ Spec.map _ = _
  rw [← Spec.map_comp]
  apply congrArg Spec.map
  apply CommRingCat.hom_ext
  exact RingHom.ext
    (laurentStandardPunctureEvaluation_base W s b3 b4 b6 I hI ha hs h2 h3 h4 h6)

end FLT.Mazur.WeierstrassModificationX
