/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.RaynaudCharacterMonomials
public import FLT.GroupScheme.RaynaudMixedRankOneConvolution
public import FLT.GroupScheme.RaynaudRankOneProjector

/-!
# Universal products of actual mixed monomial coefficients

The normalized rank-one projectors and the scalar-addition law compute
the same mixed convolution product. Pairing the output generator identifies
the product of the two integral coefficients with the universal constant.
-/

@[expose] public noncomputable section
namespace ThreeAdicPlan
open IsLocalRing WithConv

variable {R K F : Type} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
  [HenselianLocalRing R] [IsSepClosed (ResidueField R)] [Field K] [Algebra R K]
  [CharZero K] [IsFractionRing R K] [Field F] [Finite F] [Fintype Fˣ]
  [Invertible (Fintype.card Fˣ : R)] (X : FF R K) [Module F X.Points]
  (lift : F → ModelHom X X) (h0 : lift 0 = ModelHom.zero X X)
  (h1 : lift 1 = BialgHom.id R X.CoordinateRing)
  (hmul : ∀ a b, lift (a * b) = (lift b).comp (lift a))
  (hadd : ∀ a b, lift (a + b) = (lift a).add (lift b))
  (p : ℕ) [CharP F p] [CharP (ResidueField R) p]
  (hdim : Module.finrank F X.Points = 1)
  (hlift : ∀ a x, genericHom (lift a) x = a • x)

include h0 hadd in
/-- The two actual monomial coefficients multiply to the mixed universal constant. -/
theorem FF.exists_mixed_character_parameter_product (cs : List (Fˣ →* Rˣ)) (hne : cs ≠ []) :
    ∃ a b : R,
      (cs.map (X.characterGenerator lift h1 hmul p hdim hlift)).prod =
        a • X.characterGenerator lift h1 hmul p hdim hlift cs.prod ∧
      (cs.map (X.dualCharacterGenerator lift h1 hmul p hdim hlift)).prod =
        b • X.dualCharacterGenerator lift h1 hmul p hdim hlift cs.prod ∧
      a * b = CharacterAverage.mixedConstant cs cs.prod := by
  obtain ⟨a, ha⟩ := X.character_monomial_relation lift h1 hmul p hdim hlift cs hne
  obtain ⟨b, hb⟩ := X.dual_character_monomial_relation lift h1 hmul p hdim hlift cs hne
  refine ⟨a, b, ha, hb, ?_⟩
  have he := X.characterProjector_convProd_eigen lift h0 h1 hmul hadd cs cs.prod
    (X.characterBasis lift h1 hmul p hdim hlift cs.prod ())
  simp_rw [X.coordinateCharacterProjector_rankOne lift h1 hmul p hdim hlift] at he
  erw [rankOne_convProd] at he
  change (show HopfAlgebra.CartierDual R X.CoordinateRing from
      (cs.map (X.dualCharacterGenerator lift h1 hmul p hdim hlift)).prod)
      (X.characterGenerator lift h1 hmul p hdim hlift cs.prod) •
      (cs.map (X.characterGenerator lift h1 hmul p hdim hlift)).prod =
    CharacterAverage.mixedConstant cs cs.prod •
      X.characterGenerator lift h1 hmul p hdim hlift cs.prod at he
  rw [ha, hb] at he
  let φ : HopfAlgebra.CartierDual R X.CoordinateRing :=
    X.dualCharacterGenerator lift h1 hmul p hdim hlift cs.prod
  have hp : φ.ofConv (X.characterGenerator lift h1 hmul p hdim hlift cs.prod) = 1 :=
    X.characterGenerator_pairing lift h1 hmul p hdim hlift cs.prod
  have h := congrArg φ.ofConv he
  change φ.ofConv ((b * φ.ofConv _) • (a • _)) = φ.ofConv (_ • _) at h
  rw [hp, mul_one, map_smul, map_smul, map_smul, hp] at h
  simpa only [smul_eq_mul, mul_one, mul_comm b a] using h

end ThreeAdicPlan
