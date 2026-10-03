/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.RaynaudRankOneConvolution
public import FLT.GroupScheme.RaynaudMixedCharacterAverage

/-!
# Mixed rank-one convolution and actual character projectors

Products of projectors have both a rank-one expansion and a universal
scalar expansion. These identities apply to the actual coordinate ring.
-/

@[expose] public noncomputable section
namespace ThreeAdicPlan
open WithConv

section RankOne

variable {R A C ι : Type*} [CommRing R] [Ring A] [Algebra R A]
  [AddCommGroup C] [Module R C] [Coalgebra R C]

/-- A list of rank-one convolution maps multiplies vectors and functionals separately. -/
theorem rankOne_convProd (l : List ι) (φ : ι → WithConv (C →ₗ[R] R)) (x : ι → A) :
    (l.map (fun i ↦ toConv ((φ i).ofConv.smulRight (x i)))).prod =
      toConv ((l.map φ).prod.ofConv.smulRight (l.map x).prod) := by
  induction l with
  | nil =>
    ext c
    simp [Algebra.algebraMap_eq_smul_one]
  | cons i l ih =>
    simp only [List.map_cons, List.prod_cons, ih, rankOne_convMul]

end RankOne

variable {R K F : Type} [CommRing R] [Field K] [Algebra R K]
  [PerfectField K] [IsFractionRing R K] [Field F] [Fintype Fˣ]
  [Invertible (Fintype.card Fˣ : R)] (X : FF R K)
  (lift : F → ModelHom X X) (h0 : lift 0 = ModelHom.zero X X)
  (h1 : lift 1 = BialgHom.id R X.CoordinateRing)
  (hmul : ∀ a b, lift (a * b) = (lift b).comp (lift a))
  (hadd : ∀ a b, lift (a + b) = (lift a).add (lift b))

include h0 hadd in
/-- Products of actual projectors expand as mixed scalar differences. -/
theorem FF.characterProjector_convProd (cs : List (Fˣ →* Rˣ)) :
    (cs.map (fun χ ↦ toConv (X.coordinateCharacterProjector lift h1 hmul χ))).prod =
      CharacterAverage.mixed cs (fun a ↦ toConv (lift a).toLinearMap) 0 := by
  rw [CharacterAverage.mixed_eq_prod_mul cs _ (X.scalar_add_conv lift hadd),
    X.scalar_zero_conv lift h0, one_mul]
  congr 1
  apply List.map_congr_left
  intro χ hχ
  exact X.coordinateCharacterProjector_conv_average lift h0 h1 hmul χ

include h0 hadd in
/-- On a character vector the mixed projector product is its universal constant. -/
theorem FF.characterProjector_convProd_eigen (cs : List (Fˣ →* Rˣ)) (ψ : Fˣ →* Rˣ)
    (v : X.integralCharacter lift h1 hmul ψ) :
    (cs.map (fun χ ↦ toConv (X.coordinateCharacterProjector lift h1 hmul χ))).prod
      (v.val : X.CoordinateRing) =
      CharacterAverage.mixedConstant cs ψ • (v.val : X.CoordinateRing) := by
  let ev : WithConv (X.CoordinateRing →ₗ[R] X.CoordinateRing) →ₗ[R] X.CoordinateRing :=
    { toFun := fun f ↦ f (v.val : X.CoordinateRing)
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun _ _ ↦ rfl }
  change ev _ = _
  rw [X.characterProjector_convProd lift h0 h1 hmul hadd, CharacterAverage.map_mixed]
  change CharacterAverage.mixed cs (fun a ↦ lift a (v.val : X.CoordinateRing)) 0 = _
  simp_rw [X.integralCharacter_scalar_value lift h0 h1 hmul ψ v]
  exact (CharacterAverage.map_mixed cs (CharacterAverage.value ψ)
    (LinearMap.toSpanSingleton R X.CoordinateRing (v.val : X.CoordinateRing)) 0).symm

end ThreeAdicPlan
