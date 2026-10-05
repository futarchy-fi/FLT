/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.RationalPlaceHodgeTateRealization
public import FLT.GroupScheme.RationalPlaceCoefficientGalois
public import FLT.GroupScheme.PDivisibleRationalTateAction

/-! # The original diagonal semilinear action on the C_p Tate realization -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open PadicHodgeTheory
open scoped TensorProduct
attribute [local instance 2000] IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField
  IsDedekindDomain.HeightOneSpectrum.instAlgebraAdicCompletion
attribute [local instance 2000] Algebra.toModule Algebra.toSMul
namespace ThreeAdicPlan
variable {p height : ℕ} [Fact p.Prime]
local notation "O" =>
  IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ (LocalCyclotomic.rationalPlace p)

/-- The actual completed Galois action is linear over the fixed Z_p scalars. -/
def rationalPlaceComplexGaloisPadicLinear (σ : PadicGalois p) : ℂ_[p] →ₗ[ℤ_[p]] ℂ_[p] where
  toFun := complexGalois p σ
  map_add' := map_add _
  map_smul' a c := by
    simp only [Algebra.smul_def, map_mul, RingHom.id_apply]
    congr 1
    exact complexGalois_algebraMap p σ (a : ℚ_[p])

variable (X : PDivisibleSystem ((LocalCyclotomic.rationalPlace p).adicCompletionIntegers ℚ)
  ((LocalCyclotomic.rationalPlace p).adicCompletion ℚ) p height)

/-- Act on both the actual coefficient and the original Tate vector. -/
def rationalPlaceTateRealizationGalois (σ : PadicGalois p) :
    RationalPlaceTateRealization X →ₗ[ℤ_[p]] RationalPlaceTateRealization X :=
  TensorProduct.map (rationalPlaceComplexGaloisPadicLinear σ)
    (X.rationalTateAction σ).toLinearMap

/-- The diagonal action retains the original two factors on pure tensors. -/
theorem rationalPlaceTateRealizationGalois_tmul (σ : PadicGalois p)
    (c : ℂ_[p]) (x : X.tateSequences) :
    rationalPlaceTateRealizationGalois X σ (c ⊗ₜ x) =
      complexGalois p σ c ⊗ₜ X.rationalTateAction σ x := rfl

/-- The identity automorphism acts identically on the entire realization. -/
theorem rationalPlaceTateRealizationGalois_one (v : RationalPlaceTateRealization X) :
    rationalPlaceTateRealizationGalois X 1 v = v := by
  induction v using TensorProduct.inductionOn with
  | tmul c x => simp [rationalPlaceTateRealizationGalois_tmul, complexGalois_one]
  | add v w hv hw => simp only [map_add, hv, hw]

/-- Composition is the original Galois group law on every C_p Tate vector. -/
theorem rationalPlaceTateRealizationGalois_mul (σ τ : PadicGalois p)
    (v : RationalPlaceTateRealization X) :
    rationalPlaceTateRealizationGalois X (σ * τ) v =
      rationalPlaceTateRealizationGalois X σ (rationalPlaceTateRealizationGalois X τ v) := by
  induction v using TensorProduct.inductionOn with
  | tmul c x =>
    simp only [rationalPlaceTateRealizationGalois_tmul, complexGalois_mul, map_mul,
      LinearEquiv.mul_apply, RingHom.comp_apply]
  | add v w hv hw => simp only [map_add, hv, hw]

/-- The action is semilinear for the actual automorphism of C_p. -/
theorem rationalPlaceTateRealizationGalois_smul (σ : PadicGalois p)
    (c : ℂ_[p]) (v : RationalPlaceTateRealization X) :
    rationalPlaceTateRealizationGalois X σ (c • v) =
      complexGalois p σ c • rationalPlaceTateRealizationGalois X σ v := by
  induction v using TensorProduct.inductionOn with
  | tmul d x => simp only [TensorProduct.smul_tmul', smul_eq_mul,
      rationalPlaceTateRealizationGalois_tmul, map_mul]
  | add v w hv hw => simp only [smul_add, map_add, hv, hw]

/-- On the Lie-dual target Galois acts only on the actual coefficient factor. -/
def rationalPlaceHodgeTateTargetGalois (σ : PadicGalois p) :
    RationalPlaceHodgeTateTarget X →ₗ[O] RationalPlaceHodgeTateTarget X :=
  (rationalPlaceComplexGalois σ).toLinearMap.rTensor _

/-- The target action is semilinear for the same automorphism of C_p. -/
theorem rationalPlaceHodgeTateTargetGalois_smul (σ : PadicGalois p)
    (c : ℂ_[p]) (v : RationalPlaceHodgeTateTarget X) :
    rationalPlaceHodgeTateTargetGalois X σ (c • v) =
      complexGalois p σ c • rationalPlaceHodgeTateTargetGalois X σ v := by
  induction v using TensorProduct.inductionOn with
  | tmul d x =>
    change _ = complexGalois p σ c • (complexGalois p σ d ⊗ₜ[O] x)
    simp only [TensorProduct.smul_tmul', smul_eq_mul, rationalPlaceHodgeTateTargetGalois,
      LinearMap.rTensor_tmul]
    change complexGalois p σ (c * d) ⊗ₜ[O] x = _
    rw [map_mul]
  | add v w hv hw => simp only [smul_add, map_add, hv, hw]
end ThreeAdicPlan
