/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassSmoothHorizontalTensorAction
public import FLT.Mazur.TensorOpenChart

/-!
# The original conic inputs inside the horizontal tensor chart

The two tensor inputs use the independently retained conic punctures.
Their integral projections agree on every equation function with the
original horizontal residue inputs.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory IsLocalRing
open scoped TensorProduct LaurentPolynomial
namespace FLT.Mazur.WeierstrassIntegralChart
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] [IsDomain R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} {depth k : ℕ} (D : SplitNodeDepth W π depth)
  (d : WeierstrassDividedDepth.Data W π k) (hk0 : 0 < k) (hk : 2 * k < depth) (hπ : π ≠ 0)
open WeierstrassModificationX WeierstrassSuccessiveX
local notation "K" => ResidueField R
local notation "C" => SmoothHorizontalResidueRing D
local notation "A" => WeierstrassModificationX.Coordinate W (π ^ k) d.b3 d.b4 d.b6
local notation "E" => horizontalReesChartEquiv W (π ^ k) d.b3 d.b4 d.b6
  d.factor3 d.factor4 d.factor6 (pow_ne_zero k hπ)
local notation "F" => residueFiberEquiv D k hk0 (Nat.le_of_lt hk)
  d.b3 d.b4 d.b6 d.factor3 d.factor4
local notation "N" => residueNormalMap D k hk0 (Nat.le_of_lt hk)
  d.b3 d.b4 d.b6 d.factor3 d.factor4
local notation "a" => residue R W.a₁
local notation "c" => residue R d.b6
local notation "hc" => Iff.mpr (residue_eq_zero_iff _)
  (WeierstrassDilatation.divided_constant_mem D k hk d.b6 d.factor6)
local notation "P₁" => conicPuncturedFirst (W.map (residue R)) c hc
local notation "P₂" => conicPuncturedSecond (W.map (residue R)) c hc
local notation "τ" => smoothHorizontalTangentUnit D
local notation "z" => smoothHorizontalConicUnit D

local notation "ψ" => smoothHorizontalInput W (π ^ k)
local notation "e₁" => smoothHorizontalFirstResidue D k hk0 hk hπ
  d.b3 d.b4 d.b6 d.factor3 d.factor4 d.factor6
local notation "e₂" => smoothHorizontalSecondResidue D k hk0 hk hπ
  d.b3 d.b4 d.b6 d.factor3 d.factor4 d.factor6

omit hπ in
/-- The original first conic puncture on the whole horizontal tensor equation algebra. -/
def smoothHorizontalFirstTensorInput : K ⊗[R] A →ₐ[K] C :=
  (smoothHorizontalResidueConic D).comp
    ((P₁).comp ((fiberConicMap a c).comp (F).toAlgHom))

/-- The first tensor input retains every original horizontal equation function. -/
theorem smoothHorizontalFirstTensorInput_tmul (t : A) :
    smoothHorizontalFirstTensorInput D d hk0 hk ((1 : K) ⊗ₜ[R] t) =
      e₁ (ψ (E t)) := by
  rw [smoothHorizontalFirstResidue_input]
  change smoothHorizontalResidueConic D (P₁ (fiberConicMap a c
    (F ((1 : K) ⊗ₜ[R] t)))) =
      smoothHorizontalResidueConic D (P₁ (fiberConicMap a c (N ((E).symm (E t)))))
  rw [AlgEquiv.symm_apply_apply, residueFiberEquiv_tmul, one_smul]

/-- The first tensor input projects to the actual original integral equation input. -/
theorem smoothHorizontalFirstTensorInput_projection :
    Spec.map (CommRingCat.ofHom
        (smoothHorizontalFirstTensorInput D d hk0 hk).toRingHom) ≫
      TensorOpenChart.projection =
        Spec.map (CommRingCat.ofHom
          ((e₁).toRingHom.comp ((ψ).comp (E).toAlgHom.toRingHom))) := by
  rw [TensorOpenChart.projection, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 2
  apply RingHom.ext
  intro t
  exact smoothHorizontalFirstTensorInput_tmul D d hk0 hk hπ t

omit hπ in
/-- The original second conic puncture on the whole horizontal tensor equation algebra. -/
def smoothHorizontalSecondTensorInput : K ⊗[R] A →ₐ[K] C :=
  (smoothHorizontalResidueConic D).comp
    ((P₂).comp ((fiberConicMap a c).comp (F).toAlgHom))

/-- The second tensor input retains every original horizontal equation function. -/
theorem smoothHorizontalSecondTensorInput_tmul (t : A) :
    smoothHorizontalSecondTensorInput D d hk0 hk ((1 : K) ⊗ₜ[R] t) =
      e₂ (ψ (E t)) := by
  rw [smoothHorizontalSecondResidue_input]
  change smoothHorizontalResidueConic D (P₂ (fiberConicMap a c
    (F ((1 : K) ⊗ₜ[R] t)))) =
      smoothHorizontalResidueConic D (P₂ (fiberConicMap a c (N ((E).symm (E t)))))
  rw [AlgEquiv.symm_apply_apply, residueFiberEquiv_tmul, one_smul]

/-- The second tensor input projects to the actual original integral equation input. -/
theorem smoothHorizontalSecondTensorInput_projection :
    Spec.map (CommRingCat.ofHom
        (smoothHorizontalSecondTensorInput D d hk0 hk).toRingHom) ≫
      TensorOpenChart.projection =
        Spec.map (CommRingCat.ofHom
          ((e₂).toRingHom.comp ((ψ).comp (E).toAlgHom.toRingHom))) := by
  rw [TensorOpenChart.projection, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 2
  apply RingHom.ext
  intro t
  exact smoothHorizontalSecondTensorInput_tmul D d hk0 hk hπ t

end FLT.Mazur.WeierstrassIntegralChart
