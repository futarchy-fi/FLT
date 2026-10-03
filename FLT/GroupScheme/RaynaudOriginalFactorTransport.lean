/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.FiniteFlatPrescribedClosure
public import FLT.GroupScheme.RaynaudDescentFraction
public import FLT.GroupScheme.RaynaudOriginalTowerAction

/-!
# Transport of the actual descended factor to the original tower

The finite descent embedding is constructed inside the original union.
Base change and closure transport retain the same original inertia action.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace RaynaudParameters
open NumberField GaloisModule

variable {K X W F : Type} [Field K] [NumberField K]
  (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) [AddCommGroup X]
  [DistribMulAction (AlgebraicClosure (v.adicCompletion K) ≃ₐ[v.adicCompletion K]
    AlgebraicClosure (v.adicCompletion K)) X]
  [Finite X] [ContinuousSMulDiscrete (AlgebraicClosure (v.adicCompletion K) ≃ₐ[v.adicCompletion K]
    AlgebraicClosure (v.adicCompletion K)) X]
local notation "Kv" => v.adicCompletion K
local notation "O" => v.adicCompletionIntegers K
local notation "Ωv" => AlgebraicClosure Kv
local notation "I" => localInertiaGroup v
local notation "L₀" => InertiaDescent.field (X := X) I
local notation "S₀" => IntegralClosure O L₀
variable {π : v.adicCompletionIntegers K} (hπ : Irreducible π)
local notation "Rsh" => unramifiedUnion (Ω := Ωv) π
local notation "Lsh" => FractionRing Rsh

/-- Retain the canonical fraction-ring base algebra in the completion-field tower. -/
local instance descentTowerBaseAlgebra : Algebra O Lsh := inferInstance

variable [Algebra (v.adicCompletion K) (FractionRing
    (unramifiedUnion (Ω := AlgebraicClosure (v.adicCompletion K)) π))]
  [IsScalarTower (v.adicCompletionIntegers K) (v.adicCompletion K) (FractionRing
    (unramifiedUnion (Ω := AlgebraicClosure (v.adicCompletion K)) π))]
  [Field F] [AddCommGroup W] [Module F W] [DistribMulAction (localInertiaGroup v) W]
  [DistribMulAction (AlgebraicClosure (v.adicCompletion K) ≃ₐ[InertiaDescent.field
      (X := X) (localInertiaGroup v)] AlgebraicClosure (v.adicCompletion K)) W]
  [SMulCommClass F (AlgebraicClosure (v.adicCompletion K) ≃ₐ[InertiaDescent.field
      (X := X) (localInertiaGroup v)] AlgebraicClosure (v.adicCompletion K)) W]

-- The two fraction-field towers have large dependent algebra instances.
set_option synthInstance.maxHeartbeats 100000 in
-- Checking their compatibility requires more than the default elaboration budget.
set_option maxHeartbeats 800000 in
include hπ in
/-- Actual finite descent followed by tower base change preserves each original inertia element. -/
theorem exists_original_factor_tower_action
    (hW : IsFiniteFlat S₀ L₀ Ωv W)
    (hmatch : ∀ (σ : Ωv ≃ₐ[L₀] Ωv) (t : I),
      (∀ x : X, σ.restrictScalars Kv • x = t.1 • x) → ∀ w : W, σ • w = t • w)
    (e : Lsh →ₐ[Kv] Ωv) (he : ∀ a : Rsh, e (algebraMap Rsh Lsh a) = (a : Ωv)) :
    ∃ d : DistribMulAction (AlgebraicClosure Lsh ≃ₐ[Lsh] AlgebraicClosure Lsh) W,
      letI := d
      IsFiniteFlat Rsh Lsh (AlgebraicClosure Lsh) W ∧
      SMulCommClass F (AlgebraicClosure Lsh ≃ₐ[Lsh] AlgebraicClosure Lsh) W ∧
      ∀ (σ : I) (w : W), originalTowerInertia v π e he σ • w = σ • w := by
  let : Algebra Rsh Lsh := inferInstance
  let f := inertiaDescentIntegersToUnion (X := X) v hπ
  let g := inertiaDescentFieldToTower (X := X) v hπ
  let : Algebra S₀ Rsh := f.toRingHom.toAlgebra
  let : Algebra L₀ Lsh := g.toRingHom.toAlgebra
  let : Algebra S₀ Lsh := ((algebraMap Rsh Lsh).comp f.toRingHom).toAlgebra
  let : SMul Rsh Lsh := (inferInstance : Algebra Rsh Lsh).toSMul
  let : SMul S₀ Lsh := (inferInstance : Algebra S₀ Lsh).toSMul
  let : SMul L₀ Lsh := (inferInstance : Algebra L₀ Lsh).toSMul
  let : IsScalarTower S₀ Rsh Lsh := .of_algebraMap_eq fun _ ↦ rfl
  let : IsScalarTower S₀ L₀ Lsh := .of_algebraMap_eq fun x ↦
    (inertiaDescentFieldToTower_algebraMap (X := X) v hπ x).symm
  let : Algebra Lsh Ωv := e.toRingHom.toAlgebra
  let : IsScalarTower L₀ Lsh Ωv := .of_algebraMap_eq fun x ↦
    (AlgHom.congr_fun (inertiaDescentFieldToTower_comp (X := X) v hπ
      (e.restrictScalars O) he) x).symm
  let c : AlgebraicClosure Lsh ≃ₐ[Lsh] Ωv :=
    { towerClosureEquiv e with commutes' := towerClosureEquiv_algebraMap e }
  let d : DistribMulAction (AlgebraicClosure Lsh ≃ₐ[Lsh] AlgebraicClosure Lsh) W :=
    inferInstanceAs (DistribMulAction _
      (ClosureChangedPoints c.symm (RestrictedPoints L₀ Lsh Ωv W)))
  refine ⟨d, hW.baseChange_prescribedClosure (S := Rsh) c, ?_, ?_⟩
  · exact inferInstanceAs
      (SMulCommClass F _ (ClosureChangedPoints c.symm (RestrictedPoints L₀ Lsh Ωv W)))
  · intro σ w
    let τ := (AlgEquiv.autCongr c (originalTowerInertia v π e he σ)).restrictScalars L₀
    have hτ : τ.restrictScalars Kv = σ.1 := by
      ext x
      change towerClosureEquiv e
        (towerAutomorphism e σ.1
          (inertia_fixes_fractionField v (e.restrictScalars O) he σ)
          ((towerClosureEquiv e).symm x)) = σ.1 x
      rw [towerAutomorphism_apply, RingEquiv.apply_symm_apply]
    exact hmatch τ σ (fun x ↦ by rw [hτ]) w

end RaynaudParameters
