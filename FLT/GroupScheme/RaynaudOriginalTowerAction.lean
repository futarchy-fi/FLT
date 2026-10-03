/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.RaynaudTowerEvaluation
public import FLT.GroupScheme.RaynaudTowerInertia

/-!
# Original inertia on the actual unramified tower closure

Fixedness is proved from the finite unramified stages. The original inertia
action and coordinate evaluation therefore use the same prescribed embedding.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
namespace RaynaudParameters
open NumberField

variable {K : Type} [Field K] [NumberField K]
  (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
local notation "Kv" => v.adicCompletion K
local notation "O" => v.adicCompletionIntegers K
local notation "Ωv" => AlgebraicClosure Kv

variable (π : v.adicCompletionIntegers K)
local notation "Rsh" => unramifiedUnion (Ω := Ωv) π
local notation "Lsh" => FractionRing Rsh

/-- Keep the canonical fraction-ring base algebra when adding the completion-field algebra. -/
local instance towerBaseAlgebra : Algebra O Lsh := inferInstance

variable [Algebra (v.adicCompletion K)
    (FractionRing (unramifiedUnion (Ω := AlgebraicClosure (v.adicCompletion K)) π))]
  [IsScalarTower (v.adicCompletionIntegers K) (v.adicCompletion K)
    (FractionRing (unramifiedUnion (Ω := AlgebraicClosure (v.adicCompletion K)) π))]

/-- Original inertia acts over the constructed tower field via its prescribed embedding. -/
def originalTowerInertia (e : Lsh →ₐ[Kv] Ωv)
    (he : ∀ a : Rsh, e (algebraMap Rsh Lsh a) = (a : Ωv)) :
    localInertiaGroup v →* (AlgebraicClosure Lsh ≃ₐ[Lsh] AlgebraicClosure Lsh) where
  toFun σ := towerAutomorphism e σ.1
    (inertia_fixes_fractionField v (π := π) (e.restrictScalars O) he σ)
  map_one' := towerAutomorphism_one e
  map_mul' σ τ := towerAutomorphism_mul e σ.1 τ.1 _ _

/-- Actual point evaluation intertwines original inertia, with no fixedness hypothesis. -/
theorem originalTowerInertia_evaluation [PerfectField Lsh]
    (e : Lsh →ₐ[Kv] Ωv) (he : ∀ a : Rsh, e (algebraMap Rsh Lsh a) = (a : Ωv))
    (X : ThreeAdicPlan.FF Rsh Lsh) (c : X.CoordinateRing) (x : X.Points)
    (σ : localInertiaGroup v) :
    X.towerValue e c (originalTowerInertia v π e he σ • x) = σ.1 (X.towerValue e c x) :=
  X.towerValue_smul e c x σ.1
    (inertia_fixes_fractionField v (π := π) (e.restrictScalars O) he σ)

end RaynaudParameters
