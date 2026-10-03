/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.RaynaudDescentStage
public import FLT.GroupScheme.RaynaudStrictHenselian

/-!
# The original descent field inside the unramified tower field

Extend the actual integral embedding to fraction fields. Composition with
the prescribed tower embedding recovers the original descent-field inclusion.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace RaynaudParameters
open NumberField

variable {F X : Type} [Field F] [NumberField F]
  (v : IsDedekindDomain.HeightOneSpectrum (𝓞 F)) [AddCommGroup X]
  [DistribMulAction (AlgebraicClosure (v.adicCompletion F) ≃ₐ[v.adicCompletion F]
    AlgebraicClosure (v.adicCompletion F)) X]
  [Finite X] [ContinuousSMulDiscrete (AlgebraicClosure (v.adicCompletion F) ≃ₐ[v.adicCompletion F]
    AlgebraicClosure (v.adicCompletion F)) X]
local notation "O" => v.adicCompletionIntegers F
local notation "Ωv" => AlgebraicClosure (v.adicCompletion F)
local notation "L₀" => InertiaDescent.field (X := X) (localInertiaGroup v)
local notation "S₀" => IntegralClosure O L₀
variable {π : v.adicCompletionIntegers F} (hπ : Irreducible π)
local notation "Rsh" => unramifiedUnion (Ω := Ωv) π
local notation "Lsh" => FractionRing Rsh

/-- The actual finite descent field embeds in the fraction field of the original union. -/
def inertiaDescentFieldToTower : L₀ →ₐ[O] Lsh := by
  let f : S₀ →ₐ[O] Lsh := (IsScalarTower.toAlgHom O Rsh Lsh).comp
    (inertiaDescentIntegersToUnion (X := X) v hπ)
  have hi : Function.Injective (inertiaDescentIntegersToUnion (X := X) v hπ) := by
    intro x y h
    apply (IsFractionRing.injective S₀ L₀)
    apply (algebraMap L₀ Ωv).injective
    exact congrArg (fun a : Rsh ↦ (a : Ωv)) h
  exact IsFractionRing.liftAlgHom (g := f) ((IsFractionRing.injective Rsh Lsh).comp hi)

/-- The fraction-field lift restricts to the constructed integral embedding. -/
theorem inertiaDescentFieldToTower_algebraMap (x : S₀) :
    inertiaDescentFieldToTower (X := X) v hπ (algebraMap S₀ L₀ x) =
      algebraMap Rsh Lsh (inertiaDescentIntegersToUnion (X := X) v hπ x) :=
by
  simp [inertiaDescentFieldToTower, IsFractionRing.liftAlgHom, IsLocalization.liftAlgHom]

/-- The embedding agrees with the original descent-field inclusion, not a conjugate. -/
theorem inertiaDescentFieldToTower_comp
    (e : Lsh →ₐ[O] Ωv) (he : ∀ a : Rsh, e (algebraMap Rsh Lsh a) = (a : Ωv)) :
    e.comp (inertiaDescentFieldToTower (X := X) v hπ) = IsScalarTower.toAlgHom O L₀ Ωv := by
  apply AlgHom.coe_ringHom_injective
  apply IsFractionRing.ringHom_ext (A := S₀)
  intro a
  change e (inertiaDescentFieldToTower (X := X) v hπ (algebraMap S₀ L₀ a)) = _
  rw [inertiaDescentFieldToTower_algebraMap, he]
  rfl

end RaynaudParameters
