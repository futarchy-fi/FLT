/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.RaynaudLocalPowerRigidity
public import FLT.GroupScheme.RaynaudPowerPrescribedExtension

/-!
# Prescribed extension from p-power-killed models over a local completion

The actual graph projection is an integral isomorphism by the derived
inertia rigidity theorem. Its inverse followed by the second projection
extends the prescribed map, and every coordinate pullback is integral.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace ThreeAdicPlan
open NumberField IsLocalRing
open scoped TensorProduct

variable {K : Type} [Field K] [NumberField K]
  (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
local notation "Kv" => v.adicCompletion K
local notation "O" => v.adicCompletionIntegers K

variable [IsAdicComplete (maximalIdeal (v.adicCompletionIntegers K))
  (v.adicCompletionIntegers K)]

variable (p : ℕ) [Fact p.Prime] [CharP (ResidueField (v.adicCompletionIntegers K)) p]
  {X Y : FF (v.adicCompletionIntegers K) (v.adicCompletion K)}


/-- Every prescribed map from a p-power-killed model extends uniquely in small ramification. -/
theorem extend_from_local_power (he : RaynaudParameters.order (p : O) < p - 1)
    (hX : KilledByPowerOf p X) (f : GenericGaloisHom X Y) :
    ∃! g : ModelHom X Y, genericHom g = f := by
  apply extend_of_power_rigidity p (fun {A B} hA a ha ↦ ?_) hX f
  obtain ⟨n, hn⟩ := hA
  exact ModelHom.surjective_of_local_power v p (X := A) (Y := B) he hn a ha

/-- Coordinate pullbacks of the prescribed generic map lie in the original integral model. -/
theorem GenericGaloisHom.integral_of_local_power
    (he : RaynaudParameters.order (p : O) < p - 1) (hX : KilledByPowerOf p X)
    (f : GenericGaloisHom X Y) (y : Y.CoordinateRing) :
    ∃ x : X.CoordinateRing, f.toBialgHom (1 ⊗ₜ[O] y) = 1 ⊗ₜ[O] x := by
  obtain ⟨g, hg, _⟩ := extend_from_local_power v p he hX f
  refine ⟨g y, ?_⟩
  rw [← hg, ModelHom.toBialgHom_genericHom]
  rfl

end ThreeAdicPlan
