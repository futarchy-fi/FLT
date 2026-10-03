/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.RaynaudLocalInertiaRigidity
public import FLT.GroupScheme.RaynaudPowerDevissage

/-!
# Local integral rigidity for all p-power-killed models

Induction on the annihilating exponent uses the flat p-torsion closure and
the actual image of multiplication by p. General integral exactness descends
rigidity from those two smaller layers, without a generic splitting.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace ThreeAdicPlan
open NumberField IsLocalRing

variable {K : Type} [Field K] [NumberField K]
  (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
local notation "Kv" => v.adicCompletion K
local notation "O" => v.adicCompletionIntegers K

variable [IsAdicComplete (maximalIdeal (v.adicCompletionIntegers K))
  (v.adicCompletionIntegers K)]

variable (p : ℕ) [Fact p.Prime] [CharP (ResidueField (v.adicCompletionIntegers K)) p]

set_option maxRecDepth 4000 in
/-- Local p-killed rigidity implies rigidity for every annihilating p-power. -/
theorem ModelHom.surjective_of_local_power
    (he : RaynaudParameters.order (p : O) < p - 1) {n : ℕ}
    {X Y : FF (v.adicCompletionIntegers K) (v.adicCompletion K)}
    (hX : ∀ x : X.Points, p ^ n • x = 0)
    (g : ModelHom X Y) (hg : Function.Bijective (genericHom g)) : Function.Surjective g := by
  let : IsPrincipalIdealRing O := IsDiscreteValuationRing.toIsPrincipalIdealRing
  let : IsDedekindDomain O := IsPrincipalIdealRing.isDedekindDomain O
  have H : ∀ {A B : FF O Kv}, (∀ a : A.Points, p • a = 0) →
      ∀ a : ModelHom A B, Function.Bijective (genericHom a) → Function.Surjective a := by
    intro A B hA a ha
    exact ModelHom.surjective_of_local_killed v p (X := A) (Y := B) he hA a ha
  exact @ModelHom.surjective_of_power_of_killed O Kv _ _ _ _ _ _ _ p H n X Y hX g hg

end ThreeAdicPlan
