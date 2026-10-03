/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.RaynaudPadicPowerExtension

/-!
# Compatible integral transition maps over the p-adic integers

The proved unique extension chooses integral maps between actual models.
Generic diagrams commute integrally by faithfulness. Constructing the models
and the generic maps of the HR torsion tower is a separate obligation.
-/

@[expose] public noncomputable section

namespace ThreeAdicPlan

variable {p : ℕ} [Fact p.Prime] {X Y Z T : FF ℤ_[p] ℚ_[p]}

/-- The integral extension of a prescribed generic map from a p-power-killed model. -/
def GenericGaloisHom.padicExtension (f : GenericGaloisHom X Y)
    (hp : 2 < p) (hX : KilledByPowerOf p X) : ModelHom X Y :=
  (extend_from_padic_power p hp hX f).exists.choose

/-- The chosen extension has exactly the prescribed generic point map. -/
@[simp] theorem GenericGaloisHom.genericHom_padicExtension (f : GenericGaloisHom X Y)
    (hp : 2 < p) (hX : KilledByPowerOf p X) :
    genericHom (f.padicExtension hp hX) = f :=
  (extend_from_padic_power p hp hX f).exists.choose_spec

/-- Extending successive generic transitions agrees with their integral composite. -/
theorem GenericGaloisHom.padicExtension_comp
    (f : GenericGaloisHom X Y) (g : GenericGaloisHom Y Z)
    (hp : 2 < p) (hX : KilledByPowerOf p X) (hY : KilledByPowerOf p Y) :
    GenericGaloisHom.padicExtension (g.comp f) hp hX =
      (f.padicExtension hp hX).comp (g.padicExtension hp hY) := by
  apply genericHom_injective
  ext x
  rw [genericHom_padicExtension, genericHom_comp,
    genericHom_padicExtension, genericHom_padicExtension]
  rfl

/-- Every commuting generic square of p-power levels commutes integrally. -/
theorem GenericGaloisHom.padicExtension_square
    (f : GenericGaloisHom X Y) (g : GenericGaloisHom Y T)
    (a : GenericGaloisHom X Z) (b : GenericGaloisHom Z T)
    (hp : 2 < p) (hX : KilledByPowerOf p X)
    (hY : KilledByPowerOf p Y) (hZ : KilledByPowerOf p Z)
    (hsq : g.comp f = b.comp a) :
    (f.padicExtension hp hX).comp (g.padicExtension hp hY) =
      (a.padicExtension hp hX).comp (b.padicExtension hp hZ) := by
  rw [← padicExtension_comp, ← padicExtension_comp, hsq]

end ThreeAdicPlan
