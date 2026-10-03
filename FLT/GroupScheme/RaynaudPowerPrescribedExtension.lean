/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.RaynaudPowerDevissage

/-!
# Graph extension from proved p-power rigidity

The actual graph projection is an integral isomorphism by the derived
p-power rigidity theorem. Its inverse followed by the second projection
extends the prescribed map, and every coordinate pullback is integral.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace ThreeAdicPlan
open scoped TensorProduct

variable {R K : Type} [CommRing R] [Field K] [Algebra R K]
  [PerfectField K] [IsDedekindDomain R] [IsFractionRing R K]
  (p : ℕ)
  (hRigidity : ∀ {A B : FF R K}, KilledByPowerOf p A →
    ∀ g : ModelHom A B, Function.Bijective (genericHom g) → Function.Surjective g)
  {X Y : FF R K}

include hRigidity in
/-- Every prescribed map from a p-power-killed model extends uniquely in small ramification. -/
theorem extend_of_power_rigidity
    (hX : KilledByPowerOf p X) (f : GenericGaloisHom X Y) :
    ∃! g : ModelHom X Y, genericHom g = f := by
  have hf : Function.Bijective (genericHom f.graphFst) := by
    constructor
    · intro x y hxy
      simpa only [f.genericHom_graphFst] using hxy
    · exact fun x ↦ ⟨x, f.genericHom_graphFst x⟩
  let e := BialgEquiv.ofBijective f.graphFst
    ⟨f.graphFst_injective, hRigidity (A := f.graphClosure) (B := X)
      (f.graphClosure_killedByPowerOf p hX) f.graphFst hf⟩
  let a : ModelHom X f.graphClosure := e.symm.toBialgHom
  have ha : ∀ x : X.Points, genericHom a x = x := by
    have hid : a.comp f.graphFst = BialgHom.id R X.CoordinateRing := by
      ext x
      exact e.symm_apply_apply x
    intro x
    have h := congrArg (fun g : ModelHom X X ↦ genericHom g x) hid
    simpa only [genericHom_comp, f.genericHom_graphFst, genericHom_id] using h
  have hg : genericHom (a.comp f.graphSnd) = f := by
    ext x
    rw [genericHom_comp, f.genericHom_graphSnd, ha]
  exact ⟨a.comp f.graphSnd, hg, fun g hg' ↦ genericHom_injective X Y (hg'.trans hg.symm)⟩

include hRigidity in
/-- Coordinate pullbacks of the prescribed generic map lie in the original integral model. -/
theorem GenericGaloisHom.integral_of_power_rigidity (hX : KilledByPowerOf p X)
    (f : GenericGaloisHom X Y) (y : Y.CoordinateRing) :
    ∃ x : X.CoordinateRing, f.toBialgHom (1 ⊗ₜ[R] y) = 1 ⊗ₜ[R] x := by
  obtain ⟨g, hg, _⟩ := extend_of_power_rigidity p hRigidity hX f
  refine ⟨g y, ?_⟩
  rw [← hg, ModelHom.toBialgHom_genericHom]
  rfl

end ThreeAdicPlan
