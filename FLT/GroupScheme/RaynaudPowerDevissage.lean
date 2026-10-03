/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.RaynaudGeneralLayerDescent
public import FLT.GroupScheme.RaynaudTorsionFiltration
public import FLT.GroupScheme.RaynaudModelUpperBound

/-!
# Exponent induction from p-killed rigidity

Induction on the annihilating exponent uses the flat p-torsion closure and
the actual image of multiplication by p. General integral exactness descends
rigidity from those two smaller layers, without a generic splitting.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace ThreeAdicPlan

variable {R K : Type} [CommRing R] [Field K] [Algebra R K]
  [PerfectField K] [IsDedekindDomain R] [IsPrincipalIdealRing R] [IsFractionRing R K]
  (p : ℕ)
  (hkilled : ∀ {A B : FF R K}, (∀ a : A.Points, p • a = 0) →
    ∀ g : ModelHom A B, Function.Bijective (genericHom g) → Function.Surjective g)

include hkilled in
/-- A generically bijective integral comparison is surjective for every p-power-killed source. -/
theorem ModelHom.surjective_of_power_of_killed {n : ℕ}
    {X Y : FF R K}
    (hX : ∀ x : X.Points, p ^ n • x = 0)
    (g : ModelHom X Y) (hg : Function.Bijective (genericHom g)) : Function.Surjective g := by
  induction n generalizing X Y with
  | zero =>
    have hz : ∀ x : X.Points, x = 0 := by simpa using hX
    exact hkilled (A := X) (B := Y)
      (fun x ↦ by rw [hz x, smul_zero]) g hg
  | succ n ih =>
    let i : GenericGaloisHom (X.torsionAuxModel p) X := X.torsionInclusion p
    let q : GenericGaloisHom X (X.multipleModel p) := X.multiplyGeneric p
    have hi : Function.Injective i := Subtype.val_injective
    have hq : Function.Surjective q := X.multiplyGeneric_surjective p
    have hex : ∀ x, q x = 0 ↔ ∃ s, i s = x := by
      intro x
      constructor
      · intro hx
        exact ⟨⟨x, congrArg Subtype.val hx⟩, rfl⟩
      · rintro ⟨s, rfl⟩
        exact Subtype.ext s.property
    let inv := (genericHom g).inverse hg
    let q' : GenericGaloisHom Y (X.multipleModel p) := q.comp inv
    have hq' : Function.Surjective q' := by
      intro y
      obtain ⟨x, hx⟩ := hq y
      refine ⟨genericHom g x, ?_⟩
      change q ((genericHom g).inverse hg (genericHom g x)) = y
      rw [GenericGaloisHom.inverse_apply, hx]
    let h : GenericGaloisHom (X.multipleModel p) (X.multipleModel p) := DistribMulActionHom.id _
    have hc : q'.comp (genericHom g) = h.comp q := by
      ext x
      change q ((genericHom g).inverse hg (genericHom g x)) = q x
      rw [GenericGaloisHom.inverse_apply]
    have hj : Function.Injective ((genericHom g).comp i) := hg.injective.comp hi
    apply i.middle_surjective_of_layer_maps_pid q q' hi hq hq' hex g hj h hc
    · apply hkilled (A := i.closure hi)
        (B := GenericGaloisHom.closure (X := X.torsionAuxModel p) (Y := Y)
          ((genericHom g).comp i) hj)
        (fun x ↦ X.torsionClosure_killed p x) (i.closureMap hi g hj)
      constructor
      · intro x y hxy
        simpa only [i.genericHom_closureMap hi g hj] using hxy
      · intro x
        exact ⟨x, i.genericHom_closureMap hi g hj x⟩
    · refine ⟨q.flatQuotientMap_injective q' hq hq' g h hc Function.surjective_id, ?_⟩
      apply ih (X := q.flatQuotient hq) (Y := q'.flatQuotient hq')
        (fun x ↦ X.multipleModel_killed p n hX x) (q.flatQuotientMap q' hq hq' g h hc)
      constructor
      · intro x y hxy
        simpa only [q.genericHom_flatQuotientMap q' hq hq' g h hc,
          h, DistribMulActionHom.id_apply] using hxy
      · intro x
        exact ⟨x, q.genericHom_flatQuotientMap q' hq hq' g h hc x⟩

end ThreeAdicPlan
