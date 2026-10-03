/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.RootModuleLinear
public import FLT.GroupScheme.ContinuousKummerClass
public import FLT.GaloisRepresentation.Extensions.LinearContinuousClass

/-!
# Additivity of the continuous Kummer comparison

Multiplying Kummer parameters adds their root-ratio cocycles. Root-choice
independence upgrades the previously proved bijection to an additive equivalence.
-/

@[expose] public section

namespace KummerTheory

open GaloisRepresentation.Extensions

variable {K L : Type*} [Field K] [Field L] [Algebra K L] [IsGalois K L]
    {p : ℕ} [Fact p.Prime]

/-- The linear cohomology class of a particular Kummer root. -/
def linearRootClass (q : Kˣ) (b : Lˣ) (hb : b ^ p = Units.map (algebraMap K L) q) :
    LinearContinuousClass (ZMod p) Gal(L/K) (RootModule L p) :=
  Submodule.Quotient.mk (linearCocycleOf (continuousRootCocycle q b hb))

/-- The linear class is independent of the chosen root. -/
theorem linearRootClass_independent (q : Kˣ) (b d : Lˣ)
    (hb : b ^ p = Units.map (algebraMap K L) q)
    (hd : d ^ p = Units.map (algebraMap K L) q) :
    linearRootClass q b hb = linearRootClass q d hd := by
  apply linearClassEquiv.injective
  exact continuousRootCocycle_independent q b d hb hd

/-- The product root represents the sum of the two root classes. -/
theorem linearRootClass_mul (q r : Kˣ) (b d : Lˣ)
    (hb : b ^ p = Units.map (algebraMap K L) q)
    (hd : d ^ p = Units.map (algebraMap K L) r)
    (hbd : (b * d) ^ p = Units.map (algebraMap K L) (q * r)) :
    linearRootClass (q * r) (b * d) hbd = linearRootClass q b hb + linearRootClass r d hd := by
  change Submodule.Quotient.mk _ = Submodule.Quotient.mk _
  congr 1
  apply Subtype.ext
  apply ContinuousMap.ext
  intro g
  apply rootUnit_injective
  exact unitRatio_mul b d g

variable (roots : ∀ q : Kˣ, ∃ b : Lˣ, b ^ p = Units.map (algebraMap K L) q)

/-- The Kummer comparison in the linear presentation of continuous cohomology. -/
noncomputable def linearKummerMap (x : PowerClass K p) :
    LinearContinuousClass (ZMod p) Gal(L/K) (RootModule L p) :=
  linearClassEquiv.symm (kummerClassMap roots x)

/-- The linear comparison computes the chosen root class on parameters. -/
theorem linearKummerMap_mk (q : Kˣ) :
    linearKummerMap roots (powerClassMap p q) =
      linearRootClass q (roots q).choose (roots q).choose_spec := by
  apply linearClassEquiv.injective
  exact linearClassEquiv.apply_symm_apply _

/-- Multiplication of power classes is addition of their continuous Kummer classes. -/
theorem linearKummerMap_mul (x y : PowerClass K p) :
    linearKummerMap roots (x * y) = linearKummerMap roots x + linearKummerMap roots y := by
  induction x using Quotient.inductionOn with | h q =>
    induction y using Quotient.inductionOn with | h r =>
      change linearKummerMap roots (powerClassMap p q * powerClassMap p r) =
        linearKummerMap roots (powerClassMap p q) + linearKummerMap roots (powerClassMap p r)
      rw [← map_mul, linearKummerMap_mk, linearKummerMap_mk, linearKummerMap_mk]
      have hbd : ((roots q).choose * (roots r).choose) ^ p =
          Units.map (algebraMap K L) (q * r) := by
        rw [mul_pow, (roots q).choose_spec, (roots r).choose_spec, map_mul]
      rw [linearRootClass_independent (q * r) _ _ (roots (q * r)).choose_spec hbd]
      exact linearRootClass_mul q r _ _ (roots q).choose_spec (roots r).choose_spec hbd

/-- Kummer identifies the additive power-class group with linear continuous cohomology. -/
noncomputable def linearKummerEquiv : Additive (PowerClass K p) ≃+
    LinearContinuousClass (ZMod p) Gal(L/K) (RootModule L p) :=
  { toFun := fun x ↦ linearKummerMap roots x.toMul
    invFun := fun x ↦ Additive.ofMul ((continuousKummerEquiv roots).symm (linearClassEquiv x))
    left_inv := fun x ↦ by
      change Additive.ofMul ((continuousKummerEquiv roots).symm
        (linearClassEquiv (linearClassEquiv.symm ((continuousKummerEquiv roots) x.toMul)))) = x
      rw [Equiv.apply_symm_apply, Equiv.symm_apply_apply]
      rfl
    right_inv := fun x ↦ by
      change linearClassEquiv.symm ((continuousKummerEquiv roots)
        ((continuousKummerEquiv roots).symm (linearClassEquiv x))) = x
      rw [Equiv.apply_symm_apply, Equiv.symm_apply_apply]
    map_add' := fun x y ↦ linearKummerMap_mul roots x.toMul y.toMul }

end KummerTheory
