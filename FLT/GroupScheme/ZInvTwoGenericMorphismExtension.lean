/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.EtaleGenericMorphismExtension
public import FLT.GroupScheme.GenericMorphismScalarExtension
public import FLT.GroupScheme.RaynaudFilteredExtension
public import FLT.GroupScheme.ZInvTwoArithmeticSquare

/-!
# Extending rational morphisms over `ℤ[1/2]`

A rational morphism extends uniquely if its source is étale away from three
and its actual three-adic model has an order-three filtration. Both integral
lifts are constructed. Their compatibility is a consequence of their prescribed
rational origin, rather than an additional hypothesis.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open scoped TensorProduct

namespace ThreeAdicPlan


open PadicPatching

local instance : Fact (¬ (3 : ℤ) ∣ 2) := ⟨by norm_num⟩

private theorem scalarExtensionMap_self (B : Type) [AddCommGroup B] [Module ZInvTwo B]
    (z : ℚ ⊗[ZInvTwo] B) : scalarExtensionMap ℚ ℚ B z = z := by
  induction z using TensorProduct.inductionOn with
  | tmul k x => simp
  | add a b ha hb => simpa using congrArg₂ (· + ·) ha hb

private theorem scalarExtensionMap_away_rat (B : Type) [AddCommGroup B] [Module ZInvTwo B]
    (z : Away 2 3 ⊗[ZInvTwo] B) :
    scalarExtensionMap ℚ ℚ_[3] B (scalarExtensionMap (Away 2 3) ℚ B z) =
      scalarExtensionMap (Away 2 3) ℚ_[3] B z := by
  induction z using TensorProduct.inductionOn with
  | tmul k x =>
    simp only [scalarExtensionMap_tmul]
    rw [← IsScalarTower.algebraMap_apply (Away 2 3) ℚ ℚ_[3]]
  | add a b ha hb => simpa using congrArg₂ (· + ·) ha hb

/-- A generic morphism from an away-étale model with a three-adically filtered
source extends uniquely to the specified global integral models. -/
theorem extend_generic_morphism_over_zInvTwo
    (X Y : FF ZInvTwo ℚ)
    [Algebra.Etale (Away 2 3) (Away 2 3 ⊗[ZInvTwo] X.CoordinateRing)]
    {n : ℕ} (hX : (X.scalarExtension ℤ_[3] ℚ_[3]).HasOrderThreeFiltration n)
    (f : GenericGaloisHom X Y) :
    ∃! g : ModelHom X Y, genericHom g = f := by
  let : Algebra.Etale (Away 2 3) (X.scalarExtension (Away 2 3) ℚ).CoordinateRing :=
    inferInstanceAs (Algebra.Etale (Away 2 3) (Away 2 3 ⊗[ZInvTwo] X.CoordinateRing))
  obtain ⟨a, ha, _⟩ := extend_generic_morphism_of_etale
    (X.scalarExtension (Away 2 3) ℚ) (Y.scalarExtension (Away 2 3) ℚ)
      (f.scalarExtension (Away 2 3) ℚ)
  obtain ⟨b, hb, _⟩ := raynaud_extend_generic_morphism_of_orderThreeFiltration
    (X.scalarExtension ℤ_[3] ℚ_[3]) (Y.scalarExtension ℤ_[3] ℚ_[3])
      hX (f.scalarExtension ℤ_[3] ℚ_[3])
  change Away 2 3 ⊗[ZInvTwo] Y.CoordinateRing →ₐc[Away 2 3]
    Away 2 3 ⊗[ZInvTwo] X.CoordinateRing at a
  change ℤ_[3] ⊗[ZInvTwo] Y.CoordinateRing →ₐc[ℤ_[3]]
    ℤ_[3] ⊗[ZInvTwo] X.CoordinateRing at b
  have ha' (y : Y.CoordinateRing) :
      scalarExtensionMap (Away 2 3) ℚ X.CoordinateRing (a (1 ⊗ₜ[ZInvTwo] y)) =
        f.toBialgHom (1 ⊗ₜ[ZInvTwo] y) := by
    exact (ModelHom.scalarExtension_cancel (Away 2 3) ℚ a f ha y).trans
      (scalarExtensionMap_self X.CoordinateRing _)
  have hc (y : Y.CoordinateRing) :
      scalarExtensionMap (Away 2 3) ℚ_[3] X.CoordinateRing (a (1 ⊗ₜ[ZInvTwo] y)) =
        scalarExtensionMap ℤ_[3] ℚ_[3] X.CoordinateRing (b (1 ⊗ₜ[ZInvTwo] y)) := by
    exact (scalarExtensionMap_away_rat X.CoordinateRing _).symm.trans
      ((congrArg (scalarExtensionMap ℚ ℚ_[3] X.CoordinateRing) (ha' y)).trans
        (ModelHom.scalarExtension_cancel ℤ_[3] ℚ_[3] b f hb y).symm)
  let : Module.FinitePresentation ZInvTwo X.CoordinateRing :=
    Module.finitePresentation_of_finite ZInvTwo X.CoordinateRing
  let : Module.Projective ZInvTwo X.CoordinateRing := Module.Flat.projective_of_finitePresentation
  obtain ⟨g, hg, _⟩ := existsUnique_bialgHom_of_away_local 3 2
    Y.CoordinateRing X.CoordinateRing a b hc
  have hg' (y : Y.CoordinateRing) :
      (1 : ℚ) ⊗ₜ[ZInvTwo] g y = f.toBialgHom (1 ⊗ₜ[ZInvTwo] y) := by
    have h := congrArg (scalarExtensionMap (Away 2 3) ℚ X.CoordinateRing) (hg.1 y)
    calc
      _ = scalarExtensionMap (Away 2 3) ℚ X.CoordinateRing
          (a (1 ⊗ₜ[ZInvTwo] y)) := by
        simpa only [scalarExtensionMap_tmul, map_one] using h
      _ = _ := ha' y
  have hbase : ModelHom.baseChange (X := X) (Y := Y) g = f.toBialgHom := by
    ext z
    induction z using TensorProduct.inductionOn with
    | tmul k y =>
      change k ⊗ₜ[ZInvTwo] g y = f.toBialgHom (k ⊗ₜ[ZInvTwo] y)
      rw [show k ⊗ₜ[ZInvTwo] y = k • ((1 : ℚ) ⊗ₜ[ZInvTwo] y) by
        rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one], map_smul, ← hg']
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    | add u v hu hv => simpa using congrArg₂ (· + ·) hu hv
  have hgf : genericHom (X := X) (Y := Y) g = f := by
    ext x
    obtain ⟨p, rfl⟩ := X.points_bijective.2 x
    rw [genericHom_points, hbase]
    exact f.toBialgHom_points p
  exact ⟨g, hgf, fun g' hg' ↦ genericHom_injective X Y (hg'.trans hgf.symm)⟩

end ThreeAdicPlan
