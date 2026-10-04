/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.PDivisibleTateModule

/-! # Compatible system morphisms allowing different heights -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace ThreeAdicPlan.PDivisibleSystem
variable {R K : Type} [CommRing R] [IsLocalRing R] [Field K] [Algebra R K]
  [PerfectField K] [IsFractionRing R K] {p h₁ h₂ h₃ : ℕ} [Fact p.Prime]

/-- An integral morphism of systems whose source and target heights may differ. -/
@[ext] structure VariableHeightHom (X : PDivisibleSystem R K p h₁)
    (Y : PDivisibleSystem R K p h₂) where
  /-- The original map on each finite-flat level. -/
  app : ∀ n, ModelHom (X.level n) (Y.level n)
  inclusion_naturality : ∀ {m n} (h : m ≤ n),
    (X.inclusion h).comp (app n) = (app m).comp (Y.inclusion h)
  reduction_naturality : ∀ {m n} (h : m ≤ n),
    (X.reduction h).comp (app m) = (app n).comp (Y.reduction h)

/-- Composition retains the actual integral maps at each level. -/
def VariableHeightHom.comp {X : PDivisibleSystem R K p h₁}
    {Y : PDivisibleSystem R K p h₂} {Z : PDivisibleSystem R K p h₃}
    (f : VariableHeightHom X Y) (g : VariableHeightHom Y Z) : VariableHeightHom X Z where
  app n := (f.app n).comp (g.app n)
  inclusion_naturality h := by
    rw [← BialgHom.comp_assoc, f.inclusion_naturality, BialgHom.comp_assoc,
      g.inclusion_naturality, ← BialgHom.comp_assoc]
  reduction_naturality h := by
    rw [← BialgHom.comp_assoc, f.reduction_naturality, BialgHom.comp_assoc,
      g.reduction_naturality, ← BialgHom.comp_assoc]

/-- A morphism of arbitrary heights induces the original map on Tate sequences. -/
def VariableHeightHom.tateMap {X : PDivisibleSystem R K p h₁}
    {Y : PDivisibleSystem R K p h₂} (f : VariableHeightHom X Y) :
    X.tateSequences →ₗ[ℤ_[p]] Y.tateSequences where
  __ := Y.tateLift (fun n ↦ (genericHom (f.app n)).toAddMonoidHom.comp (X.tateEval n)) (by
    intro m n h x
    change genericHom (Y.reduction h) (genericHom (f.app n) (X.tateEval n x)) =
      genericHom (f.app m) (X.tateEval m x)
    have hn := congrArg (fun k ↦ genericHom k (X.tateEval n x)) (f.reduction_naturality h)
    simpa only [genericHom_comp, X.tateEval_reduction] using hn.symm)
  map_smul' a x := by
    apply Y.tate_ext
    intro n
    change genericHom (f.app n) (a • X.tateEval n x) = a • genericHom (f.app n) (X.tateEval n x)
    rw [X.padic_smul_points, Y.padic_smul_points,
      ← ZMod.natCast_zmod_val (PadicInt.toZModPow n a), Nat.cast_smul_eq_nsmul,
      Nat.cast_smul_eq_nsmul, map_nsmul]
end ThreeAdicPlan.PDivisibleSystem
