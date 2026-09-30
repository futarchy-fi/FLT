/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ModuleCohomologyRing

/-! # Vanishing transport and the quotient step for module cohomology -/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace FLT.Mazur.FCurve

local instance vanishingHasExt (X : Scheme.{u}) :
    HasExt.{u + 1} (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) :=
  HasExt.standard _

variable {X : Scheme.{u}}

/-- Isomorphic coefficients have the same cohomological vanishing. -/
theorem moduleH_subsingleton_of_iso {M N : X.Modules} (e : M ≅ N) (q : ℕ)
    [Subsingleton (ModuleH N q)] : Subsingleton (ModuleH M q) := by
  let _zeroTarget : Subsingleton
      ((moduleRingHFunctor (RingHom.id Γ(X, ⊤)) q).obj N) :=
    inferInstanceAs (Subsingleton (ModuleH N q))
  exact ((moduleRingHFunctor (RingHom.id Γ(X, ⊤)) q).mapIso e).toLinearEquiv.injective.subsingleton

/-- A finite sum of coefficients with vanishing cohomology also has vanishing cohomology. -/
theorem moduleH_subsingleton_coproduct {κ : Type u} [Finite κ]
    (M : κ → X.Modules) (q : ℕ) [∀ i, Subsingleton (ModuleH (M i) q)] :
    Subsingleton (ModuleH (∐ M) q) := by
  let G := moduleRingHFunctor (RingHom.id Γ(X, ⊤)) q
  let e := PreservesCoproduct.iso G M ≪≫
    (biproduct.isoCoproduct (fun i ↦ G.obj (M i))).symm ≪≫
      IsLimit.conePointUniqueUpToIso (biproduct.isLimit (fun i ↦ G.obj (M i)))
        (ModuleCat.HasLimit.productLimitCone.{u, u + 1, u} (fun i : κ ↦ G.obj (M i))).isLimit
  let _zeroProduct : Subsingleton
      (ModuleCat.HasLimit.productLimitCone.{u, u + 1, u}
        (fun i : κ ↦ G.obj (M i))).cone.pt :=
    inferInstanceAs (Subsingleton (∀ i, ModuleH (M i) q))
  exact e.toLinearEquiv.injective.subsingleton

/-- Vanishing of middle cohomology and next kernel cohomology kills quotient cohomology. -/
theorem moduleH_subsingleton_right (S : ShortComplex X.Modules) (hS : S.ShortExact)
    (q : ℕ) [Subsingleton (ModuleH S.X₂ q)] [Subsingleton (ModuleH S.X₁ (q + 1))] :
    Subsingleton (ModuleH S.X₃ q) := by
  have hAb : (moduleAbelianComplex S).ShortExact :=
    CoherentDevissage.moduleToSheaf_shortExact hS
  have he : Function.Exact (moduleHMap S.g q) (moduleHConnecting S hAb q) :=
    (ShortComplex.ab_exact_iff_function_exact _).mp
      (Sheaf.H.longSequence_exact₃' hAb q (q + 1) rfl)
  have hz (x : ModuleH S.X₃ q) : x = 0 := by
    obtain ⟨y, hy⟩ := (he x).mp (Subsingleton.elim _ _)
    rw [Subsingleton.elim y 0, map_zero] at hy
    exact hy.symm
  exact ⟨fun x y ↦ (hz x).trans (hz y).symm⟩

end FLT.Mazur.FCurve
