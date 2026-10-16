/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ModuleSectionTransportRestriction
public import FLT.Mazur.ModulePullbackSectionTransport

/-!
# Transport of local scalar relations between retained global sections

Both coefficients in a local clearing identity are transported along the
actual scheme morphism. Neither section needs to generate its module.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Scheme.Modules
namespace FLT.Mazur.ModuleSectionTransportRestriction
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
universe u
variable {X Y : Scheme.{u}} (f : X ⟶ Y) {M : Y.Modules} {N : X.Modules}

/-- A local relation transports both original coefficients and both original sections. -/
theorem local_scalar_relation (a : M ⟶ (pushforward f).obj N)
    (s c : Γ(M, ⊤)) (U : Y.Opens) (V : X.Opens) (h : V ≤ f ⁻¹ᵁ U)
    (r v : Γ(Y, U))
    (hs : r • M.presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op s =
      v • M.presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op c) :
    f.appLE U V h r • N.presheaf.map (homOfLE (show V ≤ ⊤ from le_top)).op
        (a.app ⊤ s) =
      f.appLE U V h v • N.presheaf.map (homOfLE (show V ≤ ⊤ from le_top)).op
        (a.app ⊤ c) := by
  have ht := congrArg (a.app U) hs
  rw [app_smul, app_smul, ← restrict_global, ← restrict_global] at ht
  have hh := congrArg (N.presheaf.map (homOfLE h).op) ht
  have hh' := (Scheme.Modules.map_smul N (homOfLE h) (f.app U r)
    (N.presheaf.map (homOfLE (show f ⁻¹ᵁ U ≤ ⊤ from le_top)).op (a.app ⊤ s))).symm.trans
      (hh.trans (Scheme.Modules.map_smul N (homOfLE h) (f.app U v)
        (N.presheaf.map (homOfLE (show f ⁻¹ᵁ U ≤ ⊤ from le_top)).op (a.app ⊤ c))))
  have hi : (homOfLE (show f ⁻¹ᵁ U ≤ ⊤ from le_top)).op ≫ (homOfLE h).op =
      (homOfLE (show V ≤ ⊤ from le_top)).op := Subsingleton.elim _ _
  simpa only [← ConcreteCategory.comp_apply, ← Functor.map_comp, hi,
    Scheme.Hom.appLE] using hh'

/-- A full target chart retains the same relation under the chosen pullback map. -/
theorem pullGlobal_scalar_relation (a : (pullback f).obj M ⟶ N)
    (s c : Γ(M, ⊤)) (U : Y.Opens) (h : ⊤ ≤ f ⁻¹ᵁ U) (r v : Γ(Y, U))
    (hs : r • M.presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op s =
      v • M.presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op c) :
    f.appLE U ⊤ h r • a.app ⊤ (FCurve.pullGlobal f M s) =
      f.appLE U ⊤ h v • a.app ⊤ (FCurve.pullGlobal f M c) := by
  have ht := local_scalar_relation f (FCurve.moduleSectionTransport f a) s c U ⊤ h r v hs
  have hid (z : Γ(N, ⊤)) : N.presheaf.map (homOfLE (show (⊤ : X.Opens) ≤ ⊤ from le_top)).op
      z = z := by
    change N.presheaf.map (𝟙 _) z = z
    exact congrArg (fun k ↦ k z) (N.presheaf.map_id _)
  simpa only [hid, FCurve.moduleSectionTransport_top] using ht

end FLT.Mazur.ModuleSectionTransportRestriction
