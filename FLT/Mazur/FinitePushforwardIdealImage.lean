/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FinitePushforwardCoherent
public import FLT.Mazur.GlobalIdealPowerCompatibility

/-!
# Ideal-action images and finite direct image

The affine identity `I M = (IB) M` identifies the actual image subsheaves.
The resulting isomorphism commutes with their inclusions, so its affine maps
are the original direct-image section maps. This is Stacks 01YP for finite
maps and coherent coefficients over a locally Noetherian target.
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry Opposite
open Scheme.Modules
open FLT.Mazur.FCurve FLT.Mazur.GlobalIdealPower
open FLT.Mazur.GlobalIdealPowerCompatibility

universe u

namespace FLT.Mazur.FinitePushforwardIdealImage

variable {X Y : Scheme.{u}} [IsLocallyNoetherian X]
  (f : Y ⟶ X) [IsFinite f] (I : X.IdealSheafData)
  (M : Y.Modules) [M.IsFinitePresentation]

/-- The affine range of the pushed-forward ideal inclusion is the target ideal multiple. -/
theorem pushforward_inclusion_range (V : X.affineOpens) :
    LinearMap.range (((pushforward f).map (inclusion (I.comap f) M)).val.app (op V.1)).hom =
      I.ideal V • (⊤ : Submodule Γ(X, V.1) Γ((pushforward f).obj M, V.1)) := by
  have := LocallyOfFiniteType.isLocallyNoetherian f
  let W : Y.affineOpens := ⟨f ⁻¹ᵁ V.1, V.2.preimage f⟩
  let := (f.app V.1).hom.toAlgebra
  let : Module Γ(X, V.1) Γ(M, W.1) := Module.compHom _ (f.app V.1).hom
  let : IsScalarTower Γ(X, V.1) Γ(Y, W.1) Γ(M, W.1) :=
    ⟨fun r s m ↦ mul_smul (f.app V.1 r) s m⟩
  have h := congrArg (fun N : Submodule Γ(Y, W.1) Γ(M, W.1) ↦
    N.restrictScalars Γ(X, V.1)) (inclusion_range (I.comap f) M W)
  rw [Scheme.IdealSheafData.ideal_comap I f V W le_rfl] at h
  have he : f.appLE V W le_rfl = f.app V.1 := by simp [Scheme.Hom.appLE, W]
  rw [he] at h
  exact h.trans (Ideal.smul_restrictScalars (I.ideal V)
    (⊤ : Submodule Γ(Y, W.1) Γ(M, W.1)))

/-- The actual ideal image commutes with finite direct image. -/
def iso : multiple I ((pushforward f).obj M) ≅
    (pushforward f).obj (multiple (I.comap f) M) := by
  have := LocallyOfFiniteType.isLocallyNoetherian f
  have := finitePushforward_isFinitePresentation f M
  exact affineImageIso (inclusion I ((pushforward f).obj M))
    ((pushforward f).map (inclusion (I.comap f) M)) (fun V ↦ by
      rw [inclusion_range, pushforward_inclusion_range])

/-- The comparison preserves the inclusions into the same direct image. -/
@[reassoc (attr := simp)]
theorem iso_inclusion :
    (iso f I M).hom ≫ (pushforward f).map (inclusion (I.comap f) M) =
      inclusion I ((pushforward f).obj M) := by
  unfold iso
  apply affineImageIso_comp

/-- On every open, the comparison is characterized by the original section inclusions. -/
theorem iso_sections (U : X.Opens) (s : Γ(multiple I ((pushforward f).obj M), U)) :
    (inclusion (I.comap f) M).app (f ⁻¹ᵁ U) ((iso f I M).hom.app U s) =
      (inclusion I ((pushforward f).obj M)).app U s :=
  congr($(iso_inclusion f I M).app U s)

end FLT.Mazur.FinitePushforwardIdealImage
