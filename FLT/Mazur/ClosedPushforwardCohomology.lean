/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineCoverCohomology
public import FLT.Mazur.CoherentClosedPushforward
public import FLT.Mazur.PushforwardCech

/-!
# Cohomology of coherent closed direct images

For a closed immersion into a separated locally Noetherian scheme, coherence
of direct image and the affine-cover computation identify the actual module
cohomology groups. The identification is linear over the target global sections
and after restriction along any base-ring map. No comparison data is required.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open AlgebraicGeometry.Scheme.Modules

universe u v

namespace FLT.Mazur.FCurve

open CechSheafHZero

variable {X Y : Scheme.{u}} [Y.IsSeparated] [IsLocallyNoetherian Y]
  (f : X ⟶ Y) [IsClosedImmersion f] (M : X.Modules) [M.IsFinitePresentation]

local instance closedCohomologyPushforwardCoherent :
    ((pushforward f).obj M).IsFinitePresentation :=
  CoherentDevissage.closedPushforward_isFinitePresentation f M

/-- The two affine-cover computations are identified by the actual direct-image sections. -/
def closedPushforwardCoverHEquiv {ι : Type u} (U : ι → Y.Opens)
    (hU : ∀ i, IsAffineOpen (U i)) (hCover : iSup U = ⊤) (n : ℕ) :
    letI _sourceScalars := Module.compHom (ModuleH M n) f.appTop.hom
    ModuleH ((pushforward f).obj M) n ≃ₗ[Γ(Y, ⊤)] ModuleH M n := by
  letI _sourceSeparated : X.IsSeparated := ⟨by
    rw [← terminal.comp_from f]
    infer_instance⟩
  letI _sourceCechScalars := Module.compHom
    (CH (fun i ↦ f ⁻¹ᵁ U i) (moduleAbelianSheaf M) n) f.appTop.hom
  letI _sourceScalars := Module.compHom (ModuleH M n) f.appTop.hom
  exact (affineCoverCechEquiv ((pushforward f).obj M) U hU hCover n).symm.trans
    ((PushforwardCech.moduleCechEquiv f U M n).trans
      (affineCoverRingCechEquiv M (fun i ↦ f ⁻¹ᵁ U i)
        (fun i ↦ (hU i).preimage f) (f.iSup_preimage_eq_top hCover) f.appTop.hom n))

/-- Closed direct image preserves cohomology, linearly over target global sections. -/
def closedPushforwardModuleHEquiv (n : ℕ) :
    letI _sourceScalars := Module.compHom (ModuleH M n) f.appTop.hom
    ModuleH ((pushforward f).obj M) n ≃ₗ[Γ(Y, ⊤)] ModuleH M n :=
  closedPushforwardCoverHEquiv f M (fun U : Y.affineOpens ↦ U.1)
    (fun U ↦ U.2) (iSup_affineOpens_eq_top Y) n

/-- Restriction of scalars gives closed-direct-image comparison over any base ring. -/
def closedPushforwardRingHEquiv {R : Type v} [Ring R]
    (ρ : R →+* Γ(Y, ⊤)) (n : ℕ) :
    letI _targetScalars := Module.compHom (ModuleH ((pushforward f).obj M) n) ρ
    letI _sourceScalars := Module.compHom (ModuleH M n) (f.appTop.hom.comp ρ)
    ModuleH ((pushforward f).obj M) n ≃ₗ[R] ModuleH M n := by
  letI _sourceTargetScalars := Module.compHom (ModuleH M n) f.appTop.hom
  letI _targetScalars := Module.compHom (ModuleH ((pushforward f).obj M) n) ρ
  letI _sourceScalars := Module.compHom (ModuleH M n) (f.appTop.hom.comp ρ)
  exact
    { toAddEquiv := (closedPushforwardModuleHEquiv f M n).toAddEquiv
      map_smul' := fun r x ↦ (closedPushforwardModuleHEquiv f M n).map_smul (ρ r) x }

/-- The comparison retains the specified structure morphisms over a field. -/
def closedPushforwardScalarHEquiv {k : Type u} [Field k]
    (g : Y ⟶ Spec (CommRingCat.of k)) (n : ℕ) :
    ModuleScalarH g ((pushforward f).obj M) n ≃ₗ[k] ModuleScalarH (f ≫ g) M n := by
  letI _sourceTargetScalars := Module.compHom (ModuleH M n) f.appTop.hom
  refine
    { toAddEquiv := (closedPushforwardModuleHEquiv f M n).toAddEquiv
      map_smul' := ?_ }
  intro r x
  change ModuleH ((pushforward f).obj M) n at x
  have h : structureScalarMap (f ≫ g) r = f.appTop (structureScalarMap g r) := by
    simp [structureScalarMap]
  change closedPushforwardModuleHEquiv f M n
      (structureScalarMap g r • (x : ModuleH ((pushforward f).obj M) n)) =
    structureScalarMap (f ≫ g) r • (closedPushforwardModuleHEquiv f M n x : ModuleH M n)
  rw [h]
  exact (closedPushforwardModuleHEquiv f M n).map_smul (structureScalarMap g r) x

end FLT.Mazur.FCurve
