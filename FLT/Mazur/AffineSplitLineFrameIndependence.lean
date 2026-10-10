/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineSplitLineCoordinates
public import FLT.Mazur.LinearRankOneFrameUnit

/-!
# Frame independence for the projective point of an actual sheaf inclusion

Recover the coordinate automorphism induced by two genuine sheaf frames
through fully faithful affine tilde. Its value at one is a constructed
unit. The resulting global projective point therefore depends only on the
original inclusion, not on its source frame or chosen retraction.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace FLT.Mazur.AffineSplitLineCoordinates
open AffineModuleGlobalSections AffineFreeSheafCoordinates FCurve LinearRankOneFrameUnit
variable {X : Scheme.{u}} [IsAffine X] {L : X.Modules}
variable (e d : L ≅ structureModule X)

/-- The original change of sheaf frame recovered as a scalar-module automorphism. -/
def frameChange : Γ(X, ⊤) ≃ₗ[Γ(X, ⊤)] Γ(X, ⊤) :=
  ((affineTilde X).preimageIso (sourceIso d ≪≫ (sourceIso e).symm)).toLinearEquiv

attribute [local irreducible] affineTilde sourceIso vectorFreeIso

/-- Reconstructing the recovered frame change gives the actual original sheaf comparison. -/
lemma frameChange_reconstruct :
    (affineTilde X).map (ModuleCat.ofHom (frameChange e d).toLinearMap) =
      (sourceIso d).hom ≫ (sourceIso e).inv :=
  (affineTilde X).map_preimage _

variable {ι : Type u} [Finite ι] (s : L ⟶ SheafOfModules.free ι)

/-- The recovered inclusions transform by the actual recovered scalar automorphism. -/
lemma inclusion_frame : inclusion d s = (inclusion e s).comp (frameChange e d).toLinearMap := by
  suffices h : ModuleCat.ofHom (inclusion d s) =
      ModuleCat.ofHom (frameChange e d).toLinearMap ≫ ModuleCat.ofHom (inclusion e s)
      from congrArg ModuleCat.Hom.hom h
  apply (affineTilde X).map_injective
  rw [Functor.map_comp, frameChange_reconstruct]
  change (affineTilde X).map ((affineTilde X).preimage _) =
    _ ≫ (affineTilde X).map ((affineTilde X).preimage _)
  rw [Functor.map_preimage, Functor.map_preimage]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]

/-- The vectors of two actual frames differ by the constructed unit. -/
lemma vector_frame : vector d s = (scalarUnit (frameChange e d) : Γ(X, ⊤)) • vector e s := by
  unfold vector
  rw [inclusion_frame e d]
  change inclusion e s (frameChange e d 1) = _
  simpa only [scalarUnit, smul_eq_mul, mul_one] using
    (inclusion e s).map_smul (scalarUnit (frameChange e d) : Γ(X, ⊤)) (1 : Γ(X, ⊤))

/-- Changing the genuine source sheaf frame preserves its actual global projective point. -/
lemma projectivePoint_frame (r : SheafOfModules.free ι ⟶ L) (hs : s ≫ r = 𝟙 L) :
    projectivePoint d s r hs = projectivePoint e s r hs := by
  let c := scalarUnit (frameChange e d)
  have hv : vector d s = (c : Γ(X, ⊤)) • vector e s := vector_frame e d s
  have hr : retraction d r ((c : Γ(X, ⊤)) • vector e s) = 1 := by
    rw [← hv]
    exact vector_retraction d s r hs
  calc
    projectivePoint d s r hs = SplitLinePrincipalPoints.morphism
        ((c : Γ(X, ⊤)) • vector e s) (retraction d r) hr := by
      unfold projectivePoint
      congr 1
    _ = projectivePoint e s r hs :=
      SplitLinePrincipalPoints.morphism_unit_smul _ _ _ c _ hr

/-- Both arbitrary source frames and arbitrary retractions give the same actual point. -/
lemma projectivePoint_choices (r q : SheafOfModules.free ι ⟶ L)
    (hr : s ≫ r = 𝟙 L) (hq : s ≫ q = 𝟙 L) :
    projectivePoint d s r hr = projectivePoint e s q hq :=
  (projectivePoint_frame e d s r hr).trans (projectivePoint_retraction_eq e s r hr q hq)

end FLT.Mazur.AffineSplitLineCoordinates
