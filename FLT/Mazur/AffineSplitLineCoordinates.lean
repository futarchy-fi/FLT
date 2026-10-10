/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineSectionLineRankOne
public import FLT.Mazur.SplitLineProjectiveFrame

/-!
# Actual affine coordinates of a framed split sheaf inclusion

Full faithfulness of affine tilde recovers the original inclusion and its
retraction as linear maps. Their composite is proved to be the identity.
The resulting split vector constructs a global projective morphism without
requiring any coordinate to be globally invertible.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace FLT.Mazur.AffineSplitLineCoordinates
open AffineModuleGlobalSections AffineFreeSheafCoordinates FCurve
variable {X : Scheme.{u}} [IsAffine X] {ι : Type u} [Finite ι]
variable {L : X.Modules} (e : L ≅ structureModule X)
variable (s : L ⟶ SheafOfModules.free ι) (r : SheafOfModules.free ι ⟶ L)

/-- The actual scalar affine sheaf identifies with the chosen line frame. -/
def sourceIso : (affineTilde X).obj (ModuleCat.of Γ(X, ⊤) Γ(X, ⊤)) ≅ L :=
  (pullback X.isoSpec.hom).mapIso tildeSelf ≪≫ modulePullbackUnitIso X.isoSpec.hom ≪≫ e.symm

/-- Recover the original inclusion in actual vector coordinates. -/
def inclusion : Γ(X, ⊤) →ₗ[Γ(X, ⊤)] (ι → Γ(X, ⊤)) :=
  ((affineTilde X).preimage ((sourceIso e).hom ≫ s ≫ (vectorFreeIso X ι).inv)).hom

/-- Recover the original splitting through the same actual coordinate comparisons. -/
def retraction : (ι → Γ(X, ⊤)) →ₗ[Γ(X, ⊤)] Γ(X, ⊤) :=
  ((affineTilde X).preimage ((vectorFreeIso X ι).hom ≫ r ≫ (sourceIso e).inv)).hom

attribute [local irreducible] affineTilde sourceIso vectorFreeIso

/-- Reconstruction preserves the original sheaf inclusion, including its ambient target. -/
lemma inclusion_reconstruct :
    (affineTilde X).map (ModuleCat.ofHom (inclusion e s)) ≫ (vectorFreeIso X ι).hom =
      (sourceIso e).hom ≫ s := by
  change (affineTilde X).map ((affineTilde X).preimage _) ≫ _ = _
  rw [Functor.map_preimage]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]

/-- The recovered linear maps inherit the actual original splitting. -/
lemma retraction_inclusion (hs : s ≫ r = 𝟙 L) :
    (retraction e r).comp (inclusion e s) = LinearMap.id := by
  suffices h : ModuleCat.ofHom (inclusion e s) ≫ ModuleCat.ofHom (retraction e r) =
      𝟙 (ModuleCat.of Γ(X, ⊤) Γ(X, ⊤)) from congrArg ModuleCat.Hom.hom h
  apply (affineTilde X).map_injective
  rw [Functor.map_comp, (affineTilde X).map_id]
  change (affineTilde X).map ((affineTilde X).preimage _) ≫
    (affineTilde X).map ((affineTilde X).preimage _) = _
  rw [Functor.map_preimage, Functor.map_preimage]
  simp only [Category.assoc, Iso.inv_hom_id_assoc, ← Category.assoc s r, hs,
    Category.id_comp, Iso.hom_inv_id]

/-- The image of the chosen unit frame is an actual split vector. -/
def vector : ι → Γ(X, ⊤) := inclusion e s 1

/-- The original sheaf retraction certifies the coordinate principal cover. -/
lemma vector_retraction (hs : s ≫ r = 𝟙 L) : retraction e r (vector e s) = 1 :=
  DFunLike.congr_fun (retraction_inclusion e s r hs) 1

/-- A framed split sheaf inclusion constructs an actual global projective point. -/
def projectivePoint (hs : s ≫ r = 𝟙 L) : X ⟶ ProjectiveSpace.space Γ(X, ⊤) ι :=
  SplitLinePrincipalPoints.morphism (vector e s) (retraction e r) (vector_retraction e s r hs)

/-- The constructed point has the original coefficient-spectrum structural map. -/
lemma projectivePoint_baseProjection (hs : s ≫ r = 𝟙 L) :
    projectivePoint e s r hs ≫ ProjectiveSpace.baseProjection Γ(X, ⊤) ι = X.isoSpec.hom :=
  SplitLinePrincipalPoints.morphism_baseProjection _ _ _

/-- Changing the splitting leaves the point of the original framed inclusion unchanged. -/
lemma projectivePoint_retraction_eq (hs : s ≫ r = 𝟙 L)
    (q : SheafOfModules.free ι ⟶ L) (hq : s ≫ q = 𝟙 L) :
    projectivePoint e s r hs = projectivePoint e s q hq :=
  SplitLinePrincipalPoints.morphism_retraction_eq _ _ _ _ _

end FLT.Mazur.AffineSplitLineCoordinates
