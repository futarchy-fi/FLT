/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineStalkMorphism
public import Mathlib.Algebra.Module.FinitePresentation

/-!
# Realizing affine stalk maps on principal opens

Finite presentation clears the denominator of a prescribed stalk map. Dividing
by the resulting unit section on a principal open gives an actual sheaf morphism
whose stalk is exactly the prescribed map.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite

universe u

namespace FLT.Mazur.FCurve.CoherentDevissage

variable {R : CommRingCat.{u}} {M N : ModuleCat.{u} R}

/-- A principal open regarded as an open subscheme of the affine scheme. -/
abbrev affinePrincipalOpen (s : R) : (Spec R).Opens := PrimeSpectrum.basicOpen s

/-- Clear a denominator for the full stalk map, using finite presentation of its source. -/
lemma exists_stalk_denominator [Module.FinitePresentation R M] (x : PrimeSpectrum R)
    (f : (tilde M).presheaf.stalk x →ₗ[R] (tilde N).presheaf.stalk x) :
    ∃ (a : M ⟶ N) (s : x.asIdeal.primeCompl),
      tildeStalkMap (tilde.map a) x = (s : R) • f := by
  obtain ⟨a, s, ha⟩ := Module.FinitePresentation.exists_lift_of_isLocalizedModule
    x.asIdeal.primeCompl (tilde.toStalk N x).hom (f.comp (tilde.toStalk M x).hom)
  refine ⟨ModuleCat.ofHom a, s, ?_⟩
  apply IsLocalizedModule.linearMap_ext x.asIdeal.primeCompl
    (tilde.toStalk M x).hom (tilde.toStalk N x).hom
  ext m
  exact (tildeStalkMap_toStalk (ModuleCat.ofHom a) x m).trans
    (DFunLike.congr_fun ha m)

section Scalar

variable {X : Scheme.{u}} (U : X.Opens) (P Q : X.Modules)

/-- The image-open structure ring acts on the identical restricted section module. -/
instance restrictedAmbientSectionModule (V : U.toScheme.Opens) :
    Module Γ(X, U.ι ''ᵁ V) Γ(P.restrict U.ι, V) :=
  inferInstanceAs (Module Γ(X, U.ι ''ᵁ V) Γ(P, U.ι ''ᵁ V))

/-- Multiply a restricted morphism by the restriction of a section on its ambient open. -/
def restrictedSectionMul (r : Γ(X, U)) (f : P.restrict U.ι ⟶ Q.restrict U.ι) :
    P.restrict U.ι ⟶ Q.restrict U.ι :=
  ⟨PresheafOfModules.homMk
    { app V := AddCommGrpCat.ofHom
        { toFun := fun m ↦ HSMul.hSMul (α := Γ(X, U.ι ''ᵁ V.unop))
            (β := Γ(Q, U.ι ''ᵁ V.unop)) (γ := Γ(Q, U.ι ''ᵁ V.unop))
            (X.presheaf.map (homOfLE (U.ι_image_le V.unop)).op r) (f.app V.unop m)
          map_zero' := by simp
          map_add' := by intros; simp [smul_add] }
      naturality := fun V W i ↦ by
        ext m
        have hf := PresheafOfModules.naturality_apply f.val i m
        change f.app W.unop (P.presheaf.map (U.ι.opensFunctor.map i.unop).op m) =
          Q.presheaf.map (U.ι.opensFunctor.map i.unop).op (f.app V.unop m) at hf
        change X.presheaf.map (homOfLE (U.ι_image_le W.unop)).op r •
          f.app W.unop (P.presheaf.map (U.ι.opensFunctor.map i.unop).op m) =
          Q.presheaf.map (U.ι.opensFunctor.map i.unop).op
            (X.presheaf.map (homOfLE (U.ι_image_le V.unop)).op r • f.app V.unop m)
        rw [Scheme.Modules.map_smul, hf]
        congr 1
        exact congr($(X.presheaf.map_comp
          (homOfLE (U.ι_image_le V.unop)).op (U.ι.opensFunctor.map i.unop).op) r) }
    (fun V a m ↦ by
      change Γ(U.toScheme, V.unop) at a
      change X.presheaf.map (homOfLE (U.ι_image_le V.unop)).op r •
        f.app V.unop (a • m) = a •
          (X.presheaf.map (homOfLE (U.ι_image_le V.unop)).op r • f.app V.unop m)
      rw [Scheme.Modules.Hom.app_smul]
      exact smul_comm _ ((U.ι.appIso V.unop).inv a) _)⟩

@[simp]
lemma restrictedSectionMul_app (r : Γ(X, U)) (f : P.restrict U.ι ⟶ Q.restrict U.ι)
    (V : U.toScheme.Opens) (m : Γ(P.restrict U.ι, V)) :
    (restrictedSectionMul U P Q r f).app V m =
      HSMul.hSMul (α := Γ(X, U.ι ''ᵁ V))
        (β := Γ(Q, U.ι ''ᵁ V)) (γ := Γ(Q, U.ι ''ᵁ V))
        (X.presheaf.map (homOfLE (U.ι_image_le V)).op r) (f.app V m) := rfl

/-- Multiplication by a section followed by its inverse leaves the morphism unchanged. -/
lemma restrictedSectionMul_unit_cancel (r : Γ(X, U)ˣ)
    (f : P.restrict U.ι ⟶ Q.restrict U.ι) :
    restrictedSectionMul U P Q (r : Γ(X, U))
      (restrictedSectionMul U P Q (↑r⁻¹) f) = f := by
  apply Scheme.Modules.hom_ext
  intro V
  ext m
  simp only [restrictedSectionMul_app, smul_smul, ← map_mul, Units.mul_inv, map_one,
    one_smul]

end Scalar

/-- The coefficient defining a principal open is an invertible section there. -/
def principalSectionUnit (s : R) : Γ(Spec R, affinePrincipalOpen s)ˣ :=
  (IsLocalization.Away.algebraMap_isUnit (S := Γ(Spec R, affinePrincipalOpen s)) s).unit

@[simp]
lemma principalSectionUnit_val (s : R) :
    (principalSectionUnit s : Γ(Spec R, affinePrincipalOpen s)) =
      algebraMap R _ s :=
  (IsLocalization.Away.algebraMap_isUnit (S := Γ(Spec R, affinePrincipalOpen s)) s).unit_spec

/-- Divide the restricted coefficient morphism by the invertible section `s`. -/
def principalStalkExtension (s : R) (a : M ⟶ N) :
    (tilde M).restrict (affinePrincipalOpen s).ι ⟶
      (tilde N).restrict (affinePrincipalOpen s).ι :=
  restrictedSectionMul (affinePrincipalOpen s) (tilde M) (tilde N)
    (↑(principalSectionUnit s)⁻¹)
    ((Scheme.Modules.restrictFunctor (affinePrincipalOpen s).ι).map (tilde.map a))

/-- Scalar multiplication on a restriction becomes multiplication by the scalar germ. -/
lemma restrictedSectionMul_stalk (U : (Spec R).Opens) (x : U) (r : Γ(Spec R, U))
    (f : (tilde M).restrict U.ι ⟶ (tilde N).restrict U.ι)
    (m : ((tilde M).restrict U.ι).presheaf.stalk x) :
    affineRestrictStalkEquiv U x N
      ((stalk (X := U.toScheme) x).map (restrictedSectionMul U (tilde M) (tilde N) r f) m) =
      HSMul.hSMul (α := (structurePresheafInCommRingCat R).stalk x.1)
        (β := (tilde N).presheaf.stalk x.1) (γ := (tilde N).presheaf.stalk x.1)
        ((Spec R).presheaf.germ U x.1 x.2 r)
        (affineRestrictStalkEquiv U x N ((stalk (X := U.toScheme) x).map f m)) := by
  obtain ⟨V, hx, m, rfl⟩ := ((tilde M).restrict U.ι).presheaf.exists_germ_eq m
  have hg (g : (tilde M).restrict U.ι ⟶ (tilde N).restrict U.ι) :
      (stalk (X := U.toScheme) x).map g
          (((tilde M).restrict U.ι).presheaf.germ V x hx m) =
        ((tilde N).restrict U.ι).presheaf.germ V x hx (g.app V m) :=
    TopCat.Presheaf.stalkFunctor_map_germ_apply V x hx g.mapPresheaf m
  rw [hg, hg, affineRestrictStalkEquiv_germ, affineRestrictStalkEquiv_germ,
    restrictedSectionMul_app]
  exact ((tilde N).val.germ_smul x.1 (U.ι ''ᵁ V) (by simpa) _ _).trans
    (congrArg (fun r : (structurePresheafInCommRingCat R).stalk x.1 ↦
      r • (tilde N).presheaf.germ (U.ι ''ᵁ V) x.1 (by simpa) (f.app V m))
      ((Spec R).presheaf.germ_res_apply (homOfLE (U.ι_image_le V)) x.1 (by simpa) r))

/-- Multiplication by the denominator recovers the restricted coefficient map on stalks. -/
lemma principalStalkExtension_smul (s : R) (a : M ⟶ N)
    (x : affinePrincipalOpen s)
    (m : ((tilde M).restrict (affinePrincipalOpen s).ι).presheaf.stalk x) :
    s • affineRestrictStalkEquiv (affinePrincipalOpen s) x N
      ((stalk (X := (affinePrincipalOpen s).toScheme) x).map
        (principalStalkExtension s a) m) =
      tildeStalkMap (tilde.map a) x.1
        (affineRestrictStalkEquiv (affinePrincipalOpen s) x M m) := by
  let U := affinePrincipalOpen s
  let g := (Scheme.Modules.restrictFunctor U.ι).map (tilde.map a)
  have h := congrArg (fun f : (tilde M).restrict U.ι ⟶ (tilde N).restrict U.ι ↦
    affineRestrictStalkEquiv U x N
    ((stalk (X := U.toScheme) x).map f m))
      (restrictedSectionMul_unit_cancel U (tilde M) (tilde N) (principalSectionUnit s) g)
  rw [restrictedSectionMul_stalk, principalSectionUnit_val] at h
  have hg : (Spec R).presheaf.germ U x.1 x.2 (algebraMap R Γ(Spec R, U) s) =
      StructureSheaf.toStalk R x.1 s :=
    StructureSheaf.algebraMap_germ_apply U x.1 x.2 s
  rw [hg] at h
  exact h.trans (affineRestrictStalkEquiv_naturality U x (tilde.map a) m)

/-- Every coefficient-linear stalk map with finitely presented source is realized nearby. -/
theorem exists_principal_stalk_extension [Module.FinitePresentation R M]
    (x : PrimeSpectrum R)
    (f : (tilde M).presheaf.stalk x →ₗ[R] (tilde N).presheaf.stalk x) :
    ∃ (s : R) (hs : x ∈ affinePrincipalOpen s)
      (g : (tilde M).restrict (affinePrincipalOpen s).ι ⟶
        (tilde N).restrict (affinePrincipalOpen s).ι),
      ∀ m : ((tilde M).restrict (affinePrincipalOpen s).ι).presheaf.stalk ⟨x, hs⟩,
        affineRestrictStalkEquiv (affinePrincipalOpen s) ⟨x, hs⟩ N
        ((stalk (X := (affinePrincipalOpen s).toScheme) ⟨x, hs⟩).map g m) =
          f (affineRestrictStalkEquiv (affinePrincipalOpen s) ⟨x, hs⟩ M m) := by
  obtain ⟨a, s, ha⟩ := exists_stalk_denominator (M := M) (N := N) x f
  refine ⟨s, s.2, principalStalkExtension (s : R) a, ?_⟩
  intro m
  have hs : Function.Injective (fun z : (tilde N).presheaf.stalk x ↦ (s : R) • z) :=
    ((Module.End.isUnit_iff _).mp
      (IsLocalizedModule.map_units (tilde.toStalk N x).hom s)).injective
  apply hs
  exact (principalStalkExtension_smul (s : R) a ⟨x, s.2⟩ m).trans
    (DFunLike.congr_fun ha _)

/-- A prescribed structure-stalk-linear map has an exact principal-open realization. -/
theorem exists_principal_stalk_extension_linear [Module.FinitePresentation R M]
    (x : PrimeSpectrum R)
    (f : (tilde M).presheaf.stalk x →ₗ[(structurePresheafInCommRingCat R).stalk x]
      (tilde N).presheaf.stalk x) :
    ∃ (s : R) (hs : x ∈ affinePrincipalOpen s)
      (g : (tilde M).restrict (affinePrincipalOpen s).ι ⟶
        (tilde N).restrict (affinePrincipalOpen s).ι),
      ∀ m : ((tilde M).restrict (affinePrincipalOpen s).ι).presheaf.stalk ⟨x, hs⟩,
        affineRestrictStalkEquiv (affinePrincipalOpen s) ⟨x, hs⟩ N
        ((stalk (X := (affinePrincipalOpen s).toScheme) ⟨x, hs⟩).map g m) =
          f (affineRestrictStalkEquiv (affinePrincipalOpen s) ⟨x, hs⟩ M m) :=
  exists_principal_stalk_extension (M := M) (N := N) x (stalkMapBaseLinear x f)

end FLT.Mazur.FCurve.CoherentDevissage
