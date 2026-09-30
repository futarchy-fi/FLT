/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.NestedOpenCohomologyCoherence
public import FLT.Mazur.ModuleOpenCohomology
public import FLT.Mazur.ModuleCohomologyRing

/-!
# Scalar compatibility of restriction in module cohomology
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxSynthPendingDepth 1

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite

universe u v

namespace FLT.Mazur.FCurve

open OpenSheafRestriction OpenSheafCohomologyRestriction SchemeCohomologyIso

local instance moduleRestrictionHasExt (T : TopCat.{u}) :
    HasExt.{u + 1} (Sheaf (Opens.grothendieckTopology T) AddCommGrpCat.{u}) :=
  HasExt.standard _

local instance moduleRestrictionOpenHasExt {T : TopCat.{u}} (W : Opens T) :
    HasExt.{u + 1} (Sheaf (Opens.grothendieckTopology W) AddCommGrpCat.{u}) :=
  HasExt.standard _
/-- Multiplication by an ambient section commutes with restriction along an open immersion. -/
lemma restrict_multiply_app {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f]
    (M : Y.Modules) (r : Γ(Y, ⊤)) (W : X.Opens) :
    (moduleMultiply (M.restrict f) (f.appTop r)).hom.app (op W) =
      (moduleMultiply M r).hom.app (op (f ''ᵁ W)) := by
  ext x
  change M.val.obj (op (f ''ᵁ W)) at x
  change (f.appIso W).inv (X.presheaf.map (homOfLE (show W ≤ ⊤ from le_top)).op (f.appTop r)) • x =
    Y.presheaf.map (homOfLE (show f ''ᵁ W ≤ ⊤ from le_top)).op r • x
  congr 1
  rw [← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply,
    Scheme.Hom.appIso_inv_naturality, ← Category.assoc]
  erw [Scheme.Hom.app_appIso_inv f ⊤, ← Functor.map_comp]
  rfl
/-- Ordinary restriction, with the actual module cohomology types retained. -/
def moduleGlobalRestriction {X : Scheme.{u}} (W : X.Opens) (M : X.Modules) (n : ℕ) :
    ModuleH M n →+ ModuleH (M.restrict W.ι) n :=
  globalOpenRestriction W (moduleAbelianSheaf M) n
/-- Restriction to an open is semilinear over the map of global sections. -/
lemma globalOpenRestriction_smul {X : Scheme.{u}} (W : X.Opens) (M : X.Modules)
    (n : ℕ) (r : Γ(X, ⊤)) (x : ModuleH M n) :
    moduleGlobalRestriction W M n (r • x) =
      W.ι.appTop r • moduleGlobalRestriction W M n x := by
  have h : (restriction W).map (moduleMultiply M r) =
      moduleMultiply (M.restrict W.ι) (W.ι.appTop r) := by
    apply Sheaf.hom_ext
    apply NatTrans.ext
    funext O
    exact (restrict_multiply_app W.ι M r O.unop).symm
  change globalOpenRestriction W (moduleAbelianSheaf M) n
    (Sheaf.H.map (moduleMultiply M r) n x) = _
  rw [globalOpenRestriction_naturality, h]
  rfl
/-- Scheme-isomorphism transport is semilinear over its map of global sections. -/
lemma moduleHIsoEquiv_smul {X Y : Scheme.{u}} (e : X ≅ Y) (M : Y.Modules)
    (n : ℕ) (r : Γ(Y, ⊤)) (x : ModuleH M n) :
    moduleHIsoEquiv e M n (r • x) =
      e.hom.appTop r • moduleHIsoEquiv e M n x := by
  have h : (abelianSheafEquivalence e).inverse.map (moduleMultiply M r) =
      moduleMultiply (M.restrict e.hom) (e.hom.appTop r) := by
    apply Sheaf.hom_ext
    apply NatTrans.ext
    funext O
    exact (restrict_multiply_app e.hom M r O.unop).symm
  change sheafHEquiv e (moduleAbelianSheaf M) n (Sheaf.H.map (moduleMultiply M r) n x) = _
  rw [sheafHEquiv_naturality, h]
  rfl

variable {S : Scheme.{u}} (U : S.Opens) (V : U.toScheme.Opens)
/-- The actual module restrictions agree through the flattening scheme isomorphism. -/
def nestedModuleIso (M : S.Modules) :
    (M.restrict (U.ι ''ᵁ V).ι).restrict (U.ι.isoImage V).hom ≅
      (M.restrict U.ι).restrict V.ι :=
  (Scheme.Modules.restrictFunctorComp (U.ι.isoImage V).hom (U.ι ''ᵁ V).ι).symm.app M ≪≫
    (Scheme.Modules.restrictFunctorCongr (Scheme.Hom.isoImage_hom_ι U.ι V)).app M ≪≫
      (Scheme.Modules.restrictFunctorComp V.ι U.ι).app M
/-- The canonical sheaf comparison transported through actual module restriction isomorphisms. -/
def nestedModuleAbelianIso (M : S.Modules) :
    moduleAbelianSheaf ((M.restrict (U.ι ''ᵁ V).ι).restrict (U.ι.isoImage V).hom) ≅
      moduleAbelianSheaf ((M.restrict U.ι).restrict V.ι) :=
  (moduleRestrictionIso (U.ι.isoImage V) (M.restrict (U.ι ''ᵁ V).ι)).symm ≪≫
    (abelianSheafEquivalence (U.ι.isoImage V)).inverse.mapIso
      (ModuleOpenCohomology.restrictionIso (U.ι ''ᵁ V) M).symm ≪≫
    (nestedRestrictionIso U V).app (moduleAbelianSheaf M) ≪≫
    (restriction V).mapIso (ModuleOpenCohomology.restrictionIso U M) ≪≫
    ModuleOpenCohomology.restrictionIso V (M.restrict U.ι)

private lemma restrictionSquare_hom_app {T A B Z : Scheme.{u}}
    (f : T ⟶ A) (g : A ⟶ Z) (h : T ⟶ B) (k : B ⟶ Z)
    [IsOpenImmersion f] [IsOpenImmersion g] [IsOpenImmersion h] [IsOpenImmersion k]
    (w : f ≫ g = h ≫ k) (M : Z.Modules) (O : T.Opens) :
    (((Scheme.Modules.restrictFunctorComp f g).symm.app M ≪≫
      (Scheme.Modules.restrictFunctorCongr w).app M ≪≫
      (Scheme.Modules.restrictFunctorComp h k).app M).hom).app O =
        M.presheaf.map (eqToHom (show k ''ᵁ (h ''ᵁ O) = g ''ᵁ (f ''ᵁ O) by
          simp only [← Scheme.Hom.comp_image, w])).op := by
  simp only [Iso.trans_hom, Iso.app_hom, Iso.symm_hom, Scheme.Modules.Hom.comp_app,
    Scheme.Modules.restrictFunctorComp_inv_app_app,
    Scheme.Modules.restrictFunctorCongr_hom_app_app,
    Scheme.Modules.restrictFunctorComp_hom_app_app, ← Functor.map_comp]
  rfl
/-- The module comparison uses the canonical equality of ambient image opens. -/
lemma nestedModuleIso_hom_app (M : S.Modules) (O : V.toScheme.Opens) :
    ((nestedModuleIso U V M).hom).app O =
      M.presheaf.map (eqToHom (nestedImage_eq U V O).symm).op :=
  restrictionSquare_hom_app (U.ι.isoImage V).hom (U.ι ''ᵁ V).ι V.ι U.ι
    (Scheme.Hom.isoImage_hom_ι U.ι V) M O
/-- Forgetting the module comparison gives the canonical nested sheaf comparison. -/
lemma nestedModuleIso_hom (M : S.Modules) :
    (SheafOfModules.toSheaf V.toScheme.ringCatSheaf).map (nestedModuleIso U V M).hom =
      (nestedModuleAbelianIso U V M).hom := by
  apply Sheaf.hom_ext
  apply NatTrans.ext
  funext O
  change ((nestedModuleIso U V M).hom).app O.unop = _
  rw [nestedModuleIso_hom_app]
  rfl
/-- An isomorphism of modules induces a linear cohomology equivalence. -/
def moduleHIsoOfIso {T : Scheme.{u}} {M N : T.Modules} (e : M ≅ N) (n : ℕ) :
    ModuleH M n ≃ₗ[Γ(T, ⊤)] ModuleH N n :=
  ((moduleRingHFunctor (RingHom.id Γ(T, ⊤)) n).mapIso e).toLinearEquiv
/-- The canonical additive comparison with iterated module cohomology. -/
def nestedModuleHEquiv (M : S.Modules) (n : ℕ) :
    ModuleH (M.restrict (U.ι ''ᵁ V).ι) n ≃+
      ModuleH ((M.restrict U.ι).restrict V.ι) n :=
  (moduleHIsoEquiv (U.ι.isoImage V) (M.restrict (U.ι ''ᵁ V).ι) n).trans
    (moduleHIsoOfIso (nestedModuleIso U V M) n).toAddEquiv

lemma nestedModuleHEquiv_smul (M : S.Modules) (n : ℕ)
    (r : Γ((U.ι ''ᵁ V).toScheme, ⊤)) (x : ModuleH (M.restrict (U.ι ''ᵁ V).ι) n) :
    nestedModuleHEquiv U V M n (r • x) =
      (U.ι.isoImage V).hom.appTop r • nestedModuleHEquiv U V M n x := by
  change moduleHMap (nestedModuleIso U V M).hom n (moduleHIsoEquiv _ _ n (r • x)) = _
  rw [moduleHIsoEquiv_smul, map_smul]
  rfl
/-- Ambient cohomology restriction transported to the actual restricted modules. -/
def moduleOpenRestriction (M : S.Modules) {W U : S.Opens} (i : W ⟶ U) (n : ℕ) :
    ModuleH (M.restrict U.ι) n →+ ModuleH (M.restrict W.ι) n :=
  (moduleOpenHEquiv W M n).toAddMonoidHom.comp
    (((moduleAbelianSheaf M).cohomologyPresheaf n).map i.op).hom |>.comp
      (moduleOpenHEquiv U M n).symm.toAddMonoidHom

private lemma iso_H_inv {T T' : Scheme.{u}} (e : T ≅ T') (M : T'.Modules)
    (n : ℕ) (x : ModuleH M n) :
    Sheaf.H.map (moduleRestrictionIso e M).inv n (moduleHIsoEquiv e M n x) =
      sheafHEquiv e (moduleAbelianSheaf M) n x := Sheaf.H.map_id_apply _

private lemma open_H_inv (W : S.Opens) (M : S.Modules) (n : ℕ)
    (x : Sheaf.H'.{u + 1} (moduleAbelianSheaf M) n W) :
    Sheaf.H.map (ModuleOpenCohomology.restrictionIso W M).inv n
      (moduleOpenHEquiv W M n x) =
        OpenSheafCohomology.openHEquiv W (moduleAbelianSheaf M) n x := Sheaf.H.map_id_apply _

private lemma open_H_hom {T : Scheme.{u}} (W : T.Opens) (M : T.Modules) (n : ℕ)
    (x : Sheaf.H.{u + 1} ((restriction W).obj (moduleAbelianSheaf M)) n) :
    Sheaf.H.map (ModuleOpenCohomology.restrictionIso W M).hom n x = x := Sheaf.H.map_id_apply _

private lemma restriction_transport {T : Scheme.{u}} (W : S.Opens) (M : S.Modules)
    (e : T ≅ W.toScheme) {B : TopCat.Sheaf AddCommGrpCat.{u} T.toTopCat}
    (a : (abelianSheafEquivalence e).inverse.obj
      ((restriction W).obj (moduleAbelianSheaf M)) ⟶ B) (n : ℕ)
    (z : Sheaf.H'.{u + 1} (moduleAbelianSheaf M) n W) :
    Sheaf.H.map ((moduleRestrictionIso e (M.restrict W.ι)).inv ≫
      (abelianSheafEquivalence e).inverse.map
        (ModuleOpenCohomology.restrictionIso W M).inv ≫ a) n
      (moduleHIsoEquiv e (M.restrict W.ι) n (moduleOpenHEquiv W M n z)) =
      Sheaf.H.map a n (sheafHEquiv e ((restriction W).obj (moduleAbelianSheaf M)) n
        (OpenSheafCohomology.openHEquiv W (moduleAbelianSheaf M) n z)) := by
  rw [Sheaf.H.map_comp_apply, Sheaf.H.map_comp_apply, iso_H_inv,
    ← sheafHEquiv_naturality, open_H_inv]

private lemma moduleHIsoOfIso_apply {T : Scheme.{u}} {M N : T.Modules}
    (e : M ≅ N) (n : ℕ) (x : ModuleH M n) :
    moduleHIsoOfIso e n x = moduleHMap e.hom n x := rfl
/-- The transported restriction is the ordinary restriction on the intermediate scheme. -/
lemma moduleOpenRestriction_nested (M : S.Modules) (n : ℕ)
    (x : ModuleH (M.restrict U.ι) n) :
    nestedModuleHEquiv U V M n
      (moduleOpenRestriction M (homOfLE (openImage_le U V)) n x) =
        moduleGlobalRestriction V (M.restrict U.ι) n x := by
  change moduleHIsoOfIso (nestedModuleIso U V M) n
    (moduleHIsoEquiv (U.ι.isoImage V) (M.restrict (U.ι ''ᵁ V).ι) n
      (moduleOpenRestriction M (homOfLE (openImage_le U V)) n x)) = _
  rw [moduleHIsoOfIso_apply]
  change Sheaf.H.map
    ((SheafOfModules.toSheaf V.toScheme.ringCatSheaf).map (nestedModuleIso U V M).hom) n
    (moduleHIsoEquiv (U.ι.isoImage V) (M.restrict (U.ι ''ᵁ V).ι) n
      (moduleOpenHEquiv (U.ι ''ᵁ V) M n
        (((moduleAbelianSheaf M).cohomologyPresheaf n).map
          (homOfLE (openImage_le U V)).op ((moduleOpenHEquiv U M n).symm x)))) = _
  rw [nestedModuleIso_hom]
  simp only [nestedModuleAbelianIso, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom]
  rw [restriction_transport, Sheaf.H.map_comp_apply]
  refine (congrArg (Sheaf.H.map
    ((restriction V).map (ModuleOpenCohomology.restrictionIso U M).hom ≫
      (ModuleOpenCohomology.restrictionIso V (M.restrict U.ι)).hom) n)
    (nested_global_restriction U V (moduleAbelianSheaf M) n
      ((moduleOpenHEquiv U M n).symm x))).trans ?_
  rw [Sheaf.H.map_comp_apply, open_H_hom, ← globalOpenRestriction_naturality]
  exact congrArg (globalOpenRestriction V (moduleAbelianSheaf (M.restrict U.ι)) n)
    ((open_H_hom U M n _).trans ((moduleOpenHEquiv U M n).apply_symm_apply x))

/-- Every section on the intermediate open acts compatibly with ambient restriction. -/
lemma moduleOpenRestriction_image_smul (M : S.Modules) (n : ℕ)
    (r : Γ(U.toScheme, ⊤)) (x : ModuleH (M.restrict U.ι) n) :
    moduleOpenRestriction M (homOfLE (openImage_le U V)) n (r • x) =
      (S.homOfLE (openImage_le U V)).appTop r •
        moduleOpenRestriction M (homOfLE (openImage_le U V)) n x := by
  apply (nestedModuleHEquiv U V M n).injective
  rw [moduleOpenRestriction_nested, globalOpenRestriction_smul,
    nestedModuleHEquiv_smul, moduleOpenRestriction_nested]
  have h : (U.ι.isoImage V).hom ≫ S.homOfLE (openImage_le U V) = V.ι := by
    rw [← cancel_mono U.ι]
    simp only [Category.assoc, Scheme.homOfLE_ι, Scheme.Hom.isoImage_hom_ι]
  have hs := congrArg (fun f ↦ (Scheme.Hom.appTop f) r) h
  rw [Scheme.Hom.comp_appTop, ConcreteCategory.comp_apply] at hs
  exact congrArg (fun a : Γ(V.toScheme, ⊤) ↦
    a • moduleGlobalRestriction V (M.restrict U.ι) n x) hs.symm
/-- Semilinearity holds for arbitrary inclusions and all local scalar sections. -/
lemma moduleOpenRestriction_smul (M : S.Modules) {W U : S.Opens} (i : W ⟶ U)
    (n : ℕ) (r : Γ(U.toScheme, ⊤)) (x : ModuleH (M.restrict U.ι) n) :
    moduleOpenRestriction M i n (r • x) =
      (S.homOfLE (leOfHom i)).appTop r • moduleOpenRestriction M i n x := by
  have h : U.ι ''ᵁ (U.ι ⁻¹ᵁ W) = W := by
    simpa [Scheme.Hom.image_preimage_eq_opensRange_inf] using
      inf_eq_right.mpr (leOfHom i)
  obtain ⟨V, rfl⟩ : ∃ V : U.toScheme.Opens, U.ι ''ᵁ V = W := ⟨_, h⟩
  exact moduleOpenRestriction_image_smul U V M n r x
/-- Restriction as a semilinear map between actual module cohomology groups. -/
def moduleOpenRestrictionLinear (M : S.Modules) {W U : S.Opens} (i : W ⟶ U) (n : ℕ) :
    ModuleH (M.restrict U.ι) n →ₛₗ[(S.homOfLE (leOfHom i)).appTop.hom]
      ModuleH (M.restrict W.ι) n where
  toAddHom := (moduleOpenRestriction M i n).toAddHom
  map_smul' := moduleOpenRestriction_smul M i n

@[simp]
lemma moduleOpenRestriction_id (M : S.Modules) (U : S.Opens) (n : ℕ)
    (x : ModuleH (M.restrict U.ι) n) : moduleOpenRestriction M (𝟙 U) n x = x := by
  simp [moduleOpenRestriction]

lemma moduleOpenRestriction_comp (M : S.Modules) {U V W : S.Opens}
    (i : V ⟶ U) (j : W ⟶ V) (n : ℕ) (x : ModuleH (M.restrict U.ι) n) :
    moduleOpenRestriction M (j ≫ i) n x =
      moduleOpenRestriction M j n (moduleOpenRestriction M i n x) := by
  simp [moduleOpenRestriction, Functor.map_comp]
/-- Restrict scalars along any ring map into the intermediate global-section ring. -/
def moduleOpenRestrictionRing {R : Type v} [Ring R] (M : S.Modules)
    {W U : S.Opens} (i : W ⟶ U) (ρ : R →+* Γ(U.toScheme, ⊤)) (n : ℕ) :
    letI := Module.compHom (ModuleH (M.restrict U.ι) n) ρ
    letI := Module.compHom (ModuleH (M.restrict W.ι) n)
      ((S.homOfLE (leOfHom i)).appTop.hom.comp ρ)
    ModuleH (M.restrict U.ι) n →ₗ[R] ModuleH (M.restrict W.ι) n := by
  letI := Module.compHom (ModuleH (M.restrict U.ι) n) ρ
  letI := Module.compHom (ModuleH (M.restrict W.ι) n)
    ((S.homOfLE (leOfHom i)).appTop.hom.comp ρ)
  exact { toAddHom := (moduleOpenRestriction M i n).toAddHom
          map_smul' := fun r x ↦ moduleOpenRestriction_smul M i n (ρ r) x }

/-- The same map in the existing ring-cohomology functor's codomain. -/
def moduleOpenRestrictionRingHom {R : Type u} [CommRing R] (M : S.Modules)
    {W U : S.Opens} (i : W ⟶ U) (ρ : R →+* Γ(U.toScheme, ⊤)) (n : ℕ) :
    (moduleRingHFunctor ρ n).obj (M.restrict U.ι) ⟶
      (moduleRingHFunctor ((S.homOfLE (leOfHom i)).appTop.hom.comp ρ) n).obj
        (M.restrict W.ι) :=
  ModuleCat.ofHom (moduleOpenRestrictionRing M i ρ n)

/-- The restriction map for the existing cohomology with field scalars. -/
def moduleOpenRestrictionScalar {k : Type u} [Field k] (M : S.Modules)
    {W U : S.Opens} (i : W ⟶ U) (g : U.toScheme ⟶ Spec (CommRingCat.of k)) (n : ℕ) :
    ModuleScalarH g (M.restrict U.ι) n →ₗ[k]
      ModuleScalarH (S.homOfLE (leOfHom i) ≫ g) (M.restrict W.ι) n where
  toAddHom := (moduleOpenRestriction M i n).toAddHom
  map_smul' r x := by
    change ModuleH (M.restrict U.ι) n at x
    have h : structureScalarMap (S.homOfLE (leOfHom i) ≫ g) r =
        (S.homOfLE (leOfHom i)).appTop (structureScalarMap g r) := by
      simp [structureScalarMap]
    change moduleOpenRestriction M i n (structureScalarMap g r • x) =
      structureScalarMap (S.homOfLE (leOfHom i) ≫ g) r • moduleOpenRestriction M i n x
    rw [h]
    exact moduleOpenRestriction_smul M i n (structureScalarMap g r) x

end FLT.Mazur.FCurve
