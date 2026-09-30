/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.HigherDirectImageOpenSheafification

/-!
# Relative composition of acyclic direct images

An acyclic module resolution constructs composition for actual module higher
images. Independently, the open comparison sheafifies to a natural comparison
of actual abelian higher images and retains the local scalar comparison.
Forgetting is compatible with the canonical map from the exact resolution;
identifying the two endpoint comparisons is a separate coherence statement.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxSynthPendingDepth 1

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite AlgebraicGeometry

universe u

namespace FLT.Mazur.RelativeDirectImageComposition

open HigherDirectImagePresheaf HigherDirectImageOpenSheafification
open OpenDirectImageCohomology
open AbsoluteDirectImageCohomology (Acyclic)

local instance sheafHasExt (T : TopCat.{u}) :
    HasExt.{u + 1} (Sheaf (Opens.grothendieckTopology T) AddCommGrpCat.{u}) := HasExt.standard _

local instance topSheafHasExt (T : TopCat.{u}) :
    HasExt.{u + 1} (TopCat.Sheaf AddCommGrpCat.{u} T) := HasExt.standard _

variable {X Y Z : TopCat.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
  (F : TopCat.Sheaf AddCommGrpCat.{u} X) (hF : Acyclic f F)

/-- Evaluate the acyclic open comparison on each inverse image of a base open. -/
def valueEquiv (U : Opens Z) (n : ℕ) :
    (openPresheaf g ((directImage f).obj F) n).obj (op U) ≃+
      (openPresheaf (f ≫ g) F n).obj (op U) :=
  (openValueEquiv g ((directImage f).obj F) U n).trans
    ((cohomologyEquiv f F hF ((Opens.map g).obj U) n).trans
      (openValueEquiv (f ≫ g) F U n).symm)

/-- Decoding the small comparison recovers the original open Ext comparison. -/
lemma valueEquiv_decode (U : Opens Z) (n : ℕ)
    (x : (openPresheaf g ((directImage f).obj F) n).obj (op U)) :
    openValueEquiv (f ≫ g) F U n (valueEquiv f g F hF U n x) =
      cohomologyEquiv f F hF ((Opens.map g).obj U) n
        (openValueEquiv g ((directImage f).obj F) U n x) := by
  exact (openValueEquiv (f ≫ g) F U n).apply_symm_apply _

/-- The small comparison commutes with restriction of base opens. -/
lemma valueEquiv_restrict {V U : Opens Z} (i : V ⟶ U) (n : ℕ)
    (x : (openPresheaf g ((directImage f).obj F) n).obj (op U)) :
    valueEquiv f g F hF V n ((openPresheaf g _ n).map i.op x) =
      (openPresheaf (f ≫ g) F n).map i.op (valueEquiv f g F hF U n x) := by
  apply (openValueEquiv (f ≫ g) F V n).injective
  exact (valueEquiv_decode f g F hF V n _).trans
    ((congrArg (cohomologyEquiv f F hF ((Opens.map g).obj V) n)
      (openValueEquiv_restrict g ((directImage f).obj F) i n x)).trans
    ((OpenDirectImageNaturality.cohomologyEquiv_restrict f F hF
      ((Opens.map g).map i) n (openValueEquiv g _ U n x)).trans
    ((congrArg ((F.cohomologyPresheaf n).map ((Opens.map (f ≫ g)).map i).op)
      (valueEquiv_decode f g F hF U n x).symm).trans
        (openValueEquiv_restrict (f ≫ g) F i n _).symm)))

/-- The pulled-back open comparisons form a small presheaf isomorphism. -/
def presheafIso (n : ℕ) :
    openPresheaf g ((directImage f).obj F) n ≅ openPresheaf (f ≫ g) F n :=
  NatIso.ofComponents (fun U ↦ (valueEquiv f g F hF U.unop n).toAddCommGrpIso)
    (fun i ↦ by ext x; exact valueEquiv_restrict f g F hF i.unop n x)

private lemma openPresheafMap_decode {X Y : TopCat.{u}} (f : X ⟶ Y)
    {F G : TopCat.Sheaf AddCommGrpCat.{u} X} (a : F ⟶ G) (U : Opens Y) (n : ℕ)
    (x : (openPresheaf f F n).obj (op U)) :
    openValueEquiv f G U n ((openPresheafMap f a n).app (op U) x) =
      ((Sheaf.cohomologyPresheafFunctor (Opens.grothendieckTopology X) n).map a).app
        (op ((Opens.map f).obj U)) (openValueEquiv f F U n x) :=
  (openValueEquiv f G U n).apply_symm_apply _

/-- The small value comparison commutes with coefficient maps. -/
lemma valueEquiv_naturality {F G : TopCat.Sheaf AddCommGrpCat.{u} X}
    (a : F ⟶ G) (hF : Acyclic f F) (hG : Acyclic f G) (U : Opens Z) (n : ℕ)
    (x : (openPresheaf g ((directImage f).obj F) n).obj (op U)) :
    valueEquiv f g G hG U n ((openPresheafMap g ((directImage f).map a) n).app (op U) x) =
      (openPresheafMap (f ≫ g) a n).app (op U) (valueEquiv f g F hF U n x) := by
  apply (openValueEquiv (f ≫ g) G U n).injective
  exact (valueEquiv_decode f g G hG U n _).trans
    ((congrArg (cohomologyEquiv f G hG ((Opens.map g).obj U) n)
      (openPresheafMap_decode g ((directImage f).map a) U n x)).trans
    ((cohomologyEquiv_naturality f a hF hG ((Opens.map g).obj U) n
      (openValueEquiv g _ U n x)).trans
    ((congrArg (((Sheaf.cohomologyPresheafFunctor (Opens.grothendieckTopology X) n).map a).app
      (op ((Opens.map (f ≫ g)).obj U))) (valueEquiv_decode f g F hF U n x).symm).trans
        (openPresheafMap_decode (f ≫ g) a U n _).symm)))

/-- The presheaf comparison is natural for maps of acyclic coefficients. -/
@[reassoc]
lemma presheafIso_naturality {F G : TopCat.Sheaf AddCommGrpCat.{u} X}
    (a : F ⟶ G) (hF : Acyclic f F) (hG : Acyclic f G) (n : ℕ) :
    openPresheafMap g ((directImage f).map a) n ≫ (presheafIso f g G hG n).hom =
      (presheafIso f g F hF n).hom ≫ openPresheafMap (f ≫ g) a n := by
  ext U x
  exact valueEquiv_naturality f g a hF hG U.unop n x

/-- Sheafify the open comparison and identify both actual higher direct images. -/
def abelianIso (n : ℕ) :
    ((directImage g).rightDerived n).obj ((directImage f).obj F) ≅
      ((directImage (f ≫ g)).rightDerived n).obj F :=
  openComparison g (injectiveResolution ((directImage f).obj F)) n ≪≫
    (presheafToSheaf (Opens.grothendieckTopology Z) AddCommGrpCat.{u}).mapIso
      (presheafIso f g F hF n) ≪≫
    (openComparison (f ≫ g) (injectiveResolution F) n).symm

/-- The sheafified comparison retains coefficient naturality. -/
@[reassoc]
lemma abelianIso_naturality {F G : TopCat.Sheaf AddCommGrpCat.{u} X}
    (a : F ⟶ G) (hF : Acyclic f F) (hG : Acyclic f G) (n : ℕ) :
    ((directImage g).rightDerived n).map ((directImage f).map a) ≫
        (abelianIso f g G hG n).hom =
      (abelianIso f g F hF n).hom ≫ ((directImage (f ≫ g)).rightDerived n).map a := by
  let φ : (injectiveResolution F).Hom (injectiveResolution G) a :=
    ⟨InjectiveResolution.desc a _ _, InjectiveResolution.desc_commutes_zero a _ _⟩
  let ψ : (injectiveResolution ((directImage f).obj F)).Hom
      (injectiveResolution ((directImage f).obj G)) ((directImage f).map a) :=
    ⟨InjectiveResolution.desc _ _ _, InjectiveResolution.desc_commutes_zero _ _ _⟩
  rw [← cancel_mono (openComparison (f ≫ g) (injectiveResolution G) n).hom]
  simp only [abelianIso, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, Category.assoc,
    Iso.inv_hom_id, Category.comp_id]
  rw [openComparison_naturality_assoc g ψ n, openComparison_naturality (f ≫ g) φ n]
  simp only [Iso.inv_hom_id_assoc, ← Functor.map_comp]
  exact congrArg (fun k ↦ (openComparison g (injectiveResolution ((directImage f).obj F)) n).hom ≫
    (presheafToSheaf (Opens.grothendieckTopology Z) AddCommGrpCat.{u}).map k)
      (presheafIso_naturality f g a hF hG n)

open FCurve CoherentDevissage

variable {S T B : Scheme.{u}} (f : S ⟶ T) (g : T ⟶ B)
  (M : S.Modules) (hM : ModulePushforwardAcyclic f M)

/-- Actual module higher images have the sheafified comparison after forgetting scalars. -/
def forgottenIso (n : ℕ) :
    (moduleToSheaf B).obj (((Scheme.Modules.pushforward g).rightDerived n).obj
      ((Scheme.Modules.pushforward f).obj M)) ≅
    (moduleToSheaf B).obj (((Scheme.Modules.pushforward (f ≫ g)).rightDerived n).obj M) :=
  ModuleDerivedAbelianComparison.comparisonObj g _ n ≪≫
    abelianIso f.base g.base (moduleAbelianSheaf M)
      (modulePushforwardAcyclic_abelian f M hM) n ≪≫
    (ModuleDerivedAbelianComparison.comparisonObj (f ≫ g) M n).symm

/-- The comparison of forgotten module images is natural in acyclic coefficients. -/
@[reassoc]
lemma forgottenIso_naturality {M N : S.Modules} (a : M ⟶ N)
    (hM : ModulePushforwardAcyclic f M) (hN : ModulePushforwardAcyclic f N) (n : ℕ) :
    (moduleToSheaf B).map (((Scheme.Modules.pushforward g).rightDerived n).map
        ((Scheme.Modules.pushforward f).map a)) ≫ (forgottenIso f g N hN n).hom =
      (forgottenIso f g M hM n).hom ≫
        (moduleToSheaf B).map (((Scheme.Modules.pushforward (f ≫ g)).rightDerived n).map a) := by
  rw [← cancel_mono (ModuleDerivedAbelianComparison.comparisonObj (f ≫ g) N n).hom]
  simp only [forgottenIso, Iso.trans_hom, Iso.symm_hom, Category.assoc,
    Iso.inv_hom_id, Category.comp_id]
  rw [ModuleDerivedAbelianComparison.comparisonObj_naturality_assoc,
    ModuleDerivedAbelianComparison.comparisonObj_naturality]
  simp only [Iso.inv_hom_id_assoc]
  exact congrArg ((ModuleDerivedAbelianComparison.comparisonObj g
    ((Scheme.Modules.pushforward f).obj M) n).hom ≫ ·)
      (abelianIso_naturality f.base g.base ((moduleToSheaf S).map a)
        (modulePushforwardAcyclic_abelian f M hM) (modulePushforwardAcyclic_abelian f N hN) n)

/-- Before sheafification, the comparison is exactly the established local linear map. -/
lemma valueEquiv_module (U : B.Opens) (n : ℕ)
    (x : (openPresheaf g.base (moduleAbelianSheaf ((Scheme.Modules.pushforward f).obj M))
      n).obj (op U)) :
    moduleValueEquiv (f ≫ g) M U n
      (valueEquiv f.base g.base (moduleAbelianSheaf M)
        (modulePushforwardAcyclic_abelian f M hM) U n x) =
      openAcyclicPushforwardModuleHEquiv f (g ⁻¹ᵁ U) M hM n
        (moduleValueEquiv g ((Scheme.Modules.pushforward f).obj M) U n x) := by
  change moduleOpenHEquiv _ M n
    (openValueEquiv _ _ U n (valueEquiv _ _ _ _ U n x)) = _
  rw [valueEquiv_decode]
  exact (openAcyclicPushforwardModuleHEquiv_eq f (g ⁻¹ᵁ U) M hM n
    (openValueEquiv g.base (moduleAbelianSheaf ((Scheme.Modules.pushforward f).obj M))
      U n x)).symm

/-- After decoding, the open comparison respects every intermediate local scalar. -/
lemma valueEquiv_smul (U : B.Opens) (n : ℕ) (r : Γ((g ⁻¹ᵁ U).toScheme, ⊤))
    (x : ModuleH (((Scheme.Modules.pushforward f).obj M).restrict (g ⁻¹ᵁ U).ι) n) :
    moduleValueEquiv (f ≫ g) M U n
      (valueEquiv f.base g.base (moduleAbelianSheaf M)
        (modulePushforwardAcyclic_abelian f M hM) U n
          ((moduleValueEquiv g ((Scheme.Modules.pushforward f).obj M) U n).symm (r • x))) =
      (f ∣_ (g ⁻¹ᵁ U)).appTop r • moduleValueEquiv (f ≫ g) M U n
        (valueEquiv f.base g.base (moduleAbelianSheaf M)
          (modulePushforwardAcyclic_abelian f M hM) U n
            ((moduleValueEquiv g ((Scheme.Modules.pushforward f).obj M) U n).symm x)) := by
  rw [valueEquiv_module, valueEquiv_module, AddEquiv.apply_symm_apply,
    AddEquiv.apply_symm_apply]
  exact (openAcyclicPushforwardModuleHEquiv f (g ⁻¹ᵁ U) M hM n).map_smul r x

open AcyclicResolutionComparison HomologicalComplex
open ModuleDerivedAbelianComparison (abelianPushforward)

/-- The pushed module resolution is exact by the original acyclicity hypothesis. -/
def moduleResolution : ExactResolution ((Scheme.Modules.pushforward f).obj M) where
  cocomplex := AcyclicDirectImageResolution.imageComplex (Scheme.Modules.pushforward f)
    (injectiveResolution M)
  ι := AcyclicDirectImageResolution.augmentation (Scheme.Modules.pushforward f)
    (injectiveResolution M)
  quasiIso := AcyclicDirectImageResolution.augmentation_quasiIso
    (Scheme.Modules.pushforward f) (injectiveResolution M) hM

/-- Its terms are acyclic for every subsequent direct image, by flasqueness. -/
lemma moduleResolution_acyclic : IsAcyclic (moduleResolution f M hM)
    (Scheme.Modules.pushforward g) := by
  intro n q
  apply ModuleDerivedAbelianComparison.isZero_module_of_abelian
  let I := injectiveResolution M
  have : TopCat.Sheaf.IsFlasque (moduleAbelianSheaf (I.cocomplex.X n)) :=
    ModuleInjectiveFlasque.isFlasque_toSheaf _
  have : TopCat.Sheaf.IsFlasque
      ((directImage f.base).obj (moduleAbelianSheaf (I.cocomplex.X n))) :=
    TopCat.Sheaf.IsFlasque.pushforward_isFlasque (moduleAbelianSheaf (I.cocomplex.X n)) f.base
  exact FlasqueDirectImageAcyclic.isZero_rightDerived_obj g.base
    ((directImage f.base).obj (moduleAbelianSheaf (I.cocomplex.X n))) q

/-- The two module image complexes are identified by the actual pushforward composition. -/
def moduleComplexIso :
    ((Scheme.Modules.pushforward g).mapHomologicalComplex _).obj
        (moduleResolution f M hM).cocomplex ≅
      ((Scheme.Modules.pushforward (f ≫ g)).mapHomologicalComplex _).obj
        (injectiveResolution M).cocomplex :=
  (Functor.mapHomologicalComplexCompIso (Scheme.Modules.pushforwardComp f g)
    (ComplexShape.up ℕ)).app (injectiveResolution M).cocomplex

/-- Relative composition for actual module higher images, with no vanishing input on `g`. -/
def moduleIso (n : ℕ) :
    ((Scheme.Modules.pushforward g).rightDerived n).obj ((Scheme.Modules.pushforward f).obj M) ≅
      ((Scheme.Modules.pushforward (f ≫ g)).rightDerived n).obj M :=
  isoRightDerivedObj (moduleResolution f M hM) (Scheme.Modules.pushforward g)
    (moduleResolution_acyclic f g M hM) n ≪≫
    (homologyFunctor _ (ComplexShape.up ℕ) n).mapIso (moduleComplexIso f g M hM) ≪≫
    ((injectiveResolution M).isoRightDerivedObj (Scheme.Modules.pushforward (f ≫ g)) n).symm

/-- Coefficient maps induce maps of the pushed exact module resolutions. -/
def moduleResolutionMap {M N : S.Modules} (a : M ⟶ N)
    (hM : ModulePushforwardAcyclic f M) (hN : ModulePushforwardAcyclic f N) :
    (moduleResolution f M hM).cocomplex ⟶ (moduleResolution f N hN).cocomplex :=
  ((Scheme.Modules.pushforward f).mapHomologicalComplex _).map
    (InjectiveResolution.desc a (injectiveResolution N) (injectiveResolution M))

/-- The pushed resolution map respects the actual module augmentation. -/
lemma moduleResolutionMap_comm {M N : S.Modules} (a : M ⟶ N)
    (hM : ModulePushforwardAcyclic f M) (hN : ModulePushforwardAcyclic f N) :
    (moduleResolution f M hM).ι ≫ moduleResolutionMap f a hM hN =
      (CochainComplex.single₀ _).map ((Scheme.Modules.pushforward f).map a) ≫
        (moduleResolution f N hN).ι := by
  apply HomologicalComplex.from_single_hom_ext
  change (Scheme.Modules.pushforward f).map ((injectiveResolution M).ι.f 0) ≫
    (Scheme.Modules.pushforward f).map (InjectiveResolution.desc a _ _ |>.f 0) =
    (Scheme.Modules.pushforward f).map a ≫
      (Scheme.Modules.pushforward f).map ((injectiveResolution N).ι.f 0)
  rw [← Functor.map_comp, ← Functor.map_comp, InjectiveResolution.desc_commutes_zero]

/-- The module comparison is natural for every map between acyclic coefficients. -/
@[reassoc]
lemma moduleIso_naturality {M N : S.Modules} (a : M ⟶ N)
    (hM : ModulePushforwardAcyclic f M) (hN : ModulePushforwardAcyclic f N) (n : ℕ) :
    ((Scheme.Modules.pushforward g).rightDerived n).map ((Scheme.Modules.pushforward f).map a) ≫
      (moduleIso f g N hN n).hom =
    (moduleIso f g M hM n).hom ≫
      ((Scheme.Modules.pushforward (f ≫ g)).rightDerived n).map a := by
  let φ := InjectiveResolution.desc a (injectiveResolution N) (injectiveResolution M)
  have h := congrArg (fun k ↦ (homologyFunctor _ (ComplexShape.up ℕ) n).map k)
    ((Functor.mapHomologicalComplexCompIso (Scheme.Modules.pushforwardComp f g)
      (ComplexShape.up ℕ)).hom.naturality φ)
  dsimp only [moduleIso, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom]
  rw [isoRightDerivedObj_naturality_assoc (moduleResolution f M hM)
    (Scheme.Modules.pushforward g) (moduleResolution_acyclic f g M hM)
    (moduleResolution f N hN) (moduleResolution_acyclic f g N hN)
    ((Scheme.Modules.pushforward f).map a) (moduleResolutionMap f a hM hN)
    (moduleResolutionMap_comm f a hM hN) n]
  simp only [Category.assoc]
  rw [(injectiveResolution M).isoRightDerivedObj_inv_naturality a
    (injectiveResolution N) φ (InjectiveResolution.desc_commutes_zero a _ _)
    (Scheme.Modules.pushforward (f ≫ g)) n]
  simp only [Functor.map_comp] at h
  simpa only [Category.assoc, Functor.comp_map, homologyFunctor_map, moduleComplexIso,
    moduleResolutionMap, Iso.app_hom] using congrArg
    (fun k ↦ (isoRightDerivedObj (moduleResolution f M hM) (Scheme.Modules.pushforward g)
      (moduleResolution_acyclic f g M hM) n).hom ≫ k ≫
        ((injectiveResolution N).isoRightDerivedObj (Scheme.Modules.pushforward (f ≫ g)) n).inv) h

/-- Forget the action on the exact pushed module resolution. -/
def forgottenResolution :
    ExactResolution ((moduleToSheaf T).obj ((Scheme.Modules.pushforward f).obj M)) where
  cocomplex := ((moduleToSheaf T).mapHomologicalComplex _).obj (moduleResolution f M hM).cocomplex
  ι := (singleMapHomologicalComplex (moduleToSheaf T) (ComplexShape.up ℕ) 0).inv.app _ ≫
    ((moduleToSheaf T).mapHomologicalComplex _).map (moduleResolution f M hM).ι
  quasiIso := by
    have : QuasiIso (((moduleToSheaf T).mapHomologicalComplex _).map
        (moduleResolution f M hM).ι) :=
      quasiIso_map_of_preservesHomology (moduleResolution f M hM).ι (moduleToSheaf T)
    infer_instance

/-- The comparison with the chosen target module resolution, after forgetting. -/
def forgottenResolutionMap : (forgottenResolution f M hM).cocomplex ⟶
    (ModuleDerivedAbelianComparison.underlyingResolution
      ((Scheme.Modules.pushforward f).obj M)).cocomplex :=
  ((moduleToSheaf T).mapHomologicalComplex _).map
    (ExactResolution.desc (𝟙 _) (injectiveResolution _) (moduleResolution f M hM))

/-- This comparison preserves the forgotten augmentation. -/
lemma forgottenResolutionMap_comm :
    (forgottenResolution f M hM).ι ≫ forgottenResolutionMap f M hM =
      (ModuleDerivedAbelianComparison.underlyingResolution
        ((Scheme.Modules.pushforward f).obj M)).ι := by
  dsimp only [forgottenResolution, forgottenResolutionMap,
    ModuleDerivedAbelianComparison.underlyingResolution]
  rw [Category.assoc, ← Functor.map_comp, ExactResolution.desc_commutes]
  simp

/-- Exact forgetting commutes with computing homology on the pushed resolution. -/
def forgottenHomologyIso (n : ℕ) :
    (moduleToSheaf B).obj
      ((((Scheme.Modules.pushforward g).mapHomologicalComplex _).obj
        (moduleResolution f M hM).cocomplex).homology n) ≅
    (((abelianPushforward g).mapHomologicalComplex _).obj
      (forgottenResolution f M hM).cocomplex).homology n :=
  (((((Scheme.Modules.pushforward g).mapHomologicalComplex _).obj
    (moduleResolution f M hM).cocomplex).sc n).mapHomologyIso (moduleToSheaf B)).symm

private lemma forget_push_map {A N : T.Modules} (a : A ⟶ N) :
    (moduleToSheaf B).map ((Scheme.Modules.pushforward g).map a) =
      (abelianPushforward g).map ((moduleToSheaf T).map a) := rfl

set_option maxHeartbeats 800000 in
-- As in moduleComputation_naturality, elaboration compares module and sheaf homology.
/-- Forgetting the canonical acyclic-resolution map gives the abelian resolution map. -/
lemma toRightDerived_forget (n : ℕ) :
    (moduleToSheaf B).map ((moduleResolution f M hM).toRightDerived
        (Scheme.Modules.pushforward g) n) ≫
      (ModuleDerivedAbelianComparison.comparisonObj g
        ((Scheme.Modules.pushforward f).obj M) n).hom =
    (forgottenHomologyIso f g M hM n).hom ≫
      (forgottenResolution f M hM).toRightDerived (abelianPushforward g) n := by
  let P := moduleResolution f M hM
  let N := (Scheme.Modules.pushforward f).obj M
  let J := injectiveResolution N
  let φ := ExactResolution.desc (𝟙 N) J P
  have h := ShortComplex.mapHomologyIso_inv_naturality
    ((shortComplexFunctor _ (ComplexShape.up ℕ) n).map
      (((Scheme.Modules.pushforward g).mapHomologicalComplex _).map φ)) (moduleToSheaf B)
  have ht := (forgottenResolution f M hM).toRightDerived_naturality (abelianPushforward g)
    (ModuleDerivedAbelianComparison.underlyingResolution N) (𝟙 _)
    (forgottenResolutionMap f M hM)
    (by simpa using forgottenResolutionMap_comm f M hM) n
  have ht' := ht.trans ((congrArg
    ((forgottenResolution f M hM).toRightDerived (abelianPushforward g) n ≫ ·)
    (((abelianPushforward g).rightDerived n).map_id _)).trans (Category.comp_id _))
  change (moduleToSheaf B).map
      (homologyMap (((Scheme.Modules.pushforward g).mapHomologicalComplex _).map φ) n ≫
        (J.isoRightDerivedObj (Scheme.Modules.pushforward g) n).inv) ≫
    ((moduleToSheaf B).map (J.isoRightDerivedObj (Scheme.Modules.pushforward g) n).hom ≫
      _) ≫ _ = _
  rw [Functor.map_comp]
  simp only [Category.assoc, ← Functor.map_comp_assoc, Iso.inv_hom_id]
  change (moduleToSheaf B).map
      (homologyMap (((Scheme.Modules.pushforward g).mapHomologicalComplex _).map φ) n) ≫
    _ ≫ (ModuleDerivedAbelianComparison.underlyingResolution N).toRightDerived
      (abelianPushforward g) n = _
  rw [← Category.assoc]
  refine (congrArg (· ≫ (ModuleDerivedAbelianComparison.underlyingResolution N).toRightDerived
    (abelianPushforward g) n) h).trans ?_
  simpa only [Category.assoc, forgottenHomologyIso, Iso.symm_hom,
    ExactResolution.imageHomology, Functor.comp_map, homologyFunctor_map,
    forgottenResolutionMap, homologyMap, homology, shortComplexFunctor,
    shortComplexFunctor', Functor.mapShortComplex, Functor.mapHomologicalComplex,
    sc, P, N, J, φ, ← forget_push_map] using
    congrArg ((forgottenHomologyIso f g M hM n).hom ≫ ·) ht'

end FLT.Mazur.RelativeDirectImageComposition
