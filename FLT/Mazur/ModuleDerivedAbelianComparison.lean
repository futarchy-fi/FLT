/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AcyclicResolutionComparison
public import FLT.Mazur.FlasqueDirectImageAcyclic
public import FLT.Mazur.ModuleStalkExact

/-!
# Module and abelian higher direct images

The underlying complex of the chosen module injective resolution is exact and
its terms are acyclic for abelian direct image. Computing on that complex
identifies the underlying module higher direct images with abelian higher direct
images, naturally in the coefficient module.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry HomologicalComplex
open FLT.Mazur.AcyclicResolutionComparison
open FLT.Mazur.FCurve.CoherentDevissage

universe u

namespace FLT.Mazur.ModuleDerivedAbelianComparison

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- The actual direct image of abelian sheaves. -/
abbrev abelianPushforward := TopCat.Sheaf.pushforward AddCommGrpCat.{u} f.base

/-- Forgetting the module action commutes with actual pushforward. -/
def pushforwardForgetIso :
    Scheme.Modules.pushforward f ⋙ moduleToSheaf Y ≅
      moduleToSheaf X ⋙ abelianPushforward f :=
  NatIso.ofComponents (fun _ => Iso.refl _)

variable (M : X.Modules)

/-- The exact augmented abelian complex underlying the chosen module resolution. -/
def underlyingResolution : ExactResolution ((moduleToSheaf X).obj M) where
  cocomplex := ((moduleToSheaf X).mapHomologicalComplex _).obj
    (injectiveResolution M).cocomplex
  ι := (singleMapHomologicalComplex (moduleToSheaf X) (ComplexShape.up ℕ) 0).inv.app M ≫
    ((moduleToSheaf X).mapHomologicalComplex _).map (injectiveResolution M).ι
  quasiIso := inferInstance

/-- Every term is direct-image acyclic, by injective-module flasqueness. -/
lemma underlyingResolution_acyclic :
    IsAcyclic (underlyingResolution M) (abelianPushforward f) :=
  fun n q => FlasqueDirectImageAcyclic.isZero_rightDerived_toSheaf f.base
    ((injectiveResolution M).cocomplex.X n) q

/-- The two degreewise images of the module resolution agree. -/
def imageComplexIso :
    ((moduleToSheaf Y).mapHomologicalComplex _).obj
      (((Scheme.Modules.pushforward f).mapHomologicalComplex _).obj
        (injectiveResolution M).cocomplex) ≅
      ((abelianPushforward f).mapHomologicalComplex _).obj
        (underlyingResolution M).cocomplex :=
  Iso.refl _

/-- Compute the underlying module-derived object on the common image complex. -/
def moduleComputation (n : ℕ) :
    (moduleToSheaf Y).obj (((Scheme.Modules.pushforward f).rightDerived n).obj M) ≅
      (((abelianPushforward f).mapHomologicalComplex _).obj
        (underlyingResolution M).cocomplex).homology n :=
  (moduleToSheaf Y).mapIso
    ((injectiveResolution M).isoRightDerivedObj (Scheme.Modules.pushforward f) n) ≪≫
    (((((Scheme.Modules.pushforward f).mapHomologicalComplex _).obj
      (injectiveResolution M).cocomplex).sc n).mapHomologyIso (moduleToSheaf Y)).symm

/-- The objectwise comparison, with both resolving complexes chosen internally. -/
def comparisonObj (n : ℕ) :
    (moduleToSheaf Y).obj (((Scheme.Modules.pushforward f).rightDerived n).obj M) ≅
      ((abelianPushforward f).rightDerived n).obj ((moduleToSheaf X).obj M) :=
  moduleComputation f M n ≪≫
    (isoRightDerivedObj (underlyingResolution M) (abelianPushforward f)
      (underlyingResolution_acyclic f M) n).symm

variable {M} {N : X.Modules}

/-- Forget the action on a comparison between the chosen module resolutions. -/
def underlyingResolutionMap (g : M ⟶ N) :
    (underlyingResolution M).cocomplex ⟶ (underlyingResolution N).cocomplex :=
  ((moduleToSheaf X).mapHomologicalComplex _).map
    (InjectiveResolution.desc g (injectiveResolution N) (injectiveResolution M))

/-- The constructed comparison respects the augmentation. -/
lemma underlyingResolutionMap_comm (g : M ⟶ N) :
    (underlyingResolution M).ι ≫ underlyingResolutionMap g =
      (CochainComplex.single₀ _).map ((moduleToSheaf X).map g) ≫
        (underlyingResolution N).ι := by
  dsimp only [underlyingResolution, underlyingResolutionMap]
  rw [Category.assoc, ← Functor.map_comp, InjectiveResolution.desc_commutes, Functor.map_comp,
    ← Category.assoc]
  have h := (singleMapHomologicalComplex (moduleToSheaf X)
    (ComplexShape.up ℕ) 0).inv.naturality g
  dsimp only [Functor.comp_map] at h
  rw [← h, Category.assoc]

set_option maxHeartbeats 800000 in
-- Elaborating naturality unfolds both module and sheaf homology along the forgetful functor.
/-- Exact forgetting commutes with the injective-resolution computation naturally. -/
@[reassoc]
lemma moduleComputation_naturality (g : M ⟶ N) (n : ℕ) :
    (moduleToSheaf Y).map (((Scheme.Modules.pushforward f).rightDerived n).map g) ≫
        (moduleComputation f N n).hom =
      (moduleComputation f M n).hom ≫
        homologyMap (((abelianPushforward f).mapHomologicalComplex _).map
          (underlyingResolutionMap g)) n := by
  let φ := InjectiveResolution.desc g (injectiveResolution N) (injectiveResolution M)
  have h := (injectiveResolution M).isoRightDerivedObj_hom_naturality g
    (injectiveResolution N) φ (InjectiveResolution.desc_commutes_zero _ _ _)
    (Scheme.Modules.pushforward f) n
  dsimp only [moduleComputation, Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom]
  rw [← (moduleToSheaf Y).map_comp_assoc, h, Functor.map_comp, Category.assoc]
  exact congrArg ((moduleToSheaf Y).map
    ((injectiveResolution M).isoRightDerivedObj (Scheme.Modules.pushforward f) n).hom ≫ ·)
    (ShortComplex.mapHomologyIso_inv_naturality
      ((shortComplexFunctor _ (ComplexShape.up ℕ) n).map
        (((Scheme.Modules.pushforward f).mapHomologicalComplex _).map φ)) (moduleToSheaf Y))

/-- Coefficient naturality of the comparison on actual higher direct images. -/
@[reassoc]
lemma comparisonObj_naturality (g : M ⟶ N) (n : ℕ) :
    (moduleToSheaf Y).map (((Scheme.Modules.pushforward f).rightDerived n).map g) ≫
        (comparisonObj f N n).hom =
      (comparisonObj f M n).hom ≫
        ((abelianPushforward f).rightDerived n).map ((moduleToSheaf X).map g) := by
  dsimp only [comparisonObj, Iso.trans_hom, Iso.symm_hom]
  rw [moduleComputation_naturality_assoc]
  exact congrArg ((moduleComputation f M n).hom ≫ ·)
    ((underlyingResolution M).toRightDerived_naturality (abelianPushforward f)
      (underlyingResolution N) ((moduleToSheaf X).map g) (underlyingResolutionMap g)
      (underlyingResolutionMap_comm g) n)

/-- Module higher direct images forget to the abelian higher direct images. -/
def comparison (n : ℕ) :
    (Scheme.Modules.pushforward f).rightDerived n ⋙ moduleToSheaf Y ≅
      moduleToSheaf X ⋙ (abelianPushforward f).rightDerived n :=
  NatIso.ofComponents (fun M => comparisonObj f M n) (fun g => comparisonObj_naturality f g n)

/-- Positive module-derived vanishing implies abelian-derived vanishing. -/
lemma isZero_abelian_of_module (M : X.Modules) (n : ℕ)
    (h : IsZero (((Scheme.Modules.pushforward f).rightDerived (n + 1)).obj M)) :
    IsZero (((abelianPushforward f).rightDerived (n + 1)).obj ((moduleToSheaf X).obj M)) :=
  ((moduleToSheaf Y).map_isZero h).of_iso (comparisonObj f M (n + 1)).symm

/-- Faithfulness of forgetting transports vanishing back to module higher direct images. -/
lemma isZero_module_of_abelian (M : X.Modules) (n : ℕ)
    (h : IsZero (((abelianPushforward f).rightDerived (n + 1)).obj
      ((moduleToSheaf X).obj M))) :
    IsZero (((Scheme.Modules.pushforward f).rightDerived (n + 1)).obj M) := by
  have h' := h.of_iso (comparisonObj f M (n + 1))
  rw [IsZero.iff_id_eq_zero]
  apply (SheafOfModules.toSheaf.{u} Y.ringCatSheaf).map_injective
  exact h'.eq_of_src _ _

/-- Positive higher direct-image vanishing is equivalent in the two categories. -/
lemma isZero_rightDerived_iff (M : X.Modules) (n : ℕ) :
    IsZero (((Scheme.Modules.pushforward f).rightDerived (n + 1)).obj M) ↔
      IsZero (((abelianPushforward f).rightDerived (n + 1)).obj ((moduleToSheaf X).obj M)) :=
  ⟨isZero_abelian_of_module f M n, isZero_module_of_abelian f M n⟩

/-- Simultaneous vanishing in every positive degree transports without additional inputs. -/
lemma acyclic_iff (M : X.Modules) :
    (∀ n : ℕ, IsZero (((Scheme.Modules.pushforward f).rightDerived (n + 1)).obj M)) ↔
      ∀ n : ℕ, IsZero (((abelianPushforward f).rightDerived (n + 1)).obj
        ((moduleToSheaf X).obj M)) :=
  forall_congr' (isZero_rightDerived_iff f M)

end FLT.Mazur.ModuleDerivedAbelianComparison
