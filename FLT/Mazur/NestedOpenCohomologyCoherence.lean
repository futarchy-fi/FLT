/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeCohomologyIsoCocycles
public import FLT.Mazur.OpenSheafCohomologyRestriction

/-!
# Canonical coherence for cohomology on nested opens

The scheme isomorphism flattening an iterated open identifies its Ext
comparison with the comparison of the cohomology presheaves.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxSynthPendingDepth 1

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
open AlgebraicGeometry TopologicalSpace Opposite

universe u

namespace FLT.Mazur.OpenSheafCohomologyRestriction

open OpenSheafRestriction ExactFunctorInjectiveExt AbsoluteDirectImageCohomology
open OpenDirectImageRestriction SchemeCohomologyIso

variable {S : Scheme.{u}} (U : S.Opens) (V : U.toScheme.Opens)

/-- Direct restriction followed by the flattening scheme isomorphism. -/
def directResolution {A : TopCat.Sheaf AddCommGrpCat.{u} S} (I : InjectiveResolution A) :=
  imageResolution (abelianSheafEquivalence (U.ι.isoImage V)).inverse
    (imageResolution (restriction (U.ι ''ᵁ V)) I)

/-- Restriction of a resolution in two stages. -/
def iteratedResolution {A : TopCat.Sheaf AddCommGrpCat.{u} S} (I : InjectiveResolution A) :=
  imageResolution (restriction V) (imageResolution (restriction U) I)

/-- The underived nested-restriction isomorphism induces a map of resolutions. -/
def nestedResolutionHom {A : TopCat.Sheaf AddCommGrpCat.{u} S}
    (I : InjectiveResolution A) :
    (directResolution U V I).Hom (iteratedResolution U V I)
      ((nestedRestrictionIso U V).hom.app A) where
  hom :=
    { f := fun n ↦ (nestedRestrictionIso U V).hom.app (I.cocomplex.X n)
      comm' := fun i j _ ↦ ((nestedRestrictionIso U V).hom.naturality
        (I.cocomplex.d i j)).symm }
  ι_f_zero_comp_hom_f_zero := by
    change ((restriction (U.ι ''ᵁ V) ⋙
      (abelianSheafEquivalence (U.ι.isoImage V)).inverse).map (I.ι.f 0)) ≫
      (nestedRestrictionIso U V).hom.app _ =
        (nestedRestrictionIso U V).hom.app A ≫
          (restriction U ⋙ restriction V).map (I.ι.f 0)
    exact (nestedRestrictionIso U V).hom.naturality _

local instance nestedSheafHasExt (T : TopCat.{u}) :
    HasExt.{u + 1} (Sheaf (Opens.grothendieckTopology T) AddCommGrpCat.{u}) :=
  HasExt.standard _

local instance nestedTopSheafHasExt (T : TopCat.{u}) :
    HasExt.{u + 1} (TopCat.Sheaf AddCommGrpCat.{u} T) := HasExt.standard _

local instance nestedRestrictedHasExt {T : TopCat.{u}} (W : Opens T) :
    HasExt.{u + 1} (Sheaf (Opens.grothendieckTopology W) AddCommGrpCat.{u}) :=
  HasExt.standard _

/-- The two resolution maps give the same section on the iterated top open. -/
lemma nestedResolutionHom_cycles {A : TopCat.Sheaf AddCommGrpCat.{u} S}
    (I : InjectiveResolution A) (n : ℕ)
    (x : OpenDirectImageCohomology.sectionCycles (U.ι ''ᵁ V) I n) :
    sectionCyclesMap (nestedResolutionHom U V I).hom n
      (isoCycles (U.ι.isoImage V) (imageResolution (restriction (U.ι ''ᵁ V)) I) n
        (restrictedCycles (U.ι ''ᵁ V) I n x)) =
      restrictedCycles V (imageResolution (restriction U) I) n x := by
  apply Subtype.ext
  change (I.cocomplex.X n).obj.map _
    ((I.cocomplex.X n).obj.map _ ((I.cocomplex.X n).obj.map _ x.1)) =
      (I.cocomplex.X n).obj.map _ x.1
  simp only [← ConcreteCategory.comp_apply, ← Functor.map_comp]
  rfl

/-- The canonical scheme and presheaf comparisons agree on nested-open cohomology. -/
private lemma nested_openHEquiv_aux (A : TopCat.Sheaf AddCommGrpCat.{u} S)
    (I : InjectiveResolution A) (n : ℕ)
    (z : Sheaf.H'.{u + 1} A n (U.ι ''ᵁ V)) :
    Sheaf.H.map ((nestedRestrictionIso U V).hom.app A) n
      (sheafHEquiv (U.ι.isoImage V) ((restriction (U.ι ''ᵁ V)).obj A) n
        (OpenSheafCohomology.openHEquiv (U.ι ''ᵁ V) A n z)) =
      OpenSheafCohomology.openHEquiv V ((restriction U).obj A) n
        (imageHEquiv U V A n z) := by
  obtain ⟨x, rfl⟩ := OpenDirectImageCohomology.sectionClass_surjective _ I n z
  refine (congrArg (fun y ↦ Sheaf.H.map ((nestedRestrictionIso U V).hom.app A) n
    (sheafHEquiv (U.ι.isoImage V) ((restriction (U.ι ''ᵁ V)).obj A) n y))
    (openHEquiv_sectionClass (U.ι ''ᵁ V) I n x)).trans ?_
  refine (congrArg (Sheaf.H.map ((nestedRestrictionIso U V).hom.app A) n)
    (sheafHEquiv_sectionClass (U.ι.isoImage V)
      (imageResolution (restriction (U.ι ''ᵁ V)) I) n _)).trans ?_
  refine (sectionClass_naturality (nestedResolutionHom U V I) n _).trans ?_
  refine (congrArg (sectionClass (iteratedResolution U V I) n)
    (nestedResolutionHom_cycles U V I n x)).trans ?_
  refine (openHEquiv_sectionClass V (imageResolution (restriction U) I) n x).symm.trans ?_
  exact congrArg (OpenSheafCohomology.openHEquiv V ((restriction U).obj A) n)
    (imageHEquiv_sectionClass U V I n x).symm

/-- The canonical scheme and presheaf comparisons agree on nested-open cohomology. -/
lemma nested_openHEquiv (A : TopCat.Sheaf AddCommGrpCat.{u} S) (n : ℕ)
    (z : Sheaf.H'.{u + 1} A n (U.ι ''ᵁ V)) :
    Sheaf.H.map ((nestedRestrictionIso U V).hom.app A) n
      (sheafHEquiv (U.ι.isoImage V) ((restriction (U.ι ''ᵁ V)).obj A) n
        (OpenSheafCohomology.openHEquiv (U.ι ''ᵁ V) A n z)) =
      OpenSheafCohomology.openHEquiv V ((restriction U).obj A) n
        (imageHEquiv U V A n z) :=
  nested_openHEquiv_aux U V A (injectiveResolution A) n z

/-- Restrict a global cohomology class to the cohomology of the open subspace. -/
def globalOpenRestriction {T : TopCat.{u}} (W : Opens T)
    (A : TopCat.Sheaf AddCommGrpCat.{u} T) (n : ℕ) :
    Sheaf.H A n →+ Sheaf.H ((restriction W).obj A) n :=
  (OpenSheafCohomology.openHEquiv W A n).toAddMonoidHom.comp
    (AffineCohomologyVanishingLocal.restrictSheafH A n W)

/-- Global restriction is natural for every coefficient map on the intermediate space. -/
lemma globalOpenRestriction_naturality {T : TopCat.{u}} (W : Opens T)
    {A B : TopCat.Sheaf AddCommGrpCat.{u} T} (f : A ⟶ B) (n : ℕ) (x : Sheaf.H A n) :
    globalOpenRestriction W B n (Sheaf.H.map f n x) =
      Sheaf.H.map ((restriction W).map f) n (globalOpenRestriction W A n x) := by
  change OpenSheafCohomology.openHEquiv W B n
    (AffineCohomologyVanishingLocal.restrictSheafH B n W (Sheaf.H.map f n x)) = _
  rw [restrictSheafH_coeff]
  exact OpenSheafCohomology.openHEquiv_naturality W f n _

/-- Ambient restriction agrees with global restriction on the intermediate open,
after the canonical flattening isomorphism. -/
lemma nested_global_restriction (A : TopCat.Sheaf AddCommGrpCat.{u} S) (n : ℕ)
    (z : Sheaf.H'.{u + 1} A n U) :
    Sheaf.H.map ((nestedRestrictionIso U V).hom.app A) n
      (sheafHEquiv (U.ι.isoImage V) ((restriction (U.ι ''ᵁ V)).obj A) n
        (OpenSheafCohomology.openHEquiv (U.ι ''ᵁ V) A n
          ((Sheaf.cohomologyPresheaf A n).map (homOfLE (openImage_le U V)).op z))) =
      globalOpenRestriction V ((restriction U).obj A) n
        (OpenSheafCohomology.openHEquiv U A n z) := by
  rw [nested_openHEquiv, imageHEquiv_restrict_openHEquiv]
  rfl

end FLT.Mazur.OpenSheafCohomologyRestriction
