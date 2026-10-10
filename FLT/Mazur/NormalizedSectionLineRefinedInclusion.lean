/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.NormalizedSectionLinePullbackComposition

/-!
# Refinement of actual line inclusion squares

An ambient-preserving comparison remains ambient-preserving after a further
coefficient extension. Both sides use the canonical geometric comparison
between successive pullbacks and pullback by the composite map.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace FLT.Mazur.NormalizedSectionLine
open AffineIteratedPullbackSections

/-- Naturality of the forward canonical geometric comparison. -/
lemma pullbackComposition_hom_naturality {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) (k : X ⟶ Z) (w : f ≫ g = k)
    {M N : Z.Modules} (a : M ⟶ N) :
    (compositeIso f g k w M).hom ≫ (pullback k).map a =
      (pullback f).map ((pullback g).map a) ≫ (compositeIso f g k w N).hom :=
  (((pullbackComp f g) ≪≫ pullbackCongr w).hom.naturality a).symm

attribute [local irreducible] compositeIso Scheme.Modules.pullback vectorSheafBaseChange
variable {R S T V : Type u} [CommRing R] [CommRing S] [CommRing T] [CommRing V]
variable {ι : Type u} [Finite ι]

/-- Direct ambient extension agrees with successive extension after the forward comparison. -/
lemma vectorSheafBaseChange_comp_hom (φ : R →+* T) (χ : T →+* V)
    (w : Spec.map (CommRingCat.ofHom χ) ≫ Spec.map (CommRingCat.ofHom φ) =
      Spec.map (CommRingCat.ofHom (χ.comp φ))) :
    (compositeIso _ _ _ w (tilde (ModuleCat.of R (ι → R)))).hom ≫
        (vectorSheafBaseChange ι (χ.comp φ)).hom =
      (pullback (Spec.map (CommRingCat.ofHom χ))).map (vectorSheafBaseChange ι φ).hom ≫
        (vectorSheafBaseChange ι χ).hom := by
  rw [← vectorSheafBaseChange_comp φ χ w, Iso.hom_inv_id_assoc]

/-- Refinement carries an actual inclusion square through canonical geometric pullbacks. -/
lemma refine_inclusion (φ : R →+* T) (ψ : S →+* T) (χ : T →+* V)
    (i j : ι) (L : Chart R ι i) (M : Chart S ι j)
    (wφ : Spec.map (CommRingCat.ofHom χ) ≫ Spec.map (CommRingCat.ofHom φ) =
      Spec.map (CommRingCat.ofHom (χ.comp φ)))
    (wψ : Spec.map (CommRingCat.ofHom χ) ≫ Spec.map (CommRingCat.ofHom ψ) =
      Spec.map (CommRingCat.ofHom (χ.comp ψ)))
    (a : (pullback (Spec.map (CommRingCat.ofHom φ))).obj (sheaf i L) ⟶
      (pullback (Spec.map (CommRingCat.ofHom ψ))).obj (sheaf j M))
    (ha : a ≫ (pullback (Spec.map (CommRingCat.ofHom ψ))).map (sheafInclusion j M) ≫
        (vectorSheafBaseChange ι ψ).hom =
      (pullback (Spec.map (CommRingCat.ofHom φ))).map (sheafInclusion i L) ≫
        (vectorSheafBaseChange ι φ).hom) :
    (compositeIso _ _ _ wφ (sheaf i L)).inv ≫
        (pullback (Spec.map (CommRingCat.ofHom χ))).map a ≫
        (compositeIso _ _ _ wψ (sheaf j M)).hom ≫
        (pullback (Spec.map (CommRingCat.ofHom (χ.comp ψ)))).map (sheafInclusion j M) ≫
        (vectorSheafBaseChange ι (χ.comp ψ)).hom =
      (pullback (Spec.map (CommRingCat.ofHom (χ.comp φ)))).map (sheafInclusion i L) ≫
        (vectorSheafBaseChange ι (χ.comp φ)).hom := by
  rw [← Category.assoc (compositeIso _ _ _ wψ (sheaf j M)).hom,
    pullbackComposition_hom_naturality]
  simp only [Category.assoc]
  rw [vectorSheafBaseChange_comp_hom]
  simp only [← Functor.map_comp_assoc, ha]
  rw [Functor.map_comp]
  simp only [← Category.assoc]
  rw [pullbackComposition_inv_naturality]
  simp only [Category.assoc]
  rw [vectorSheafBaseChange_comp]

end FLT.Mazur.NormalizedSectionLine
