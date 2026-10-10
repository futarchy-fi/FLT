/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.NormalizedSectionLineOverlapBaseChange

/-!
# Geometric composition of section-line pullbacks

Successive coefficient extensions identify the actual line submodules. The
corresponding sheaf comparison agrees with the canonical geometric pullback
comparison, as checked on the original coefficient sections.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
namespace FLT.Mazur.NormalizedSectionLine
open AffineTildeSemilinearCoherence AffineIteratedPullbackSections
variable {R S T : Type u} [CommRing R] [CommRing S] [CommRing T] {ι : Type u}

/-- The comparison from successive extension to direct extension retains the actual inclusion. -/
def sheafExtensionComp (φ : R →+* S) (ψ : S →+* T) (i : ι) (L : Chart R ι i) :
    sheaf i (baseChange ψ i (baseChange φ i L)) ≅
      sheaf i (baseChange (ψ.comp φ) i L) :=
  sheafChartChange i i _ _ (congrArg Subtype.val (baseChange_comp φ ψ i L))

/-- The extension comparison preserves the coordinate inclusion. -/
lemma sheafExtensionComp_inclusion (φ : R →+* S) (ψ : S →+* T)
    (i : ι) (L : Chart R ι i) :
    (sheafExtensionComp φ ψ i L).hom ≫ sheafInclusion i (baseChange (ψ.comp φ) i L) =
      sheafInclusion i (baseChange ψ i (baseChange φ i L)) :=
  sheafChartChange_inclusion _ _ _ _ _

/-- Naturality of the canonical geometric comparison, in the inverse direction. -/
lemma pullbackComposition_inv_naturality {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) (k : X ⟶ Z) (w : f ≫ g = k)
    {M N : Z.Modules} (a : M ⟶ N) :
    (compositeIso f g k w M).inv ≫ (pullback f).map ((pullback g).map a) =
      (pullback k).map a ≫ (compositeIso f g k w N).inv :=
  (((pullbackComp f g) ≪≫ pullbackCongr w).inv.naturality a).symm

attribute [local irreducible] compositeIso Scheme.Modules.pullback sheafBaseChange
attribute [local irreducible] AffineTildeSemilinearMap.map moduleSpecΓFunctor

/-- Finite ambient coordinate sheaves respect the canonical geometric composition. -/
lemma vectorSheafBaseChange_comp [Finite ι] (φ : R →+* S) (ψ : S →+* T)
    (w : Spec.map (CommRingCat.ofHom ψ) ≫ Spec.map (CommRingCat.ofHom φ) =
      Spec.map (CommRingCat.ofHom (ψ.comp φ))) :
    (compositeIso _ _ _ w (tilde (ModuleCat.of R (ι → R)))).inv ≫
        (pullback (Spec.map (CommRingCat.ofHom ψ))).map (vectorSheafBaseChange ι φ).hom ≫
        (vectorSheafBaseChange ι ψ).hom = (vectorSheafBaseChange ι (ψ.comp φ)).hom := by
  rw [vectorSheafBaseChange_hom, vectorSheafBaseChange_hom, vectorSheafBaseChange_hom]
  exact map_comp (CommRingCat.ofHom φ) (CommRingCat.ofHom ψ)
    (CommRingCat.ofHom (ψ.comp φ)) w _ _ _
    (vectorCoefficientMap ι φ) (vectorCoefficientMap ι ψ)
    (vectorCoefficientMap ι (ψ.comp φ)) (fun _ ↦ rfl)

attribute [local irreducible] sheafExtensionComp vectorSheafBaseChange

/-- The line comparison uses the canonical geometric comparison of the two pullbacks. -/
lemma sheafBaseChange_comp [Finite ι] (φ : R →+* S) (ψ : S →+* T)
    (i : ι) (L : Chart R ι i)
    (w : Spec.map (CommRingCat.ofHom ψ) ≫ Spec.map (CommRingCat.ofHom φ) =
      Spec.map (CommRingCat.ofHom (ψ.comp φ))) :
    (compositeIso _ _ _ w (sheaf i L)).inv ≫
        (pullback (Spec.map (CommRingCat.ofHom ψ))).map (sheafBaseChange φ i L).hom ≫
        (sheafBaseChange ψ i (baseChange φ i L)).hom ≫
        (sheafExtensionComp φ ψ i L).hom =
      (sheafBaseChange (ψ.comp φ) i L).hom := by
  apply (cancel_mono (sheafInclusion i (baseChange (ψ.comp φ) i L))).mp
  simp only [Category.assoc, sheafExtensionComp_inclusion, sheafBaseChange_inclusion]
  rw [← Category.assoc ((pullback (Spec.map (CommRingCat.ofHom ψ))).map _),
    ← Functor.map_comp, sheafBaseChange_inclusion, Functor.map_comp]
  simp only [← Category.assoc]
  rw [pullbackComposition_inv_naturality]
  simp only [Category.assoc]
  rw [vectorSheafBaseChange_comp]

end FLT.Mazur.NormalizedSectionLine
