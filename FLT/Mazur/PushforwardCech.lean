/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ModuleCechScalar

/-!
# Cech complexes of direct images

Inverse image preserves finite intersections of opens. The resulting section
identifications give a natural isomorphism of Cech complexes and their cohomology.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite

universe u

namespace FLT.Mazur.PushforwardCech

open CechSheafHZero

variable {X Y : Scheme.{u}} (f : X ⟶ Y) {ι : Type u} (U : ι → Y.Opens)

/-- Inverse image commutes with each finite product of opens in the Cech object. -/
lemma preimage_product (n : ℕ) (a : Fin (n + 1) → ι) :
    f ⁻¹ᵁ (∏ᶜ (U ∘ a)) = ∏ᶜ ((fun i ↦ f ⁻¹ᵁ U i) ∘ a) := by
  rw [productOpen_eq, productOpen_eq]
  apply Opens.ext
  simp only [Scheme.Hom.coe_preimage, V, Opens.coe_iInf, Set.preimage_iInter]

variable (F : X.Opensᵒᵖ ⥤ AddCommGrpCat.{u})

/-- The sectionwise isomorphism of the cosimplicial objects. -/
def cosimplicialIso :
    (FormalCoproduct.cosimplicialObjectFunctor (FormalCoproduct.mk _ U).cech).obj
        ((Opens.map f.base).op ⋙ F) ≅
      (FormalCoproduct.cosimplicialObjectFunctor
        (FormalCoproduct.mk _ (fun i ↦ f ⁻¹ᵁ U i)).cech).obj F :=
  NatIso.ofComponents (fun n ↦ Pi.mapIso fun a ↦
    F.mapIso (eqToIso (congrArg op (preimage_product f U n.len a)))) (by
      intro n m g
      apply Pi.hom_ext
      intro a
      dsimp
      simp only [Pi.mapIso_hom_π, Category.assoc, Pi.lift_comp_π, Pi.lift_comp_π_assoc,
        Pi.mapIso_hom_π_assoc, Functor.mapIso_hom, ← Functor.map_comp]
      congr 1)

/-- The direct-image Cech complex is the Cech complex on the inverse-image family. -/
def complexIso :
    (cechComplexFunctor U).obj ((Opens.map f.base).op ⋙ F) ≅
      (cechComplexFunctor (fun i ↦ f ⁻¹ᵁ U i)).obj F :=
  (AlgebraicTopology.alternatingCofaceMapComplex AddCommGrpCat).mapIso
    (cosimplicialIso f U F)

/-- The complex identification is natural in the coefficient presheaf. -/
lemma complexIso_naturality {G : X.Opensᵒᵖ ⥤ AddCommGrpCat.{u}} (g : F ⟶ G) :
    (cechComplexFunctor U).map (Functor.whiskerLeft (Opens.map f.base).op g) ≫
        (complexIso f U G).hom =
      (complexIso f U F).hom ≫
        (cechComplexFunctor (fun i ↦ f ⁻¹ᵁ U i)).map g := by
  ext n : 1
  apply Pi.hom_ext
  intro a
  change Limits.Pi.map (fun a : Fin (n + 1) → ι ↦
      g.app (op (f ⁻¹ᵁ (∏ᶜ (U ∘ a))))) ≫
      (Pi.mapIso (fun a ↦ G.mapIso
        (eqToIso (congrArg op (preimage_product f U n a))))).hom ≫ Pi.π _ a =
    (Pi.mapIso (fun a ↦ F.mapIso
      (eqToIso (congrArg op (preimage_product f U n a))))).hom ≫
      Limits.Pi.map (fun a : Fin (n + 1) → ι ↦
        g.app (op (∏ᶜ ((fun i ↦ f ⁻¹ᵁ U i) ∘ a)))) ≫ Pi.π _ a
  simp only [Pi.mapIso_hom_π, Pi.map_π, Pi.map_π_assoc,
    Pi.mapIso_hom_π_assoc, Functor.mapIso_hom]
  rw [g.naturality]

/-- Cohomology of direct-image Cech complexes agrees with inverse-image Cech cohomology. -/
def cohomologyIso (n : ℕ) :
    ((cechComplexFunctor U).obj ((Opens.map f.base).op ⋙ F)).homology n ≅
      ((cechComplexFunctor (fun i ↦ f ⁻¹ᵁ U i)).obj F).homology n :=
  (HomologicalComplex.homologyFunctor _ _ n).mapIso (complexIso f U F)

/-- Naturality descends to Cech cohomology. -/
lemma cohomologyIso_naturality {G : X.Opensᵒᵖ ⥤ AddCommGrpCat.{u}}
    (g : F ⟶ G) (n : ℕ) :
    HomologicalComplex.homologyMap
        ((cechComplexFunctor U).map (Functor.whiskerLeft (Opens.map f.base).op g)) n ≫
        (cohomologyIso f U G n).hom =
      (cohomologyIso f U F n).hom ≫ HomologicalComplex.homologyMap
        ((cechComplexFunctor (fun i ↦ f ⁻¹ᵁ U i)).map g) n := by
  simpa only [cohomologyIso, Functor.mapIso_hom,
    HomologicalComplex.homologyFunctor_map, HomologicalComplex.homologyMap_comp] using
    congrArg ((HomologicalComplex.homologyFunctor _ _ n).map)
      (complexIso_naturality f U F g)

open FCurve AlgebraicGeometry.Scheme.Modules

/-- Multiplication on a direct image is multiplication by the image global section. -/
lemma pushforward_multiply (M : X.Modules) (r : Γ(Y, ⊤)) :
    (moduleMultiply ((pushforward f).obj M) r).hom =
      Functor.whiskerLeft (Opens.map f.base).op (moduleMultiply M (f.appTop r)).hom := by
  ext W x
  change M.val.obj (op (f ⁻¹ᵁ W.unop)) at x
  change (f.app W.unop) (Y.presheaf.map (homOfLE le_top).op r) • x =
    X.presheaf.map (homOfLE (show f ⁻¹ᵁ W.unop ≤ ⊤ from le_top)).op (f.appTop r) • x
  exact congrArg (fun s ↦ s • x)
    (ConcreteCategory.congr_hom (f.naturality (homOfLE le_top).op) r)

/-- The Cech comparison respects the global sections of the target scheme. -/
def moduleCechEquiv (M : X.Modules) (n : ℕ) :
    letI _sourceScalars := Module.compHom
      (CH (fun i ↦ f ⁻¹ᵁ U i) (moduleAbelianSheaf M) n) f.appTop.hom
    CH U (moduleAbelianSheaf ((pushforward f).obj M)) n ≃ₗ[Γ(Y, ⊤)]
      CH (fun i ↦ f ⁻¹ᵁ U i) (moduleAbelianSheaf M) n := by
  letI _sourceScalars := Module.compHom
    (CH (fun i ↦ f ⁻¹ᵁ U i) (moduleAbelianSheaf M) n) f.appTop.hom
  refine
    { toAddEquiv := (cohomologyIso f U (moduleAbelianSheaf M).obj n).addCommGroupIsoToAddEquiv
      map_smul' := ?_ }
  intro r x
  change (cohomologyIso f U (moduleAbelianSheaf M).obj n).hom
      (CHmap U (moduleMultiply ((pushforward f).obj M) r) n x) =
    CHmap (fun i ↦ f ⁻¹ᵁ U i) (moduleMultiply M (f.appTop r)) n
      ((cohomologyIso f U (moduleAbelianSheaf M).obj n).hom x)
  change (HomologicalComplex.homologyMap
    ((cechComplexFunctor U).map (moduleMultiply ((pushforward f).obj M) r).hom) n ≫
      (cohomologyIso f U (moduleAbelianSheaf M).obj n).hom) x = _
  rw [pushforward_multiply]
  exact ConcreteCategory.congr_hom
    (cohomologyIso_naturality f U _ (moduleMultiply M (f.appTop r)).hom n) x

end FLT.Mazur.PushforwardCech
