/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CechFreeResolution
public import Mathlib.Algebra.FreeAbelianGroup.Finsupp
public import Mathlib.Topology.Sheaves.Sheafify

/-!
# Stalks of free open sheaves

The stalk of the representable of an open is its membership type. Free abelian
groups and sheafification preserve this computation. Coproduct coordinates then
identify the stalks of the augmented free Cech complex.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor TopologicalSpace Opposite
open TopCat.Presheaf

universe u

namespace FLT.Mazur.CechFreeOpen

variable {X : TopCat.{u}}

/-- Membership as a type in the universe of the space. -/
abbrev OpenFiber (W : Opens X) (x : X) := ULift.{u} (PLift (x ∈ W))

/-- The neighborhood diagram of a representable has membership as its cocone point. -/
def openFiberCocone (W : Opens X) (x : X) :
    Cocone ((OpenNhds.inclusion x).op ⋙ yoneda.obj W) where
  pt := OpenFiber W x
  ι :=
    { app := fun T ↦ TypeCat.ofHom fun f ↦ ⟨⟨f.le T.unop.property⟩⟩
      naturality := fun _ _ _ ↦ by ext; rfl }

/-- Every membership witness comes from the identity section on the open itself. -/
def openFiberIsColimit (W : Opens X) (x : X) : IsColimit (openFiberCocone W x) where
  desc s := TypeCat.ofHom fun h ↦ s.ι.app (op ⟨W, h.down.down⟩) (𝟙 W)
  fac s T := by
    ext f
    exact (ConcreteCategory.congr_hom (s.w
      (show op ⟨W, f.le T.unop.property⟩ ⟶ T from
        (show T.unop ⟶ (⟨W, f.le T.unop.property⟩ : OpenNhds x) from f).op)) (𝟙 W)).symm
  uniq s m hm := by
    ext h
    exact ConcreteCategory.congr_hom (hm (op ⟨W, h.down.down⟩)) (𝟙 W)

/-- The stalk of the free representable before sheafification. -/
def freePresheafStalkIso (W : Opens X) (x : X) :
    stalk (yoneda.obj W ⋙ AddCommGrpCat.free) x ≅
      AddCommGrpCat.of (FreeAbelianGroup (OpenFiber W x)) :=
  colimit.isoColimitCocone
    ⟨AddCommGrpCat.free.mapCocone (openFiberCocone W x),
      isColimitOfPreserves AddCommGrpCat.free (openFiberIsColimit W x)⟩

/-- Sheafification induces the canonical stalk isomorphism. -/
def freeOpenSheafifyStalkIso (W : Opens X) (x : X) :
    stalk (yoneda.obj W ⋙ AddCommGrpCat.free) x ≅ stalk (freeOpen W).obj x := by
  letI := stalkFunctor_map_unit_toSheafify_isIso x AddCommGrpCat.{u}
    (yoneda.obj W ⋙ AddCommGrpCat.free)
  exact asIso ((stalkFunctor AddCommGrpCat.{u} x).map
    (toSheafify (Opens.grothendieckTopology X) (yoneda.obj W ⋙ AddCommGrpCat.free)))

/-- The stalk of the free sheaf on an open is free on its membership type. -/
def freeOpenStalkIso (W : Opens X) (x : X) :
    ((TopCat.Sheaf.forget AddCommGrpCat.{u} X ⋙ stalkFunctor AddCommGrpCat.{u} x).obj
      (freeOpen W)) ≅ AddCommGrpCat.of (OpenFiber W x →₀ ℤ) :=
  (freeOpenSheafifyStalkIso W x).symm ≪≫ freePresheafStalkIso W x ≪≫
    (FreeAbelianGroup.equivFinsupp (OpenFiber W x)).toAddCommGrpIso

/-- The presheaf stalk computation sends each local generator to membership. -/
@[reassoc (attr := simp)]
lemma germ_freePresheafStalkIso (W T : Opens X) (x : X) (hx : x ∈ T) :
    germ (yoneda.obj W ⋙ AddCommGrpCat.free) T x hx ≫
      (freePresheafStalkIso W x).hom =
    AddCommGrpCat.free.map (TypeCat.ofHom fun f : T ⟶ W ↦
      (⟨⟨f.le hx⟩⟩ : OpenFiber W x)) :=
  colimit.isoColimitCocone_ι_hom
    ⟨AddCommGrpCat.free.mapCocone (openFiberCocone W x),
      isColimitOfPreserves AddCommGrpCat.free (openFiberIsColimit W x)⟩ (op ⟨T, hx⟩)

/-- The stalk coordinates send the germ of a sheafified generator to its basis vector. -/
lemma freeOpenStalkIso_generator (W T : Opens X) (x : X) (hx : x ∈ T) (f : T ⟶ W) :
    (freeOpenStalkIso W x).hom
      (germ (freeOpen W).obj T x hx (CechFreeResolution.freeOpenGenerator W T f)) =
    Finsupp.single (⟨⟨f.le hx⟩⟩ : OpenFiber W x) 1 := by
  have h := stalkFunctor_map_germ_apply T x hx
    (toSheafify (Opens.grothendieckTopology X) (yoneda.obj W ⋙ AddCommGrpCat.free))
    (FreeAbelianGroup.of f)
  change (freeOpenSheafifyStalkIso W x).hom
    (germ (yoneda.obj W ⋙ AddCommGrpCat.free) T x hx (FreeAbelianGroup.of f)) =
      germ (freeOpen W).obj T x hx (CechFreeResolution.freeOpenGenerator W T f) at h
  rw [← h]
  change ((freeOpenSheafifyStalkIso W x).hom ≫ (freeOpenStalkIso W x).hom)
    (germ (yoneda.obj W ⋙ AddCommGrpCat.free) T x hx (FreeAbelianGroup.of f)) = _
  simp only [freeOpenStalkIso, Iso.trans_hom, Iso.symm_hom, Iso.hom_inv_id_assoc]
  change (germ (yoneda.obj W ⋙ AddCommGrpCat.free) T x hx ≫
    (freePresheafStalkIso W x).hom ≫
      ((FreeAbelianGroup.equivFinsupp (OpenFiber W x)).toAddCommGrpIso
        (Y := AddCommGrpCat.of (OpenFiber W x →₀ ℤ))).hom) (FreeAbelianGroup.of f) = _
  rw [germ_freePresheafStalkIso_assoc]
  simp [AddCommGrpCat.free_map, FreeAbelianGroup.equivFinsupp]

/-- Membership is covariant in the open. -/
def openFiberMap {W W' : Opens X} (i : W ⟶ W') (x : X) :
    OpenFiber W x → OpenFiber W' x := fun h ↦ ⟨⟨i.le h.down.down⟩⟩

/-- The induced homomorphism on the free groups in stalk coordinates. -/
def freeOpenStalkMap {W W' : Opens X} (i : W ⟶ W') (x : X) :
    AddCommGrpCat.of (OpenFiber W x →₀ ℤ) ⟶
      AddCommGrpCat.of (OpenFiber W' x →₀ ℤ) :=
  AddCommGrpCat.ofHom (Finsupp.mapDomain.addMonoidHom (openFiberMap i x))

/-- The stalk map carries a membership generator to the same point in the larger open. -/
@[simp]
lemma freeOpenStalkMap_single {W W' : Opens X} (i : W ⟶ W') (x : X)
    (h : OpenFiber W x) (n : ℤ) :
    freeOpenStalkMap i x (Finsupp.single h n) =
      Finsupp.single (openFiberMap i x h) n := by
  simp [freeOpenStalkMap]

/-- Naturality of the free presheaf stalk computation. -/
@[reassoc]
lemma freePresheafStalkIso_naturality {W W' : Opens X} (i : W ⟶ W') (x : X) :
    (stalkFunctor AddCommGrpCat.{u} x).map
        (whiskerRight (yoneda.map i) AddCommGrpCat.free) ≫
      (freePresheafStalkIso W' x).hom =
    (freePresheafStalkIso W x).hom ≫
      AddCommGrpCat.free.map (TypeCat.ofHom (openFiberMap i x)) := by
  apply stalk_hom_ext
  intro T hx
  simp only [stalkFunctor_map_germ_assoc, germ_freePresheafStalkIso,
    germ_freePresheafStalkIso_assoc]
  change AddCommGrpCat.free.map _ ≫ AddCommGrpCat.free.map _ =
    AddCommGrpCat.free.map _ ≫ AddCommGrpCat.free.map _
  rw [← Functor.map_comp, ← Functor.map_comp]
  congr 1

/-- The free-group and finitely-supported-function coordinates agree on maps. -/
@[reassoc]
lemma freeFiberFinsupp_naturality {W W' : Opens X} (i : W ⟶ W') (x : X) :
    AddCommGrpCat.free.map (TypeCat.ofHom (openFiberMap i x)) ≫
      (FreeAbelianGroup.equivFinsupp (OpenFiber W' x)).toAddCommGrpIso.hom =
    (FreeAbelianGroup.equivFinsupp (OpenFiber W x)).toAddCommGrpIso.hom ≫
      freeOpenStalkMap i x := by
  apply AddCommGrpCat.hom_ext
  apply FreeAbelianGroup.lift_ext
  intro h
  simp [FreeAbelianGroup.equivFinsupp, AddCommGrpCat.free_map, freeOpenStalkMap]

/-- Naturality of the sheafification comparison on stalks. -/
@[reassoc]
lemma freeOpenSheafifyStalkIso_naturality {W W' : Opens X} (i : W ⟶ W') (x : X) :
    (freeOpenSheafifyStalkIso W x).hom ≫
      (stalkFunctor AddCommGrpCat.{u} x).map (freeOpenMap i).hom =
    (stalkFunctor AddCommGrpCat.{u} x).map
        (whiskerRight (yoneda.map i) AddCommGrpCat.free) ≫
      (freeOpenSheafifyStalkIso W' x).hom := by
  change (stalkFunctor AddCommGrpCat.{u} x).map _ ≫
      (stalkFunctor AddCommGrpCat.{u} x).map _ =
    (stalkFunctor AddCommGrpCat.{u} x).map _ ≫
      (stalkFunctor AddCommGrpCat.{u} x).map _
  rw [← Functor.map_comp, ← Functor.map_comp]
  exact congrArg _ (toSheafify_naturality (Opens.grothendieckTopology X) _).symm

/-- Stalk coordinates commute with every inclusion of opens. -/
@[reassoc]
lemma freeOpenStalkIso_naturality {W W' : Opens X} (i : W ⟶ W') (x : X) :
    (stalkFunctor AddCommGrpCat.{u} x).map (freeOpenMap i).hom ≫
      (freeOpenStalkIso W' x).hom =
    (freeOpenStalkIso W x).hom ≫ freeOpenStalkMap i x := by
  apply (cancel_epi (freeOpenSheafifyStalkIso W x).hom).mp
  simp only [freeOpenStalkIso, Iso.trans_hom, Iso.symm_hom, Category.assoc,
    freeOpenSheafifyStalkIso_naturality_assoc, Iso.hom_inv_id_assoc]
  rw [freePresheafStalkIso_naturality_assoc, freeFiberFinsupp_naturality]

/-- The inverse coordinates also commute with inclusions. -/
@[reassoc]
lemma freeOpenStalkIso_inv_naturality {W W' : Opens X} (i : W ⟶ W') (x : X) :
    (freeOpenStalkIso W x).inv ≫ (stalkFunctor AddCommGrpCat.{u} x).map
      (freeOpenMap i).hom = freeOpenStalkMap i x ≫ (freeOpenStalkIso W' x).inv := by
  apply (cancel_mono (freeOpenStalkIso W' x).hom).mp
  simp only [Category.assoc, freeOpenStalkIso_naturality, Iso.inv_hom_id_assoc,
    Iso.inv_hom_id, Category.comp_id]

end FLT.Mazur.CechFreeOpen

namespace FLT.Mazur.CechFreeResolution

open FLT.Mazur.CechFreeOpen

variable {X : TopCat.{u}} {ι : Type u}

/-- The colimit-preserving stalk functor on abelian sheaves. -/
abbrev sheafStalk (x : X) : TopCat.Sheaf AddCommGrpCat.{u} X ⥤ AddCommGrpCat.{u} :=
  TopCat.Sheaf.forget AddCommGrpCat.{u} X ⋙ stalkFunctor AddCommGrpCat.{u} x

/-- Stalks of formal coproducts of free opens, in membership coordinates. -/
def freeCoproductStalkIso (A : FormalCoproduct.{u} (Opens X)) (x : X) :
    (sheafStalk x).obj ((freeCoproductFunctor (X := X)).obj A) ≅
      ∐ (fun a ↦ AddCommGrpCat.of (OpenFiber (A.obj a) x →₀ ℤ)) :=
  PreservesCoproduct.iso (sheafStalk x) (fun a ↦ freeOpen (A.obj a)) ≪≫
    Sigma.mapIso (fun a ↦ freeOpenStalkIso (A.obj a) x)

/-- Each coproduct injection becomes the injection of the corresponding stalk group. -/
@[reassoc]
lemma freeCoproductStalkIso_ι (A : FormalCoproduct.{u} (Opens X)) (x : X) (a : A.I) :
    (sheafStalk x).map (Sigma.ι (fun b ↦ freeOpen (A.obj b)) a) ≫
      (freeCoproductStalkIso A x).hom =
    (freeOpenStalkIso (A.obj a) x).hom ≫
      Sigma.ι (fun b ↦ AddCommGrpCat.of (OpenFiber (A.obj b) x →₀ ℤ)) a := by
  have h : (PreservesCoproduct.iso (sheafStalk x) (fun b ↦ freeOpen (A.obj b))).hom =
      inv (sigmaComparison (sheafStalk x) (fun b ↦ freeOpen (A.obj b))) := by
    simp only [← PreservesCoproduct.inv_hom, IsIso.Iso.inv_inv]
  simp only [freeCoproductStalkIso, Iso.trans_hom, h,
    map_ι_comp_inv_sigmaComparison_assoc, Sigma.ι_mapIso_hom]

/-- A formal coproduct map acts by its index map and the induced membership maps. -/
def freeCoproductStalkMap {A B : FormalCoproduct.{u} (Opens X)} (f : A ⟶ B) (x : X) :
    (∐ fun a ↦ AddCommGrpCat.of (OpenFiber (A.obj a) x →₀ ℤ)) ⟶
      ∐ (fun b ↦ AddCommGrpCat.of (OpenFiber (B.obj b) x →₀ ℤ)) :=
  Sigma.desc fun a ↦ freeOpenStalkMap (f.φ a) x ≫
    Sigma.ι (fun b ↦ AddCommGrpCat.of (OpenFiber (B.obj b) x →₀ ℤ)) (f.f a)

/-- The coproduct stalk comparison is natural in all formal coproduct maps. -/
@[reassoc]
lemma freeCoproductStalkIso_naturality {A B : FormalCoproduct.{u} (Opens X)}
    (f : A ⟶ B) (x : X) :
    (sheafStalk x).map ((freeCoproductFunctor (X := X)).map f) ≫ (freeCoproductStalkIso B x).hom =
      (freeCoproductStalkIso A x).hom ≫ freeCoproductStalkMap f x := by
  apply (cancel_epi
    (PreservesCoproduct.iso (sheafStalk x) (fun a ↦ freeOpen (A.obj a))).inv).mp
  apply Sigma.hom_ext
  intro a
  simp only [PreservesCoproduct.inv_hom, ι_comp_sigmaComparison_assoc]
  rw [← Functor.map_comp_assoc]
  change (sheafStalk x).map (Sigma.ι _ a ≫ Sigma.desc _) ≫ _ = _
  rw [Sigma.ι_comp_desc, Functor.map_comp, Category.assoc]
  change (sheafStalk x).map (freeOpenMap (f.φ a)) ≫
      (sheafStalk x).map (Sigma.ι (fun b ↦ freeOpen (B.obj b)) (f.f a)) ≫
        (freeCoproductStalkIso B x).hom = _
  rw [freeCoproductStalkIso_ι]
  erw [freeCoproductStalkIso_ι_assoc A x a]
  dsimp only [freeCoproductStalkMap]
  rw [Sigma.ι_comp_desc]
  exact freeOpenStalkIso_naturality_assoc (f.φ a) x _

variable (U : ι → Opens X)

/-- Positive-degree stalks of the augmented complex are coproducts of membership groups. -/
def freeAugmentedStalkIso (n : ℕ) (x : X) :
    (sheafStalk x).obj ((freeAugmented U).X (n + 1)) ≅
      ∐ (fun a : Fin (n + 1) → ι ↦ AddCommGrpCat.of (OpenFiber (V U n a) x →₀ ℤ)) :=
  (sheafStalk x).mapIso (freeAugmentedTermIso U n) ≪≫
    freeCoproductStalkIso (FormalCoproduct.mk _ (V U n)) x

/-- The term comparison respects the summand coordinates used in the differential formula. -/
@[reassoc]
lemma freeAugmentedStalkIso_ι (n : ℕ) (x : X) (a : Fin (n + 1) → ι) :
    (sheafStalk x).map (freeAugmentedι U n a) ≫ (freeAugmentedStalkIso U n x).hom =
      (freeOpenStalkIso (V U n a) x).hom ≫
        Sigma.ι (fun b ↦ AddCommGrpCat.of (OpenFiber (V U n b) x →₀ ℤ)) a := by
  dsimp only [freeAugmentedStalkIso, Iso.trans_hom, Functor.mapIso_hom]
  rw [← Functor.map_comp_assoc]
  simp only [freeAugmentedι, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  exact freeCoproductStalkIso_ι (FormalCoproduct.mk _ (V U n)) x a

/-- A membership group included in the stalk of a positive-degree term. -/
def freeAugmentedStalkι (n : ℕ) (x : X) (a : Fin (n + 1) → ι) :
    AddCommGrpCat.of (OpenFiber (V U n a) x →₀ ℤ) ⟶
      (sheafStalk x).obj ((freeAugmented U).X (n + 1)) :=
  (freeOpenStalkIso (V U n a) x).inv ≫ (sheafStalk x).map (freeAugmentedι U n a)

/-- These maps are the coproduct injections in the stalk coordinates. -/
@[reassoc (attr := simp)]
lemma freeAugmentedStalkι_iso (n : ℕ) (x : X) (a : Fin (n + 1) → ι) :
    freeAugmentedStalkι U n x a ≫ (freeAugmentedStalkIso U n x).hom =
      Sigma.ι (fun b ↦ AddCommGrpCat.of (OpenFiber (V U n b) x →₀ ℤ)) a := by
  rw [freeAugmentedStalkι, Category.assoc, freeAugmentedStalkIso_ι,
    Iso.inv_hom_id_assoc]

/-- On stalk summands, the differential deletes an entry and carries membership along it. -/
lemma freeAugmentedStalkι_d (n : ℕ) (x : X) (a : Fin (n + 2) → ι) :
    freeAugmentedStalkι U (n + 1) x a ≫
      (sheafStalk x).map ((freeAugmented U).d (n + 2) (n + 1)) =
    ∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) •
      (freeOpenStalkMap (faceInclusion U n a i) x ≫
        freeAugmentedStalkι U n x (a ∘ i.succAbove)) := by
  dsimp only [freeAugmentedStalkι]
  rw [Category.assoc, ← Functor.map_comp, freeAugmentedι_d,
    Functor.map_sum, Preadditive.comp_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [Functor.map_zsmul, Preadditive.comp_zsmul, Functor.map_comp]
  congr 1
  exact freeOpenStalkIso_inv_naturality_assoc (faceInclusion U n a i) x _

end FLT.Mazur.CechFreeResolution
