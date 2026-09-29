/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ProjectiveTwistTensor
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Free
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor

/-!
# Zero twists and twists of finite free sheaves

The concrete sheaf tensor is additive in each variable. It therefore commutes
with finite coproducts, giving a canonical comparison between a twist of a finite
free sheaf and a finite sum of twisting sheaves. The degree-zero twist is
naturally isomorphic to the identity functor.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Limits TensorProduct
open FLT.Mazur.FCurve

universe u

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

namespace FLT.Mazur.FCurve.ModuleSheafTensor

variable {X : Scheme.{u}}

@[simp]
lemma pure_add_left (M N : X.Modules) (U : X.Opens)
    (m m' : Γ(M, U)) (n : Γ(N, U)) :
    pure M N U (m + m') n = pure M N U m n + pure M N U m' n := by
  simp [pure, add_tmul]

@[simp]
lemma pure_add_right (M N : X.Modules) (U : X.Opens)
    (m : Γ(M, U)) (n n' : Γ(N, U)) :
    pure M N U m (n + n') = pure M N U m n + pure M N U m n' := by
  simp [pure, tmul_add]

/-- Tensor morphisms are additive in their first argument. -/
lemma map_add_left {M M' N N' : X.Modules} (f f' : M ⟶ M') (g : N ⟶ N') :
    map (f + f') g = map f g + map f' g := by
  apply hom_ext
  intro U m n
  simp [Scheme.Modules.Hom.add_app]

/-- Tensor morphisms are additive in their second argument. -/
lemma map_add_right {M M' N N' : X.Modules} (f : M ⟶ M') (g g' : N ⟶ N') :
    map f (g + g') = map f g + map f g' := by
  apply hom_ext
  intro U m n
  simp [Scheme.Modules.Hom.add_app]

/-- Tensoring on the right by a fixed module sheaf. -/
def rightFunctor (N : X.Modules) : X.Modules ⥤ X.Modules where
  obj M := tensor M N
  map f := map f (𝟙 N)
  map_id M := map_id M N
  map_comp f g := by simpa using map_comp f g (𝟙 N) (𝟙 N)

instance rightFunctor_additive (N : X.Modules) : (rightFunctor N).Additive where
  map_add := map_add_left _ _ (𝟙 N)

/-- Tensoring on the left by a fixed module sheaf. -/
def leftFunctor (M : X.Modules) : X.Modules ⥤ X.Modules where
  obj N := tensor M N
  map f := map (𝟙 M) f
  map_id N := map_id M N
  map_comp f g := by simpa using map_comp (𝟙 M) (𝟙 M) f g

instance leftFunctor_additive (M : X.Modules) : (leftFunctor M).Additive where
  map_add := map_add_right (𝟙 M) _ _

/-- Tensoring commutes with every finite coproduct in the first variable. -/
def finiteCoproductIso (N : X.Modules) (I : Type u) [Finite I] (M : I → X.Modules) :
    tensor (∐ M) N ≅ ∐ (fun i ↦ tensor (M i) N) :=
  PreservesCoproduct.iso (rightFunctor N) M

/-- The coproduct comparison is determined by the tensor of each inclusion. -/
@[reassoc (attr := simp)]
lemma ι_finiteCoproductIso_inv (N : X.Modules) (I : Type u) [Finite I]
    (M : I → X.Modules) (i : I) :
    Sigma.ι (fun j ↦ tensor (M j) N) i ≫ (finiteCoproductIso N I M).inv =
      map (Sigma.ι M i) (𝟙 N) := by
  exact ι_comp_sigmaComparison (rightFunctor N) M i

/-- A tensor of a finite free sheaf is a finite sum of the other factor. -/
def freeTensorIso (N : X.Modules) (I : Type u) [Finite I] :
    tensor (SheafOfModules.free (R := X.ringCatSheaf) I) N ≅ ∐ (fun _ : I ↦ N) :=
  finiteCoproductIso N I (fun _ ↦ SheafOfModules.unit X.ringCatSheaf) ≪≫
    Sigma.mapIso (fun _ ↦ leftUnitor N)

/-- The inverse finite-free comparison sends each summand through its free generator. -/
@[reassoc (attr := simp)]
lemma ι_freeTensorIso_inv (N : X.Modules) (I : Type u) [Finite I] (i : I) :
    Sigma.ι (fun _ : I ↦ N) i ≫ (freeTensorIso N I).inv =
      (leftUnitor N).inv ≫ map (SheafOfModules.ιFree i) (𝟙 N) := by
  simp [freeTensorIso, SheafOfModules.ιFree]

/-- Forward coordinates of each free generator select its summand. -/
@[reassoc (attr := simp)]
lemma map_ιFree_freeTensorIso_hom (N : X.Modules) (I : Type u) [Finite I] (i : I) :
    map (SheafOfModules.ιFree i) (𝟙 N) ≫ (freeTensorIso N I).hom =
      (leftUnitor N).hom ≫ Sigma.ι (fun _ : I ↦ N) i := by
  apply (cancel_mono (freeTensorIso N I).inv).mp
  simp

/-- The finite-free comparison sends a pure generator tensor to its scalar multiple. -/
lemma freeTensorIso_pure_generator (N : X.Modules) (I : Type u) [Finite I]
    (i : I) (U : X.Opens) (r : Γ(X, U)) (n : Γ(N, U)) :
    (freeTensorIso N I).hom.app U
      (pure (SheafOfModules.free I) N U
        ((SheafOfModules.ιFree (R := X.ringCatSheaf) i).val.app (.op U) r) n) =
      (Sigma.ι (fun _ : I ↦ N) i).app U (r • n) := by
  have h := congrArg (fun f ↦ f.app U
    (pure (SheafOfModules.unit X.ringCatSheaf) N U r n))
      (map_ιFree_freeTensorIso_hom N I i)
  change (freeTensorIso N I).hom.app U
    ((map (SheafOfModules.ιFree i) (𝟙 N)).app U
      (pure (SheafOfModules.unit X.ringCatSheaf) N U r n)) =
    (Sigma.ι (fun _ : I ↦ N) i).app U
      ((leftUnitor N).hom.app U (pure (SheafOfModules.unit X.ringCatSheaf) N U r n)) at h
  rw [map_pure, leftUnitor_pure] at h
  exact h

/-- The right unit comparison commutes with arbitrary module morphisms. -/
@[reassoc]
lemma rightUnitor_naturality {M N : X.Modules} (f : M ⟶ N) :
    map f (𝟙 (SheafOfModules.unit X.ringCatSheaf)) ≫ (rightUnitor N).hom =
      (rightUnitor M).hom ≫ f := by
  apply hom_ext
  intro U m r
  change (rightUnitor N).hom.app U ((map f (𝟙 _)).app U _) =
    f.app U ((rightUnitor M).hom.app U _)
  rw [map_pure, rightUnitor_pure, rightUnitor_pure]
  exact ((f.val.app (.op U)).hom.map_smul r m).symm

end FLT.Mazur.FCurve.ModuleSheafTensor

namespace FLT.Mazur.ProjectiveSpace

open ModuleSheafTensor

variable (R : Type u) [CommRing R] (ι : Type u)

/-- Twisting, including its action on all sheaf morphisms. -/
def twistTensorFunctor (d : ℤ) : (space R ι).Modules ⥤ (space R ι).Modules :=
  rightFunctor (twistingSheaf R ι d)

instance twistTensorFunctor_additive (d : ℤ) : (twistTensorFunctor R ι d).Additive :=
  inferInstanceAs (rightFunctor (twistingSheaf R ι d)).Additive

/-- Tensoring with the zero twisting sheaf is canonically the identity. -/
def twistTensorZeroIso (F : (space R ι).Modules) : twistTensor R ι F 0 ≅ F :=
  rightTrivialIso F (twistingSheafZeroIso R ι)

/-- The zero-twist comparison is natural in the arbitrary sheaf being twisted. -/
@[reassoc]
lemma twistTensorZeroIso_naturality {F G : (space R ι).Modules} (f : F ⟶ G) :
    (twistTensorFunctor R ι 0).map f ≫ (twistTensorZeroIso R ι G).hom =
      (twistTensorZeroIso R ι F).hom ≫ f := by
  let e := twistingSheafZeroIso R ι
  change map f (𝟙 _) ≫ (map (𝟙 G) e.hom ≫ (rightUnitor G).hom) =
    (map (𝟙 F) e.hom ≫ (rightUnitor F).hom) ≫ f
  rw [← map_comp_assoc]
  simp only [Category.comp_id, Category.id_comp]
  rw [Category.assoc, ← rightUnitor_naturality, ← map_comp_assoc]
  simp only [Category.id_comp]
  exact congrArg (fun g : twistingSheaf R ι 0 ⟶ structureModule (space R ι) ↦
    map f g ≫ (rightUnitor G).hom) (Category.comp_id e.hom).symm

/-- The degree-zero twist functor is naturally isomorphic to the identity. -/
def twistTensorZeroNatIso : twistTensorFunctor R ι 0 ≅ 𝟭 (space R ι).Modules :=
  NatIso.ofComponents (twistTensorZeroIso R ι) (fun f ↦
    twistTensorZeroIso_naturality R ι f)

/-- A finite free twist is the actual finite coproduct of copies of `O(d)`. -/
def twistTensorFreeIso (d : ℤ) (I : Type u) [Finite I] :
    twistTensor R ι (SheafOfModules.free I) d ≅ ∐ (fun _ : I ↦ twistingSheaf R ι d) :=
  freeTensorIso (twistingSheaf R ι d) I

/-- Each free generator corresponds to the matching summand of twists. -/
@[reassoc (attr := simp)]
lemma twistTensorFreeIso_generator (d : ℤ) (I : Type u) [Finite I] (i : I) :
    map (SheafOfModules.ιFree i) (𝟙 (twistingSheaf R ι d)) ≫
      (twistTensorFreeIso R ι d I).hom =
    (leftUnitor (twistingSheaf R ι d)).hom ≫
      Sigma.ι (fun _ : I ↦ twistingSheaf R ι d) i :=
  map_ιFree_freeTensorIso_hom (twistingSheaf R ι d) I i

end FLT.Mazur.ProjectiveSpace
