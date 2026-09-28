/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CechFreeExact
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.CategoryTheory.Abelian.Injective.Basic

/-!
# Injective coefficients have no positive Cech cohomology

Maps from the free terms are identified with Cech cochains. Exactness of the
augmented free complex and exactness of Hom into an injective give vanishing
in every positive degree.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open scoped Simplicial
open FLT.Mazur.CechFreeOpen FLT.Mazur.CechFreeResolution FLT.Mazur.CechSheafHZero

universe u

namespace FLT.Mazur.CechInjectiveAcyclic

variable {X : TopCat.{u}} {ι : Type u} (U : ι → Opens X)
variable (F : TopCat.Sheaf AddCommGrpCat.{u} X)

/-- Maps from a coproduct are families of maps, additively. -/
def coproductHomEquiv {α : Type u} (A : α → TopCat.Sheaf AddCommGrpCat.{u} X) :
    (∐ A ⟶ F) ≃+ (∀ a, A a ⟶ F) where
  toFun f a := Sigma.ι A a ≫ f
  invFun f := Sigma.desc f
  left_inv f := by apply Sigma.hom_ext; intro a; simp
  right_inv f := by funext a; simp
  map_add' f g := by funext a; simp

/-- Hom from a free term is the corresponding group of Cech cochains. -/
def homTermEquiv (n : ℕ) : ((freeComplex U).X n ⟶ F) ≃+ (C U F).X n :=
  ((coproductHomEquiv F (fun a : Fin (n + 1) → ι ↦ freeOpen (∏ᶜ (U ∘ a)))).trans
    (AddEquiv.piCongrRight fun a ↦ freeOpenHomEquiv (∏ᶜ (U ∘ a)) F)).trans
      (productIso (fun a : Fin (n + 1) → ι ↦ F.obj.obj (op (∏ᶜ (U ∘ a))))
        ).addCommGroupIsoToAddEquiv.symm

lemma homTermEquiv_π (n : ℕ) (f : (freeComplex U).X n ⟶ F)
    (a : Fin (n + 1) → ι) :
    Pi.π (fun b : Fin (n + 1) → ι ↦ F.obj.obj (op (∏ᶜ (U ∘ b)))) a
      (homTermEquiv U F n f) =
    freeOpenHomEquiv (∏ᶜ (U ∘ a)) F
      (Sigma.ι (fun b : Fin (n + 1) → ι ↦ freeOpen (∏ᶜ (U ∘ b))) a ≫ f) := by
  change (productIso _).hom ((productIso _).inv _) a = _
  rw [← ConcreteCategory.comp_apply, Iso.inv_hom_id]
  rfl

/-- Evaluation intertwines one free face with its Cech coface. -/
lemma homTermEquiv_face (n : ℕ) (i : Fin (n + 2))
    (f : (freeComplex U).X n ⟶ F) :
    homTermEquiv U F (n + 1) ((freeSimplicial U).δ i ≫ f) =
      (cosimplicial U F).δ i (homTermEquiv U F n f) := by
  apply (productIso _).addCommGroupIsoToAddEquiv.injective
  funext a
  change Pi.π (fun b : Fin (n + 2) → ι ↦ F.obj.obj (op (∏ᶜ (U ∘ b)))) a _ =
    Pi.π (fun b : Fin (n + 2) → ι ↦ F.obj.obj (op (∏ᶜ (U ∘ b)))) a _
  rw [homTermEquiv_π]
  have hface :
      Sigma.ι (fun b : Fin (n + 2) → ι ↦ freeOpen (∏ᶜ (U ∘ b))) a ≫
        (freeSimplicial U).δ i =
      freeOpenMap (Pi.lift (fun j : Fin (n + 1) ↦ Pi.π (U ∘ a) (i.succAbove j))) ≫
        Sigma.ι (fun b : Fin (n + 1) → ι ↦ freeOpen (∏ᶜ (U ∘ b)))
          (a ∘ i.succAbove) := by
    change Sigma.ι _ a ≫ Sigma.desc _ = _
    rw [Sigma.ι_comp_desc]
    rfl
  rw [← Category.assoc, hface, Category.assoc, freeOpenHomEquiv_naturality_open]
  have hcoface : (cosimplicial U F).δ i ≫
      Pi.π (fun b : Fin (n + 2) → ι ↦ F.obj.obj (op (∏ᶜ (U ∘ b)))) a =
      Pi.π (fun b : Fin (n + 1) → ι ↦ F.obj.obj (op (∏ᶜ (U ∘ b))))
        (a ∘ i.succAbove) ≫
      F.obj.map (Pi.lift (fun j : Fin (n + 1) ↦ Pi.π (U ∘ a) (i.succAbove j))).op := by
    change Pi.lift _ ≫ Pi.π _ a = _
    rw [Pi.lift_comp_π]
    rfl
  have hc := ConcreteCategory.congr_hom hcoface (homTermEquiv U F n f)
  change Pi.π (fun b : Fin (n + 2) → ι ↦ F.obj.obj (op (∏ᶜ (U ∘ b)))) a
      ((cosimplicial U F).δ i (homTermEquiv U F n f)) =
    F.obj.map _ (Pi.π (fun b : Fin (n + 1) → ι ↦ F.obj.obj (op (∏ᶜ (U ∘ b))))
      (a ∘ i.succAbove) (homTermEquiv U F n f)) at hc
  rw [homTermEquiv_π] at hc
  exact hc.symm

/-- The identification respects the alternating differentials. -/
lemma homTermEquiv_d (n : ℕ) (f : (freeComplex U).X n ⟶ F) :
    homTermEquiv U F (n + 1) ((freeComplex U).d (n + 1) n ≫ f) =
      (C U F).d n (n + 1) (homTermEquiv U F n f) := by
  change homTermEquiv U F (n + 1)
    ((AlgebraicTopology.AlternatingFaceMapComplex.obj (freeSimplicial U)).d (n + 1) n ≫ f) = _
  rw [AlgebraicTopology.AlternatingFaceMapComplex.obj_d_eq]
  change _ = (AlgebraicTopology.AlternatingCofaceMapComplex.obj
    (cosimplicial U F)).d n (n + 1) _
  dsimp only [AlgebraicTopology.AlternatingCofaceMapComplex.obj]
  rw [CochainComplex.of_d]
  simp only [AlgebraicTopology.AlternatingCofaceMapComplex.objD, Preadditive.sum_comp,
    Preadditive.zsmul_comp, map_sum, map_zsmul, homTermEquiv_face]
  change _ = (AddCommGrpCat.homAddEquiv
    (∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) • (cosimplicial U F).δ i)) _
  simp only [map_sum, map_zsmul, AddMonoidHom.coe_finsetSum, Finset.sum_apply,
    AddMonoidHom.zsmul_apply]
  rfl

/-- Exactness of the augmented resolution survives applying Hom into an injective. -/
lemma hom_exact_of_injective (hU : iSup U = ⊤)
    (I : TopCat.Sheaf AddCommGrpCat.{u} X) [Injective I] (n : ℕ)
    (f : (freeComplex U).X (n + 1) ⟶ I)
    (hf : (freeComplex U).d (n + 2) (n + 1) ≫ f = 0) :
    ∃ g : (freeComplex U).X n ⟶ I, (freeComplex U).d (n + 1) n ≫ g = f := by
  have h := (HomologicalComplex.exactAt_iff' (freeAugmented U)
    (n + 3) (n + 2) (n + 1) (by simp) (by simp)).mp
      (freeAugmented_exactAt U hU (n + 2))
  have he := h.op.map (preadditiveYonedaObj I)
  rw [ShortComplex.moduleCat_exact_iff] at he
  change ∀ (f : (freeComplex U).X (n + 1) ⟶ I),
    (freeComplex U).d (n + 2) (n + 1) ≫ f = 0 →
    ∃ g : (freeComplex U).X n ⟶ I, (freeComplex U).d (n + 1) n ≫ g = f at he
  exact he f hf

/-- Positive-degree Cech cochains with injective coefficients are exact. -/
lemma cech_exactAt_of_injective (hU : iSup U = ⊤)
    (I : TopCat.Sheaf AddCommGrpCat.{u} X) [Injective I] (n : ℕ) :
    (C U I).ExactAt (n + 1) := by
  rw [HomologicalComplex.exactAt_iff' _ n (n + 1) (n + 2) (by simp) (by simp),
    ShortComplex.ab_exact_iff]
  intro z hz
  change (C U I).d (n + 1) (n + 2) z = 0 at hz
  let f := (homTermEquiv U I (n + 1)).symm z
  have hf : (freeComplex U).d (n + 2) (n + 1) ≫ f = 0 := by
    apply (homTermEquiv U I (n + 2)).injective
    rw [homTermEquiv_d, map_zero]
    simpa only [f, AddEquiv.apply_symm_apply] using hz
  obtain ⟨g, hg⟩ := hom_exact_of_injective U hU I n f hf
  refine ⟨homTermEquiv U I n g, ?_⟩
  change (C U I).d n (n + 1) _ = z
  rw [← homTermEquiv_d, hg]
  exact (homTermEquiv U I (n + 1)).apply_symm_apply z

/-- Every positive Cech cohomology group of an injective sheaf is zero. -/
lemma cech_isZero_of_injective (hU : iSup U = ⊤)
    (I : TopCat.Sheaf AddCommGrpCat.{u} X) [Injective I] (n : ℕ) :
    IsZero (CH U I (n + 1)) :=
  (cech_exactAt_of_injective U hU I n).isZero_homology

end FLT.Mazur.CechInjectiveAcyclic
