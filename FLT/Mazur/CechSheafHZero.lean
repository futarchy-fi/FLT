/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CechSheafH
public import Mathlib.Algebra.Category.Grp.Biproducts
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.CategoryTheory.Limits.Lattice
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Cech

/-!
# Categorical Cech cohomology in degree zero

Product coordinates identify the categorical first differential with the
ordered-pair differential on sections.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open scoped Simplicial

universe u

namespace FLT.Mazur.CechSheafHZero

variable {X : TopCat.{u}} {ι : Type u} (U : ι → Opens X)

/-- The categorical Cech complex. -/
abbrev C (F : TopCat.Sheaf AddCommGrpCat.{u} X) := (cechComplexFunctor U).obj F.obj

/-- Categorical Cech cohomology. -/
abbrev CH (F : TopCat.Sheaf AddCommGrpCat.{u} X) (n : ℕ) := (C U F).homology n

/-- The induced map on categorical Cech cohomology. -/
abbrev CHmap {F G : TopCat.Sheaf AddCommGrpCat.{u} X} (f : F ⟶ G) (n : ℕ) :=
  HomologicalComplex.homologyMap ((cechComplexFunctor U).map f.hom) n

/-- The intersection indexed by a tuple. -/
abbrev V (n : ℕ) (a : Fin (n + 1) → ι) : Opens X := ⨅ j, U (a j)

lemma productOpen_eq (n : ℕ) (a : Fin (n + 1) → ι) :
    ∏ᶜ (U ∘ a) = V U n a := by
  change limit (Discrete.functor (U ∘ a)) = _
  rw [CategoryTheory.Limits.CompleteLattice.limit_eq_iInf]
  apply le_antisymm
  · exact le_iInf fun j ↦ iInf_le _ (Discrete.mk j)
  · exact le_iInf fun j ↦ iInf_le (fun k ↦ U (a k)) j.as

/-- Categorical products of abelian groups have dependent-function coordinates. -/
def productIso (A : ι → AddCommGrpCat.{u}) :
    ∏ᶜ A ≅ AddCommGrpCat.of (∀ i, A i) :=
  (limit.isLimit _).conePointUniqueUpToIso (AddCommGrpCat.HasLimit.productLimitCone A).isLimit

lemma productIso_apply (A : ι → AddCommGrpCat.{u}) (x : (∏ᶜ A : AddCommGrpCat.{u})) (i : ι) :
    (productIso A).hom x i = Pi.π A i x := rfl

/-- The actual categorical term in dependent-function coordinates. -/
def termEquiv (F : TopCat.Sheaf AddCommGrpCat.{u} X) (n : ℕ) :
    (C U F).X n ≃+ (∀ a : Fin (n + 1) → ι, F.obj.obj (op (V U n a))) :=
  (productIso (fun a : Fin (n + 1) → ι ↦ F.obj.obj (op (∏ᶜ (U ∘ a))))
    ).addCommGroupIsoToAddEquiv.trans (AddEquiv.piCongrRight fun a ↦
      (F.obj.mapIso (eqToIso (congrArg op (productOpen_eq U n a)))).addCommGroupIsoToAddEquiv)

lemma termEquiv_apply (F : TopCat.Sheaf AddCommGrpCat.{u} X) (n : ℕ) (x : (C U F).X n)
    (a : Fin (n + 1) → ι) :
    termEquiv U F n x a = F.obj.map (eqToHom
      (congrArg op (productOpen_eq U n a))) (Pi.π (fun b ↦ F.obj.obj (op (∏ᶜ (U ∘ b)))) a x) := rfl

/-- One-entry tuples are indexed by their unique entry. -/
def singleIndex : (Fin 1 → ι) ≃ ι where
  toFun a := a 0
  invFun i _ := i
  left_inv a := by ext j; have : j = 0 := Subsingleton.elim _ _; simp [this]
  right_inv _ := rfl

/-- Two-entry tuples correspond to ordered pairs, in order. -/
def pairIndex : (Fin 2 → ι) ≃ ι × ι where
  toFun a := (a 0, a 1)
  invFun p := ![p.1, p.2]
  left_inv a := by ext j; fin_cases j <;> rfl
  right_inv _ := rfl

/-- Reindexing dependent families as an additive equivalence. -/
def reindexEquiv {α β : Type u} (A : β → Type u) [∀ b, AddCommGroup (A b)]
    (e : α ≃ β) : (∀ a, A (e a)) ≃+ (∀ b, A b) where
  __ := Equiv.piCongrLeft A e
  map_add' x y := by
    funext b
    obtain ⟨a, rfl⟩ := e.surjective b
    exact Equiv.piCongrLeft_apply_apply A e (x + y) a |>.trans
      (congrArg₂ (· + ·) (Equiv.piCongrLeft_apply_apply A e x a).symm
        (Equiv.piCongrLeft_apply_apply A e y a).symm)

lemma singleOpen_eq (a : Fin 1 → ι) : V U 0 a = U (a 0) := by
  simp [V]

lemma pairOpen_eq (a : Fin 2 → ι) : V U 1 a = U (a 0) ⊓ U (a 1) := by
  apply le_antisymm
  · exact le_inf (iInf_le _ 0) (iInf_le _ 1)
  · apply le_iInf
    intro j
    fin_cases j
    · exact inf_le_left
    · exact inf_le_right

/-- Degree-zero coordinates, indexed by cover members. -/
def zeroTermEquiv (F : TopCat.Sheaf AddCommGrpCat.{u} X) :
    (C U F).X 0 ≃+ (∀ i, F.obj.obj (op (U i))) :=
  (termEquiv U F 0).trans ((AddEquiv.piCongrRight fun a ↦
    (F.obj.mapIso (eqToIso (congrArg op (singleOpen_eq U a)))).addCommGroupIsoToAddEquiv).trans
    (reindexEquiv (fun i ↦ F.obj.obj (op (U i))) singleIndex))

/-- Degree-one coordinates, indexed by ordered pairs. -/
def oneTermEquiv (F : TopCat.Sheaf AddCommGrpCat.{u} X) :
    (C U F).X 1 ≃+ (∀ p : ι × ι, F.obj.obj (op (U p.1 ⊓ U p.2))) :=
  (termEquiv U F 1).trans ((AddEquiv.piCongrRight fun a ↦
    (F.obj.mapIso (eqToIso (congrArg op (pairOpen_eq U a)))).addCommGroupIsoToAddEquiv).trans
    (reindexEquiv (fun p : ι × ι ↦ F.obj.obj (op (U p.1 ⊓ U p.2))) pairIndex))

lemma zeroTermEquiv_apply (F : TopCat.Sheaf AddCommGrpCat.{u} X)
    (x : (C U F).X 0) (i : ι) :
    zeroTermEquiv U F x i = F.obj.map (eqToHom (congrArg op
      ((productOpen_eq U 0 (fun _ ↦ i)).trans (singleOpen_eq U _))))
      (Pi.π (fun a : Fin 1 → ι ↦ F.obj.obj (op (∏ᶜ (U ∘ a)))) (fun _ ↦ i) x) := by
  change F.obj.map _ (F.obj.map _ _) = _
  rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
  rfl

lemma oneTermEquiv_apply (F : TopCat.Sheaf AddCommGrpCat.{u} X)
    (x : (C U F).X 1) (p : ι × ι) :
    oneTermEquiv U F x p = F.obj.map (eqToHom (congrArg op
      ((productOpen_eq U 1 ![p.1, p.2]).trans (pairOpen_eq U _))))
      (Pi.π (fun a : Fin 2 → ι ↦ F.obj.obj (op (∏ᶜ (U ∘ a)))) ![p.1, p.2] x) := by
  change F.obj.map _ (F.obj.map _ _) = _
  rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
  rfl

/-- The cosimplicial object underlying the Cech complex. -/
abbrev cosimplicial (F : TopCat.Sheaf AddCommGrpCat.{u} X) :=
  (FormalCoproduct.cosimplicialObjectFunctor (FormalCoproduct.mk _ U).cech).obj F.obj

lemma first_d (F : TopCat.Sheaf AddCommGrpCat.{u} X) :
    (C U F).d 0 1 = (cosimplicial U F).δ 0 - (cosimplicial U F).δ 1 := by
  change CochainComplex.of.d _ _ 0 (0 + 1) = _
  rw [CochainComplex.of_d]
  simp [AlgebraicTopology.AlternatingCofaceMapComplex.objD, Fin.sum_univ_two,
    sub_eq_add_neg]

lemma coface_π (F : TopCat.Sheaf AddCommGrpCat.{u} X) (k : Fin 2) (a : Fin 2 → ι) :
    (cosimplicial U F).δ k ≫
      Pi.π (fun b : Fin 2 → ι ↦ F.obj.obj (op (∏ᶜ (U ∘ b)))) a =
    Pi.π (fun b : Fin 1 → ι ↦ F.obj.obj (op (∏ᶜ (U ∘ b)))) (a ∘ k.succAbove) ≫
      F.obj.map (Pi.lift (fun j : Fin 1 ↦ Pi.π (U ∘ a) (k.succAbove j))).op := by
  change Pi.lift _ ≫ Pi.π _ a = _
  rw [Pi.lift_comp_π]
  rfl

lemma projection_restrict_congr (F : TopCat.Sheaf AddCommGrpCat.{u} X)
    {a b : Fin 1 → ι} (h : a = b) {W : Opens X}
    (g : op (∏ᶜ (U ∘ a)) ⟶ op W) (g' : op (∏ᶜ (U ∘ b)) ⟶ op W) :
    Pi.π (fun c : Fin 1 → ι ↦ F.obj.obj (op (∏ᶜ (U ∘ c)))) a ≫ F.obj.map g =
      Pi.π (fun c : Fin 1 → ι ↦ F.obj.obj (op (∏ᶜ (U ∘ c)))) b ≫ F.obj.map g' := by
  subst b
  rw [Subsingleton.elim g g']

/-- The first alternating coface sum has the ordered-pair sign convention. -/
lemma differentialZero_coordinates (F : TopCat.Sheaf AddCommGrpCat.{u} X)
    (x : (C U F).X 0) :
    oneTermEquiv U F ((C U F).d 0 1 x) =
      CechSheafH.differentialZero F U (zeroTermEquiv U F x) := by
  ext p
  rw [oneTermEquiv_apply, first_d]
  change F.obj.map _ (Pi.π (fun a : Fin 2 → ι ↦ F.obj.obj (op (∏ᶜ (U ∘ a))))
    ![p.1, p.2] ((cosimplicial U F).δ 0 x - (cosimplicial U F).δ 1 x)) = _
  simp only [map_sub]
  simp only [← ConcreteCategory.comp_apply]
  erw [← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply]
  simp only [← Category.assoc, coface_π]
  change _ = F.obj.map (homOfLE inf_le_right).op (zeroTermEquiv U F x p.2) -
    F.obj.map (homOfLE inf_le_left).op (zeroTermEquiv U F x p.1)
  rw [zeroTermEquiv_apply, zeroTermEquiv_apply]
  have h0 : ![p.1, p.2] ∘ (0 : Fin 2).succAbove = fun _ : Fin 1 ↦ p.2 := by
    ext j; fin_cases j; rfl
  have h1 : ![p.1, p.2] ∘ (1 : Fin 2).succAbove = fun _ : Fin 1 ↦ p.1 := by
    ext j; fin_cases j; rfl
  simp only [Category.assoc, ← Functor.map_comp]
  congr 1
  all_goals
    erw [← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply]
    apply ConcreteCategory.congr_hom
    simp only [← Functor.map_comp]
  · exact projection_restrict_congr U F h0 _ _
  · exact projection_restrict_congr U F h1 _ _


lemma coordinates_mem_iff (F : TopCat.Sheaf AddCommGrpCat.{u} X) (x : (C U F).X 0) :
    zeroTermEquiv U F x ∈ CechSheafH.zeroCocycles F U ↔ (C U F).d 0 1 x = 0 := by
  change CechSheafH.differentialZero F U (zeroTermEquiv U F x) = 0 ↔ _
  rw [← differentialZero_coordinates, (oneTermEquiv U F).map_eq_zero_iff]

/-- Categorical zero-cocycles are exactly compatible families of sections. -/
lemma d_zero_iff_compatible (F : TopCat.Sheaf AddCommGrpCat.{u} X)
    (x : (C U F).X 0) :
    (C U F).d 0 1 x = 0 ↔ TopCat.Presheaf.IsCompatible F.obj U (zeroTermEquiv U F x) :=
  (coordinates_mem_iff U F x).symm.trans (CechSheafH.mem_zeroCocycles_iff F U _)

/-- The concrete kernels agree under the coordinate equivalence. -/
def kernelEquiv (F : TopCat.Sheaf AddCommGrpCat.{u} X) :
    ((C U F).d 0 1).hom.ker ≃+ CechSheafH.zeroCocycles F U where
  toFun x := ⟨zeroTermEquiv U F x, (coordinates_mem_iff U F x).mpr x.property⟩
  invFun y := ⟨(zeroTermEquiv U F).symm y, (coordinates_mem_iff U F _).mp
    (by simpa only [AddEquiv.apply_symm_apply] using y.property)⟩
  left_inv x := Subtype.ext ((zeroTermEquiv U F).symm_apply_apply x)
  right_inv y := Subtype.ext ((zeroTermEquiv U F).apply_symm_apply y)
  map_add' x y := Subtype.ext (map_add (zeroTermEquiv U F) x.val y.val)

/-- Cycles at the first degree are the concrete kernel of the first differential. -/
def cyclesKernelIso (F : TopCat.Sheaf AddCommGrpCat.{u} X) :
    (C U F).cycles 0 ≅ AddCommGrpCat.of ((C U F).d 0 1).hom.ker :=
  ((C U F).cyclesIsKernel 0 1 (by simp)).conePointUniqueUpToIso
    (kernelIsKernel ((C U F).d 0 1)) ≪≫ AddCommGrpCat.kernelIsoKer ((C U F).d 0 1)

lemma cyclesKernelIso_apply (F : TopCat.Sheaf AddCommGrpCat.{u} X)
    (x : (C U F).cycles 0) :
    ((cyclesKernelIso U F).hom x).val = (C U F).iCycles 0 x := by
  change kernel.ι ((C U F).d 0 1)
    (kernel.lift ((C U F).d 0 1) ((C U F).iCycles 0) _ x) = _
  exact ConcreteCategory.congr_hom (kernel.lift_ι _ _ _) x

/-- Categorical degree-zero homology equals the explicit zero-cocycle group. -/
def zeroHomologyEquiv (F : TopCat.Sheaf AddCommGrpCat.{u} X) :
    CH U F 0 ≃+ CechSheafH.zeroCocycles F U :=
  (CochainComplex.isoHomologyπ₀ (C U F)).symm.addCommGroupIsoToAddEquiv.trans
    ((cyclesKernelIso U F).addCommGroupIsoToAddEquiv.trans (kernelEquiv U F))

lemma zeroHomologyEquiv_apply (F : TopCat.Sheaf AddCommGrpCat.{u} X) (x : CH U F 0) :
    (zeroHomologyEquiv U F x).val =
      zeroTermEquiv U F ((C U F).iCycles 0 ((C U F).isoHomologyπ₀.inv x)) := by
  change zeroTermEquiv U F (((cyclesKernelIso U F).hom _).val) = _
  rw [cyclesKernelIso_apply]
  rfl

lemma zeroTermEquiv_naturality {F G : TopCat.Sheaf AddCommGrpCat.{u} X}
    (f : F ⟶ G) (x : (C U F).X 0) (i : ι) :
    zeroTermEquiv U G (((cechComplexFunctor U).map f.hom).f 0 x) i =
      f.hom.app (op (U i)) (zeroTermEquiv U F x i) := by
  rw [zeroTermEquiv_apply, zeroTermEquiv_apply]
  change G.obj.map _ (Pi.π (fun a : Fin 1 → ι ↦ G.obj.obj (op (∏ᶜ (U ∘ a))))
    (fun _ ↦ i) ((Limits.Pi.map (fun a : Fin 1 → ι ↦ f.hom.app (op (∏ᶜ (U ∘ a))))) x)) = _
  erw [← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply,
    ← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply]
  apply ConcreteCategory.congr_hom
  rw [← Category.assoc, Pi.map_π, Category.assoc, f.hom.naturality]

/-- The categorical comparison is natural in the coefficient sheaf. -/
lemma zeroHomologyEquiv_naturality {F G : TopCat.Sheaf AddCommGrpCat.{u} X}
    (f : F ⟶ G) (x : CH U F 0) :
    zeroHomologyEquiv U G (CHmap U f 0 x) =
      CechSheafH.zeroCocyclesMap U f (zeroHomologyEquiv U F x) := by
  apply Subtype.ext
  rw [zeroHomologyEquiv_apply]
  have h := ConcreteCategory.congr_hom
    (CochainComplex.isoHomologyπ₀_inv_naturality ((cechComplexFunctor U).map f.hom)) x
  rw [show (C U G).isoHomologyπ₀.inv (CHmap U f 0 x) =
    HomologicalComplex.cyclesMap ((cechComplexFunctor U).map f.hom) 0
      ((C U F).isoHomologyπ₀.inv x) from h]
  have h' := ConcreteCategory.congr_hom
    (HomologicalComplex.cyclesMap_i ((cechComplexFunctor U).map f.hom) 0)
    ((C U F).isoHomologyπ₀.inv x)
  erw [show (C U G).iCycles 0 _ = _ from h']
  funext i
  change zeroTermEquiv U G (((cechComplexFunctor U).map f.hom).f 0
    ((C U F).iCycles 0 ((C U F).isoHomologyπ₀.inv x))) i = _
  rw [zeroTermEquiv_naturality]
  change _ = f.hom.app (op (U i)) ((zeroHomologyEquiv U F x).val i)
  rw [zeroHomologyEquiv_apply]

end FLT.Mazur.CechSheafHZero
