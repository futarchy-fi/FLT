/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ModuleSheafOpenIsoDetection
public import FLT.Mazur.ProjectiveTwistTensor

/-!
# Multiplication of twisting sheaves

Componentwise multiplication of compatible chart coefficients induces
`O(a) ⊗ O(b) → O(a + b)`. Chart evaluation identifies this map with multiplication
of regular functions, so the standard open cover detects its invertibility.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open FLT.Mazur.FCurve FLT.Mazur.FCurve.ModuleSheafUnitCocycle
open FLT.Mazur.FCurve.ModuleSheafTensor

universe u

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

namespace FLT.Mazur.FCurve.ModuleSheafUnitCocycle.Cocycle

/-- The chart map on sections is coefficient evaluation. -/
lemma onOpenIso_hom_app {X : Scheme.{u}} {κ : Type u} {U : κ → X.Opens}
    (g : Cocycle U) (i : κ) (V : X.Opens) (hi : V ≤ U i) (W : V.toScheme.Opens)
    (s : g.sections (V.ι ''ᵁ W)) :
    (g.onOpenIso i V hi).hom.app W s =
      g.evaluate i ((V.ι_image_le W).trans hi) s := rfl

/-- Evaluation transports a tensor pairing to multiplication in chart coordinates. -/
lemma tensor_coordinates {X : Scheme.{u}} {κ : Type u} {U : κ → X.Opens}
    (g h k : Cocycle U) (f : tensor g.sheaf h.sheaf ⟶ k.sheaf)
    (q : ∀ V, g.sections V → h.sections V → k.sections V)
    (hf : ∀ V s t, f.app V (pure g.sheaf h.sheaf V s t) = q V s t)
    (hq : ∀ i V hi s t, k.evaluate i hi (q V s t) =
      g.evaluate i hi s * h.evaluate i hi t)
    (i : κ) (V : X.Opens) (hi : V ≤ U i) (W : V.toScheme.Opens)
    (s : g.sections (V.ι ''ᵁ W)) (t : h.sections (V.ι ''ᵁ W)) :
    (k.onOpenIso i V hi).hom.app W
      (f.app (V.ι ''ᵁ W) (pure g.sheaf h.sheaf (V.ι ''ᵁ W) s t)) =
    (show Γ(X, V.ι ''ᵁ W) from (g.onOpenIso i V hi).hom.app W s) *
      (show Γ(X, V.ι ''ᵁ W) from (h.onOpenIso i V hi).hom.app W t) := by
  let hj := (V.ι_image_le W).trans hi
  exact ((onOpenIso_hom_app k i V hi W _).trans
    ((congrArg (k.evaluate i hj) (hf (V.ι ''ᵁ W) s t)).trans
      (hq i (V.ι ''ᵁ W) hj s t))).trans
        (congrArg₂ (fun x y : Γ(X, V.ι ''ᵁ W) ↦ x * y)
          (onOpenIso_hom_app g i V hi W s).symm
          (onOpenIso_hom_app h i V hi W t).symm)

/-- The coordinate law identifies the restriction of a tensor multiplication. -/
lemma tensor_onOpen {X : Scheme.{u}} {κ : Type u} {U : κ → X.Opens}
    (g h k : Cocycle U) (f : tensor g.sheaf h.sheaf ⟶ k.sheaf)
    (i : κ) (V : X.Opens) (hi : V ≤ U i)
    (hf : ∀ (W : V.toScheme.Opens) (s : g.sections (V.ι ''ᵁ W))
      (t : h.sections (V.ι ''ᵁ W)),
      (k.onOpenIso i V hi).hom.app W
        (f.app (V.ι ''ᵁ W) (pure g.sheaf h.sheaf (V.ι ''ᵁ W) s t)) =
      (show Γ(X, V.ι ''ᵁ W) from (g.onOpenIso i V hi).hom.app W s) *
        (show Γ(X, V.ι ''ᵁ W) from (h.onOpenIso i V hi).hom.app W t)) :
    (Scheme.Modules.restrictFunctor V.ι).map f ≫ (k.onOpenIso i V hi).hom =
      (ModuleSheafTensor.restrictIso g.sheaf h.sheaf V.ι).hom ≫
        (trivialTensorIso (g.onOpenIso i V hi) (h.onOpenIso i V hi)).hom := by
  apply restrict_hom_ext V.ι
  intro W s t
  change (k.onOpenIso i V hi).hom.app W
    (f.app (V.ι ''ᵁ W) (pure g.sheaf h.sheaf (V.ι ''ᵁ W) s t)) = _
  rw [hf]
  change _ = (trivialTensorIso (g.onOpenIso i V hi) (h.onOpenIso i V hi)).hom.app W
    ((ModuleSheafTensor.restrictIso g.sheaf h.sheaf V.ι).hom.app W _)
  rw [restrictIso_hom_pure]
  exact (trivialTensorIso_pure (g.onOpenIso i V hi) (h.onOpenIso i V hi) W s t).symm

/-- A tuple product determines multiplication in the restricted chart coordinates. -/
lemma tensor_onOpen_of_mul {X : Scheme.{u}} {κ : Type u} {U : κ → X.Opens}
    (g h k : Cocycle U) (f : tensor g.sheaf h.sheaf ⟶ k.sheaf)
    (q : ∀ V, g.sections V → h.sections V → k.sections V)
    (hf : ∀ V s t, f.app V (pure g.sheaf h.sheaf V s t) = q V s t)
    (hq : ∀ i V hi s t, k.evaluate i hi (q V s t) =
      g.evaluate i hi s * h.evaluate i hi t)
    (i : κ) (V : X.Opens) (hi : V ≤ U i) :
    (Scheme.Modules.restrictFunctor V.ι).map f ≫ (k.onOpenIso i V hi).hom =
      (ModuleSheafTensor.restrictIso g.sheaf h.sheaf V.ι).hom ≫
        (trivialTensorIso (g.onOpenIso i V hi) (h.onOpenIso i V hi)).hom :=
  tensor_onOpen g h k f i V hi (tensor_coordinates g h k f q hf hq i V hi)

/-- A tensor multiplication with the chart-coordinate formula is locally invertible. -/
lemma tensor_isIso_onOpen {X : Scheme.{u}} {κ : Type u} {U : κ → X.Opens}
    (g h k : Cocycle U) (f : tensor g.sheaf h.sheaf ⟶ k.sheaf)
    (i : κ) (V : X.Opens) (hi : V ≤ U i)
    (hf : (Scheme.Modules.restrictFunctor V.ι).map f ≫ (k.onOpenIso i V hi).hom =
      (ModuleSheafTensor.restrictIso g.sheaf h.sheaf V.ι).hom ≫
        (trivialTensorIso (g.onOpenIso i V hi) (h.onOpenIso i V hi)).hom) :
    IsIso ((Scheme.Modules.restrictFunctor V.ι).map f) := by
  have hcomp : IsIso
      ((Scheme.Modules.restrictFunctor V.ι).map f ≫ (k.onOpenIso i V hi).hom) := by
    rw [hf]
    infer_instance
  exact IsIso.of_isIso_comp_right _ (k.onOpenIso i V hi).hom

end FLT.Mazur.FCurve.ModuleSheafUnitCocycle.Cocycle

namespace FLT.Mazur.ProjectiveSpace

variable (R : Type u) [CommRing R] (ι : Type u)

/-- Transition units multiply when degrees add. -/
lemma twistCocycle_add_unit (a b : ℤ) (i j : ι) (V : (space R ι).Opens)
    (hi : V ≤ chart R ι i) (hj : V ≤ chart R ι j) :
    (twistCocycle R ι (a + b)).unit i j V hi hj =
      (twistCocycle R ι a).unit i j V hi hj *
        (twistCocycle R ι b).unit i j V hi hj := by
  simp only [twistCocycle_unit, zpow_add]

/-- Multiply actual compatible tuples component by component. -/
def twistSectionsMul (a b : ℤ) (V : (space R ι).Opens)
    (s : (twistCocycle R ι a).sections V) (t : (twistCocycle R ι b).sections V) :
    (twistCocycle R ι (a + b)).sections V :=
  ⟨fun i ↦ s.1 i * t.1 i, by
    intro i j W hi hj
    rw [map_mul, s.2 i j W hi hj, t.2 i j W hi hj, twistCocycle_add_unit]
    simp only [Units.val_mul, map_mul]
    ring⟩

@[simp]
lemma twistSectionsMul_apply (a b : ℤ) (V : (space R ι).Opens)
    (s : (twistCocycle R ι a).sections V) (t : (twistCocycle R ι b).sections V)
    (i : ι) : (twistSectionsMul R ι a b V s t).1 i = s.1 i * t.1 i := rfl

/-- The product respects restriction to any smaller open. -/
lemma twistSectionsMul_restrict (a b : ℤ) {V W : (space R ι).Opens} (h : W ≤ V)
    (s : (twistCocycle R ι a).sections V) (t : (twistCocycle R ι b).sections V) :
    (twistCocycle R ι (a + b)).restrict h (twistSectionsMul R ι a b V s t) =
      twistSectionsMul R ι a b W ((twistCocycle R ι a).restrict h s)
        ((twistCocycle R ι b).restrict h t) := by
  apply Subtype.ext
  funext i
  exact map_mul _ _ _

/-- Chart evaluation of the tuple product is multiplication of coefficients. -/
lemma twistSectionsMul_evaluate (a b : ℤ) (i : ι) (V : (space R ι).Opens)
    (hi : V ≤ chart R ι i) (s : (twistCocycle R ι a).sections V)
    (t : (twistCocycle R ι b).sections V) :
    (twistCocycle R ι (a + b)).evaluate i hi (twistSectionsMul R ι a b V s t) =
      (twistCocycle R ι a).evaluate i hi s * (twistCocycle R ι b).evaluate i hi t :=
  map_mul _ _ _

/-- Multiplication of chart extensions extends the product of their coefficients. -/
lemma twistSectionsMul_extend (a b : ℤ) (i : ι) (V : (space R ι).Opens)
    (hi : V ≤ chart R ι i) (r t : Γ(space R ι, V)) :
    twistSectionsMul R ι a b V ((twistCocycle R ι a).extend i hi r)
      ((twistCocycle R ι b).extend i hi t) =
        (twistCocycle R ι (a + b)).extend i hi (r * t) := by
  apply ((twistCocycle R ι (a + b)).evaluationEquiv i hi).injective
  change (twistCocycle R ι (a + b)).evaluate i hi _ =
    (twistCocycle R ι (a + b)).evaluate i hi _
  rw [twistSectionsMul_evaluate]
  simp only [Cocycle.evaluate_extend]

/-- The tuple product is bilinear over the functions on its open. -/
def twistSectionsMulLinear (a b : ℤ) (V : (space R ι).Opens) :
    (twistCocycle R ι a).sections V →ₗ[Γ(space R ι, V)]
      (twistCocycle R ι b).sections V →ₗ[Γ(space R ι, V)]
        (twistCocycle R ι (a + b)).sections V where
  toFun s :=
    { toFun := twistSectionsMul R ι a b V s
      map_add' := by intros; ext i; exact mul_add _ _ _
      map_smul' := by
        intro r t
        apply Subtype.ext
        funext i
        change s.1 i * (res inf_le_left r * t.1 i) =
          res inf_le_left r * (s.1 i * t.1 i)
        ring }
  map_add' := by intros; ext t i; exact add_mul _ _ _
  map_smul' := by
    intro r s
    ext t i
    change (res inf_le_left r * s.1 i) * t.1 i =
      res inf_le_left r * (s.1 i * t.1 i)
    exact mul_assoc _ _ _

/-- A natural bilinear pairing of the actual twisting sheaves. -/
def twistingSheafMulPairing (a b : ℤ) :
    Bilinear ((twistCocycle R ι a).sheaf) ((twistCocycle R ι b).sheaf)
      ((twistCocycle R ι (a + b)).sheaf) where
  app := twistSectionsMulLinear R ι a b
  naturality f s t := (twistSectionsMul_restrict R ι a b (leOfHom f) s t).symm

/-- Multiplication on the sheaf tensor, induced by componentwise tuple multiplication. -/
def twistingSheafMul (a b : ℤ) :
    tensor ((twistCocycle R ι a).sheaf) ((twistCocycle R ι b).sheaf) ⟶
      (twistCocycle R ι (a + b)).sheaf := lift (twistingSheafMulPairing R ι a b)

/-- The constructed multiplication has the specified value on pure sections. -/
@[simp]
lemma twistingSheafMul_pure (a b : ℤ) (V : (space R ι).Opens)
    (s : Γ((twistCocycle R ι a).sheaf, V)) (t : Γ((twistCocycle R ι b).sheaf, V)) :
    (twistingSheafMul R ι a b).app V
      (pure ((twistCocycle R ι a).sheaf) ((twistCocycle R ι b).sheaf) V s t) =
        twistSectionsMul R ι a b V s t := lift_pure _ _ _ _

/-- The restricted multiplication equals multiplication in the two chart coordinates. -/
lemma twistingSheafMul_onOpen (a b : ℤ) (i : ι) (V : (space R ι).Opens)
    (hi : V ≤ chart R ι i) :
    (Scheme.Modules.restrictFunctor V.ι).map (twistingSheafMul R ι a b) ≫
      ((twistCocycle R ι (a + b)).onOpenIso i V hi).hom =
    (ModuleSheafTensor.restrictIso (twistCocycle R ι a).sheaf
      (twistCocycle R ι b).sheaf V.ι).hom ≫
        (trivialTensorIso ((twistCocycle R ι a).onOpenIso i V hi)
          ((twistCocycle R ι b).onOpenIso i V hi)).hom :=
  Cocycle.tensor_onOpen_of_mul (twistCocycle R ι a) (twistCocycle R ι b)
    (twistCocycle R ι (a + b)) (twistingSheafMul R ι a b)
    (twistSectionsMul R ι a b) (twistingSheafMul_pure R ι a b)
    (twistSectionsMul_evaluate R ι a b) i V hi

/-- Multiplication is invertible on every open contained in a standard chart. -/
lemma twistingSheafMul_isIso_onOpen (a b : ℤ) (i : ι) (V : (space R ι).Opens)
    (hi : V ≤ chart R ι i) :
    IsIso ((Scheme.Modules.restrictFunctor V.ι).map (twistingSheafMul R ι a b)) :=
  Cocycle.tensor_isIso_onOpen (twistCocycle R ι a) (twistCocycle R ι b)
    (twistCocycle R ι (a + b)) (twistingSheafMul R ι a b) i V hi
      (twistingSheafMul_onOpen R ι a b i V hi)

/-- The standard chart cover detects invertibility of the actual multiplication map. -/
instance twistingSheafMul_isIso (a b : ℤ) : IsIso (twistingSheafMul R ι a b) :=
  ModuleSheafOpenIsoDetection.isIso_of_iSup_eq_top (twistingSheafMul R ι a b)
    (chart R ι) (iSup_chart R ι)
    (fun i ↦ twistingSheafMul_isIso_onOpen R ι a b i (chart R ι i) le_rfl)

/-- Tensor products of twisting sheaves add their degrees. -/
def twistingSheafTensorIso (a b : ℤ) :
    tensor (twistingSheaf R ι a) (twistingSheaf R ι b) ≅ twistingSheaf R ι (a + b) :=
  asIso (twistingSheafMul R ι a b)

@[simp]
lemma twistingSheafTensorIso_hom (a b : ℤ) :
    (twistingSheafTensorIso R ι a b).hom = twistingSheafMul R ι a b := rfl

/-- The inverse sends a product tuple back to its pure tensor. -/
lemma twistingSheafTensorIso_inv_mul (a b : ℤ) (V : (space R ι).Opens)
    (s : Γ(twistingSheaf R ι a, V)) (t : Γ(twistingSheaf R ι b, V)) :
    (twistingSheafTensorIso R ι a b).inv.app V (twistSectionsMul R ι a b V s t) =
      pure (twistingSheaf R ι a) (twistingSheaf R ι b) V s t := by
  rw [← twistingSheafMul_pure]
  exact (sectionsCongr (twistingSheafTensorIso R ι a b) V).symm_apply_apply _

/-- Opposite degrees tensor to the zero twist. -/
def twistingSheafTensorNegIso (a : ℤ) :
    tensor (twistingSheaf R ι a) (twistingSheaf R ι (-a)) ≅ twistingSheaf R ι 0 :=
  twistingSheafTensorIso R ι a (-a) ≪≫ eqToIso (by rw [add_neg_cancel])

/-- Opposite twisting sheaves are tensor inverses with value in the structure module. -/
def twistingSheafTensorInverseIso (a : ℤ) :
    tensor (twistingSheaf R ι a) (twistingSheaf R ι (-a)) ≅
      structureModule (space R ι) :=
  twistingSheafTensorNegIso R ι a ≪≫ twistingSheafZeroIso R ι

/-- Degree addition for the usual twists on finite-dimensional projective space. -/
def OTensorIso (A : Type) [CommRing A] (d : ℕ) (a b : ℤ) :
    tensor (O A d a) (O A d b) ≅ O A d (a + b) :=
  twistingSheafTensorIso A (Fin (d + 1)) a b

/-- The degree-zero target for the tensor of opposite twists. -/
def OTensorNegIso (A : Type) [CommRing A] (d : ℕ) (a : ℤ) :
    tensor (O A d a) (O A d (-a)) ≅ O A d 0 :=
  twistingSheafTensorNegIso A (Fin (d + 1)) a

/-- The tensor inverse of `O(a)` is `O(-a)`. -/
def OTensorInverseIso (A : Type) [CommRing A] (d : ℕ) (a : ℤ) :
    tensor (O A d a) (O A d (-a)) ≅ structureModule (space A (Fin (d + 1))) :=
  twistingSheafTensorInverseIso A (Fin (d + 1)) a

end FLT.Mazur.ProjectiveSpace
