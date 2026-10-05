/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SectionGradedCoordinates

/-!
# Coordinates on an open trivialization

The actual restriction comparisons identify arbitrary ambient tensor-power
sections with scalar coordinates on a trivializing open subscheme.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
universe u
namespace FLT.Mazur.SectionGradedLocalCoordinates
open FCurve ModuleLineBundleTensorPullback ModuleSheafTensor
open SectionGradedMultiplication
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {X : Scheme.{u}} {L : X.Modules} {W : X.Opens}
    (e : L.restrict W.ι ≅ structureModule W.toScheme)

/-- The tensor-power trivialization on an open subscheme. -/
def localIso (n : ℕ) : (tensorPower L n).restrict W.ι ≅ structureModule W.toScheme :=
  tensorPowerRestrictIso L W.ι n ≪≫ tensorPowerTrivialization e n

/-- Coordinate of an ambient section on the image of an open of the chart. -/
def coordinate (n : ℕ) (V : W.toScheme.Opens) (s : Piece L (W.ι ''ᵁ V) n) :
    Γ(W.toScheme, V) :=
  (localIso e n).hom.app V (((tensorPower L n).restrictAppIso W.ι V).inv s)

/-- Transporting the degree leaves its local coordinate unchanged. -/
lemma coordinate_cast {m n : ℕ} (h : m = n) (V : W.toScheme.Opens)
    (s : Piece L (W.ι ''ᵁ V) m) :
    coordinate e n V (cast L h (W.ι ''ᵁ V) s) = coordinate e m V s := by
  subst n
  rfl

/-- Coordinates preserve scalar multiplication on the ambient open. -/
lemma coordinate_smul (n : ℕ) (V : W.toScheme.Opens)
    (r : Γ(X, W.ι ''ᵁ V)) (s : Piece L (W.ι ''ᵁ V) n) :
    coordinate e n V (r • s) =
      (show Γ(W.toScheme, V) from r) * coordinate e n V s := by
  dsimp only [coordinate]
  erw [(tensorPower L n).smul_restrictAppIso_inv_apply W.ι V r]
  rw [Hom.app_smul, Scheme.Opens.ι_appIso]
  rfl

/-- The scalar coordinate in degree zero is the scalar itself. -/
lemma coordinate_zero (V : W.toScheme.Opens) (r : Γ(X, W.ι ''ᵁ V)) :
    coordinate e 0 V r = r := by
  change (W.ι.appIso V).hom r = r
  rw [Scheme.Opens.ι_appIso]
  rfl

/-- Coordinates multiply when a section is prepended to a tensor power. -/
lemma coordinate_cons (n : ℕ) (V : W.toScheme.Opens)
    (s : Γ(L, W.ι ''ᵁ V)) (t : Piece L (W.ι ''ᵁ V) n) :
    coordinate e (n + 1) V (cons L n (W.ι ''ᵁ V) s t) =
      (show Γ(W.toScheme, V) from e.hom.app V ((L.restrictAppIso W.ι V).inv s)) *
        coordinate e n V t := by
  change (tensorPowerTrivialization e (n + 1)).hom.app V
    ((ModuleSheafTensor.map (𝟙 _) (tensorPowerRestrictIso L W.ι n).hom).app V
      ((restrictIso L (tensorPower L n) W.ι).hom.app V
        (((tensor L (tensorPower L n)).restrictAppIso W.ι V).inv
          (pure _ _ (W.ι ''ᵁ V) s t)))) = _
  rw [restrictIso_hom_pure, ModuleSheafTensor.map_pure]
  exact trivialTensorIso_pure e (tensorPowerTrivialization e n) V _ _

/-- Three local pure factors detect a morphism from a restricted tensor. -/
lemma restrict_left_hom_ext {A B C : X.Modules} {P : W.toScheme.Modules}
    {f g : (tensor (tensor A B) C).restrict W.ι ⟶ P}
    (h : ∀ V a b c, f.app V (((tensor (tensor A B) C).restrictAppIso W.ι V).inv
      (pure _ _ (W.ι ''ᵁ V) (pure _ _ (W.ι ''ᵁ V) a b) c)) =
      g.app V (((tensor (tensor A B) C).restrictAppIso W.ι V).inv
        (pure _ _ (W.ι ''ᵁ V) (pure _ _ (W.ι ''ᵁ V) a b) c))) : f = g := by
  apply ((Scheme.Modules.restrictAdjunction W.ι).homEquiv _ _).injective
  apply ModuleSheafTensorAssociator.left_hom_ext
  intro V a b c
  change f.app (W.ι ⁻¹ᵁ V) ((tensor (tensor A B) C).presheaf.map
    (homOfLE (W.ι.image_preimage_le V)).op (pure _ _ V (pure _ _ V a b) c)) =
    g.app (W.ι ⁻¹ᵁ V) ((tensor (tensor A B) C).presheaf.map
      (homOfLE (W.ι.image_preimage_le V)).op (pure _ _ V (pure _ _ V a b) c))
  simp only [pure_restrict]
  exact h _ _ _ _

/-- Restricted tensor addition becomes multiplication of chart coordinates. -/
lemma addIso_coordinate (m n : ℕ) :
    (restrictFunctor W.ι).map (tensorPowerAddIso L m n).hom ≫ (localIso e (m + n)).hom =
      (restrictIso (tensorPower L m) (tensorPower L n) W.ι).hom ≫
        ModuleSheafTensor.map (localIso e m).hom (localIso e n).hom ≫
          (leftUnitor (structureModule W.toScheme)).hom := by
  induction m with
  | zero =>
    apply restrict_hom_ext W.ι
    intro V r s
    simp only [Scheme.Modules.Hom.comp_app, ConcreteCategory.comp_apply,
      restrictIso_hom_pure, ModuleSheafTensor.map_pure]
    change coordinate e (0 + n) V (mul L (W.ι ''ᵁ V) 0 n r s) =
      (leftUnitor (structureModule W.toScheme)).hom.app V
        (pure (structureModule W.toScheme) (structureModule W.toScheme) V
          (coordinate e 0 V r) (coordinate e n V s))
    rw [SectionGradedCoordinates.scalar_pure, coordinate_zero,
      SectionGradedMultiplication.zero_mul, coordinate_cast, coordinate_smul]
  | succ m ih =>
    apply restrict_left_hom_ext
    intro V a b c
    dsimp only [tensorPower]
    simp only [Scheme.Modules.Hom.comp_app, ConcreteCategory.comp_apply,
      restrictIso_hom_pure, ModuleSheafTensor.map_pure]
    have hi := congrArg (fun f ↦ f.app V
      (((tensor (tensorPower L m) (tensorPower L n)).restrictAppIso W.ι V).inv
        (pure _ _ (W.ι ''ᵁ V) b c))) ih
    simp only [Scheme.Modules.Hom.comp_app, ConcreteCategory.comp_apply,
      restrictIso_hom_pure, ModuleSheafTensor.map_pure] at hi
    change coordinate e (m + n) V (mul L (W.ι ''ᵁ V) m n b c) =
      (leftUnitor (structureModule W.toScheme)).hom.app V
        (pure (structureModule W.toScheme) (structureModule W.toScheme) V
          (coordinate e m V b) (coordinate e n V c)) at hi
    rw [SectionGradedCoordinates.scalar_pure] at hi
    change coordinate e (m + 1 + n) V
      (mul L (W.ι ''ᵁ V) (m + 1) n (cons L m (W.ι ''ᵁ V) a b) c) =
      (leftUnitor (structureModule W.toScheme)).hom.app V
        (pure (structureModule W.toScheme) (structureModule W.toScheme) V
          (coordinate e (m + 1) V (cons L m (W.ι ''ᵁ V) a b)) (coordinate e n V c))
    rw [SectionGradedCoordinates.scalar_pure, succ_mul_pure, coordinate_cast,
      coordinate_cons, coordinate_cons, hi, _root_.mul_assoc]

/-- Local coordinates multiply for arbitrary ambient sections. -/
lemma coordinate_mul (m n : ℕ) (V : W.toScheme.Opens)
    (s : Piece L (W.ι ''ᵁ V) m) (t : Piece L (W.ι ''ᵁ V) n) :
    coordinate e (m + n) V (mul L (W.ι ''ᵁ V) m n s t) =
      coordinate e m V s * coordinate e n V t := by
  have h := congrArg (fun f ↦ f.app V
    (((tensor (tensorPower L m) (tensorPower L n)).restrictAppIso W.ι V).inv
      (pure _ _ (W.ι ''ᵁ V) s t))) (addIso_coordinate e m n)
  simp only [Scheme.Modules.Hom.comp_app, ConcreteCategory.comp_apply,
    restrictIso_hom_pure, ModuleSheafTensor.map_pure] at h
  exact h.trans (SectionGradedCoordinates.scalar_pure V _ _)

/-- Local coordinates detect equality of ambient tensor-power sections. -/
lemma coordinate_injective (n : ℕ) (V : W.toScheme.Opens) :
    Function.Injective (coordinate e n V) := by
  intro s t h
  have h' := congrArg ((localIso e n).inv.app V) h
  change (localIso e n).inv.app V ((localIso e n).hom.app V s) =
    (localIso e n).inv.app V ((localIso e n).hom.app V t) at h'
  simpa only [← ConcreteCategory.comp_apply, ← Hom.comp_app,
    Iso.hom_inv_id, Hom.id_app, ConcreteCategory.id_apply] using h'

end FLT.Mazur.SectionGradedLocalCoordinates
