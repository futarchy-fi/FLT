/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CoherentOpenDescent
public import FLT.Mazur.ModuleSheafTensorAssociator
public import FLT.Mazur.ProjectiveTwistTensorInverse
public import FLT.Mazur.ProjectiveTwistingSheafTensor

/-!
# Addition and inverses of twists of module sheaves

The concrete tensor associator and multiplication of twisting sheaves give
`F(a)(b) ≅ F(a + b)`, naturally in `F`. Opposite twists cancel by the existing
zero-twist comparison. Finite local presentation is preserved by every twist:
on each standard chart it is the original sheaf, and open descent applies.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry
open FLT.Mazur.FCurve

universe u

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

namespace FLT.Mazur.ProjectiveSpace

open ModuleSheafTensor ModuleSheafTensorAssociator

variable (R : Type u) [CommRing R] (ι : Type u)

/-- Two consecutive twists add their degrees via the actual tensor multiplication. -/
def twistTensorAddIso (F : (space R ι).Modules) (a b : ℤ) :
    twistTensor R ι (twistTensor R ι F a) b ≅ twistTensor R ι F (a + b) :=
  associator F (twistingSheaf R ι a) (twistingSheaf R ι b) ≪≫
    congr (Iso.refl F) (twistingSheafTensorIso R ι a b)

/-- On nested pure sections, addition multiplies the two twisting sections. -/
@[simp]
lemma twistTensorAddIso_pure (F : (space R ι).Modules) (a b : ℤ)
    (U : (space R ι).Opens) (m : Γ(F, U))
    (s : Γ(twistingSheaf R ι a, U)) (t : Γ(twistingSheaf R ι b, U)) :
    (twistTensorAddIso R ι F a b).hom.app U
      (pure (twistTensor R ι F a) (twistingSheaf R ι b) U
        (pure F (twistingSheaf R ι a) U m s) t) =
      pure F (twistingSheaf R ι (a + b)) U m (twistSectionsMul R ι a b U s t) := by
  change (map (𝟙 F) (twistingSheafMul R ι a b)).app U
    ((associator F (twistingSheaf R ι a) (twistingSheaf R ι b)).hom.app U _) = _
  dsimp only [twistTensor, twistingSheaf]
  rw [associator_hom_pure, map_pure, twistingSheafMul_pure]
  rfl

/-- The inverse addition comparison separates a product of twisting sections. -/
lemma twistTensorAddIso_inv_pure (F : (space R ι).Modules) (a b : ℤ)
    (U : (space R ι).Opens) (m : Γ(F, U))
    (s : Γ(twistingSheaf R ι a, U)) (t : Γ(twistingSheaf R ι b, U)) :
    (twistTensorAddIso R ι F a b).inv.app U
      (pure F (twistingSheaf R ι (a + b)) U m (twistSectionsMul R ι a b U s t)) =
      pure (twistTensor R ι F a) (twistingSheaf R ι b) U
        (pure F (twistingSheaf R ι a) U m s) t := by
  rw [← twistTensorAddIso_pure]
  exact (sectionsCongr (twistTensorAddIso R ι F a b) U).symm_apply_apply _

/-- Addition commutes with every morphism of the sheaf being twisted. -/
@[reassoc]
lemma twistTensorAddIso_naturality {F G : (space R ι).Modules}
    (f : F ⟶ G) (a b : ℤ) :
    (twistTensorFunctor R ι b).map ((twistTensorFunctor R ι a).map f) ≫
      (twistTensorAddIso R ι G a b).hom =
    (twistTensorAddIso R ι F a b).hom ≫ (twistTensorFunctor R ι (a + b)).map f := by
  change map (map f (𝟙 _)) (𝟙 _) ≫
      ((associator G _ _).hom ≫ map (𝟙 G) (twistingSheafMul R ι a b)) =
    ((associator F _ _).hom ≫ map (𝟙 F) (twistingSheafMul R ι a b)) ≫ map f (𝟙 _)
  rw [associator_naturality_assoc]
  simp only [map_id, ← map_comp, Category.id_comp, Category.comp_id, Category.assoc]

/-- Addition of degrees is a natural isomorphism of twist functors. -/
def twistTensorAddNatIso (a b : ℤ) :
    twistTensorFunctor R ι a ⋙ twistTensorFunctor R ι b ≅
      twistTensorFunctor R ι (a + b) :=
  NatIso.ofComponents (fun F ↦ twistTensorAddIso R ι F a b)
    (fun f ↦ twistTensorAddIso_naturality R ι f a b)

/-- A twist followed by its opposite is naturally the identity. -/
def twistTensorNegNatIso (a : ℤ) :
    twistTensorFunctor R ι a ⋙ twistTensorFunctor R ι (-a) ≅ 𝟭 (space R ι).Modules :=
  twistTensorAddNatIso R ι a (-a) ≪≫
    eqToIso (by rw [add_neg_cancel]) ≪≫ twistTensorZeroNatIso R ι

/-- The opposite twist also cancels when applied first. -/
def twistTensorNegNatIso' (a : ℤ) :
    twistTensorFunctor R ι (-a) ⋙ twistTensorFunctor R ι a ≅ 𝟭 (space R ι).Modules :=
  twistTensorAddNatIso R ι (-a) a ≪≫
    eqToIso (by rw [neg_add_cancel]) ≪≫ twistTensorZeroNatIso R ι

/-- Opposite twists cancel for every module sheaf. -/
def twistTensorNegIso (F : (space R ι).Modules) (a : ℤ) :
    twistTensor R ι (twistTensor R ι F a) (-a) ≅ F :=
  (twistTensorNegNatIso R ι a).app F

/-- Cancellation in the reverse order. -/
def twistTensorNegIso' (F : (space R ι).Modules) (a : ℤ) :
    twistTensor R ι (twistTensor R ι F (-a)) a ≅ F :=
  (twistTensorNegNatIso' R ι a).app F

/-- Cancellation commutes with the original morphism of sheaves. -/
@[reassoc]
lemma twistTensorNegIso_naturality {F G : (space R ι).Modules} (f : F ⟶ G) (a : ℤ) :
    (twistTensorFunctor R ι (-a)).map ((twistTensorFunctor R ι a).map f) ≫
      (twistTensorNegIso R ι G a).hom = (twistTensorNegIso R ι F a).hom ≫ f :=
  (twistTensorNegNatIso R ι a).hom.naturality f

/-- Each standard chart of a coherent twist has finite local presentations. -/
lemma twistTensor_restrict_isFinitePresentation (F : (space R ι).Modules)
    [F.IsFinitePresentation] (d : ℤ) (i : ι) :
    ((twistTensor R ι F d).restrict (chart R ι i).ι).IsFinitePresentation :=
  (SheafOfModules.isFinitePresentation (chart R ι i).toScheme.ringCatSheaf).prop_of_iso
    (twistTensorRestrictIso R ι F d i).symm
    (coherent_restrict (chart R ι i).ι F)

/-- Every integer twist preserves local finite presentation, by standard-chart descent. -/
instance twistTensor_isFinitePresentation (F : (space R ι).Modules)
    [F.IsFinitePresentation] (d : ℤ) : (twistTensor R ι F d).IsFinitePresentation :=
  coherent_of_openCover (twistTensor R ι F d) (chart R ι) (iSup_chart R ι)
    (twistTensor_restrict_isFinitePresentation R ι F d)

/-- The twist functor carries finitely presented sheaves to finitely presented sheaves. -/
lemma twistTensorFunctor_isFinitePresentation (F : (space R ι).Modules)
    [F.IsFinitePresentation] (d : ℤ) :
    ((twistTensorFunctor R ι d).obj F).IsFinitePresentation :=
  twistTensor_isFinitePresentation R ι F d

/-- Twisting also reflects local finite presentation, using the constructed inverse twist. -/
theorem twistTensor_isFinitePresentation_iff (F : (space R ι).Modules) (d : ℤ) :
    (twistTensor R ι F d).IsFinitePresentation ↔ F.IsFinitePresentation := by
  constructor
  · intro h
    have := h
    exact (SheafOfModules.isFinitePresentation (space R ι).ringCatSheaf).prop_of_iso
      (twistTensorNegIso R ι F d)
      (twistTensor_isFinitePresentation R ι (twistTensor R ι F d) (-d))
  · intro h
    have := h
    exact twistTensor_isFinitePresentation R ι F d

end FLT.Mazur.ProjectiveSpace
