/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CoefficientSpectrumLimit
public import FLT.Mazur.SchemeBaseChangeLimit

/-!
# The inverse system of coefficient base changes of a scheme model

For a scheme over an initial finite coefficient ring, its pullback to `A`
is the inverse limit of its pullbacks to all finite coefficient enlargements.
The recovery maps and transition maps are cartesian over the affine bases.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory Limits AlgebraicGeometry

namespace FLT.Mazur.Approximation

universe u

variable {A : Type u} [CommRing A] (S₀ : Subalgebra ℤ A)

/-- The coefficient spectra, regarded as schemes over the initial stage. -/
def coefficientSpectrumToInitial :
    coefficientSpectrumDiagram S₀ ⟶
      (Functor.const (CoefficientStage S₀)ᵒᵖ).obj (Spec (.of S₀)) where
  app i := Spec.map (CommRingCat.ofHom
    (Subalgebra.inclusion i.unop.property.1).toRingHom)
  naturality _ _ _ := by
    change Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ 𝟙 _
    rw [Category.comp_id, ← Spec.map_comp]
    rfl

/-- All coefficient-base projections commute with the map to the initial base. -/
theorem coefficientSpectrumCone_toInitial (i : (CoefficientStage S₀)ᵒᵖ) :
    (coefficientSpectrumCone S₀).π.app i ≫ (coefficientSpectrumToInitial S₀).app i =
      Spec.map (CommRingCat.ofHom S₀.val.toRingHom) := by
  change Spec.map _ ≫ Spec.map _ = _
  rw [← Spec.map_comp]
  rfl

variable {Y : Scheme.{u}} (q : Y ⟶ Spec (.of S₀))

/-- The fixed model base-changed to every finite coefficient enlargement. -/
def coefficientModelDiagram : (CoefficientStage S₀)ᵒᵖ ⥤ Scheme.{u} :=
  schemeBaseChangeDiagram (coefficientSpectrumToInitial S₀) q

/-- The model pulled back to `A`, with its canonical recovery maps. -/
def coefficientModelCone : Cone (coefficientModelDiagram S₀ q) :=
  schemeBaseChangeCone (coefficientSpectrumToInitial S₀) q
    (coefficientSpectrumCone S₀) (Spec.map (CommRingCat.ofHom S₀.val.toRingHom))
    (coefficientSpectrumCone_toInitial S₀)

instance {i j : (CoefficientStage S₀)ᵒᵖ} (f : i ⟶ j) :
    IsAffineHom ((coefficientModelDiagram S₀ q).map f) := by
  dsimp [coefficientModelDiagram]
  infer_instance

/-- Recovery from the original ring is cartesian at each finite coefficient stage. -/
theorem coefficientModelCone_isPullback (i : (CoefficientStage S₀)ᵒᵖ) :
    IsPullback ((coefficientModelCone S₀ q).π.app i)
      (pullback.snd q (Spec.map (CommRingCat.ofHom S₀.val.toRingHom)))
      (pullback.snd q ((coefficientSpectrumToInitial S₀).app i))
      ((coefficientSpectrumCone S₀).π.app i) :=
  schemeBaseChangeCone_isPullback _ _ _ _ _ i

/-- The original-ring pullback is the inverse limit of the finite coefficient models. -/
def coefficientModelIsLimit [Algebra.FiniteType ℤ S₀] :
    IsLimit (coefficientModelCone S₀ q) := by
  letI := IsCofiltered.isConnected (CoefficientStage S₀)ᵒᵖ
  exact schemeBaseChangeIsLimit _ _ _ _ _ (coefficientSpectrumIsLimit S₀)

end FLT.Mazur.Approximation
