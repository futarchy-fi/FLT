/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.BaseAdicReesChart
public import Mathlib.AlgebraicGeometry.Pullbacks

/-!
# Affine relative Rees charts in the actual base change

The tensor-product spectrum for a source chart maps by an open immersion
into the base change to the base Rees spectrum. Both projections retain
the original structural morphisms.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory Limits AlgebraicGeometry
open scoped TensorProduct

universe u

namespace FLT.Mazur.BaseAdicRees

variable {R : CommRingCat.{u}} {X : Scheme.{u}} (f : X ⟶ Spec R)
  (J : Ideal R) (V : X.affineOpens)

/-- The original base Rees spectrum over the original affine base. -/
def baseMap : Spec (.of (reesAlgebra J)) ⟶ Spec R :=
  Spec.map (CommRingCat.ofHom (algebraMap R (reesAlgebra J)))

/-- The space on which the relative coherent power model must be glued. -/
abbrev relativeSpace := pullback f (baseMap J)

/-- Spectrum coordinates of a chart keep the original structure morphism. -/
lemma chartScalars_spec :
    Spec.map (CommRingCat.ofHom (chartScalars f V)) = V.2.fromSpec ≫ f := by
  have h := IsAffineOpen.SpecMap_appLE_fromSpec f
    (isAffineOpen_top (Spec R)) V.2 (show V.1 ≤ f ⁻¹ᵁ ⊤ by simp)
  rw [IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv, ← Spec.map_comp] at h
  exact h

/-- Inclusion of a chart's affine pullback into the actual base change. -/
def chartPullbackMap :
    pullback (Spec.map (CommRingCat.ofHom (chartScalars f V))) (baseMap J) ⟶
      relativeSpace f J :=
  pullback.map _ _ f (baseMap J) V.2.fromSpec (𝟙 _) (𝟙 _)
    (by simpa only [Category.comp_id] using chartScalars_spec f V) (by simp)

/-- The chart pullback is an actual open subscheme of the relative space. -/
instance chartPullbackMap_isOpenImmersion : IsOpenImmersion (chartPullbackMap f J V) := by
  unfold chartPullbackMap
  infer_instance

/-- Tensor coordinates for the chart's actual relative affine spectrum. -/
def chartSpaceMap :
    let _ := chartAlgebra f V
    Spec (.of (Γ(X, V.1) ⊗[R] reesAlgebra J)) ⟶ relativeSpace f J := by
  let _ := chartAlgebra f V
  exact (pullbackSpecIso R Γ(X, V.1) (reesAlgebra J)).inv ≫ chartPullbackMap f J V

/-- Each relative tensor spectrum is an open chart of the actual base change. -/
instance chartSpaceMap_isOpenImmersion : IsOpenImmersion (chartSpaceMap f J V) := by
  let _ := chartAlgebra f V
  exact inferInstanceAs (IsOpenImmersion
    ((pullbackSpecIso R Γ(X, V.1) (reesAlgebra J)).inv ≫ chartPullbackMap f J V))

/-- The chart map's first projection is the original chart inclusion. -/
@[reassoc]
lemma chartSpaceMap_fst :
    let _ := chartAlgebra f V
    chartSpaceMap f J V ≫ pullback.fst f (baseMap J) =
      Spec.map (CommRingCat.ofHom (algebraMap Γ(X, V.1)
        (Γ(X, V.1) ⊗[R] reesAlgebra J))) ≫ V.2.fromSpec := by
  let _ := chartAlgebra f V
  simp only [chartSpaceMap, chartPullbackMap, pullback.map, Category.assoc,
    pullback.lift_fst]
  rw [← Category.assoc]
  exact congrArg (fun k ↦ k ≫ V.2.fromSpec)
    (pullbackSpecIso_inv_fst' R Γ(X, V.1) (reesAlgebra J))

/-- The second projection is the unchanged base Rees coordinate. -/
@[reassoc]
lemma chartSpaceMap_snd :
    let _ := chartAlgebra f V
    chartSpaceMap f J V ≫ pullback.snd f (baseMap J) =
      Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight
        (R := R) (A := Γ(X, V.1)) (B := reesAlgebra J)).toRingHom) := by
  let _ := chartAlgebra f V
  simp only [chartSpaceMap, chartPullbackMap, pullback.map, Category.assoc, pullback.lift_snd,
    Category.comp_id]
  exact pullbackSpecIso_inv_snd R Γ(X, V.1) (reesAlgebra J)

end FLT.Mazur.BaseAdicRees
