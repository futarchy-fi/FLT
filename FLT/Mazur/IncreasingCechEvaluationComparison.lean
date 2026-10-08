/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.IncreasingCechLocalizedSectionFormula

/-!
# Actual evaluation and scalar-extended evaluation

The section formula extends to arbitrary tensors by additivity and localization.
When the actual comparison is bijective, evaluation on cartesian functions is
injective exactly when the original linear evaluation remains injective after
extension of scalars. The two tensor cancellation maps are actual equivalences.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory AlgebraicGeometry TensorProduct
namespace FLT.Mazur.IncreasingCechCartesian
open IncreasingCechScalars FCurve Chow ArtinianRelativeSectionCriterion

variable {P X T S : Scheme.{0}}
  {p : P ⟶ X} {q : P ⟶ T} {f : X ⟶ S} {g : T ⟶ S}
  (h : IsPullback p q f g) [IsAffine T] [IsAffine S] [X.IsSeparated]
  {ι : Type} [LinearOrder ι] [Finite ι] (U : ι → X.Opens)
  (hU : ∀ i, IsAffineOpen (U i)) (hCover : iSup U = ⊤)
  (W : Submonoid Γ(S, ⊤))
  (σ : S ⟶ X) (hσ : σ ≫ f = 𝟙 S) (τ : T ⟶ P)
  (hq : τ ≫ q = 𝟙 T) (hp : τ ≫ p = g ≫ σ)

include hq hp

/-- The assembled comparison commutes with section evaluation on every tensor. -/
lemma localizedSectionsComparison_evaluation_all :
    let _ : Algebra Γ(S, ⊤) Γ(T, ⊤) := g.appTop.hom.toAlgebra
    ∀ [Algebra (Localization W) Γ(T, ⊤)]
      [IsScalarTower Γ(S, ⊤) (Localization W) Γ(T, ⊤)]
      (x : Γ(T, ⊤) ⊗[Localization W]
        LocalizedModule W (baseSections (structureModule X) f.appTop.hom ⊤)),
      τ.appTop (localizedSectionsComparison h U hU hCover W x) =
        TensorProduct.rid Γ(S, ⊤) Γ(T, ⊤)
          ((evaluation f σ hσ).lTensor Γ(T, ⊤)
            (LocalizedTensorCancellation.tensorEquiv W Γ(T, ⊤)
              (baseSections (structureModule X) f.appTop.hom ⊤) x)) := by
  dsimp only
  let _ : Algebra Γ(S, ⊤) Γ(T, ⊤) := g.appTop.hom.toAlgebra
  intro _ _ x
  induction x using TensorProduct.inductionOn with
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul b s =>
    induction s using LocalizedModule.induction_on with
    | h s w =>
      rw [localizedSectionsComparison_evaluation h U hU hCover W σ τ hq hp,
        LocalizedTensorCancellation.tensorEquiv_tmul_mk, LinearMap.lTensor_tmul,
        TensorProduct.rid_tmul]
      change _ = σ.appTop s • (Localization.mk 1 w • b)
      rw [Algebra.smul_def, mul_comm]
      rfl

/-- With actual base change, geometric evaluation injectivity is tensor evaluation injectivity. -/
lemma sectionEvaluation_injective_iff_tensor :
    let _ : Algebra Γ(S, ⊤) Γ(T, ⊤) := g.appTop.hom.toAlgebra
    ∀ [Algebra (Localization W) Γ(T, ⊤)]
      [IsScalarTower Γ(S, ⊤) (Localization W) Γ(T, ⊤)],
      Function.Bijective (localizedSectionsComparison h U hU hCover W) →
      (Function.Injective τ.appTop ↔
        Function.Injective ((evaluation f σ hσ).lTensor Γ(T, ⊤))) := by
  dsimp only
  let _ : Algebra Γ(S, ⊤) Γ(T, ⊤) := g.appTop.hom.toAlgebra
  intro _ _ hc
  let c := LocalizedTensorCancellation.tensorEquiv W Γ(T, ⊤)
    (baseSections (structureModule X) f.appTop.hom ⊤)
  let e := (evaluation f σ hσ).lTensor Γ(T, ⊤)
  let r := TensorProduct.rid Γ(S, ⊤) Γ(T, ⊤)
  have he (x) := localizedSectionsComparison_evaluation_all h U hU hCover W σ hσ τ hq hp x
  constructor
  · intro hi x y hxy
    apply c.symm.injective
    apply hc.injective
    apply hi
    rw [he, he]
    change r (e (c (c.symm x))) = r (e (c (c.symm y)))
    rw [LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply, hxy]
  · intro hi x y hxy
    obtain ⟨a, rfl⟩ := hc.surjective x
    obtain ⟨b, rfl⟩ := hc.surjective y
    apply congrArg (localizedSectionsComparison h U hU hCover W)
    apply c.injective
    apply hi
    apply r.injective
    exact (he a).symm.trans (hxy.trans (he b))

end FLT.Mazur.IncreasingCechCartesian
