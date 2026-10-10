/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.IncreasingCechCartesianSectionFormula
public import FLT.Mazur.IncreasingCechPrincipalComparison

/-!
# Actual localized section and evaluation formulas

The assembled comparison transfers a fraction denominator into the coefficient
and multiplies the two actual pulled-back functions. Evaluation along a cartesian
section therefore commutes with this comparison.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory AlgebraicGeometry TensorProduct
namespace FLT.Mazur.IncreasingCechCartesian
open IncreasingCechScalars FCurve Chow

variable {P X T S : Scheme.{0}}
  {p : P ⟶ X} {q : P ⟶ T} {f : X ⟶ S} {g : T ⟶ S}
  (h : IsPullback p q f g) [IsAffine T] [IsAffine S] [X.IsSeparated]
  {ι : Type} [LinearOrder ι] [Finite ι] (U : ι → X.Opens)
  (hU : ∀ i, IsAffineOpen (U i)) (hCover : iSup U = ⊤)
  (W : Submonoid Γ(S, ⊤))

/-- A section fraction gives the actual product function with denominator in its coefficient. -/
lemma localizedSectionsComparison_tmul_mk :
    let _ : Algebra Γ(S, ⊤) Γ(T, ⊤) := g.appTop.hom.toAlgebra
    ∀ [Algebra (Localization W) Γ(T, ⊤)]
      [IsScalarTower Γ(S, ⊤) (Localization W) Γ(T, ⊤)]
      (b : Γ(T, ⊤)) (s : Γ(X, ⊤)) (w : W),
      localizedSectionsComparison h U hU hCover W
          (b ⊗ₜ[Localization W] LocalizedModule.mk s w) =
        q.appTop (Localization.mk 1 w • b) * p.appTop s := by
  dsimp only
  let _ : Algebra Γ(S, ⊤) Γ(T, ⊤) := g.appTop.hom.toAlgebra
  intro _ _ b s w
  dsimp only [localizedSectionsComparison, localizedKernelSectionsEquiv]
  apply tensorKernelSectionsEquiv_section h U hU hCover
  dsimp only
  change (LocalizedTensorCancellation.kernelEquiv W Γ(T, ⊤) _ _).val = _
  rw [LocalizedTensorCancellation.kernelEquiv_val]
  change LocalizedTensorCancellation.tensorEquiv W Γ(T, ⊤) _
    (sectionsTensorKernel (structureModule X) U f.appTop.hom hCover W Γ(T, ⊤)
      (b ⊗ₜ[Localization W] LocalizedModule.mk s w)).val = _
  rw [sectionsTensorKernel_tmul,
    localizedSectionsZeroKernelEquiv_mk, LocalizedTensorCancellation.tensorEquiv_tmul_mk]

/-- Evaluating the assembled comparison along an actual cartesian section preserves fractions. -/
lemma localizedSectionsComparison_evaluation (σ : S ⟶ X) (τ : T ⟶ P)
    (hq : τ ≫ q = 𝟙 T) (hp : τ ≫ p = g ≫ σ) :
    let _ : Algebra Γ(S, ⊤) Γ(T, ⊤) := g.appTop.hom.toAlgebra
    ∀ [Algebra (Localization W) Γ(T, ⊤)]
      [IsScalarTower Γ(S, ⊤) (Localization W) Γ(T, ⊤)]
      (b : Γ(T, ⊤)) (s : Γ(X, ⊤)) (w : W),
      τ.appTop (localizedSectionsComparison h U hU hCover W
          (b ⊗ₜ[Localization W] LocalizedModule.mk s w)) =
        (Localization.mk 1 w • b) * g.appTop (σ.appTop s) := by
  dsimp only
  let _ : Algebra Γ(S, ⊤) Γ(T, ⊤) := g.appTop.hom.toAlgebra
  intro _ _ b s w
  rw [localizedSectionsComparison_tmul_mk, map_mul]
  congr 1
  · rw [← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop, hq, Scheme.Hom.id_appTop]
    rfl
  · rw [← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop, hp, Scheme.Hom.comp_appTop]
    rfl

end FLT.Mazur.IncreasingCechCartesian
