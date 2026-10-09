/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.IncreasingCechCartesianKernel
public import FLT.Mazur.IncreasingCechGenericSections
public import FLT.Mazur.LocalizedTensorCancellation

/-!
# Actual functions from localized tensor kernels

When an affine base change factors through a localization of the structural
base-section ring, cancellation identifies the localized tensor kernel with
actual global functions. The original global-section comparison now has an
actual geometric target. Evaluation compatibility is a separate assertion.
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

/-- The localized tensor zero-kernel is the additive group of actual cartesian functions. -/
def localizedKernelSectionsEquiv :
    let _ : Algebra Γ(S, ⊤) Γ(T, ⊤) := g.appTop.hom.toAlgebra
    ∀ [Algebra (Localization W) Γ(T, ⊤)]
      [IsScalarTower Γ(S, ⊤) (Localization W) Γ(T, ⊤)],
    ((localD (structureModule X) U f.appTop.hom W 0).lTensor Γ(T, ⊤)).ker ≃+
      baseSections (structureModule P) q.appTop.hom ⊤ := by
  dsimp only
  let _ : Algebra Γ(S, ⊤) Γ(T, ⊤) := g.appTop.hom.toAlgebra
  intro _ _
  exact (LocalizedTensorCancellation.kernelEquiv W Γ(T, ⊤)
    (baseD (structureModule X) U f.appTop.hom 0)).toAddEquiv.trans
      (tensorKernelSectionsEquiv h U hU hCover).toAddEquiv

/-- The global-section tensor comparison with its actual geometric target. -/
def localizedSectionsComparison :
    let _ : Algebra Γ(S, ⊤) Γ(T, ⊤) := g.appTop.hom.toAlgebra
    ∀ [Algebra (Localization W) Γ(T, ⊤)]
      [IsScalarTower Γ(S, ⊤) (Localization W) Γ(T, ⊤)],
    Γ(T, ⊤) ⊗[Localization W]
      LocalizedModule W (baseSections (structureModule X) f.appTop.hom ⊤) →+
        baseSections (structureModule P) q.appTop.hom ⊤ := by
  dsimp only
  let _ : Algebra Γ(S, ⊤) Γ(T, ⊤) := g.appTop.hom.toAlgebra
  intro _ _
  exact (localizedKernelSectionsEquiv h U hU hCover W).toAddMonoidHom.comp
    (sectionsTensorKernel (structureModule X) U f.appTop.hom hCover W Γ(T, ⊤)).toAddMonoidHom

/-- Kernel base change gives actual global-section base change on the same localization. -/
lemma localizedSectionsComparison_bijective :
    let _ : Algebra Γ(S, ⊤) Γ(T, ⊤) := g.appTop.hom.toAlgebra
    ∀ [Algebra (Localization W) Γ(T, ⊤)]
      [IsScalarTower Γ(S, ⊤) (Localization W) Γ(T, ⊤)],
    Function.Bijective (LinearMap.tensorKer (Localization W) Γ(T, ⊤)
      (localD (structureModule X) U f.appTop.hom W 0)) →
    Function.Bijective (localizedSectionsComparison h U hU hCover W) := by
  dsimp only
  let _ : Algebra Γ(S, ⊤) Γ(T, ⊤) := g.appTop.hom.toAlgebra
  intro _ _ hk
  exact (localizedKernelSectionsEquiv h U hU hCover W).bijective.comp
    (sectionsTensorKernel_bijective (structureModule X) U f.appTop.hom hCover W Γ(T, ⊤) hk)

end FLT.Mazur.IncreasingCechCartesian
