/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.IncreasingCechCartesianKernel
public import FLT.Mazur.IncreasingCechSectionCoordinates

/-!
# The geometric section formula on actual bounded cycles

The chart comparison sends the tensor of an original section cycle to the cycle
of its pullback multiplied by the actual coefficient function. Gluing therefore
has the same formula on global sections.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory AlgebraicGeometry TensorProduct
namespace FLT.Mazur.IncreasingCechCartesian
open IncreasingCechComplex IncreasingCechScalars FCurve Chow CechSheafHZero

variable {P X T S : Scheme.{0}}
  {p : P ⟶ X} {q : P ⟶ T} {f : X ⟶ S} {g : T ⟶ S}
  (h : IsPullback p q f g) [IsAffine T] [IsAffine S] [X.IsSeparated]
  {ι : Type} [LinearOrder ι] [Finite ι] (U : ι → X.Opens)
  (hU : ∀ i, IsAffineOpen (U i)) (hCover : iSup U = ⊤)

/-- A pure tensor of a section cycle is the cycle of the product of actual pullbacks. -/
lemma geometricTermEquiv_section (b : Γ(T, ⊤)) (s : Γ(X, ⊤)) :
    let _ : Algebra Γ(S, ⊤) Γ(T, ⊤) := g.appTop.hom.toAlgebra
    geometricTermEquiv h U hU 0
        (b ⊗ₜ[Γ(S, ⊤)] (baseSectionsZeroKernelEquiv
          (structureModule X) U f.appTop.hom hCover s).val) =
      (baseSectionsZeroKernelEquiv (structureModule P) (fun i ↦ p ⁻¹ᵁ U i)
        q.appTop.hom (p.iSup_preimage_eq_top hCover) (q.appTop b * p.appTop s)).val := by
  dsimp only
  let _ : Algebra Γ(S, ⊤) Γ(T, ⊤) := g.appTop.hom.toAlgebra
  apply (baseTermCoordinates (structureModule P) (fun i ↦ p ⁻¹ᵁ U i)
    q.appTop.hom 0).injective
  funext a
  change baseTermCoordinates _ _ _ 0 (chartTermEquiv p q U 0
    (termComparison h U 0 (_ ⊗ₜ[Γ(S, ⊤)] _))) a = _
  rw [chartTermEquiv_apply, termComparison_tmul, baseSectionsZeroKernelEquiv_apply]
  change _ = (baseSectionsZeroKernelEquiv (structureModule P) (fun i ↦ p ⁻¹ᵁ U i)
    q.appTop.hom (p.iSup_preimage_eq_top hCover) (q.appTop b * p.appTop s)).val a
  rw [baseSectionsZeroKernelEquiv_apply]
  change P.presheaf.map _ (_ * _) = P.presheaf.map _ (_ * _)
  rw [map_mul, map_mul]
  congr 1
  · rw [← Functor.map_comp_apply]
    rfl
  · have hn := congrArg (fun k ↦ k s) (p.naturality (homOfLE
      (show V U 0 a.val ≤ ⊤ from le_top)).op)
    simp only [CommRingCat.comp_apply] at hn
    change P.presheaf.map _ (p.app _ (X.presheaf.map _ s)) = _
    rw [hn, ← Functor.map_comp_apply]
    rfl

/-- Gluing a tensor cycle with this numerator gives the actual product section. -/
lemma tensorKernelSectionsEquiv_section (b : Γ(T, ⊤)) (s : Γ(X, ⊤))
    (z : (tensorD (f := f) (g := g) U 0).ker)
    (hz : let _ : Algebra Γ(S, ⊤) Γ(T, ⊤) := g.appTop.hom.toAlgebra
      z.val = b ⊗ₜ[Γ(S, ⊤)]
        (baseSectionsZeroKernelEquiv (structureModule X) U f.appTop.hom hCover s).val) :
    tensorKernelSectionsEquiv h U hU hCover z = q.appTop b * p.appTop s := by
  apply (baseSectionsZeroKernelEquiv (structureModule P) (fun i ↦ p ⁻¹ᵁ U i)
    q.appTop.hom (p.iSup_preimage_eq_top hCover)).injective
  dsimp only [tensorKernelSectionsEquiv, LinearEquiv.trans_apply]
  rw [LinearEquiv.apply_symm_apply]
  apply Subtype.ext
  change geometricTermEquiv h U hU 0 z.val = _
  rw [hz]
  exact geometricTermEquiv_section h U hU hCover b s

end FLT.Mazur.IncreasingCechCartesian
