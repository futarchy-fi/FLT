/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.FreyCurve.Serre.VeluCoefficientOverlap
public import FLT.Mazur.WeierstrassCoefficientOverlapReduced

/-!
# Galois graphs cover and detect maps from the actual source overlap

Cartesian transfer of coefficient evaluations covers every point of the
original cubic kernel pair. Its proved reducedness then detects equality
of maps to a relatively separated target.
-/

@[expose] public noncomputable section

open CategoryTheory Limits AlgebraicGeometry
open FLT.Mazur.WeierstrassIntegralChart FLT.Mazur.GaloisTensorPrime

namespace WeierstrassCurve.Velu

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {K L : Type} [Field K] [Field L] [Algebra K L]
  (E : WeierstrassCurve K)

local notation "c" => integralCoefficientMorphism (S := L) E
local notation "EL" => E.map (algebraMap K L)

/-- The actual Galois graphs assembled as a single map to the source kernel pair. -/
def coefficientGraphCover : (∐ fun _ : L ≃ₐ[K] L ↦ integralCurve EL) ⟶ pullback c c :=
  Sigma.desc (coefficientGaloisGraph E)

variable [Algebra.IsAlgebraic K L] [IsAlgClosed L]

/-- Every point of the original source overlap lies on an actual Galois graph. -/
theorem coefficientGaloisGraph_jointly_surjective (x : ↥(pullback c c)) :
    ∃ (g : L ≃ₐ[K] L) (y : integralCurve EL), coefficientGaloisGraph E g y = x := by
  obtain ⟨g, hg⟩ := prime_surjective (coefficientOverlapBase E x)
  obtain ⟨y, hy, _⟩ := Scheme.exists_preimage_of_isPullback
    (coefficientGaloisGraph_isPullback E g) x (IsLocalRing.closedPoint L) (by
      rw [evaluationSpec_point, hg])
  exact ⟨g, y, hy⟩

/-- The original graph family covers the whole kernel-pair scheme. -/
instance coefficientGraphCover_surjective : Surjective (coefficientGraphCover (L := L) E) := by
  constructor
  intro x
  obtain ⟨g, y, hy⟩ := coefficientGaloisGraph_jointly_surjective E x
  refine ⟨Sigma.ι (fun _ : L ≃ₐ[K] L ↦ integralCurve EL) g y, ?_⟩
  rw [← Scheme.Hom.comp_apply, coefficientGraphCover, Sigma.ι_comp_desc]
  exact hy

variable [CharZero K]

/-- Equality on actual Galois graphs detects whole morphisms out of the source overlap. -/
theorem coefficientOverlap_hom_ext {Y Z : Scheme} (i : Y ⟶ Z) [IsSeparated i]
    (f g : pullback c c ⟶ Y) (hb : f ≫ i = g ≫ i)
    (h : ∀ a : L ≃ₐ[K] L, coefficientGaloisGraph E a ≫ f =
      coefficientGaloisGraph E a ≫ g) : f = g := by
  apply ext_of_isDominant_of_isSeparated i hb (coefficientGraphCover E)
  apply Sigma.hom_ext
  intro a
  simpa only [coefficientGraphCover, Sigma.ι_comp_desc_assoc] using h a

/-- Galois invariance gives compatibility on the full original kernel pair. -/
theorem coefficientInvariant_kernelPair {Y Z : Scheme} (i : Y ⟶ Z) [IsSeparated i]
    (j : integralCurve E ⟶ Z) (f : integralCurve EL ⟶ Y) (hb : f ≫ i = c ≫ j)
    (h : ∀ a : L ≃ₐ[K] L, integralGaloisMap E a ≫ f = f) :
    pullback.fst c c ≫ f = pullback.snd c c ≫ f := by
  apply coefficientOverlap_hom_ext E i
  · simp only [Category.assoc, hb, pullback.condition_assoc]
  · intro a
    rw [coefficientGaloisGraph_fst_assoc, coefficientGaloisGraph_snd_assoc, h a]

end WeierstrassCurve.Velu
