/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.FreyCurve.Serre.VeluKernelRationalMultiplication

/-!
# A geometric cover of the rational kernel product

The original constant kernel identifies with the coefficient pullback as an
object over Qbar. Its product therefore covers the actual rational product.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
open CartesianMonoidalCategory

namespace WeierstrassCurve.Velu

open FLT.Mazur

variable (E : WeierstrassCurve ℚ) [E.IsElliptic] (p : ℕ) [Fact p.Prime]
  (q : (E.map (algebraMap ℚ (AlgebraicClosure ℚ))).nTorsion p →ₗ[ZMod p] ZMod p)
  (hq : Function.Surjective q)
  (hfixed : ∀ g t, q (E.torsionGaloisRepresentation p g t) = q t)

local notation "b" => Spec.map (CommRingCat.ofHom (algebraMap ℚ (AlgebraicClosure ℚ)))
local notation "K" => primeKernelRationalScheme E p q hq hfixed
local notation "C" => ConstantCyclicGroup.model (Spec (CommRingCat.of (AlgebraicClosure ℚ))) p

/-- The existing geometric comparison as an isomorphism over the geometric base. -/
def primeKernelPullbackOverIso : C ≅ (Over.pullback b).obj K :=
  Over.isoMk (primeKernelPullbackIso E p q hq hfixed ≪≫ pullbackSymmetry _ _)
    (by
      change _ ≫ pullback.snd (K).hom b = _
      simp only [Iso.trans_hom, Category.assoc, pullbackSymmetry_hom_comp_snd]
      exact primeKernelPullbackIso_fst E p q hq hfixed)

/-- The product of the original geometric kernels is the pullback of the rational product. -/
def primeKernelProductPullbackIso : C ⊗ C ≅ (Over.pullback b).obj (K ⊗ K) :=
  tensorIso (primeKernelPullbackOverIso E p q hq hfixed)
    (primeKernelPullbackOverIso E p q hq hfixed) ≪≫
      (prodComparisonIso (Over.pullback b) K K).symm

/-- Projection from the original geometric product to the actual rational product. -/
def primeKernelProductProjection : (C ⊗ C).left ⟶ (K ⊗ K).left :=
  (primeKernelProductPullbackIso E p q hq hfixed).hom.left ≫ pullback.fst _ _

/-- The geometric product projection is an epimorphism by faithful flatness. -/
instance primeKernelProductProjection_epi :
    Epi (primeKernelProductProjection E p q hq hfixed) := by
  have hb := (flat_and_surjective_SpecMap_iff
    (CommRingCat.ofHom (algebraMap ℚ (AlgebraicClosure ℚ)))).mpr
      (RingHom.faithfullyFlat_algebraMap_iff.mpr inferInstance)
  let _ : Flat b := hb.1
  let _ : Surjective b := hb.2
  let _ : Epi (pullback.fst (K ⊗ K).hom b) :=
    Flat.epi_of_flat_of_surjective _
  unfold primeKernelProductProjection
  infer_instance

/-- The first projection is the original geometric comparison followed by coefficient descent. -/
@[reassoc] theorem primeKernelProductProjection_fst :
    primeKernelProductProjection E p q hq hfixed ≫ pullback.fst _ _ =
      pullback.fst (C).hom (C).hom ≫ (primeKernelPullbackIso E p q hq hfixed).hom ≫
        pullback.snd _ _ := by
  change (tensorIso (primeKernelPullbackOverIso E p q hq hfixed)
    (primeKernelPullbackOverIso E p q hq hfixed)).hom.left ≫
      (prodComparisonIso (Over.pullback b) K K).inv.left ≫
        pullback.fst (pullback.fst (K).hom (K).hom ≫ (K).hom) b ≫
          pullback.fst (K).hom (K).hom = _
  rw [Over.prodComparisonIso_pullback_inv_left_fst_fst]
  change ((primeKernelPullbackOverIso E p q hq hfixed).hom ⊗ₘ
    (primeKernelPullbackOverIso E p q hq hfixed).hom).left ≫
      (fst ((Over.pullback b).obj K) ((Over.pullback b).obj K)).left ≫ pullback.fst (K).hom b = _
  rw [← Category.assoc, ← Over.comp_left, tensorHom_fst, Over.comp_left]
  change pullback.fst (C).hom (C).hom ≫
    ((primeKernelPullbackIso E p q hq hfixed).hom ≫ (pullbackSymmetry b (K).hom).hom) ≫
      pullback.fst (K).hom b = _
  rw [Category.assoc, pullbackSymmetry_hom_comp_fst]

/-- The second projection is the original geometric comparison followed by coefficient descent. -/
@[reassoc] theorem primeKernelProductProjection_snd :
    primeKernelProductProjection E p q hq hfixed ≫ pullback.snd _ _ =
      pullback.snd (C).hom (C).hom ≫ (primeKernelPullbackIso E p q hq hfixed).hom ≫
        pullback.snd _ _ := by
  change (tensorIso (primeKernelPullbackOverIso E p q hq hfixed)
    (primeKernelPullbackOverIso E p q hq hfixed)).hom.left ≫
      (prodComparisonIso (Over.pullback b) K K).inv.left ≫
        pullback.fst (pullback.fst (K).hom (K).hom ≫ (K).hom) b ≫
          pullback.snd (K).hom (K).hom = _
  have hs : (prodComparisonIso (Over.pullback b) K K).inv.left ≫
      pullback.fst (pullback.fst (K).hom (K).hom ≫ (K).hom) b ≫
        pullback.snd (K).hom (K).hom =
      pullback.snd (pullback.snd (K).hom b) (pullback.snd (K).hom b) ≫
        pullback.fst (K).hom b :=
    Over.prodComparisonIso_pullback_inv_left_fst_snd' b (K).hom (K).hom
  rw [hs]
  change ((primeKernelPullbackOverIso E p q hq hfixed).hom ⊗ₘ
    (primeKernelPullbackOverIso E p q hq hfixed).hom).left ≫
      (snd ((Over.pullback b).obj K) ((Over.pullback b).obj K)).left ≫ pullback.fst (K).hom b = _
  rw [← Category.assoc, ← Over.comp_left, tensorHom_snd, Over.comp_left]
  change pullback.snd (C).hom (C).hom ≫
    ((primeKernelPullbackIso E p q hq hfixed).hom ≫ (pullbackSymmetry b (K).hom).hom) ≫
      pullback.fst (K).hom b = _
  rw [Category.assoc, pullbackSymmetry_hom_comp_fst]


end WeierstrassCurve.Velu
