/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.FreyCurve.Serre.VeluKernelProductCover
public import FLT.GroupScheme.ConstantProductSections

/-!
# Original label pairs detect rational kernel product morphisms

The geometric product cover retains both original evaluations. Faithfully
flat descent and coproduct extensionality detect equality of entire morphisms.
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

local notation "K" => primeKernelRationalScheme E p q hq hfixed
local notation "C" => ConstantCyclicGroup.model (Spec (CommRingCat.of (AlgebraicClosure ℚ))) p
local notation "c" => ConstantCyclicGroup.component (Spec (CommRingCat.of (AlgebraicClosure ℚ))) p

/-- The geometric product cover retains the original pair section exactly. -/
@[reassoc] theorem primeKernelProductProjection_pair (i j : ZMod p) :
    (lift (c i) (c j)).left ≫ primeKernelProductProjection E p q hq hfixed =
      primeKernelPairSection E p q hq hfixed i j := by
  apply pullback.hom_ext
  · rw [Category.assoc, primeKernelProductProjection_fst, primeKernelPairSection_fst]
    change (lift (c i) (c j)).left ≫ (fst C C).left ≫ _ = _
    rw [← Over.comp_left_assoc, lift_fst]
    exact primeKernelPullbackIso_component_snd E p q hq hfixed i
  · rw [Category.assoc, primeKernelProductProjection_snd, primeKernelPairSection_snd]
    change (lift (c i) (c j)).left ≫ (snd C C).left ≫ _ = _
    rw [← Over.comp_left_assoc, lift_snd]
    exact primeKernelPullbackIso_component_snd E p q hq hfixed j

/-- Original pairs jointly detect all scheme morphisms from the rational kernel product. -/
theorem primeKernelPairSection_hom_ext {T : Scheme} {f g : (K ⊗ K).left ⟶ T}
    (h : ∀ i j, primeKernelPairSection E p q hq hfixed i j ≫ f =
      primeKernelPairSection E p q hq hfixed i j ≫ g) : f = g := by
  apply (cancel_epi (primeKernelProductProjection E p q hq hfixed)).mp
  apply FLT.GroupScheme.constantCyclic_pair_hom_ext _ _ p
  intro i j
  simpa only [primeKernelProductProjection_pair_assoc] using h i j

end WeierstrassCurve.Velu
