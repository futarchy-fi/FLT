/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.LaurentPairSwap
public import FLT.Mazur.PolygonCompleteIdentityFiniteAlgebra
public import FLT.Mazur.PolygonCompleteIdentityNilpotentDefect

/-!
# Symmetry of the actual original finite multiplication error

Commutativity of the constructed original identity group exchanges the two
full Laurent inputs. Its actual coordinate map, unit and additive error
retain this symmetry before any reduction of the coefficient ring.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory MonObj
open scoped LaurentPolynomial
namespace FLT.Mazur.PolygonInfinitesimalStages
open LaurentPolynomial PolygonScalingNaturality LaurentPairSwap
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase
  completePointWeierstrassCurve completePointToIntegralCubic originalStageToCompatibleProj
variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n] (i : Fin n) (m : ℕ)
local notation "A" => Ring K m
local notation "G" => completePointOriginalBaseGroup K n h i
local notation "e" => completeIdentityStageTorus K n h i m
local notation "σ" => Spec.map (CommRingCat.ofHom (swap (A)))
local notation "b" => Spec.map (CommRingCat.ofHom (algebraMap (A) (A)[T;T⁻¹]))
local notation "p" => Spec.map (CommRingCat.ofHom
  (algebraMap (A)[T;T⁻¹] (A)[T;T⁻¹][T;T⁻¹]))
local notation "r" => Spec.map (CommRingCat.ofHom (coeffMap (C : (A) →+* (A)[T;T⁻¹])))

/-- Swapping the double Laurent input exchanges the original group pair. -/
@[reassoc] theorem completeIdentityFinitePair_swap :
    (σ) ≫ completeIdentityFinitePair K n h i m =
      completeIdentityFinitePair K n h i m ≫ (β_ (G).X (G).X).hom.left := by
  have hs₁ : (σ) ≫ (p) = (r) := by
    rw [← Spec.map_comp]
    exact congrArg (fun f ↦ Spec.map (CommRingCat.ofHom f)) (RingHom.ext (swap_C (A)))
  have hs₂ : (σ) ≫ (r) = (p) := by
    rw [← Spec.map_comp]
    exact congrArg (fun f ↦ Spec.map (CommRingCat.ofHom f))
      (RingHom.ext (swap_coeffMap (A)))
  apply pullback.hom_ext
  · rw [Category.assoc, completeIdentityFinitePair_fst, ← Category.assoc, hs₁]
    rw [Category.assoc, Over.braiding_hom_left, pullbackSymmetry_hom_comp_fst,
      completeIdentityFinitePair_snd]
  · rw [Category.assoc, completeIdentityFinitePair_snd, ← Category.assoc, hs₂]
    rw [Category.assoc, Over.braiding_hom_left, pullbackSymmetry_hom_comp_snd,
      completeIdentityFinitePair_fst]

/-- Original commutativity applies to the unchanged finite Laurent pair. -/
@[reassoc] theorem completeIdentityFiniteOriginalMul_swap :
    (σ) ≫ completeIdentityFiniteOriginalMul K n h i m =
      completeIdentityFiniteOriginalMul K n h i m := by
  rw [completeIdentityFiniteOriginalMul, completeIdentityFinitePair_swap_assoc]
  have he := congrArg Over.Hom.left (IsCommMonObj.mul_comm (X := (G).X))
  change (β_ (G).X (G).X).hom.left ≫ (μ[(G).X]).left = (μ[(G).X]).left at he
  rw [he]

/-- The actual full coordinate morphism is symmetric, with its coefficient base fixed. -/
@[reassoc] theorem completeIdentityFiniteMulCoordinates_swap :
    (σ) ≫ completeIdentityFiniteMulCoordinates K n h i m =
      completeIdentityFiniteMulCoordinates K n h i m := by
  apply completeIdentityFiniteMulCoordinates_unique K n h i m
  · rw [Category.assoc, completeIdentityFiniteMulCoordinates_original,
      completeIdentityFiniteOriginalMul_swap]
  · rw [Category.assoc, completeIdentityFiniteMulCoordinates_base,
      ← Spec.map_comp, ← Spec.map_comp]
    apply congrArg (fun f ↦ Spec.map (CommRingCat.ofHom f))
    apply RingHom.ext
    intro a
    change swap (A) (C (C a)) = C (C a)
    rw [swap_C, coeffMap_C]

/-- The original coefficient algebra map retains both full Laurent variables symmetrically. -/
theorem completeIdentityFiniteMulAlgebra_swap :
    (swap (A)).comp (completeIdentityFiniteMulAlgebra K n h i m).toRingHom =
      (completeIdentityFiniteMulAlgebra K n h i m).toRingHom := by
  have he := completeIdentityFiniteMulCoordinates_swap K n h i m
  rw [← completeIdentityFiniteMulAlgebra_spec, ← Spec.map_comp] at he
  exact congrArg CommRingCat.Hom.hom (Spec.map_injective he)

/-- The actual additive multiplication error is invariant under exchanging inputs. -/
theorem completeIdentityFiniteMulDefect_swap :
    swap (A) (completeIdentityFiniteMulDefect K n h i m) =
      completeIdentityFiniteMulDefect K n h i m := by
  have he := congrArg (fun f : (A)[T;T⁻¹] →+* (A)[T;T⁻¹][T;T⁻¹] ↦ f (T 1))
    (completeIdentityFiniteMulAlgebra_swap K n h i m)
  change swap (A) (completeIdentityFiniteMulUnit K n h i m).val =
    (completeIdentityFiniteMulUnit K n h i m).val at he
  rw [completeIdentityFiniteMulDefect, map_sub, he, swap_product]

end FLT.Mazur.PolygonInfinitesimalStages
