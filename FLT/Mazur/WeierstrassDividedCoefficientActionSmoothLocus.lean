/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedGlobalActionSmoothLocus
public import FLT.Mazur.WeierstrassDividedGlobalCoefficientAction

/-!
# Smooth-locus invariance after arbitrary coefficient extension

The existing coefficient action preserves the full relative smooth locus.
The proof uses the Cartesian smooth-locus formula, so it also applies to
residue fields and nonreduced coefficient rings.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassIntegralChart
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option quotPrecheck false
universe u
variable {R : Type u} [CommRing R] [IsDomain R] [IsBezout R] [IsNoetherianRing R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val)) (j : ℕ) (hj : j ≤ n)
  (S : Type u) [CommRing S] [Algebra R S]
local notation "V" => W.map (algebraMap R S)
local notation "q" => Spec.map (CommRingCat.ofHom (algebraMap R S))
local notation "base" => finiteGlobalStructure hπ data j hj
local notation "fst" => pullback.fst q base
local notation "snd" => pullback.snd q base

/-- The full extended smooth locus is precisely the inverse image of the original one. -/
theorem finiteGlobalTensor_preimage_smooth :
    snd ⁻¹ᵁ (base).smoothLocus = (fst).smoothLocus :=
  smoothLocus_preimage_of_isPullback (IsPullback.of_hasPullback q base).flip

/-- The actual coefficient action preserves smoothness on every scheme of inputs. -/
theorem finiteGlobalCoefficientPointAction_preimage_smooth {T : Scheme.{u}}
    (a : T ⟶ (integralSmoothOpen V).toScheme)
    (b : T ⟶ finiteGlobalTensorModel hπ data S j hj)
    (h : a ≫ integralSmoothStructure V = b ≫ fst) :
    finiteGlobalCoefficientPointAction hπ data j hj S a b h ⁻¹ᵁ (fst).smoothLocus =
      b ⁻¹ᵁ (fst).smoothLocus := by
  rw [← finiteGlobalTensor_preimage_smooth hπ data j hj S,
    ← Scheme.Hom.comp_preimage, finiteGlobalCoefficientPointAction_projection,
    finiteGlobalPointAction_preimage_smooth, Scheme.Hom.comp_preimage]

/-- Universal coefficient translation has exactly the full smooth second-input domain. -/
theorem finiteGlobalCoefficientAction_preimage_smooth :
    finiteGlobalCoefficientAction hπ data j hj S ⁻¹ᵁ (fst).smoothLocus =
      pullback.snd (integralSmoothStructure V) fst ⁻¹ᵁ (fst).smoothLocus :=
  finiteGlobalCoefficientPointAction_preimage_smooth hπ data j hj S _ _ _

/-- Restrict the existing coefficient action to the entire extended smooth model. -/
def finiteGlobalCoefficientSmoothPointAction {T : Scheme.{u}}
    (a : T ⟶ (integralSmoothOpen V).toScheme) (b : T ⟶ (fst).smoothLocus.toScheme)
    (h : a ≫ integralSmoothStructure V = b ≫ (fst).smoothLocus.ι ≫ fst) :
    T ⟶ (fst).smoothLocus.toScheme :=
  IsOpenImmersion.lift (fst).smoothLocus.ι
    (finiteGlobalCoefficientPointAction hπ data j hj S a (b ≫ (fst).smoothLocus.ι)
      (by simpa only [Category.assoc] using h)) (by
      rw [Scheme.Opens.range_ι]
      have he := finiteGlobalCoefficientPointAction_preimage_smooth hπ data j hj S a
        (b ≫ (fst).smoothLocus.ι) (by simpa only [Category.assoc] using h)
      rw [Scheme.Hom.comp_preimage, Scheme.Opens.ι_preimage_self] at he
      rintro _ ⟨x, rfl⟩
      exact he.ge (Set.mem_univ x))

/-- Inclusion recovers the previously constructed full coefficient action exactly. -/
@[reassoc] theorem finiteGlobalCoefficientSmoothPointAction_inclusion {T : Scheme.{u}}
    (a : T ⟶ (integralSmoothOpen V).toScheme) (b : T ⟶ (fst).smoothLocus.toScheme)
    (h : a ≫ integralSmoothStructure V = b ≫ (fst).smoothLocus.ι ≫ fst) :
    finiteGlobalCoefficientSmoothPointAction hπ data j hj S a b h ≫ (fst).smoothLocus.ι =
      finiteGlobalCoefficientPointAction hπ data j hj S a (b ≫ (fst).smoothLocus.ι)
        (by simpa only [Category.assoc] using h) := IsOpenImmersion.lift_fac _ _ _

/-- The restricted coefficient action retains the original extended base morphism. -/
@[reassoc] theorem finiteGlobalCoefficientSmoothPointAction_structure {T : Scheme.{u}}
    (a : T ⟶ (integralSmoothOpen V).toScheme) (b : T ⟶ (fst).smoothLocus.toScheme)
    (h : a ≫ integralSmoothStructure V = b ≫ (fst).smoothLocus.ι ≫ fst) :
    finiteGlobalCoefficientSmoothPointAction hπ data j hj S a b h ≫
        (fst).smoothLocus.ι ≫ fst = a ≫ integralSmoothStructure V := by
  rw [finiteGlobalCoefficientSmoothPointAction_inclusion_assoc,
    finiteGlobalCoefficientPointAction_structure]

end FLT.Mazur.WeierstrassDividedDepth
