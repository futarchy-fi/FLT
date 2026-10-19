/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedCoefficientActionSmoothLocus
public import FLT.Mazur.WeierstrassDividedResolvedSmoothAction

/-!
# Cartesian coefficient comparison of the full resolved smooth action

The full smooth locus and its constructed action commute with the actual
coefficient projection. No replacement model or component coordinates enter.
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
local notation "U" => (fst).smoothLocus
local notation "U₀" => (base).smoothLocus

/-- The actual coefficient projection restricted to the full smooth opens. -/
def finiteGlobalTensorSmoothProjection : (U).toScheme ⟶ (U₀).toScheme :=
  IsOpenImmersion.lift (U₀).ι ((U).ι ≫ snd) (by
    rw [Scheme.Opens.range_ι]
    have he : ((U).ι ≫ snd) ⁻¹ᵁ U₀ = ⊤ := by
      rw [Scheme.Hom.comp_preimage, finiteGlobalTensor_preimage_smooth,
        Scheme.Opens.ι_preimage_self]
    rintro _ ⟨x, rfl⟩
    exact he.ge (Set.mem_univ x))

/-- The smooth comparison retains the original full-model coefficient projection. -/
@[reassoc] theorem finiteGlobalTensorSmoothProjection_inclusion :
    finiteGlobalTensorSmoothProjection hπ data j hj S ≫ (U₀).ι = (U).ι ≫ snd :=
  IsOpenImmersion.lift_fac _ _ _

/-- The full smooth-open square is Cartesian over the original model projection. -/
theorem finiteGlobalTensorSmoothProjection_isPullback :
    IsPullback (finiteGlobalTensorSmoothProjection hπ data j hj S) (U).ι (U₀).ι snd := by
  apply IsOpenImmersion.isPullback _ _ _ _
    (finiteGlobalTensorSmoothProjection_inclusion hπ data j hj S).symm
  rw [Scheme.Opens.opensRange_ι, Scheme.Opens.opensRange_ι,
    finiteGlobalTensor_preimage_smooth]

/-- The restricted comparison retains the exact coefficient square. -/
@[reassoc] theorem finiteGlobalTensorSmoothProjection_structure :
    finiteGlobalTensorSmoothProjection hπ data j hj S ≫ (U₀).ι ≫ base =
      (U).ι ≫ fst ≫ q := by
  rw [finiteGlobalTensorSmoothProjection_inclusion_assoc, pullback.condition]

/-- The coefficient action projects to the constructed action on the original smooth model. -/
theorem finiteGlobalCoefficientSmoothPointAction_projection {T : Scheme.{u}}
    (a : T ⟶ (integralSmoothOpen V).toScheme) (b : T ⟶ (U).toScheme)
    (h : a ≫ integralSmoothStructure V = b ≫ (U).ι ≫ fst) :
    finiteGlobalCoefficientSmoothPointAction hπ data j hj S a b h ≫
        finiteGlobalTensorSmoothProjection hπ data j hj S =
      finiteGlobalSmoothPointAction hπ data j hj (a ≫ originalSmoothCoefficientMap S W)
        (b ≫ finiteGlobalTensorSmoothProjection hπ data j hj S)
        (by
          simp only [Category.assoc, originalSmoothCoefficientMap_structure,
            finiteGlobalTensorSmoothProjection_structure]
          simpa only [Category.assoc] using congrArg (· ≫ q) h) := by
  apply (cancel_mono (U₀).ι).mp
  rw [Category.assoc, finiteGlobalTensorSmoothProjection_inclusion,
    finiteGlobalCoefficientSmoothPointAction_inclusion_assoc,
    finiteGlobalCoefficientPointAction_projection, finiteGlobalSmoothPointAction_inclusion]
  simp only [Category.assoc, finiteGlobalTensorSmoothProjection_inclusion]

end FLT.Mazur.WeierstrassDividedDepth
