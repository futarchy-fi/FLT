/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OneGonAdicCharacterChartTower
public import FLT.Mazur.FiniteCharacterAdicHom

/-!
# Effectivity of the constructed character tower in the original Y chart

For a finite character group and an adically complete base, the constructed
homomorphisms determine an actual map from the original character spectrum
into the original Y chart. Every prescribed finite-stage map is recovered exactly.
The relative structure equation, factorization through the full smooth group,
and the group law over the complete base are separate subsequent steps.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

namespace FLT.Mazur.OneGonAdicCharacterTower

open OneGonSmoothing WeierstrassIntegralChart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {R G : Type} [CommRing R] [AddCommGroup G] (I : Ideal R) (t : R)
  (ht : t ∈ I) (g : stageSource I G 0 ⟶ stageGroup I t 0)

/-- The full coordinate homomorphism of each constructed map to the original Y chart. -/
def towerCoordinates (m : ℕ) : Coordinate (equation t) 1 →+*
    AddMonoidAlgebra (StageRing I m) G := (Spec.preimage (towerAffine I t ht g m)).hom

/-- The coordinate maps retain the genuine adjacent coefficient reductions. -/
theorem towerCoordinates_reduction (m : ℕ) :
    (FiniteCharacterAdicElements.restriction I m).comp (towerCoordinates I t ht g (m + 1)) =
      towerCoordinates I t ht g m := by
  have h := towerAffine_reduction I t ht g m
  rw [← Spec.map_preimage (towerAffine I t ht g (m + 1)),
    ← Spec.map_preimage (towerAffine I t ht g m), ← Spec.map_comp] at h
  exact congrArg (fun k => k.hom) (Spec.map_injective h)

variable [Finite G] [IsAdicComplete I R]

/-- The constructed tower as an actual map from the original complete-base character spectrum. -/
def effectiveAffine : Spec (.of (AddMonoidAlgebra R G)) ⟶ chartScheme (equation t) 1 :=
  Spec.map (CommRingCat.ofHom (FiniteCharacterAdicHom.liftHom I
    (towerCoordinates I t ht g) (towerCoordinates_reduction I t ht g)))

/-- Every finite-stage map is the actual coefficient restriction of the effective affine map. -/
theorem effectiveAffine_reduction (m : ℕ) :
    Spec.map (CommRingCat.ofHom (FiniteCharacterAdicElements.reduction (G := G) I m)) ≫
      effectiveAffine I t ht g = towerAffine I t ht g m := by
  rw [effectiveAffine, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
    FiniteCharacterAdicHom.reduction_liftHom]
  exact Spec.map_preimage _

/-- The original complete affine map is uniquely determined by these full finite reductions. -/
theorem effectiveAffine_unique
    (q : Spec (.of (AddMonoidAlgebra R G)) ⟶ chartScheme (equation t) 1)
    (hq : ∀ m, Spec.map
      (CommRingCat.ofHom (FiniteCharacterAdicElements.reduction (G := G) I m)) ≫
        q = towerAffine I t ht g m) : q = effectiveAffine I t ht g := by
  rw [← Spec.map_preimage q, effectiveAffine]
  congr 1
  apply CommRingCat.hom_ext
  apply FiniteCharacterAdicHom.liftHom_unique I (towerCoordinates I t ht g)
    (towerCoordinates_reduction I t ht g) (Spec.preimage q).hom
  intro m
  have h := hq m
  rw [← Spec.map_preimage q, ← Spec.map_preimage (towerAffine I t ht g m),
    ← Spec.map_comp] at h
  exact congrArg (fun k => k.hom) (Spec.map_injective h)

end FLT.Mazur.OneGonAdicCharacterTower
