/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassSuccessiveXResidueMiddleOverlap
public import FLT.Mazur.WeierstrassSuccessiveXResidueComponentPoints
public import FLT.Mazur.PrincipalOpenTensorGeometry
public import Mathlib.AlgebraicGeometry.Pullbacks

/-!
# The full conic boundary square in the original residue chart

The established algebra equivalence gives the actual scheme isomorphism
between the whole transition open and the conic incidence open. Its square
is cartesian and retains restriction of every original tensor function.
-/

@[expose] public noncomputable section
open IsLocalRing AlgebraicGeometry CategoryTheory Limits
namespace FLT.Mazur.WeierstrassSuccessiveX
open WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] [IsDomain R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} {n : ℕ} (D : SplitNodeDepth W π n)
  (k : ℕ) (hk0 : 0 < k) (hk : 2 * (k + 1) ≤ n) (b3 b4 b6 : R)
  (h3 : W.a₃ = π ^ (k + 1) * b3) (h4 : W.a₄ = π ^ (k + 1) * b4)
local notation "K" => ResidueField R
local notation "W₀" => W.map (residue R)
local notation "c" => residue R b6
local notation "C₀" => ConicCoordinate (WeierstrassCurve.a₁ W₀) c
local notation "B" => MiddleConicOpen W₀ c
local notation "t" => coord W (π ^ k) π b3 b4 b6 0
local notation "C" => residueSuccessiveConicImmersion D k hk0 hk b3 b4 b6 h3 h4
local notation "i" => Spec.map (CommRingCat.ofHom (algebraMap C₀ B))

/-- The entire conic incidence open is the entire original tensor transition open. -/
def residueConicBoundaryIso : Spec (.of B) ≅
    Spec (.of (ResidueMiddleOpen (W := W) (π := π) k b3 b4 b6)) :=
  Scheme.Spec.mapIso
    (residueMiddleConicOpenEquiv D k hk0 hk b3 b4 b6 h3 h4).toRingEquiv.toCommRingCatIso.op

/-- The boundary isomorphism retains the actual immersion and every original function. -/
@[reassoc] theorem residueConicBoundaryIso_inclusion :
    (residueConicBoundaryIso D k hk0 hk b3 b4 b6 h3 h4).hom ≫
      PrincipalOpenTensor.inclusion K t = i ≫ C := by
  rw [residueSuccessiveConicImmersion_eq_spec]
  change Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
  rw [← Spec.map_comp, ← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  exact RingHom.ext (residueMiddleConicOpenEquiv_base D k hk0 hk b3 b4 b6 h3 h4)

/-- Pulling the conic into the transition open retains that entire open. -/
theorem residueConicBoundary_isPullback :
    IsPullback (residueConicBoundaryIso D k hk0 hk b3 b4 b6 h3 h4).hom i
      (PrincipalOpenTensor.inclusion K t) C :=
  IsPullback.of_horiz_isIso_mono
    ⟨residueConicBoundaryIso_inclusion D k hk0 hk b3 b4 b6 h3 h4⟩

/-- The transition open factors through the full original conic, with no coefficient lost. -/
@[reassoc] theorem residueConicBoundaryIso_inverse_inclusion :
    (residueConicBoundaryIso D k hk0 hk b3 b4 b6 h3 h4).inv ≫ i ≫ C =
      PrincipalOpenTensor.inclusion K t := by
  rw [← residueConicBoundaryIso_inclusion, Iso.inv_hom_id_assoc]

end FLT.Mazur.WeierstrassSuccessiveX
