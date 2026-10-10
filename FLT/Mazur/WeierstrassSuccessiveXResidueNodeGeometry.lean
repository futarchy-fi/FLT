/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.PrincipalOpenTransportGeometry
public import FLT.Mazur.WeierstrassSuccessiveXResidueMiddleNodes

/-!
# An actual two-node open cover of the tensor middle fiber

Both ordered principal neighborhoods are open immersions of the same
localized standard node, cover the whole tensor spectrum, and retain
its residue-field structure map.
-/

@[expose] public noncomputable section
open IsLocalRing AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassSuccessiveX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type*} [CommRing R] [IsDomain R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} {n : ℕ} (D : SplitNodeDepth W π n)
  (k : ℕ) (hk0 : 0 < k) (hk : 2 * (k + 1) ≤ n) (b3 b4 b6 : R)
  (h3 : W.a₃ = π ^ (k + 1) * b3) (h4 : W.a₄ = π ^ (k + 1) * b4)
local notation "K" => ResidueField R
local notation "T" => ScalarExtension W (π ^ k) π b3 b4 b6 K
local notation "N" => MiddleNodeOpen (residue R b6)
local notation "v" => tensorCoord W (π ^ k) π b3 b4 b6 K 1
local notation "d" => v + algebraMap K T (residue R W.a₁)

/-- The first actual attachment-node open immersion into the original tensor fiber. -/
def residueMiddleFirstNodeChart : Spec (.of N) ⟶ Spec (.of T) :=
  PrincipalOpenTransport.chart d (residueMiddleFirstNodeEquiv D k hk0 hk b3 b4 b6 h3 h4)

/-- The second ordered node open immersion into the same original tensor fiber. -/
def residueMiddleSecondNodeChart : Spec (.of N) ⟶ Spec (.of T) :=
  PrincipalOpenTransport.chart (-v) (residueMiddleSecondNodeEquiv D k hk0 hk b3 b4 b6 h3 h4)

instance residueMiddleFirstNodeChart_isOpenImmersion :
    IsOpenImmersion (residueMiddleFirstNodeChart D k hk0 hk b3 b4 b6 h3 h4) :=
  inferInstanceAs (IsOpenImmersion (PrincipalOpenTransport.chart _ _))

instance residueMiddleSecondNodeChart_isOpenImmersion :
    IsOpenImmersion (residueMiddleSecondNodeChart D k hk0 hk b3 b4 b6 h3 h4) :=
  inferInstanceAs (IsOpenImmersion (PrincipalOpenTransport.chart _ _))

/-- The first node chart is exactly the full original first tangent open. -/
theorem residueMiddleFirstNodeChart_range :
    Set.range (residueMiddleFirstNodeChart D k hk0 hk b3 b4 b6 h3 h4) =
      (PrimeSpectrum.basicOpen d : Set (PrimeSpectrum T)) :=
  PrincipalOpenTransport.chart_range _ _

/-- The second node chart is exactly the full original second tangent open. -/
theorem residueMiddleSecondNodeChart_range :
    Set.range (residueMiddleSecondNodeChart D k hk0 hk b3 b4 b6 h3 h4) =
      (PrimeSpectrum.basicOpen (-v) : Set (PrimeSpectrum T)) :=
  PrincipalOpenTransport.chart_range _ _

/-- The ordered actual node neighborhoods cover every point of the full tensor fiber. -/
theorem residueMiddleNodeCharts_cover (p : Spec (.of T)) :
    p ∈ Set.range (residueMiddleFirstNodeChart D k hk0 hk b3 b4 b6 h3 h4) ∨
      p ∈ Set.range (residueMiddleSecondNodeChart D k hk0 hk b3 b4 b6 h3 h4) := by
  rw [residueMiddleFirstNodeChart_range, residueMiddleSecondNodeChart_range]
  exact residue_middle_tangent_cover D k b3 b4 b6 p

/-- The first node chart retains the actual residue-field structure morphism. -/
@[reassoc] theorem residueMiddleFirstNodeChart_structure :
    residueMiddleFirstNodeChart D k hk0 hk b3 b4 b6 h3 h4 ≫
      Spec.map (CommRingCat.ofHom (algebraMap K T)) =
        Spec.map (CommRingCat.ofHom (algebraMap K N)) :=
  PrincipalOpenTransport.chart_structure _ _

/-- The second ordered node chart retains the same actual residue-field structure. -/
@[reassoc] theorem residueMiddleSecondNodeChart_structure :
    residueMiddleSecondNodeChart D k hk0 hk b3 b4 b6 h3 h4 ≫
      Spec.map (CommRingCat.ofHom (algebraMap K T)) =
        Spec.map (CommRingCat.ofHom (algebraMap K N)) :=
  PrincipalOpenTransport.chart_structure _ _

end FLT.Mazur.WeierstrassSuccessiveX
