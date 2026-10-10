/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassModificationXFiberNodeGeometry
public import FLT.Mazur.WeierstrassModificationXResidueFiber
public import FLT.Mazur.WeierstrassModificationXMorphism

/-!
# The node cover of the original tensor residue fiber

The two oriented node opens map into the actual tensor residue fiber via its
existing normal-form equivalence. They cover it and retain its projection to
the original chart and its contraction to the original projective cubic.
-/

@[expose] public noncomputable section

open IsLocalRing AlgebraicGeometry CategoryTheory

namespace FLT.Mazur.WeierstrassModificationX

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u
variable {R : Type u} [CommRing R] [IsDomain R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} {n : ℕ} (D : SplitNodeDepth W π n)
  (k : ℕ) (hk0 : 0 < k) (hk : 2 * k ≤ n) (b3 b4 b6 : R)
  (h3 : W.a₃ = π ^ k * b3) (h4 : W.a₄ = π ^ k * b4)
  (h6 : W.a₆ = (π ^ k) ^ 2 * b6) (hstrict : 2 * k < n)

local notation "K" => ResidueField R
local notation "a" => residue R W.a₁
local notation "T" => ScalarExtension W (π ^ k) b3 b4 b6 K

/-- The existing normal form as an isomorphism to the actual tensor fiber scheme. -/
def residueLinesIso : Spec (.of (FiberCoordinate a 0)) ≅ Spec (.of T) :=
  Scheme.Spec.mapIso
    (residueLinesEquiv D k hk0 hk b3 b4 b6 h3 h4 h6 hstrict).toRingEquiv.toCommRingCatIso.op

/-- The first oriented node neighborhood inside the original tensor residue fiber. -/
def residueFirstNodeChart : Spec (.of (FirstNodeOpen a)) ⟶ Spec (.of T) :=
  firstNodeChart a ≫ (residueLinesIso D k hk0 hk b3 b4 b6 h3 h4 h6 hstrict).hom

/-- The second oriented node neighborhood inside the original tensor residue fiber. -/
def residueSecondNodeChart : Spec (.of (FirstNodeOpen (-a))) ⟶ Spec (.of T) :=
  secondNodeChart a ≫ (residueLinesIso D k hk0 hk b3 b4 b6 h3 h4 h6 hstrict).hom

instance residueFirstNodeChart_isOpenImmersion :
    IsOpenImmersion (residueFirstNodeChart D k hk0 hk b3 b4 b6 h3 h4 h6 hstrict) :=
  inferInstanceAs (IsOpenImmersion (_ ≫ _))

instance residueSecondNodeChart_isOpenImmersion :
    IsOpenImmersion (residueSecondNodeChart D k hk0 hk b3 b4 b6 h3 h4 h6 hstrict) :=
  inferInstanceAs (IsOpenImmersion (_ ≫ _))

/-- The two actual node schemes cover the original tensor residue fiber. -/
theorem residue_nodeCharts_cover (p : Spec (.of T)) :
    p ∈ Set.range (residueFirstNodeChart D k hk0 hk b3 b4 b6 h3 h4 h6 hstrict) ∨
      p ∈ Set.range (residueSecondNodeChart D k hk0 hk b3 b4 b6 h3 h4 h6 hstrict) := by
  let e := residueLinesIso D k hk0 hk b3 b4 b6 h3 h4 h6 hstrict
  obtain ⟨q, hq⟩ := e.hom.homeomorph.surjective p
  change e.hom q = p at hq
  rcases nodeCharts_cover a (residue_tangent_isUnit D) q with ⟨z, hz⟩ | ⟨z, hz⟩
  · refine Or.inl ⟨z, ?_⟩
    change e.hom (firstNodeChart a z) = p
    rw [hz, hq]
  · refine Or.inr ⟨z, ?_⟩
    change e.hom (secondNodeChart a z) = p
    rw [hz, hq]

/-- The tensor fiber retains its actual projection to the original horizontal chart. -/
def residueChartProjection : Spec (.of T) ⟶ Spec (.of (Coordinate W (π ^ k) b3 b4 b6)) :=
  Spec.map (CommRingCat.ofHom
    (show Coordinate W (π ^ k) b3 b4 b6 →ₐ[R] T from
      Algebra.TensorProduct.includeRight).toRingHom)

/-- The contraction of the actual tensor fiber to the same original projective cubic. -/
def residueChartContraction : Spec (.of T) ⟶ WeierstrassIntegralChart.integralCurve W :=
  residueChartProjection k b3 b4 b6 ≫ toCurve W (π ^ k) b3 b4 b6 h3 h4 h6

/-- The full normal-form fiber carries the original contraction through its proved comparison. -/
def residueNormalContraction : Spec (.of (FiberCoordinate a 0)) ⟶
    WeierstrassIntegralChart.integralCurve W :=
  (residueLinesIso D k hk0 hk b3 b4 b6 h3 h4 h6 hstrict).hom ≫
    residueChartContraction k b3 b4 b6 h3 h4 h6

/-- The first actual node chart retains the original tensor projection and cubic contraction. -/
@[reassoc] theorem residueFirstNodeChart_contraction :
    residueFirstNodeChart D k hk0 hk b3 b4 b6 h3 h4 h6 hstrict ≫
        residueChartContraction k b3 b4 b6 h3 h4 h6 =
      firstNodeChart a ≫ residueNormalContraction D k hk0 hk b3 b4 b6 h3 h4 h6 hstrict :=
  Category.assoc _ _ _

/-- The second node chart retains the same original cubic contraction. -/
@[reassoc] theorem residueSecondNodeChart_contraction :
    residueSecondNodeChart D k hk0 hk b3 b4 b6 h3 h4 h6 hstrict ≫
        residueChartContraction k b3 b4 b6 h3 h4 h6 =
      secondNodeChart a ≫ residueNormalContraction D k hk0 hk b3 b4 b6 h3 h4 h6 hstrict :=
  Category.assoc _ _ _

end FLT.Mazur.WeierstrassModificationX
