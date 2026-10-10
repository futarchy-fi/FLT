/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassModificationXFullNodeGeometry
public import FLT.Mazur.WeierstrassModificationXResidueContractionGeometry

/-!
# The full node cover of the original tensor residue fiber

The two oriented node opens map into the actual tensor residue fiber via its
existing normal-form equivalence, with c retained. They cover it and retain its projection to
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
  (h6 : W.a₆ = (π ^ k) ^ 2 * b6)

local notation "K" => ResidueField R
local notation "a" => residue R W.a₁
local notation "c" => residue R b6
local notation "T" => ScalarExtension W (π ^ k) b3 b4 b6 K

/-- The first oriented node neighborhood inside the original tensor residue fiber. -/
def residueFullFirstNodeChart : Spec (.of (FullNodeOpen a c)) ⟶ Spec (.of T) :=
  fullFirstNodeChart a c (residue_tangent_isUnit D) ≫
    (residueFiberIso D k hk0 hk b3 b4 b6 h3 h4).hom

/-- The second oriented node neighborhood inside the original tensor residue fiber. -/
def residueFullSecondNodeChart : Spec (.of (FullNodeOpen (-a) c)) ⟶ Spec (.of T) :=
  fullSecondNodeChart a c (residue_tangent_isUnit D) ≫
    (residueFiberIso D k hk0 hk b3 b4 b6 h3 h4).hom

instance residueFullFirstNodeChart_isOpenImmersion :
    IsOpenImmersion (residueFullFirstNodeChart D k hk0 hk b3 b4 b6 h3 h4) :=
  inferInstanceAs (IsOpenImmersion (_ ≫ _))

instance residueFullSecondNodeChart_isOpenImmersion :
    IsOpenImmersion (residueFullSecondNodeChart D k hk0 hk b3 b4 b6 h3 h4) :=
  inferInstanceAs (IsOpenImmersion (_ ≫ _))

/-- The two actual node schemes cover the original tensor residue fiber. -/
theorem residue_fullNodeCharts_cover (p : Spec (.of T)) :
    p ∈ Set.range (residueFullFirstNodeChart D k hk0 hk b3 b4 b6 h3 h4) ∨
      p ∈ Set.range (residueFullSecondNodeChart D k hk0 hk b3 b4 b6 h3 h4) := by
  let e := residueFiberIso D k hk0 hk b3 b4 b6 h3 h4
  obtain ⟨q, hq⟩ := e.hom.homeomorph.surjective p
  change e.hom q = p at hq
  rcases fullNodeCharts_cover a c (residue_tangent_isUnit D) q with ⟨z, hz⟩ | ⟨z, hz⟩
  · refine Or.inl ⟨z, ?_⟩
    change e.hom (fullFirstNodeChart a c (residue_tangent_isUnit D) z) = p
    rw [hz, hq]
  · refine Or.inr ⟨z, ?_⟩
    change e.hom (fullSecondNodeChart a c (residue_tangent_isUnit D) z) = p
    rw [hz, hq]

/-- The first actual node chart retains the original tensor projection and cubic contraction. -/
@[reassoc] theorem residueFullFirstNodeChart_contraction :
    residueFullFirstNodeChart D k hk0 hk b3 b4 b6 h3 h4 ≫
        residueChartContraction k b3 b4 b6 h3 h4 h6 =
      fullFirstNodeChart a c (residue_tangent_isUnit D) ≫
        residueFullContraction D k hk0 hk b3 b4 b6 h3 h4 h6 := by
  rw [residueFullFirstNodeChart, Category.assoc, residueFiberIso_contraction]

/-- The second node chart retains the same original cubic contraction. -/
@[reassoc] theorem residueFullSecondNodeChart_contraction :
    residueFullSecondNodeChart D k hk0 hk b3 b4 b6 h3 h4 ≫
        residueChartContraction k b3 b4 b6 h3 h4 h6 =
      fullSecondNodeChart a c (residue_tangent_isUnit D) ≫
        residueFullContraction D k hk0 hk b3 b4 b6 h3 h4 h6 := by
  rw [residueFullSecondNodeChart, Category.assoc, residueFiberIso_contraction]

end FLT.Mazur.WeierstrassModificationX
