/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassSuccessiveXMiddleNodeIntersectionFactors
public import FLT.Mazur.WeierstrassSuccessiveXResidueParameterBranchCharts

/-!
# Compatible target maps on both full middle nodes

A single map on the original conic supplies agreement on the actual intersection.
The horizontal restrictions need no extra condition there, at any divided constant.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory IsLocalRing
namespace FLT.Mazur.WeierstrassSuccessiveX
open WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
universe u
variable {K : Type u} [Field K] (W : WeierstrassCurve K) (c : K)
  (h2 : W.a₂ = 0) (ha : IsUnit W.a₁)
local notation "A" => Coordinate W 0 0 0 0 c
local notation "N" => Spec (CommRingCat.of (MiddleNodeOpen c))
local notation "J₁" => PrincipalOpenTransport.chart
  (coord W 0 0 0 0 c 1 + algebraMap K A W.a₁) (middleFirstNodeEquiv W c h2 ha)
local notation "J₂" => PrincipalOpenTransport.chart (-coord W 0 0 0 0 c 1)
  (middleSecondNodeEquiv W c h2 ha)
local notation "p₁" => Iso.inv (conicFirstParameterIso W.a₁ c ha) ≫
  conicFirstOpenImmersion W.a₁ c
local notation "p₂" => Spec.map (CommRingCat.ofHom
  (RingEquiv.toRingHom (AlgEquiv.toRingEquiv (conicParameterNeg c)))) ≫
  Iso.inv (conicSecondParameterIso W.a₁ c ha) ≫ conicSecondOpenImmersion W.a₁ c

/-- A common conic map makes the two full original node maps compatible on every overlap. -/
theorem middleNodeMaps_compatible {Y V : Scheme.{u}}
    (a b : N ⟶ Y) (q : Spec (.of (ConicCoordinate W.a₁ c)) ⟶ Y)
    (haq : middleParameterConicBranch c ≫ a = p₁ ≫ q)
    (hbq : middleParameterConicBranch c ≫ b = p₂ ≫ q)
    (f g : V ⟶ N) (h : f ≫ J₁ = g ≫ J₂) : f ≫ a = g ≫ b := by
  obtain ⟨hf, hg⟩ := middleNodeIntersection_factors c W h2 ha f g h
  have he : (f ≫ middleNodeConicProjection c) ≫ p₁ =
      (g ≫ middleNodeConicProjection c) ≫ p₂ := by
    apply (cancel_mono (middleConicImmersion W c h2)).mp
    simp only [Category.assoc]
    rw [← middleParameterConicBranch_firstChart,
      ← middleParameterConicBranch_secondChart]
    simpa only [Category.assoc] using
      (congrArg (fun k => k ≫ J₁) hf).trans
        (h.trans (congrArg (fun k => k ≫ J₂) hg).symm)
  calc
    f ≫ a = f ≫ middleNodeConicProjection c ≫ middleParameterConicBranch c ≫ a := by
      simpa only [Category.assoc] using (congrArg (fun k => k ≫ a) hf).symm
    _ = f ≫ middleNodeConicProjection c ≫ p₁ ≫ q := by rw [haq, Category.assoc]
    _ = g ≫ middleNodeConicProjection c ≫ p₂ ≫ q := by
      simpa only [Category.assoc] using congrArg (fun k => k ≫ q) he
    _ = g ≫ b := by
      rw [← hbq]
      simpa only [Category.assoc] using congrArg (fun k => k ≫ b) hg

variable {R : Type u} [CommRing R] [IsDomain R] [IsLocalRing R]
  {W' : WeierstrassCurve R} {π : R} {n : ℕ} (D : SplitNodeDepth W' π n)
  (k : ℕ) (hk0 : 0 < k) (hk : 2 * (k + 1) ≤ n) (b3 b4 b6 : R)
  (h3 : W'.a₃ = π ^ (k + 1) * b3) (h4 : W'.a₄ = π ^ (k + 1) * b4)
local notation "K₀" => ResidueField R
local notation "c₀" => residue R b6
local notation "α" => residue R W'.a₁
local notation "hα" => D.a₁_unit.map (residue R)
local notation "N₀" => Spec (CommRingCat.of (MiddleNodeOpen c₀))
local notation "r₁" => Iso.inv (conicFirstParameterIso α c₀ hα) ≫
  conicFirstOpenImmersion α c₀
local notation "r₂" => Spec.map (CommRingCat.ofHom
  (RingEquiv.toRingHom (AlgEquiv.toRingEquiv (conicParameterNeg c₀)))) ≫
  Iso.inv (conicSecondParameterIso α c₀ hα) ≫ conicSecondOpenImmersion α c₀

/-- Compatibility retains both actual tensor node charts and their original parameters. -/
theorem residueMiddleNodeMaps_compatible {Y V : Scheme.{u}}
    (a b : N₀ ⟶ Y) (q : Spec (.of (ConicCoordinate α c₀)) ⟶ Y)
    (haq : middleParameterConicBranch c₀ ≫ a = r₁ ≫ q)
    (hbq : middleParameterConicBranch c₀ ≫ b = r₂ ≫ q)
    (f g : V ⟶ N₀)
    (h : f ≫ residueMiddleFirstNodeChart D k hk0 hk b3 b4 b6 h3 h4 =
      g ≫ residueMiddleSecondNodeChart D k hk0 hk b3 b4 b6 h3 h4) : f ≫ a = g ≫ b := by
  apply middleNodeMaps_compatible (W'.map (residue R)) c₀
    ((residue_eq_zero_iff _).mpr D.a₂_mem) hα a b q haq hbq f g
  rw [residueMiddleFirstNodeChart_retained, residueMiddleSecondNodeChart_retained,
    ← Category.assoc, ← Category.assoc] at h
  exact (cancel_mono (residueRetainedIso D k hk0 hk b3 b4 b6 h3 h4).hom).mp h

end FLT.Mazur.WeierstrassSuccessiveX
