/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassCoefficientShearInitialRetainedSmooth
public import FLT.Mazur.WeierstrassCoefficientShearTorusPair

/-!
# The actual torus action on the retained initial boundary

Both complete tensor projections give the same action input. The existing
full torus action agrees with intrinsic smooth addition on that whole boundary,
for arbitrary test schemes.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
open scoped TensorProduct
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassIntegralChart WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type} [CommRing R] [IsDomain R] [IsBezout R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (S : Type) [CommRing S] [Algebra R S] (r : S)
  (h1 : 1 ≤ n) (m : ℕ) (hm : 1 + m ≤ n)
local notation "d" => data (Fin.mk 0 (Nat.zero_lt_succ n))
local notation "e" => data (Fin.mk 1 (Nat.lt_succ_of_le h1))
local notation "s" => π ^ start
local notation "V" => W.map (algebraMap R S)
local notation "x" => WeierstrassDilatation.x W s (Data.b3 d) (Data.b4 d) (Data.b6 d)
local notation "t" => WeierstrassModificationX.t W s (Data.b3 d) (Data.b4 d) (Data.b6 d)
local notation "v" => WeierstrassSuccessiveX.coord W s π
  (Data.b3 e) (Data.b4 e) (Data.b6 e) 2
local notation "A" => PrincipalOpenTensor.transitionIso S x t
  (overlapEquiv W s (Data.b3 d) (Data.b4 d) (Data.b6 d))
local notation "B" => PrincipalOpenTensor.transitionIso S x v (previousBoundaryEquiv hπ d e)
local notation "I" => Iso.inv A ≫ PrincipalOpenTensor.inclusion S t
local notation "J" => Iso.inv B ≫ PrincipalOpenTensor.inclusion S v
local notation "E" => coefficientShearGluedIso hπ data S r (1 + m) hm

variable (hs : algebraMap R S (π ^ start) = 1)
  (h3 : algebraMap R S (Data.b3 (data ⟨0, Nat.zero_lt_succ n⟩)) = 0)
  (h4 : algebraMap R S (Data.b4 (data ⟨0, Nat.zero_lt_succ n⟩)) = 0)
  (h6 : algebraMap R S (Data.b6 (data ⟨0, Nat.zero_lt_succ n⟩)) = 0)
  (hr : r ^ 2 + algebraMap R S W.a₁ * r - algebraMap R S W.a₂ = 0)
  (a : Sˣ) (ha : (a : S) = (W.map (algebraMap R S)).a₁ + 2 * r)
local notation "P" => tensorShearScaleOneSmoothInput W s (Data.b3 d) (Data.b4 d)
  (Data.b6 d) (Data.factor3 d) (Data.factor4 d) (Data.factor6 d) S r hs h3 h4 h6 hr a ha

local notation "hc" => tensorOriginal_nodal_coefficients W s (Data.b3 d) (Data.b4 d)
  (Data.b6 d) (Data.factor3 d) (Data.factor4 d) (Data.factor6 d) S h3 h4 h6
local notation "root" => rootShearTorusSmoothIso V r a ha hr (hc).1 (hc).2.1 (hc).2.2
local notation "ret" => coefficientShearRetainedTensorChart hπ data S r (1 + m) hm
  (Fin.mk 0 (by omega))
local notation "g" => coefficientShearGluedStructure hπ data S r (1 + m) hm
local notation "tor" => Over.hom (MultiplicativeGroupScheme.gm S)
local notation "emb" => coefficientShearSmoothEmbedding hπ data S r (1 + m) hm
/-- A concrete model input with a smooth presentation has the original smooth action. -/
theorem coefficientShearTorusAction_smoothPresentation {Y : Scheme}
    (p : Y ⟶ (MultiplicativeGroupScheme.gm S).left)
    (q : Y ⟶ (integralSmoothOpen V).toScheme)
    (z : Y ⟶ coefficientShearGlued hπ data S r (1 + m) hm)
    (hz : z = q ≫ emb) (hpz : p ≫ tor = z ≫ g)
    (hpq : (p ≫ (root).hom) ≫ integralSmoothStructure V = q ≫ integralSmoothStructure V) :
    pullback.lift p z hpz ≫ coefficientShearTorusAction hπ data S r (1 + m) hm a ha hr
        (hc).1 (hc).2.1 (hc).2.2 =
      smoothPairPointAddition V (p ≫ (root).hom) q hpq ≫ emb := by
  subst z
  rw [coefficientShearTorusAction_pair]
  exact coefficientShearAction_smoothEmbedding hπ data S r (1 + m) hm
    (p ≫ (root).hom) q hpq

variable {X : Scheme} (p : X ⟶ (MultiplicativeGroupScheme.gm S).left)
  (b : X ⟶ Spec (.of (Localization.Away ((1 : S) ⊗ₜ[R]
    WeierstrassDilatation.x W (π ^ start) (Data.b3 (data ⟨0, Nat.zero_lt_succ n⟩))
      (Data.b4 (data ⟨0, Nat.zero_lt_succ n⟩))
      (Data.b6 (data ⟨0, Nat.zero_lt_succ n⟩))))))

/-- The actual retained-boundary pair gives the same two original smooth inputs. -/
theorem coefficientShearRetainedBoundary_smoothCondition
    (hpq : p ≫ tor = (b ≫ J ≫ ret) ≫ g) :
    (p ≫ (root).hom) ≫ integralSmoothStructure V =
      (b ≫ I ≫ P) ≫ integralSmoothStructure V := by
  rw [Category.assoc, rootShearTorusSmoothIso_structure, hpq,
    coefficientShearRetained_initialSmoothInput hπ data S r h1 m hm hs h3 h4 h6 hr a ha]
  simp only [Category.assoc, coefficientShearSmoothEmbedding_structure]

set_option maxHeartbeats 600000 in
-- Comparing the indexed original tensor presentations needs additional elaboration steps.
/-- The genuine torus action on the whole retained boundary is original smooth addition. -/
theorem coefficientShearTorusAction_retainedInitialBoundary
    (hpq : p ≫ tor = (b ≫ J ≫ ret) ≫ g) :
    pullback.lift p (b ≫ J ≫ ret) hpq ≫
        coefficientShearTorusAction hπ data S r (1 + m) hm a ha hr
          (hc).1 (hc).2.1 (hc).2.2 =
      smoothPairPointAddition V (p ≫ (root).hom) (b ≫ I ≫ P)
        (coefficientShearRetainedBoundary_smoothCondition hπ data S r h1 m hm
          hs h3 h4 h6 hr a ha p b hpq) ≫ emb := by
  let hpair := coefficientShearRetainedBoundary_smoothCondition hπ data S r h1 m hm
    hs h3 h4 h6 hr a ha p b hpq
  have hb : b ≫ J ≫ ret = (b ≫ I ≫ P) ≫ emb := by
    rw [coefficientShearRetained_initialSmoothInput hπ data S r h1 m hm
      hs h3 h4 h6 hr a ha]
    simp only [Category.assoc]
  exact coefficientShearTorusAction_smoothPresentation hπ data S r m hm
    h3 h4 h6 hr a ha p (b ≫ I ≫ P) (b ≫ J ≫ ret) hb hpq hpair

end FLT.Mazur.WeierstrassDividedDepth
