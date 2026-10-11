/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedPositiveEqualityCycle
public import FLT.Mazur.WeierstrassModificationXFullNodeProjectiveDescent

/-!
# Descent on both original positive-start initial nodes

Compatible maps on the actual cyclic component family descend on both complete
original initial node opens. The original exterior denominators and opposite
slope translation are retained, including when the cycle has four components.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory IsLocalRing Polynomial
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u

/-- Cyclic compatibility at zero has the order required by the first attachment. -/
theorem positiveEqualityInitialFamily_first_attachment_compatible {K : Type u} [Field K]
    (s : ℕ) {Y : Scheme.{u}} (F : Fin (2 * s + 4) → (ProjectiveLine.scheme K ⟶ Y))
    (w : ∀ i, ProjectiveLine.zero K ≫ F i =
      ProjectiveLine.infinity K ≫ F (PolygonPinching.next (by omega) i)) :
    ProjectiveLine.infinity K ≫ F 1 = ProjectiveLine.zero K ≫ F 0 := by
  have hn : PolygonPinching.next (by omega) (0 : Fin (2 * s + 4)) = 1 := by
    apply Fin.ext
    change (0 + 1) % (2 * s + 4) = 1 % (2 * s + 4)
    rfl
  simpa only [hn] using (w 0).symm

/-- The wraparound endpoint supplies the opposite attachment's compatibility. -/
theorem positiveEqualityInitialFamily_second_attachment_compatible {K : Type u} [Field K]
    (s : ℕ) {Y : Scheme.{u}} (F : Fin (2 * s + 4) → (ProjectiveLine.scheme K ⟶ Y))
    (w : ∀ i, ProjectiveLine.zero K ≫ F i =
      ProjectiveLine.infinity K ≫ F (PolygonPinching.next (by omega) i)) :
    ProjectiveLine.zero K ≫ F ⟨2 * s + 3, by omega⟩ =
      ProjectiveLine.infinity K ≫ F 0 := by
  have hn : PolygonPinching.next (by omega) (⟨2 * s + 3, by omega⟩ : Fin (2 * s + 4)) =
      0 := by
    apply Fin.ext
    change (2 * s + 3 + 1) % (2 * s + 4) = 0
    exact Nat.mod_self _
  simpa only [hn] using w ⟨2 * s + 3, by omega⟩

variable {R : Type u} [CommRing R] [IsDomain R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} {start n depth : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (D : SplitNodeDepth W π depth) (s : ℕ)
  (hk : 2 * (start + s + 1) ≤ depth)
local notation "K" => ResidueField R
local notation "e" => data (Fin.mk 0 (Nat.zero_lt_succ n))
local notation "a" => residue R W.a₁
local notation "c" => residue R (Data.b6 e)
local notation "ha" => D.a₁_unit.map (residue R)
local notation "t" => Units.mk0 a (IsUnit.ne_zero ha)
local notation "hc" => Iff.mpr (residue_eq_zero_iff _)
  (WeierstrassDilatation.divided_constant_mem D start (by omega)
    (Data.b6 e) (Data.factor6 e))
local notation "E" => conicZeroAffineIso c hc
variable {Y : Scheme.{u}}
  (F : Fin (2 * s + 4) → (ProjectiveLine.scheme (ResidueField R) ⟶ Y))
  (w : ∀ i, ProjectiveLine.zero (ResidueField R) ≫ F i =
    ProjectiveLine.infinity (ResidueField R) ≫ F (PolygonPinching.next (by omega) i))

/-- Descent on the entire first localized initial attachment. -/
def positiveEqualityInitialFirstNodeDesc : Spec (.of (FullNodeOpen a c)) ⟶ Y :=
  (fullNodeZero_first_projective_exists_unique_desc t c hc (F 1) (F 0)
    (positiveEqualityInitialFamily_first_attachment_compatible s F w)).choose

/-- The reversed first cyclic component retains its original conic parameter. -/
@[reassoc] theorem positiveEqualityInitialFirstNodeDesc_conic :
    (E).hom ≫ (fullNodeConicParameterIso a c ha).hom ≫ fullNodeFirstBranch a c ha ≫
        positiveEqualityInitialFirstNodeDesc data D s hk F w =
          ProjectiveLine.right K ≫ F 1 := by
  simpa only [positiveEqualityInitialFirstNodeDesc, Iso.trans_hom,
    Category.assoc, Units.val_mk0] using
    (fullNodeZero_first_projective_exists_unique_desc t c hc (F 1) (F 0)
    (positiveEqualityInitialFamily_first_attachment_compatible s F w)).choose_spec.1.1

/-- The first exterior restriction retains its exact localized denominator. -/
@[reassoc] theorem positiveEqualityInitialFirstNodeDesc_exterior :
    fullNodeSecondBranch a c ha ≫
      positiveEqualityInitialFirstNodeDesc data D s hk F w =
      NodeLocalDescent.branchOpen K
        (PolygonNodeEqualizer.second (fullNodeNormalizedDenominator a c)) ≫
        ProjectiveLine.left K ≫ (ProjectiveLine.slopeNormalizationIso t).hom ≫ F 0 :=
  (fullNodeZero_first_projective_exists_unique_desc t c hc (F 1) (F 0)
    (positiveEqualityInitialFamily_first_attachment_compatible s F w)).choose_spec.1.2

/-- Descent on the opposite localized attachment from the same complete cyclic family. -/
def positiveEqualityInitialSecondNodeDesc : Spec (.of (FullNodeOpen (-a) c)) ⟶ Y :=
  (fullNodeZero_second_projective_exists_unique_desc t c hc
    (F ⟨2 * s + 3, by omega⟩) (F 0)
    (positiveEqualityInitialFamily_second_attachment_compatible s F w)).choose

/-- The opposite conic uses the unchanged left chart of the last cyclic component. -/
@[reassoc] theorem positiveEqualityInitialSecondNodeDesc_conic :
    (E).hom ≫ (fullNodeConicParameterIso (-a) c (ha).neg).hom ≫
        fullNodeFirstBranch (-a) c (ha).neg ≫
        positiveEqualityInitialSecondNodeDesc data D s hk F w =
      ProjectiveLine.left K ≫ F ⟨2 * s + 3, by omega⟩ := by
  simpa only [positiveEqualityInitialSecondNodeDesc, Iso.trans_hom,
    Category.assoc, Units.val_mk0] using
    (fullNodeZero_second_projective_exists_unique_desc t c hc
    (F ⟨2 * s + 3, by omega⟩) (F 0)
    (positiveEqualityInitialFamily_second_attachment_compatible s F w)).choose_spec.1.1

/-- The second exterior branch retains both its denominator and negative tangent translation. -/
@[reassoc] theorem positiveEqualityInitialSecondNodeDesc_exterior :
    fullNodeSecondBranch (-a) c (ha).neg ≫
        positiveEqualityInitialSecondNodeDesc data D s hk F w =
      NodeLocalDescent.branchOpen K
        (PolygonNodeEqualizer.second (fullNodeNormalizedDenominator (-a) c)) ≫
        Spec.map (CommRingCat.ofHom (aeval (X - C a)).toRingHom) ≫
        ProjectiveLine.left K ≫ (ProjectiveLine.slopeNormalizationIso t).hom ≫ F 0 :=
  (fullNodeZero_second_projective_exists_unique_desc t c hc
    (F ⟨2 * s + 3, by omega⟩) (F 0)
    (positiveEqualityInitialFamily_second_attachment_compatible s F w)).choose_spec.1.2

end FLT.Mazur.WeierstrassDividedDepth
