/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedZeroCycleLocalMaps
public import FLT.Mazur.WeierstrassModificationXFullNodeProjectiveDescent

/-!
# Local maps at the two start-zero cyclic attachments

One compatible cyclic family supplies both maps, with the original localized
exterior denominators and the opposite branch translation unchanged.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory IsLocalRing Polynomial
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u

/-- Cyclic compatibility at zero has the order required by the first attachment. -/
theorem zeroSplitCycleFamily_first_attachment_compatible {K : Type u} [Field K]
    (s : ℕ) {Y : Scheme.{u}} (F : Fin (2 * s + 3) → (ProjectiveLine.scheme K ⟶ Y))
    (w : ∀ i, ProjectiveLine.zero K ≫ F i =
      ProjectiveLine.infinity K ≫ F (PolygonPinching.next (by omega) i)) :
    ProjectiveLine.infinity K ≫ F 1 = ProjectiveLine.zero K ≫ F 0 := by
  have hn : PolygonPinching.next (by omega) (0 : Fin (2 * s + 3)) = 1 := by
    apply Fin.ext
    change (0 + 1) % (2 * s + 3) = 1 % (2 * s + 3)
    rfl
  simpa only [hn] using (w 0).symm

/-- The wraparound endpoint supplies the opposite attachment's compatibility. -/
theorem zeroSplitCycleFamily_second_attachment_compatible {K : Type u} [Field K]
    (s : ℕ) {Y : Scheme.{u}} (F : Fin (2 * s + 3) → (ProjectiveLine.scheme K ⟶ Y))
    (w : ∀ i, ProjectiveLine.zero K ≫ F i =
      ProjectiveLine.infinity K ≫ F (PolygonPinching.next (by omega) i)) :
    ProjectiveLine.zero K ≫ F ⟨2 * s + 2, by omega⟩ =
      ProjectiveLine.infinity K ≫ F 0 := by
  have hn : PolygonPinching.next (by omega) (⟨2 * s + 2, by omega⟩ : Fin (2 * s + 3)) =
      0 := by
    apply Fin.ext
    change (2 * s + 2 + 1) % (2 * s + 3) = 0
    exact Nat.mod_self _
  simpa only [hn] using w ⟨2 * s + 2, by omega⟩

variable {R : Type u} [CommRing R] [IsDomain R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} {start n depth : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (D : SplitNodeDepth W π depth) (s : ℕ) (hs : s + 1 ≤ n)
  (hp : 2 * (start + s + 1) < depth)
local notation "K" => ResidueField R
local notation "e" => data (Fin.mk 1 (by omega))
local notation "a" => residue R W.a₁
local notation "c" => residue R (Data.b6 e)
local notation "ha" => D.a₁_unit.map (residue R)
local notation "t" => Units.mk0 a (IsUnit.ne_zero ha)
local notation "hc" => Iff.mpr (residue_eq_zero_iff _)
  (WeierstrassDilatation.divided_constant_mem D (start + 1) (by omega)
    (Data.b6 e) (Data.factor6 e))
local notation "E" => conicZeroAffineIso c hc
variable {Y : Scheme.{u}}
  (F : Fin (2 * s + 3) → (ProjectiveLine.scheme (ResidueField R) ⟶ Y))
  (w : ∀ i, ProjectiveLine.zero (ResidueField R) ≫ F i =
    ProjectiveLine.infinity (ResidueField R) ≫ F (PolygonPinching.next (by omega) i))

/-- Descent on the entire first localized start-zero attachment. -/
def zeroSplitCycleFirstAttachmentDesc : Spec (.of (FullNodeOpen a c)) ⟶ Y :=
  (fullNodeZero_first_projective_exists_unique_desc t c hc (F 1) (F 0)
    (zeroSplitCycleFamily_first_attachment_compatible s F w)).choose

/-- The reversed first cyclic component retains its original conic parameter. -/
@[reassoc] theorem zeroSplitCycleFirstAttachmentDesc_conic :
    (E).hom ≫ (fullNodeConicParameterIso a c ha).hom ≫ fullNodeFirstBranch a c ha ≫
        zeroSplitCycleFirstAttachmentDesc data D s hs hp F w = ProjectiveLine.right K ≫ F 1 := by
  simpa only [zeroSplitCycleFirstAttachmentDesc, Iso.trans_hom,
    Category.assoc, Units.val_mk0] using
    (fullNodeZero_first_projective_exists_unique_desc t c hc (F 1) (F 0)
    (zeroSplitCycleFamily_first_attachment_compatible s F w)).choose_spec.1.1

/-- The first exterior restriction retains its exact localized denominator. -/
@[reassoc] theorem zeroSplitCycleFirstAttachmentDesc_exterior :
    fullNodeSecondBranch a c ha ≫ zeroSplitCycleFirstAttachmentDesc data D s hs hp F w =
      NodeLocalDescent.branchOpen K
        (PolygonNodeEqualizer.second (fullNodeNormalizedDenominator a c)) ≫
        ProjectiveLine.left K ≫ (ProjectiveLine.slopeNormalizationIso t).hom ≫ F 0 :=
  (fullNodeZero_first_projective_exists_unique_desc t c hc (F 1) (F 0)
    (zeroSplitCycleFamily_first_attachment_compatible s F w)).choose_spec.1.2

/-- Descent on the opposite localized attachment from the same complete cyclic family. -/
def zeroSplitCycleSecondAttachmentDesc : Spec (.of (FullNodeOpen (-a) c)) ⟶ Y :=
  (fullNodeZero_second_projective_exists_unique_desc t c hc
    (F ⟨2 * s + 2, by omega⟩) (F 0)
    (zeroSplitCycleFamily_second_attachment_compatible s F w)).choose

/-- The opposite conic uses the unchanged left chart of the last cyclic component. -/
@[reassoc] theorem zeroSplitCycleSecondAttachmentDesc_conic :
    (E).hom ≫ (fullNodeConicParameterIso (-a) c (ha).neg).hom ≫
        fullNodeFirstBranch (-a) c (ha).neg ≫
        zeroSplitCycleSecondAttachmentDesc data D s hs hp F w =
      ProjectiveLine.left K ≫ F ⟨2 * s + 2, by omega⟩ := by
  simpa only [zeroSplitCycleSecondAttachmentDesc, Iso.trans_hom,
    Category.assoc, Units.val_mk0] using
    (fullNodeZero_second_projective_exists_unique_desc t c hc
    (F ⟨2 * s + 2, by omega⟩) (F 0)
    (zeroSplitCycleFamily_second_attachment_compatible s F w)).choose_spec.1.1

/-- The second exterior branch retains both its denominator and negative tangent translation. -/
@[reassoc] theorem zeroSplitCycleSecondAttachmentDesc_exterior :
    fullNodeSecondBranch (-a) c (ha).neg ≫
        zeroSplitCycleSecondAttachmentDesc data D s hs hp F w =
      NodeLocalDescent.branchOpen K
        (PolygonNodeEqualizer.second (fullNodeNormalizedDenominator (-a) c)) ≫
        Spec.map (CommRingCat.ofHom (aeval (X - C a)).toRingHom) ≫
        ProjectiveLine.left K ≫ (ProjectiveLine.slopeNormalizationIso t).hom ≫ F 0 :=
  (fullNodeZero_second_projective_exists_unique_desc t c hc
    (F ⟨2 * s + 2, by omega⟩) (F 0)
    (zeroSplitCycleFamily_second_attachment_compatible s F w)).choose_spec.1.2

end FLT.Mazur.WeierstrassDividedDepth
