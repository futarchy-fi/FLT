/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedOlderGlobalZeroSections
public import FLT.Mazur.WeierstrassDividedResidueAtlasExtension

/-!
# The ordered first sections in the actual extended global model

Both full-node origins remain the two distinct ordered sections after any
nonzero coefficient extension. Their sections are constructed in the actual
global coefficient pullback, and each lifts to the entire corresponding node.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits IsLocalRing
namespace FLT.Mazur.WeierstrassDividedDepth
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u

/-- An algebra point is a section of its affine coefficient structure. -/
theorem residueAlgebraPoint_structure {A B : Type u} [CommRing A] [CommRing B]
    [Algebra A B] (t : B →ₐ[A] A) :
    Spec.map (CommRingCat.ofHom t.toRingHom) ≫
      Spec.map (CommRingCat.ofHom (algebraMap A B)) = 𝟙 (Spec (.of A)) := by
  rw [← Spec.map_comp, ← Spec.map_id]
  congr 1
  exact CommRingCat.hom_ext (RingHom.ext fun a => t.commutes a)

/-- The signed incidence points remain distinct over every nonzero coefficient extension. -/
theorem zeroIncidencePoints_extension_ne {A B : Type u} [CommRing A] [CommRing B]
    [Nontrivial B] [Algebra A B] (a c : A) (ha : IsUnit a) :
    Spec.map (CommRingCat.ofHom (algebraMap A B)) ≫
        Spec.map (CommRingCat.ofHom
          (WeierstrassModificationX.fullFirstIncidencePoint a c ha).toRingHom) ≠
      Spec.map (CommRingCat.ofHom (algebraMap A B)) ≫
        Spec.map (CommRingCat.ofHom
          (WeierstrassModificationX.fullSecondIncidencePoint a c ha).toRingHom) := by
  intro h
  rw [← Spec.map_comp, ← Spec.map_comp] at h
  have hv := congrArg (fun f => f.hom (WeierstrassModificationX.fiberV a c))
    (Spec.map_injective h)
  change algebraMap A B (WeierstrassModificationX.fullFirstIncidencePoint a c ha
    (WeierstrassModificationX.fiberV a c)) =
      algebraMap A B (WeierstrassModificationX.fullSecondIncidencePoint a c ha
        (WeierstrassModificationX.fiberV a c)) at hv
  rw [WeierstrassModificationX.fullFirstIncidencePoint_v,
    WeierstrassModificationX.fullSecondIncidencePoint_v, map_zero, map_neg] at hv
  exact (ha.map (algebraMap A B)).ne_zero (neg_eq_zero.mp hv.symm)

variable {R : Type u} [CommRing R] [IsDomain R] [IsBezout R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n depth : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (D : SplitNodeDepth W π depth) (j : ℕ) (hj : j + 1 ≤ n)
  (r : ℕ) (hr : j + 1 + r ≤ n)
  (hk0 : start + j = 0) (hk : 2 * (start + j + 1) ≤ depth)
local notation "K" => ResidueField R
local notation "q" => Spec.map (CommRingCat.ofHom (algebraMap R K))
local notation "f" => finiteGlobalStructure hπ data (j + 1 + r) hr
local notation "first" => olderGlobalZeroFirstSection hπ data D j hj r hr hk0 hk
local notation "second" => olderGlobalZeroSecondSection hπ data D j hj r hr hk0 hk

/-- The first ordered global incidence point is a section over the residue field. -/
@[reassoc] theorem olderGlobalZeroFirstSection_structure :
    first ≫ pullback.fst q f = 𝟙 (Spec (.of K)) := by
  rw [olderGlobalZeroFirstSection, Category.assoc, olderGlobalZeroSuccessiveChart_structure]
  exact residueAlgebraPoint_structure _

/-- The opposite ordered global incidence point has the same coefficient section. -/
@[reassoc] theorem olderGlobalZeroSecondSection_structure :
    second ≫ pullback.fst q f = 𝟙 (Spec (.of K)) := by
  rw [olderGlobalZeroSecondSection, Category.assoc, olderGlobalZeroSuccessiveChart_structure]
  exact residueAlgebraPoint_structure _

variable (S : Type u) [CommRing S] [Algebra R S] [Algebra (ResidueField R) S]
  [IsScalarTower R (ResidueField R) S]
local notation "e" => Spec.map (CommRingCat.ofHom (algebraMap K S))
local notation "qS" => Spec.map (CommRingCat.ofHom (algebraMap R S))
local notation "p" => globalResidueExtensionMap hπ data S (j + 1 + r) hr
local notation "H" => globalResidueExtensionMap_isPullback hπ data S (j + 1 + r) hr

/-- The first ordered section of the actual extended global model. -/
def olderZeroExtendedFirstSection : Spec (.of S) ⟶
    finiteGlobalTensorModel hπ data S (j + 1 + r) hr :=
  (H).lift (𝟙 _) (e ≫ first) (by
    rw [Category.id_comp, Category.assoc, olderGlobalZeroFirstSection_structure,
      Category.comp_id])

/-- The opposite ordered section of the actual extended global model. -/
def olderZeroExtendedSecondSection : Spec (.of S) ⟶
    finiteGlobalTensorModel hπ data S (j + 1 + r) hr :=
  (H).lift (𝟙 _) (e ≫ second) (by
    rw [Category.id_comp, Category.assoc, olderGlobalZeroSecondSection_structure,
      Category.comp_id])

/-- The first extended section keeps its precise original ordering. -/
@[reassoc] theorem olderZeroExtendedFirstSection_projection :
    olderZeroExtendedFirstSection hπ data D j hj r hr hk0 hk S ≫ p = e ≫ first :=
  (H).lift_snd _ _ _

/-- The second extended section keeps its precise original ordering. -/
@[reassoc] theorem olderZeroExtendedSecondSection_projection :
    olderZeroExtendedSecondSection hπ data D j hj r hr hk0 hk S ≫ p = e ≫ second :=
  (H).lift_snd _ _ _

/-- The first extended map is a section over the new coefficient ring. -/
@[reassoc] theorem olderZeroExtendedFirstSection_structure :
    olderZeroExtendedFirstSection hπ data D j hj r hr hk0 hk S ≫ pullback.fst qS f =
      𝟙 (Spec (.of S)) := (H).lift_fst _ _ _

/-- The second extended map is a section over the new coefficient ring. -/
@[reassoc] theorem olderZeroExtendedSecondSection_structure :
    olderZeroExtendedSecondSection hπ data D j hj r hr hk0 hk S ≫ pullback.fst qS f =
      𝟙 (Spec (.of S)) := (H).lift_fst _ _ _

/-- No nonzero extension identifies the two ordered global sections. -/
theorem olderZeroExtendedSections_ne [Nontrivial S] :
    olderZeroExtendedFirstSection hπ data D j hj r hr hk0 hk S ≠
      olderZeroExtendedSecondSection hπ data D j hj r hr hk0 hk S := by
  intro h
  have hp := congrArg (fun t => t ≫ p) h
  rw [olderZeroExtendedFirstSection_projection, olderZeroExtendedSecondSection_projection,
    olderGlobalZeroFirstSection, olderGlobalZeroSecondSection, ← Category.assoc,
    ← Category.assoc] at hp
  exact zeroIncidencePoints_extension_ne _ _ _ ((cancel_mono _).mp hp)

end FLT.Mazur.WeierstrassDividedDepth
