/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedInitialGlobalResidueNodes
public import FLT.Mazur.WeierstrassDividedOlderZeroExtendedSections

/-!
# Ordered initial sections at positive depth

The two original full-node origins give distinct sections of every retained
global residue model. Their tensor normal form and tangent ordering are unchanged.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits IsLocalRing
namespace FLT.Mazur.WeierstrassDividedDepth
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] [IsDomain R] [IsBezout R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n depth : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (D : SplitNodeDepth W π depth) (j : ℕ) (hj : j ≤ n)
  (hstart : 0 < start) (hk : 2 * start ≤ depth)
open WeierstrassModificationX
local notation "K" => ResidueField R
local notation "d" => data (Fin.mk 0 (Nat.zero_lt_succ n))
local notation "a" => residue R W.a₁
local notation "c" => residue R (Data.b6 d)
local notation "ha" => residue_tangent_isUnit D
local notation "q" => Spec.map (CommRingCat.ofHom (algebraMap R K))
local notation "f" => finiteGlobalStructure hπ data j hj

/-- The entire initial normal form embeds into every retained global model. -/
def initialGlobalResidueFiberChart :=
  (residueFiberIso D start hstart hk
    (Data.b3 d) (Data.b4 d) (Data.b6 d) (Data.factor3 d) (Data.factor4 d)).hom ≫
      globalInitialTensorChart hπ data K j hj

instance initialGlobalResidueFiberChart_isOpenImmersion :
    IsOpenImmersion (initialGlobalResidueFiberChart hπ data D j hj hstart hk) :=
  inferInstanceAs (IsOpenImmersion (_ ≫ _))

/-- The whole initial normal form retains its residue-field structure. -/
@[reassoc] theorem initialGlobalResidueFiberChart_structure :
    initialGlobalResidueFiberChart hπ data D j hj hstart hk ≫ pullback.fst q f =
      Spec.map (CommRingCat.ofHom (algebraMap K (FiberCoordinate a c))) := by
  rw [initialGlobalResidueFiberChart, Category.assoc, globalInitialTensorChart_structure]
  change Spec.map _ ≫ Spec.map _ = _
  rw [← Spec.map_comp]
  congr 1
  exact CommRingCat.hom_ext (RingHom.ext fun x =>
    (residueFiberEquiv D start hstart hk
      (Data.b3 d) (Data.b4 d) (Data.b6 d) (Data.factor3 d) (Data.factor4 d)).commutes x)

local notation "g" => initialGlobalResidueFiberChart hπ data D j hj hstart hk

/-- The first original initial incidence point in the actual global residue model. -/
def initialGlobalFirstSection :=
  Spec.map (CommRingCat.ofHom (fullFirstIncidencePoint a c ha).toRingHom) ≫ g

/-- The opposite original initial incidence point in that same global model. -/
def initialGlobalSecondSection :=
  Spec.map (CommRingCat.ofHom (fullSecondIncidencePoint a c ha).toRingHom) ≫ g

/-- The first full initial-node origin gives precisely the first global section. -/
@[reassoc] theorem initialGlobalFirstNode_origin :
    Spec.map (CommRingCat.ofHom (fullNodeOrigin a c ha).toRingHom) ≫
      initialGlobalResidueFirstNode hπ data D j hj hstart hk =
        initialGlobalFirstSection hπ data D j hj hstart hk := by
  rw [initialGlobalResidueFirstNode, residueFullFirstNodeChart, ← Category.assoc,
    ← Category.assoc, zeroFirstNodeOrigin_chart]
  rfl

/-- The opposite full initial-node origin gives precisely the second global section. -/
@[reassoc] theorem initialGlobalSecondNode_origin :
    Spec.map (CommRingCat.ofHom (fullNodeOrigin (-a) c (IsUnit.neg ha)).toRingHom) ≫
      initialGlobalResidueSecondNode hπ data D j hj hstart hk =
        initialGlobalSecondSection hπ data D j hj hstart hk := by
  rw [initialGlobalResidueSecondNode, residueFullSecondNodeChart, ← Category.assoc,
    ← Category.assoc, zeroSecondNodeOrigin_chart]
  rfl

/-- The first initial point is a section over the residue field. -/
@[reassoc] theorem initialGlobalFirstSection_structure :
    initialGlobalFirstSection hπ data D j hj hstart hk ≫ pullback.fst q f =
      𝟙 (Spec (.of K)) := by
  rw [initialGlobalFirstSection, Category.assoc, initialGlobalResidueFiberChart_structure]
  exact residueAlgebraPoint_structure _

/-- The opposite initial point is a section over the residue field. -/
@[reassoc] theorem initialGlobalSecondSection_structure :
    initialGlobalSecondSection hπ data D j hj hstart hk ≫ pullback.fst q f =
      𝟙 (Spec (.of K)) := by
  rw [initialGlobalSecondSection, Category.assoc, initialGlobalResidueFiberChart_structure]
  exact residueAlgebraPoint_structure _

/-- Nonzero coefficient extensions preserve the ordered initial incidence points. -/
theorem initialGlobalSections_extension_ne (S : Type u) [CommRing S] [Nontrivial S]
    [Algebra K S] :
    Spec.map (CommRingCat.ofHom (algebraMap K S)) ≫
        initialGlobalFirstSection hπ data D j hj hstart hk ≠
      Spec.map (CommRingCat.ofHom (algebraMap K S)) ≫
        initialGlobalSecondSection hπ data D j hj hstart hk := by
  intro h
  rw [initialGlobalFirstSection, initialGlobalSecondSection,
    ← Category.assoc, ← Category.assoc] at h
  exact zeroIncidencePoints_extension_ne a c ha ((cancel_mono g).mp h)

/-- The two initial ordered sections are distinct at every retained stage. -/
theorem initialGlobalSections_ne :
    initialGlobalFirstSection hπ data D j hj hstart hk ≠
      initialGlobalSecondSection hπ data D j hj hstart hk := by
  intro h
  exact initialGlobalSections_extension_ne hπ data D j hj hstart hk K
    (congrArg (fun t => Spec.map (CommRingCat.ofHom (algebraMap K K)) ≫ t) h)

end FLT.Mazur.WeierstrassDividedDepth
