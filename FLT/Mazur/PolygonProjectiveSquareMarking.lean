/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonProjectiveSquareComparison
public import FLT.Mazur.PolygonProjectiveAuxiliaryParameter
public import FLT.Mazur.CoprimeFieldGroupTransport

/-!
# Full marking parameters are independent of the chosen cartesian realization

The canonical original square comparison preserves the cyclic homomorphism.
Transporting auxiliary labels along it therefore preserves all mixed labels
and the actual morphisms into the faithful full-marking schemes.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry MonObj
namespace FLT.Mazur.PolygonInfinitesimalStages
open WeierstrassIntegralChart UniversalWeierstrass AuxiliaryLevel PolygonPinching
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase
variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n]
  (L : Type) [Field L] (a : PowerSeries K →+* L) (ha : a PowerSeries.X ≠ 0)
  {Y Z : Scheme} (p : Y ⟶ exactVeroneseProj K n h) (q : Y ⟶ Spec (.of L))
  (hs : IsPullback p q (exactVeroneseProjToBase K n h)
    (Spec.map (CommRingCat.ofHom a)))
  (r : Z ⟶ exactVeroneseProj K n h) (s : Z ⟶ Spec (.of L))
  (ht : IsPullback r s (exactVeroneseProjToBase K n h)
    (Spec.map (CommRingCat.ofHom a)))
local notation "G" => completeProjectiveGroup K n h L a ha p q hs
local notation "H" => completeProjectiveGroup K n h L a ha r s ht
local notation "e" => completeProjectiveSquareGroupIso K n h L a ha p q hs r s ht

/-- The original square comparison retains the full original cyclic subgroup homomorphism. -/
theorem completeProjectiveCyclicPointHom_square (i : Fin n) (b : Multiplicative (ZMod n)) :
    completeProjectiveCyclicPointHom K n h L a ha p q hs i b ≫ (e i).hom.hom.hom.hom =
      completeProjectiveCyclicPointHom K n h L a ha r s ht i b := by
  apply Over.OverMorphism.ext
  rw [Over.comp_left, completeProjectiveSquareGroupIso_hom]
  change (completeCartesianMarking K n h (Spec.map (CommRingCat.ofHom a)) p q hs
    (rotateIndex b.toAdd i) ≫
      (completeCartesianPointProjectiveIso K n h L a ha p q hs i).hom) ≫
        (completeProjectiveSquareIso K n h L a ha p q hs r s ht i).hom = _
  rw [Category.assoc]
  exact completeProjectiveSquareIso_marking K n h L a ha p q hs r s ht i
    (rotateIndex b.toAdd i)

/-- The two actual auxiliary marking schemes are canonically isomorphic over the original field. -/
def completeProjectiveAuxiliarySquareIso (i : Fin n) :
    completeProjectiveAuxiliaryScheme K n h L a ha p q hs i ≅
      completeProjectiveAuxiliaryScheme K n h L a ha r s ht i :=
  groupTransportIso (G i) (H i) (e i) (Labels 4)

/-- The original full marking is retained label by label through the actual group comparison. -/
theorem completeProjectiveFullMarking_square (i : Fin n) {T : Over (Spec (.of L))}
    (f : T ⟶ completeProjectiveAuxiliaryScheme K n h L a ha p q hs i) (c : CyclicLabels n) :
    completeProjectiveFullMarking K n h L a ha r s ht i
      (groupTransportParameter (G i) (H i) (e i) (Labels 4) f) c =
        completeProjectiveFullMarking K n h L a ha p q hs i f c ≫
          (e i).hom.hom.hom.hom :=
  coprimeFieldMarking_groupTransport (G i) (H i) (e i) (Labels 4)
    (Multiplicative (ZMod n)) (Spec.map (CommRingCat.ofHom (algebraMap L L)))
    (completeProjectiveCyclicPointHom K n h L a ha p q hs i)
    (completeProjectiveCyclicPointHom K n h L a ha r s ht i)
    (completeProjectiveCyclicPointHom_square K n h L a ha p q hs r s ht i)
    f (completeProjectiveFieldMap L T) c

/-- The actual maps to the full faithful marking schemes commute with the original square change. -/
theorem completeProjectiveFullParameter_square (hn : Nat.Coprime 4 n) (i : Fin n)
    {T : Over (Spec (.of L))}
    (f : T ⟶ completeProjectiveAuxiliaryScheme K n h L a ha p q hs i) :
    groupTransportParameter (G i) (H i) (e i) (CyclicLabels n)
      (completeProjectiveFullParameter K n h L a ha p q hs hn i f) =
        completeProjectiveFullParameter K n h L a ha r s ht hn i
          (groupTransportParameter (G i) (H i) (e i) (Labels 4) f) :=
  coprimeFieldLift_groupTransport (G i) (H i) (e i) (Labels 4)
    (Multiplicative (ZMod n)) (Spec.map (CommRingCat.ofHom (algebraMap L L)))
    (completeProjectiveCyclicPointHom K n h L a ha p q hs i)
    (completeProjectiveCyclicPointHom K n h L a ha r s ht i)
    (completeProjectiveCyclicPointHom_square K n h L a ha p q hs r s ht i)
    f (completeProjectiveFieldMap L T) (labels_pow 4)
    (fun b ↦ congrArg Multiplicative.ofAdd (ZModModule.char_nsmul_eq_zero n b.toAdd)) hn
    (completeProjectiveCyclicPointHom_injective K n h L a ha p q hs i)
    (completeProjectiveCyclicPointHom_injective K n h L a ha r s ht i)

end FLT.Mazur.PolygonInfinitesimalStages
