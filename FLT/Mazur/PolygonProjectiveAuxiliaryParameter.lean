/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonProjectiveAuxiliaryMarking
public import FLT.Mazur.AuxiliaryCoprimeFieldNaturality
public import FLT.Mazur.WeierstrassAuxiliaryFieldCover

/-!
# Actual full-marking parameters on the retained polygon fiber

The auxiliary scheme covers the original field base when two is invertible.
Its tests give actual full-marking parameters, natural in every test scheme,
whose cyclic sections are the original chosen cartesian marking maps.
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
  {Y : Scheme} (p : Y ⟶ exactVeroneseProj K n h) (q : Y ⟶ Spec (.of L))
  (hs : IsPullback p q (exactVeroneseProjToBase K n h)
    (Spec.map (CommRingCat.ofHom a)))
local notation "G" => completeProjectiveGroup K n h L a ha p q hs
local notation "g" => Spec.map (CommRingCat.ofHom (algebraMap L L))
local notation "φ" => completeProjectiveCyclicPointHom K n h L a ha p q hs

/-- Auxiliary markings actually cover the retained smooth polygon fiber's original field. -/
theorem completeProjectiveAuxiliaryScheme_surjective (h2 : (2 : L) ≠ 0) (i : Fin n) :
    Surjective (completeProjectiveAuxiliaryScheme K n h L a ha p q hs i).hom :=
  WeierstrassAuxiliaryFieldCover.surjective _ _ (isUnit_iff_ne_zero.mpr h2)

/-- The actual full-marking parameter retaining the original cyclic homomorphism. -/
def completeProjectiveFullParameter (hn : Nat.Coprime 4 n) (i : Fin n)
    {T : Over (Spec (.of L))}
    (f : T ⟶ completeProjectiveAuxiliaryScheme K n h L a ha p q hs i) :
    T ⟶ faithfulScheme (G i).X (CyclicLabels n) :=
  coprimeFieldLift (G i).X (Labels 4) (Multiplicative (ZMod n)) g (φ i)
    (labels_pow 4) (fun b ↦ congrArg Multiplicative.ofAdd
      (ZModModule.char_nsmul_eq_zero n b.toAdd)) hn
    (completeProjectiveCyclicPointHom_injective K n h L a ha p q hs i) f
    (completeProjectiveFieldMap L T)

/-- The full parameter's marked values are the previously constructed complete marking. -/
@[reassoc] theorem completeProjectiveFullParameter_value (hn : Nat.Coprime 4 n) (i : Fin n)
    {T : Over (Spec (.of L))}
    (f : T ⟶ completeProjectiveAuxiliaryScheme K n h L a ha p q hs i) (c : CyclicLabels n) :
    completeProjectiveFullParameter K n h L a ha p q hs hn i f ≫
      faithfulInclusion (G i).X (CyclicLabels n) ≫ value (G i).X (CyclicLabels n) c =
        completeProjectiveFullMarking K n h L a ha p q hs i f c :=
  coprimeFieldLift_value _ _ _ _ _ _ _ _ _ _ _ c

/-- The actual parameter morphism commutes with every map of test schemes. -/
@[reassoc] theorem completeProjectiveFullParameter_natural (hn : Nat.Coprime 4 n)
    (i : Fin n) {T U : Over (Spec (.of L))}
    (f : T ⟶ completeProjectiveAuxiliaryScheme K n h L a ha p q hs i) (k : U ⟶ T) :
    k ≫ completeProjectiveFullParameter K n h L a ha p q hs hn i f =
      completeProjectiveFullParameter K n h L a ha p q hs hn i (k ≫ f) := by
  unfold completeProjectiveFullParameter
  rw [coprimeFieldLift_natural]
  have he : k ≫ completeProjectiveFieldMap L T = completeProjectiveFieldMap L U := by
    apply Over.OverMorphism.ext
    exact k.w
  rw [he]

/-- Cyclic parameter values retain the original square and the original projective comparison. -/
@[reassoc] theorem completeProjectiveFullParameter_cyclic_left (hn : Nat.Coprime 4 n)
    (i : Fin n) {T : Over (Spec (.of L))}
    (f : T ⟶ completeProjectiveAuxiliaryScheme K n h L a ha p q hs i) (b : ZMod n) :
    (completeProjectiveFullParameter K n h L a ha p q hs hn i f ≫
      faithfulInclusion (G i).X (CyclicLabels n) ≫
        value (G i).X (CyclicLabels n) (1, Multiplicative.ofAdd b)).left =
          T.hom ≫ completeCartesianMarking K n h (Spec.map (CommRingCat.ofHom a))
            p q hs (rotateIndex b i) ≫
              completeCartesianPointToProjective K n h L a ha p q hs i := by
  have he := coprimeFieldLift_field (G i).X (Labels 4) (Multiplicative (ZMod n)) g (φ i)
    (labels_pow 4) (fun b ↦ congrArg Multiplicative.ofAdd
      (ZModModule.char_nsmul_eq_zero n b.toAdd)) hn
    (completeProjectiveCyclicPointHom_injective K n h L a ha p q hs i) f
    (completeProjectiveFieldMap L T) (Multiplicative.ofAdd b)
  exact congrArg Over.Hom.left he

end FLT.Mazur.PolygonInfinitesimalStages
