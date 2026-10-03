/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ClassifiedGenusOneFamily
public import FLT.Mazur.PolygonGeometricGenus

/-!
# Polygons as classified genus-one families

Every specified positive polygon supplies the existing family contract.
Field-extension comparison proves classification on arbitrary geometric squares;
the family can then be pulled back along any scheme morphism.
-/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
@[expose] public noncomputable section
namespace FLT.Mazur.PolygonClassifiedFamily
open PolygonPinching FCurve FCurve.DRFiberClassification
variable (K : Type) [Field K] (n : ℕ) [NeZero n] (hn : 0 < n)
  {C : Over (Spec (.of K))} (p : components K n ⟶ C) (q : nodes K n ⟶ C)
  (h : IsPushout (toComponents K n hn) (toNodes K n) p q)

include h in
/-- Every geometric fiber is an actual polygon with the full nodal core. -/
theorem classified : ClassifiedGeometricFibers C.hom := by
  refine ⟨fun L _ _ g Y fst snd hs ↦ ?_⟩
  obtain ⟨p', q', hh⟩ :=
    PolygonFieldExtension.exists_cocone_of_isPullback K L n hn p q h g fst snd hs
  exact ⟨PolygonNodalCore.nodalFiberCore L n hn p' q' hh,
    Or.inr ⟨n, hn, p', q', hh⟩⟩

include h in
/-- A specified polygon is a proper flat classified genus-one family. -/
theorem family : ClassifiedGenusOneFamily C.hom := by
  let := PolygonProper.proper K n hn p q h
  let := polygon_lfp K n hn p q h
  exact ⟨⟨inferInstance, inferInstance, inferInstance⟩, classified K n hn p q h,
    PolygonGeometricGenus.geometricFibers K n hn p q h⟩

include h in
/-- The constructed polygon family satisfies the same contract after arbitrary base change. -/
theorem baseChange {T : Scheme} (g : T ⟶ Spec (.of K)) :
    ClassifiedGenusOneFamily (pullback.snd C.hom g) :=
  (family K n hn p q h).baseChange g

end FLT.Mazur.PolygonClassifiedFamily
