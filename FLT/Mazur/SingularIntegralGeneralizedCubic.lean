/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OneGonOriginalCubic

/-!
# Original singular integral geometric generalized curves are nodal cubics

The defining geometric classification and irreducibility force a one-gon.
The constructed full comparison preserves the original group, identity and
whole action; neither a Weierstrass equation nor a node section is input.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry
namespace FLT.Mazur.SingularIntegralGeneralizedCubic
open PolygonPinching
variable {K : Type} [Field K]

/-- An irreducible polygon has exactly one normalization component. -/
theorem isNeronOneGon_of_irreducible (C : Over (Spec (.of K)))
    [IrreducibleSpace C.left] (hc : IsNeronPolygon C) :
    IsNeronNGon C 1 Nat.zero_lt_one := by
  obtain ⟨n, hn, p, q, h⟩ := hc
  let _ : NeZero n := ⟨Nat.ne_of_gt hn⟩
  let e := PolygonActionGraph.vertices K n hn p q h
  have hs : Subsingleton (irreducibleComponents C.left) := by
    rw [irreducibleComponents_eq_singleton]
    infer_instance
  have hlen : n = 1 := by
    by_contra hne
    have htwo : 2 ≤ n := by omega
    have he : e ⟨0, by omega⟩ = e ⟨1, by omega⟩ := hs.elim _ _
    have hv := congrArg Fin.val (e.injective he)
    simp only at hv
    omega
  subst n
  exact ⟨p, q, h⟩

variable [IsAlgClosed K] (E : GeneralizedEllipticCurve (Spec (.of K)))
  [IsIntegral E.curve.left]

/-- An actual singular integral geometric generalized curve is a one-gon without extra data. -/
theorem isNeronOneGon (hs : ¬ Smooth E.curve.hom) :
    IsNeronNGon E.curve 1 Nat.zero_lt_one := by
  have hc := E.family.classified.fiber K (𝟙 _) (𝟙 _) E.curve.hom IsPullback.of_id_fst
  exact isNeronOneGon_of_irreducible E.curve (hc.classification.resolve_left hs)

/-- The original singular integral geometric curve has a full arithmetic nodal presentation. -/
theorem exists_boundaryIso (hs : ¬ Smooth E.curve.hom) :
    Nonempty (E ≅ ArithmeticOneGonTorus.boundaryCurve K) :=
  OneGonOriginalCubic.exists_boundaryIso E (isNeronOneGon E hs)

end FLT.Mazur.SingularIntegralGeneralizedCubic
