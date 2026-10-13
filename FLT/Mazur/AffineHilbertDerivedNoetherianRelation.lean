/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.VariableHilbertNoetherianSource
public import FLT.Mazur.AffineHilbertNoetherianRelation

/-!
# Unconditional Noetherianity of the full selected Hilbert relation

The selected source's Noetherianity is derived from the original proper family
and étale translation. Consequently the full two-endpoint relation is Noetherian
and qcqs, and both original endpoint maps are quasi-compact. Nothing is removed
from the relation and no effective quotient is postulated.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Opposite TopologicalSpace
namespace FLT.Mazur.HilbertChart.AffineRestriction
open CartierAbel SchemePicard FCurve
set_option backward.isDefEq.respectTransparency false
variable {R : Type} [CommRing R] [Algebra.FiniteType ℤ R] {X : Scheme}
  (f : X ⟶ Spec (.of R)) [IsProper f] [Flat f] [GeometricallyIntegral f]
  [SmoothOfRelativeDimension 1 f] {L : X.Modules} (hL : AmpleLineBundle L)
  (d : ℕ) (V : Over (Spec (.of R))) [IsAffine V.left] [Etale V.hom]
  (c : (relativeFppfSheaf f).obj.obj (op V))
  {A : Over (Spec (.of R))} [IsAffine A.left]
  (k : A ⟶ variableHilbertTest f d V) [IsOpenImmersion k.left]

/-- Noetherianity of the entire actual relation, with no additional source hypothesis. -/
instance fullRelation_isNoetherian : IsNoetherian (relation f hL d V c k).left := by
  let _ := selectedHilbertSource_isLocallyNoetherian f d V k
  let _ := envelope_isLocallyNoetherian V (A := A)
  let _ := isLocallyNoetherian_of_isOpenImmersion (toEnvelope f hL d V c k).left
  let _ := relation_compactSpace f hL d V c k
  exact ⟨⟩

/-- The original first endpoint is quasi-compact on the entire relation. -/
instance fullRelation_fst_quasiCompact : QuasiCompact (fst f hL d V c k).left := by
  let _ := fullRelation_isNoetherian f hL d V c k
  infer_instance

/-- The original second endpoint is quasi-compact on the entire relation. -/
instance fullRelation_snd_quasiCompact : QuasiCompact (snd f hL d V c k).left := by
  let _ := fullRelation_isNoetherian f hL d V c k
  infer_instance

/-- The first endpoint is surjective, witnessed by the actual diagonal relation arrow. -/
instance fullRelation_fst_surjective : Surjective (fst f hL d V c k).left := by
  constructor
  intro x
  refine ⟨(equivalence f hL d V c k).r.left x, ?_⟩
  have h := congrArg (fun a ↦ a.left x) (equivalence f hL d V c k).reflexivity₁
  exact h

/-- The second endpoint is surjective, with the same original identity witness. -/
instance fullRelation_snd_surjective : Surjective (snd f hL d V c k).left := by
  constructor
  intro x
  refine ⟨(equivalence f hL d V c k).r.left x, ?_⟩
  have h := congrArg (fun a ↦ a.left x) (equivalence f hL d V c k).reflexivity₂
  exact h

end FLT.Mazur.HilbertChart.AffineRestriction
