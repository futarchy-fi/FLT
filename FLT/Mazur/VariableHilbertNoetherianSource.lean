/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OriginalHilbertFiniteType
public import FLT.Mazur.VariableTranslatedHilbertChart

/-!
# Noetherianity of the original translated Hilbert sources

The original coefficient ring is finite type over the integers. The acyclic
Hilbert open and its product with an arbitrary étale translation therefore
have locally Noetherian sources. Any selected affine open is Noetherian;
this property is derived from the original family, not an extra chart input.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.HilbertChart
open FCurve
set_option backward.isDefEq.respectTransparency false
variable {R : Type} [CommRing R] [Algebra.FiniteType ℤ R] {X : Scheme}
  (f : X ⟶ Spec (.of R)) [IsProper f] [Flat f] [GeometricallyIntegral f]
  [SmoothOfRelativeDimension 1 f] (d : ℕ)

instance ampleHilbertTest_locallyOfFiniteType :
    LocallyOfFiniteType (ampleHilbertTest f d).hom :=
  originalHilbertStructure_locallyOfFiniteType f d

instance acyclicHilbertTest_locallyOfFiniteType :
    LocallyOfFiniteType (acyclicHilbertTest f d).hom := by
  rw [← (acyclicHilbertArrow f d).w]
  infer_instance

variable (V : Over (Spec (.of R))) [Etale V.hom]

/-- Both independent factors keep their original base map and imply local finite type. -/
instance variableHilbertTest_locallyOfFiniteType :
    LocallyOfFiniteType (variableHilbertTest f d V).hom := by
  have h : LocallyOfFiniteType (variableHilbertBase f d V).left := by
    change LocallyOfFiniteType (prod.fst : prod V (acyclicHilbertTest f d) ⟶ V).left
    rw [← Over.prodLeftIsoPullback_hom_fst]
    infer_instance
  rw [← (variableHilbertBase f d V).w]
  infer_instance

/-- The whole translated parameter is locally Noetherian for every étale translation. -/
instance variableHilbertTest_isLocallyNoetherian :
    IsLocallyNoetherian (variableHilbertTest f d V).left := by
  let _ : IsNoetherianRing R := Algebra.FiniteType.isNoetherianRing ℤ R
  exact LocallyOfFiniteType.isLocallyNoetherian (variableHilbertTest f d V).hom

/-- Any original selected open chart is locally Noetherian without an extra hypothesis. -/
theorem selectedHilbertSource_isLocallyNoetherian {A : Over (Spec (.of R))}
    (k : A ⟶ variableHilbertTest f d V) [IsOpenImmersion k.left] :
    IsLocallyNoetherian A.left :=
  isLocallyNoetherian_of_isOpenImmersion k.left

/-- In particular, any selected affine chart is a Noetherian scheme. -/
theorem selectedAffineHilbertSource_isNoetherian {A : Over (Spec (.of R))}
    [IsAffine A.left] (k : A ⟶ variableHilbertTest f d V) [IsOpenImmersion k.left] :
    IsNoetherian A.left := by
  let _ := selectedHilbertSource_isLocallyNoetherian f d V k
  exact ⟨⟩

end FLT.Mazur.HilbertChart
