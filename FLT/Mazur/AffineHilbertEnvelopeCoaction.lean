/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeRelationTensorCounit
public import FLT.Mazur.SchemeRelationTensorCocycle
public import FLT.Mazur.AffineHilbertComposableEnvelope

/-!
# Actual Hilbert coactions when the original relation fills its envelope

The coaction is constructed from the ORIGINAL first endpoint. Its laws follow
from the original identity and composition. The envelope-isomorphism hypothesis
is explicit: local tensor charts alone do not provide this hypothesis.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TensorProduct
namespace FLT.Mazur.HilbertChart.AffineRestriction
open CartierAbel SchemePicard FCurve Approximation SchemeRelationTensor
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type} [CommRing R] [Algebra.FiniteType ℤ R] {X : Scheme}
  (f : X ⟶ Spec (.of R)) [IsProper f] [Flat f] [GeometricallyIntegral f]
  [SmoothOfRelativeDimension 1 f] {L : X.Modules} (hL : AmpleLineBundle L)
  (d : ℕ) (V : Over (Spec (.of R))) [IsAffine V.left]
  (c : (relativeFppfSheaf f).obj.obj (op V))
  {A : Over (Spec (.of R))} [IsAffine A.left] (k : A ⟶ variableHilbertTest f d V)
local notation "Z" => relation f hL d V c k
local notation "p" => fst f hL d V c k
local notation "q" => snd f hL d V c k
local notation "j" => toEnvelope f hL d V c k
local notation "β" => k ≫ variableHilbertBase f d V
local notation "e" => equivalence f hL d V c k
/-- The original structural algebra on the parameter coefficients. -/
local instance envelopeSourceAlgebra : Algebra R Γ(A.left, ⊤) := affineBaseSectionAlgebra A.hom
/-- The original structural algebra on the translation coefficients. -/
local instance envelopeBaseAlgebra : Algebra R Γ(V.left, ⊤) := affineBaseSectionAlgebra V.hom
variable [IsIso (toEnvelope f hL d V c k).left]

/-- Filling the affine envelope makes the ORIGINAL full relation affine. -/
theorem fullEnvelope_relation_affine : IsAffine (Z).left := by
  let _ := variableHilbertOverlap_envelope_affine V A
  exact IsAffine.of_isIso (j).left

omit [IsAffine V.left] [IsAffine A.left] in
/-- The actual composable-pair envelope is a base change of the same envelope isomorphism. -/
theorem fullEnvelope_composable_isIso :
    IsIso (composableToProduct f hL d V c k).left :=
  ((composableToProduct_isPullback f hL d V c k).map (Over.forget _)).isIso_snd_of_isIso
    (inferInstanceAs (IsIso (j).left))

/-- Genuine multiplicative descent data from the original full Hilbert relation and its laws. -/
def fullEnvelopeData :
    let _ := coefficientAlgebra β
    let _ := coefficientTower β
    AffineAlgebraDescent.Data R Γ(V.left, ⊤) Γ(A.left, ⊤) := by
  let _ := coefficientAlgebra β
  let _ := coefficientTower β
  let _ := fullEnvelope_relation_affine f hL d V c k
  let _ := fullEnvelope_composable_isIso f hL d V c k
  refine {
    coaction := coaction β p q j (toEnvelope_test f hL d V c k)
      (toEnvelope_base f hL d V c k)
    counit := coaction_counit β p q j (toEnvelope_test f hL d V c k)
      (toEnvelope_base f hL d V c k) (e).r (e).reflexivity₁ (e).reflexivity₂
    coassoc := ?_ }
  intro x
  apply coaction_coassoc β p q j (toEnvelope_test f hL d V c k)
    (toEnvelope_base f hL d V c k) (pullback.fst q p) (pullback.snd q p) (e).t
    (composableToProduct f hL d V c k)
  · exact prod.lift_fst _ _
  · change (composableToProduct f hL d V c k) ≫ prod.snd = _
    rw [composableToProduct, prod.lift_snd, toEnvelope_base]
  · exact pullback.condition
  · exact (e).transitivity₁
  · exact (e).transitivity₂

/-- The constructed coaction retains the original endpoint pullback, coefficient by coefficient. -/
theorem fullEnvelopeData_source (b : Γ(A.left, ⊤)) :
    let _ := coefficientAlgebra β
    let _ := coefficientTower β
    SchemeRelationTensor.coordinates j ((fullEnvelopeData f hL d V c k).coaction b) =
      (p).left.appTop b :=
  coordinates_source p j b

/-- Fixed coefficients are exactly the ORIGINAL full relation equation. -/
theorem fullEnvelopeData_fixed_iff (b : Γ(A.left, ⊤)) :
    let _ := coefficientAlgebra β
    let _ := coefficientTower β
    b ∈ AffineAlgebraDescent.invariants (fullEnvelopeData f hL d V c k) ↔
      (p).left.appTop b = (q).left.appTop b := by
  let _ := coefficientAlgebra β
  let _ := coefficientTower β
  dsimp only
  rw [AffineAlgebraDescent.mem_invariants,
    ← (SchemeRelationTensor.coordinates j).injective.eq_iff,
    fullEnvelopeData_source, coordinates_test β p q j (toEnvelope_test f hL d V c k)
      (toEnvelope_base f hL d V c k)]

end FLT.Mazur.HilbertChart.AffineRestriction
