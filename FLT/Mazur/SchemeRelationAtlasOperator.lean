/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeRelationSectionScalars
public import FLT.Mazur.BoundaryCorrectionOperatorIndependence

/-!
# The original atlas operator over the actual invariant scalars

The boundary and both mixed maps are the unchanged structure-sheaf maps.
Their scalar linearity follows from the original relation squares, so the
explicit section vector is the original correction operator over the equalizer.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.SchemeRelationAtlasOperator
open SchemeEffectiveEpiSections SchemeRelationSectionScalars BoundaryCorrectionIdeal
set_option backward.isDefEq.respectTransparency false
variable {D A X : Scheme} (p q : D ⟶ A) (f : X ⟶ A)
  {ι : Type} (U : ι → X.Opens)
  (B : ι → Scheme) (gB : ∀ i, B i ⟶ X) (hgB : ∀ i, ⊤ ≤ gB i ⁻¹ᵁ U i)
  (M : ι → ι → Scheme) (gM gM' : ∀ i j, M i j ⟶ X)
  (hgM : ∀ i j, ⊤ ≤ gM i j ⁻¹ᵁ U i) (hgM' : ∀ i j, ⊤ ≤ gM' i j ⁻¹ᵁ U j)
  (δ : ∀ i j, M i j ⟶ D)
  (hδ : ∀ i j, δ i j ≫ p = gM i j ≫ f)
  (hδ' : ∀ i j, δ i j ≫ q = gM' i j ≫ f)

/-- The original boundary restriction is an algebra map for the original scalars. -/
def boundaryMap (i : ι) :
    let _ := sectionAlgebra p q f (U i)
    let _ := sectionAlgebra p q (gB i ≫ f) ⊤
    Γ(X, U i) →ₐ[compatibleFunctions p q] Γ(B i, ⊤) :=
  appLEAlgHom p q f (gB i ≫ f) (gB i) rfl (U i) ⊤ (hgB i)

/-- The first mixed endpoint uses its own unchanged source square. -/
def firstMap (i j : ι) :
    let _ := sectionAlgebra p q f (U i)
    let _ := sectionAlgebra p q (gM i j ≫ f) ⊤
    Γ(X, U i) →ₐ[compatibleFunctions p q] Γ(M i j, ⊤) :=
  appLEAlgHom p q f (gM i j ≫ f) (gM i j) rfl (U i) ⊤ (hgM i j)

/-- The second endpoint is linear for that same action by the full original relation. -/
def secondMap (i j : ι) :
    let _ := sectionAlgebra p q f (U j)
    let _ := sectionAlgebra p q (gM i j ≫ f) ⊤
    Γ(X, U j) →ₐ[compatibleFunctions p q] Γ(M i j, ⊤) :=
  relationAppLEAlgHom p q f (gM i j ≫ f) (gM' i j) (δ i j) (hδ i j) (hδ' i j)
    (U j) ⊤ (hgM' i j)

/-- The whole old-atlas correction operator, with every ordered-pair equation retained. -/
def operator :
    let _ : ∀ i, Algebra (compatibleFunctions p q) Γ(X, U i) :=
      fun i ↦ sectionAlgebra p q f (U i)
    let _ : ∀ i, Algebra (compatibleFunctions p q) Γ(B i, ⊤) :=
      fun i ↦ sectionAlgebra p q (gB i ≫ f) ⊤
    let _ : ∀ i j, Algebra (compatibleFunctions p q) Γ(M i j, ⊤) :=
      fun i j ↦ sectionAlgebra p q (gM i j ≫ f) ⊤
    (∀ i, Γ(X, U i)) →ₗ[compatibleFunctions p q]
      ((∀ i, Γ(B i, ⊤)) × ∀ i j, Γ(M i j, ⊤)) := by
  let _ : ∀ i, Algebra (compatibleFunctions p q) Γ(X, U i) :=
    fun i ↦ sectionAlgebra p q f (U i)
  let _ : ∀ i, Algebra (compatibleFunctions p q) Γ(B i, ⊤) :=
    fun i ↦ sectionAlgebra p q (gB i ≫ f) ⊤
  let _ : ∀ i j, Algebra (compatibleFunctions p q) Γ(M i j, ⊤) :=
    fun i j ↦ sectionAlgebra p q (gM i j ≫ f) ⊤
  exact originalCorrectionOperator (boundaryMap p q f U B gB hgB)
    (firstMap p q f U M gM hgM)
    (secondMap p q f U M gM gM' hgM' δ hδ hδ') 0

/-- Its vector is literally the section vector used by the full geometric error tower. -/
theorem operator_apply (w : ∀ i, Γ(X, U i)) :
    operator p q f U B gB hgB M gM gM' hgM hgM' δ hδ hδ' w =
      ((fun i ↦ (gB i).appLE (U i) ⊤ (hgB i) (w i)),
        fun i j ↦ (gM i j).appLE (U i) ⊤ (hgM i j) (w i) -
          (gM' i j).appLE (U j) ⊤ (hgM' i j) (w j)) := by
  let _ : ∀ i, Algebra (compatibleFunctions p q) Γ(X, U i) :=
    fun i ↦ sectionAlgebra p q f (U i)
  let _ : ∀ i, Algebra (compatibleFunctions p q) Γ(B i, ⊤) :=
    fun i ↦ sectionAlgebra p q (gB i ≫ f) ⊤
  let _ : ∀ i j, Algebra (compatibleFunctions p q) Γ(M i j, ⊤) :=
    fun i j ↦ sectionAlgebra p q (gM i j ≫ f) ⊤
  exact originalCorrectionOperator_apply
    (boundaryMap p q f U B gB hgB) (firstMap p q f U M gM hgM)
    (secondMap p q f U M gM gM' hgM' δ hδ hδ') 0 w

end FLT.Mazur.SchemeRelationAtlasOperator
