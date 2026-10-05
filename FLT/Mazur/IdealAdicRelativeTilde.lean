/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.IdealAdicRelativePresheaf
public import FLT.Mazur.TildeSourceSectionComparison

/-!
# The relative tensor algebra as actual closed pullback sections

Pull back the affine sheaf of the original graded base module to the actual
closed subscheme. Its affine sections are the original relative tensors.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry Opposite
open Scheme.Modules FLT.Mazur.IdealAdicGradedSections
open FLT.Mazur.AffineModuleGlobalSections
open scoped TensorProduct

universe u

namespace FLT.Mazur.IdealAdicGradedPullback

variable {X Y : Scheme.{u}} [IsLocallyNoetherian X] [IsLocallyNoetherian Y] [IsAffine Y]
variable (J : Y.IdealSheafData) (f : X ⟶ Y)

omit [IsLocallyNoetherian X] [IsLocallyNoetherian Y] [IsAffine Y] in
/-- The original relative scalar map is the structural map on the actual closed open. -/
lemma closedBaseMap_eq_source (U : X.Opens) :
    closedBaseMap J f U = ModuleSourceSectionBaseChange.scalarMap
      ((J.comap f).subschemeι ≫ f) ((J.comap f).subschemeι ⁻¹ᵁ U) := by
  ext r
  exact ConcreteCategory.congr_hom
    ((J.comap f).subschemeι.naturality (homOfLE (by simp : U ≤ f ⁻¹ᵁ ⊤)).op)
      (f.app ⊤ r)

/-- The closed inverse image of an ambient affine chart is affine. -/
def closedAffineChart (U : X.affineOpens) : (J.comap f).subscheme.affineOpens :=
  ⟨(J.comap f).subschemeι ⁻¹ᵁ U.1, U.2.preimage (J.comap f).subschemeι⟩

/-- Pullback of the actual graded base module to the actual closed subscheme. -/
def relativeTildeModule : (J.comap f).subscheme.Modules :=
  (pullback ((J.comap f).subschemeι ≫ f)).obj
    ((affineTilde Y).obj (ModuleCat.of Γ(Y, ⊤) (IdealAdicGradedSections.Sections J ⊤)))

/-- The actual closed pullback module viewed on the ambient scheme. -/
def relativeTildePushforward : X.Modules :=
  (pushforward (J.comap f).subschemeι).obj (relativeTildeModule J f)

/-- The actual relative tensor algebra identifies additively with closed pullback sections. -/
def relativeTildeChartEquiv (U : X.affineOpens) :
    RelativeAlgebra J f U ≃+ Γ(relativeTildePushforward J f, U.1) :=
  TildeSourceSectionComparison.tensorSectionsEquivOfMap
    ((J.comap f).subschemeι ≫ f)
    (ModuleCat.of Γ(Y, ⊤) (IdealAdicGradedSections.Sections J ⊤)) (closedAffineChart J f U)
    (closedBaseMap J f U.1) (closedBaseMap_eq_source J f U.1)

/-- The original base section enters the closed pullback through the actual two units. -/
def relativeTildeBaseSection (U : X.Opens) (a : IdealAdicGradedSections.Sections J ⊤) :
    Γ(relativeTildeModule J f, (J.comap f).subschemeι ⁻¹ᵁ U) :=
  ModuleSourceSectionBaseChange.unitMap ((J.comap f).subschemeι ≫ f)
    ((affineTilde Y).obj (ModuleCat.of Γ(Y, ⊤) (IdealAdicGradedSections.Sections J ⊤)))
    ((J.comap f).subschemeι ⁻¹ᵁ U)
    ((affineAdjunction Y).unit.app
      (ModuleCat.of Γ(Y, ⊤) (IdealAdicGradedSections.Sections J ⊤)) a)

omit [IsLocallyNoetherian X] [IsLocallyNoetherian Y] in
/-- The chart comparison sends an original tensor to its scaled actual pullback section. -/
lemma relativeTildeChartEquiv_tmul (U : X.affineOpens)
    (a : IdealAdicGradedSections.Sections J ⊤) (r : ClosedScalars (J.comap f) U.1) :
    let := closedBaseAlgebra J f U.1
    relativeTildeChartEquiv J f U (a ⊗ₜ[Γ(Y, ⊤)] r) =
      r • relativeTildeBaseSection J f U.1 a :=
  TildeSourceSectionComparison.tensorSectionsEquivOfMap_tmul
    ((J.comap f).subschemeι ≫ f)
    (ModuleCat.of Γ(Y, ⊤) (IdealAdicGradedSections.Sections J ⊤)) (closedAffineChart J f U)
    (closedBaseMap J f U.1) (closedBaseMap_eq_source J f U.1) a r

omit [IsLocallyNoetherian X] [IsLocallyNoetherian Y] in
/-- The base section commutes with the actual closed source restrictions. -/
lemma relativeTildeBaseSection_restrict {U V : X.Opens} (i : U ⟶ V)
    (a : IdealAdicGradedSections.Sections J ⊤) :
    (relativeTildePushforward J f).presheaf.map i.op (relativeTildeBaseSection J f V a) =
      relativeTildeBaseSection J f U a :=
  ModuleSourceSectionBaseChange.unitMap_restrict ((J.comap f).subschemeι ≫ f)
    ((affineTilde Y).obj (ModuleCat.of Γ(Y, ⊤) (IdealAdicGradedSections.Sections J ⊤)))
    ((TopologicalSpace.Opens.map (J.comap f).subschemeι.base).map i)
    ((affineAdjunction Y).unit.app
      (ModuleCat.of Γ(Y, ⊤) (IdealAdicGradedSections.Sections J ⊤)) a)

omit [IsLocallyNoetherian X] in
/-- The chart equivalences intertwine the original tensor and sheaf restrictions. -/
lemma relativeTildeChartEquiv_restrict {U V : X.affineOpens} (i : U.1 ⟶ V.1)
    (t : RelativeAlgebra J f V) :
    (relativeTildePushforward J f).presheaf.map i.op (relativeTildeChartEquiv J f V t) =
      relativeTildeChartEquiv J f U (relativeRestriction J f i t) := by
  let := closedBaseAlgebra J f U.1
  let := closedBaseAlgebra J f V.1
  induction t using TensorProduct.inductionOn with
  | add t s ht hs => simp only [map_add, ht, hs]
  | tmul a r =>
    rw [relativeRestriction_tmul, relativeTildeChartEquiv_tmul, relativeTildeChartEquiv_tmul]
    change (relativeTildeModule J f).presheaf.map
      ((TopologicalSpace.Opens.map (J.comap f).subschemeι.base).map i).op
      (r • relativeTildeBaseSection J f V.1 a) = _
    rw [map_smul]
    exact congrArg (fun s ↦ closedScalarRestriction (J.comap f) i r • s)
      (relativeTildeBaseSection_restrict J f i a)

end FLT.Mazur.IdealAdicGradedPullback
