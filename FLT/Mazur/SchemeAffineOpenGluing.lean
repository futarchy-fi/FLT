/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ModuleSheafGluingTransport
public import FLT.Mazur.SchemeAffineOpenTransitionCocycle

/-!
# Gluing the effectively descended affine chart modules

The original geometric descent datum constructs the affine modules and their
pair comparisons. Transport to image opens and the proved cocycle assemble
actual gluing data, with no transition or cocycle supplied as an extra input.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
universe u
namespace FLT.Mazur.SchemeAffineDescent
open ModuleSheafMorphismGluing ModuleSheafOpenImageChart
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {X Y : Scheme.{u}} {p : Y ⟶ X} {ι : Type u}
variable (C : ι → Chart p) {M : Y.Modules} (D : SchemeGeometricDescent.Data p M)
variable [∀ i, ((pullback (C i).cover).obj M).IsQuasicoherent]
variable [∀ i, IsOpenImmersion (C i).base]
attribute [local irreducible] Chart.sheaf

/-- The independently constructed pair-open comparisons obey the gluing cocycle. -/
theorem openTransition_cocycle (i j k : ι) (V : X.Opens)
    (hi : V ≤ (C i).base.opensRange) (hj : V ≤ (C j).base.opensRange)
    (hk : V ≤ (C k).base.opensRange)
    (s : Γ((pushforward (C i).base).obj ((C i).sheaf D), V)) :
    localEval ((C j).openTestIso (C k) D
        ((C j).base.opensRange ⊓ (C k).base.opensRange) inf_le_left inf_le_right).hom
        (le_inf hj hk)
      (localEval ((C i).openTestIso (C j) D
        ((C i).base.opensRange ⊓ (C j).base.opensRange) inf_le_left inf_le_right).hom
        (le_inf hi hj) s) =
      localEval ((C i).openTestIso (C k) D
        ((C i).base.opensRange ⊓ (C k).base.opensRange) inf_le_left inf_le_right).hom
        (le_inf hi hk) s := by
  let T : Fin 3 → Chart p := ![C i, C j, C k]
  let _ : ∀ a, ((pullback (T a).cover).obj M).IsQuasicoherent := fun a ↦ by
    fin_cases a <;> dsimp [T] <;> infer_instance
  let _ : ∀ a, IsOpenImmersion (T a).base := fun a ↦ by
    fin_cases a <;> dsimp [T] <;> infer_instance
  have h : ∀ a, V ≤ (T a).base.opensRange := by
    intro a
    fin_cases a
    · exact hi
    · exact hj
    · exact hk
  exact Chart.openPairTransition_cocycle D T V h s

/-- Gluing data constructed from the original descent datum on the affine charts. -/
def openGluingData : ModuleSheafGluing.Data (fun i ↦ (C i).base.opensRange) :=
  ModuleSheafGluing.ofPushforwardIsoEval (fun i ↦ (C i).base.opensRange)
    (fun i ↦ imageModule (C i).base ((C i).sheaf D))
    (fun i ↦ (pushforward (C i).base).obj ((C i).sheaf D))
    (fun i ↦ imagePushforwardIso (C i).base ((C i).sheaf D))
    (fun i j ↦ (C i).openTestIso (C j) D
      ((C i).base.opensRange ⊓ (C j).base.opensRange) inf_le_left inf_le_right)
    (openTransition_cocycle C D)

/-- The module sheaf obtained by gluing the effectively descended chart modules. -/
def openGlued : X.Modules := (openGluingData C D).glued

/-- The glued sheaf restricts to the transported original object on every image chart. -/
def openGluedRestrictionIso (i : ι) :
    (openGlued C D).restrict (C i).base.opensRange.ι ≅
      imageModule (C i).base ((C i).sheaf D) :=
  (openGluingData C D).restrictionIso i

end FLT.Mazur.SchemeAffineDescent
