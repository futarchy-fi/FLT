/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ClosedDirectImageAcyclic
public import FLT.Mazur.RelativeDirectImageForgetting

/-!
# Closed specialization of relative direct-image composition

For a closed immersion `f` and any subsequent morphism `g`, the actual module
higher direct images of `g` on `f_* M` agree with those of `f ≫ g` on `M`.
Closed exactness supplies all acyclicity inputs. The comparison is the existing
relative composition isomorphism, and after forgetting it is the sheafification
of the open comparison built with `closedPushforwardRestriction`. This is the
closed-immersion comparison for the first Stacks 02O5 application.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxSynthPendingDepth 1

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
open AlgebraicGeometry.Scheme.Modules

universe u

namespace FLT.Mazur.ClosedDirectImageComposition

open FCurve CoherentDevissage ClosedDirectImageAcyclic
open HigherDirectImagePresheaf HigherDirectImageOpenSheafification

local instance sheafHasExt (T : TopCat.{u}) :
    HasExt.{u + 1} (Sheaf (Opens.grothendieckTopology T) AddCommGrpCat.{u}) := HasExt.standard _

local instance topSheafHasExt (T : TopCat.{u}) :
    HasExt.{u + 1} (TopCat.Sheaf AddCommGrpCat.{u} T) := HasExt.standard _

variable {X Y Z : Scheme.{u}} (f : X ⟶ Y) [IsClosedImmersion f] (g : Y ⟶ Z)

/-- The closed specialization is natural on all modules, with no acyclicity input on `g`. -/
def compositionIso (n : ℕ) :
    pushforward f ⋙ (pushforward g).rightDerived n ≅ (pushforward (f ≫ g)).rightDerived n :=
  NatIso.ofComponents
    (fun M ↦ RelativeDirectImageComposition.moduleIso f g M (modulePushforwardAcyclic f M) n)
    (fun a ↦ RelativeDirectImageComposition.moduleIso_naturality f g a
      (modulePushforwardAcyclic f _) (modulePushforwardAcyclic f _) n)

/-- Each component is precisely the previously constructed module composition comparison. -/
lemma compositionIso_app (M : X.Modules) (n : ℕ) :
    (compositionIso f g n).app M =
      RelativeDirectImageComposition.moduleIso f g M (modulePushforwardAcyclic f M) n := rfl

/-- Forgetting the closed specialization gives the sheafified open comparison. -/
lemma compositionIso_hom_forget (M : X.Modules) (n : ℕ) :
    (moduleToSheaf Z).map ((compositionIso f g n).hom.app M) =
      (RelativeDirectImageComposition.forgottenIso f g M
        (modulePushforwardAcyclic f M) n).hom :=
  RelativeDirectImageForgetting.moduleIso_hom_forget f g M (modulePushforwardAcyclic f M) n

/-- The local linear comparison for a closed immersion requires no extra hypotheses. -/
def openComparison (U : Y.Opens) (M : X.Modules) (n : ℕ) :
    letI := Module.compHom (ModuleH (M.restrict (f ⁻¹ᵁ U).ι) n) (f ∣_ U).appTop.hom
    ModuleH (((pushforward f).obj M).restrict U.ι) n ≃ₗ[Γ(U.toScheme, ⊤)]
      ModuleH (M.restrict (f ⁻¹ᵁ U).ι) n :=
  openAcyclicPushforwardModuleHEquiv f U M (modulePushforwardAcyclic f M) n

/-- The local comparison uses the existing closed pushforward-restriction isomorphism. -/
lemma openComparison_eq_restriction (U : Y.Opens) (M : X.Modules) (n : ℕ) :
    openComparison f U M n =
      (moduleHIsoOfIso ((closedPushforwardRestriction f U).app M) n).trans
        (acyclicPushforwardModuleHEquiv (f ∣_ U) (M.restrict (f ⁻¹ᵁ U).ι)
          (modulePushforwardAcyclic (f ∣_ U) (M.restrict (f ⁻¹ᵁ U).ι)) n) := rfl

/-- In degree zero, the open comparison is the actual map on restricted sections. -/
lemma openComparison_zero (U : Y.Opens) (M : X.Modules)
    (x : ModuleH (((pushforward f).obj M).restrict U.ι) 0) :
    moduleH0Equiv (M.restrict (f ⁻¹ᵁ U).ι) (openComparison f U M 0 x) =
      ((closedPushforwardRestriction f U).hom.app M).app ⊤
        (moduleH0Equiv (((pushforward f).obj M).restrict U.ι) x) := by
  exact (acyclicPushforwardModuleHEquiv_zero (f ∣_ U) (M.restrict (f ⁻¹ᵁ U).ι)
    (modulePushforwardAcyclic (f ∣_ U) (M.restrict (f ⁻¹ᵁ U).ι))
    (moduleHMap ((closedPushforwardRestriction f U).hom.app M) 0 x)).trans
      (moduleH0Equiv_naturality ((closedPushforwardRestriction f U).hom.app M) x)

/-- Before sheafification, the relative comparison is the same closed open comparison. -/
lemma valueEquiv_openComparison (U : Z.Opens) (M : X.Modules) (n : ℕ)
    (x : (openPresheaf g.base (moduleAbelianSheaf ((pushforward f).obj M)) n).obj (op U)) :
    moduleValueEquiv (f ≫ g) M U n
      (RelativeDirectImageComposition.valueEquiv f.base g.base (moduleAbelianSheaf M)
        (abelianPushforwardAcyclic f M) U n x) =
      openComparison f (g ⁻¹ᵁ U) M n
        (moduleValueEquiv g ((pushforward f).obj M) U n x) :=
  RelativeDirectImageComposition.valueEquiv_module f g M (modulePushforwardAcyclic f M) U n x

/-- The closed local comparison commutes with restriction between base opens. -/
lemma openComparison_restrict (U : Y.Opens) {V : Y.Opens} (i : V ⟶ U)
    (M : X.Modules) (n : ℕ) (x : ModuleH (((pushforward f).obj M).restrict U.ι) n) :
    openComparison f V M n (moduleOpenRestriction ((pushforward f).obj M) i n x) =
      moduleOpenRestriction M ((Opens.map f.base).map i) n (openComparison f U M n x) :=
  openAcyclicPushforwardModuleHEquiv_restrict f U M (modulePushforwardAcyclic f M) i n x

/-- Restricting the absolute closed acyclic comparison gives the same open comparison. -/
lemma openComparison_global (U : Y.Opens) (M : X.Modules) (n : ℕ)
    (x : ModuleH ((pushforward f).obj M) n) :
    openComparison f U M n
      (OpenSheafCohomologyRestriction.globalOpenRestriction U
        (moduleAbelianSheaf ((pushforward f).obj M)) n x) =
      OpenSheafCohomologyRestriction.globalOpenRestriction (f ⁻¹ᵁ U) (moduleAbelianSheaf M) n
        (acyclicPushforwardModuleHEquiv f M (modulePushforwardAcyclic f M) n x) :=
  openAcyclicPushforwardModuleHEquiv_global f U M (modulePushforwardAcyclic f M) n x

/-- The sheafified closed comparison retains the action of every base section. -/
lemma forgottenIso_hom_smul (M : X.Modules) (n : ℕ) (U : Z.Opens) (r : Γ(Z, U))
    (x : (((pushforward g).rightDerived n).obj ((pushforward f).obj M)).val.obj (op U)) :
    (RelativeDirectImageComposition.forgottenIso f g M (modulePushforwardAcyclic f M) n).hom.hom.app
        (op U) (r • x) =
      r • (show (((pushforward (f ≫ g)).rightDerived n).obj M).val.obj (op U) from
        (RelativeDirectImageComposition.forgottenIso f g M
          (modulePushforwardAcyclic f M) n).hom.hom.app (op U) x) :=
  RelativeDirectImageForgetting.forgottenIso_hom_smul f g M (modulePushforwardAcyclic f M) n U r x

/-- The first closed-immersion comparison transports vanishing in every degree. -/
theorem isZero_iff (M : X.Modules) (n : ℕ) :
    IsZero (((pushforward g).rightDerived n).obj ((pushforward f).obj M)) ↔
      IsZero (((pushforward (f ≫ g)).rightDerived n).obj M) :=
  ((compositionIso f g n).app M).isZero_iff

end FLT.Mazur.ClosedDirectImageComposition
