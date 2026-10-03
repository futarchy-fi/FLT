/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.DivisorLineBundleRestrict
public import FLT.Mazur.ModulePullbackUnitCoherence

/-!
# Pullback of the actual ideal module

The pulled-back inclusion factors through the kernel defining the comap ideal.
This construction works for every scheme morphism. It agrees with restriction
for open immersions and is invertible for the unit ideal.
-/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme.Modules
@[expose] public noncomputable section
universe u
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
namespace FLT.Mazur.FCurve
variable {X Y : Scheme.{u}}

/-- Pull the ideal inclusion back into the source structure module. -/
def idealModulePullbackι (I : Y.IdealSheafData) (f : X ⟶ Y) :
    (Scheme.Modules.pullback f).obj (idealModule I) ⟶ structureModule X :=
  (Scheme.Modules.pullback f).map (idealModuleι I) ≫ (modulePullbackUnitIso f).hom

/-- On adjunction-unit sections, the inclusion is the scheme section map. -/
lemma idealModulePullbackι_unit (I : Y.IdealSheafData) (f : X ⟶ Y)
    (U : Y.Opens) (s : Γ(idealModule I, U)) :
    (idealModulePullbackι I f).app (f ⁻¹ᵁ U)
      (((pullbackPushforwardAdjunction f).unit.app (idealModule I)).app U s) =
        f.app U ((idealModuleι I).app U s) := by
  have h := congrArg (fun k ↦ k.app U s)
    ((pullbackPushforwardAdjunction f).unit.naturality (idealModuleι I)).symm
  change ((Scheme.Modules.pullback f).map (idealModuleι I)).app _
    (((pullbackPushforwardAdjunction f).unit.app _).app U s) =
      ((pullbackPushforwardAdjunction f).unit.app _).app U ((idealModuleι I).app U s) at h
  exact (congrArg ((modulePullbackUnitIso f).hom.app (f ⁻¹ᵁ U)) h).trans
    (modulePullbackUnitIso_unit f U ((idealModuleι I).app U s))

/-- The pulled-back inclusion vanishes in the quotient by the comap ideal. -/
lemma idealModulePullbackι_quotient (I : Y.IdealSheafData) (f : X ⟶ Y) :
    idealModulePullbackι I f ≫ idealQuotientMap (I.comap f) = 0 := by
  apply ((pullbackPushforwardAdjunction f).homEquiv _ _).injective
  apply moduleHom_ext_affine
  intro U
  ext s
  change (I.comap f).subschemeι.app (f ⁻¹ᵁ U.1)
    ((idealModulePullbackι I f).app (f ⁻¹ᵁ U.1)
      (((pullbackPushforwardAdjunction f).unit.app _).app U.1 s)) = 0
  rw [idealModulePullbackι_unit]
  have hs : (idealModuleι I).app U.1 s ∈ I.ideal U := by
    rw [← idealModuleAffineEquiv_val]
    exact (idealModuleAffineEquiv I U s).property
  have ht := ((I.comap f).subschemeι ≫ f).ideal_ker_le U (I.le_map_comap f U hs)
  exact ht

/-- The canonical comparison from module pullback to the comap ideal module. -/
def idealModulePullbackHom (I : Y.IdealSheafData) (f : X ⟶ Y) :
    (Scheme.Modules.pullback f).obj (idealModule I) ⟶ idealModule (I.comap f) :=
  kernel.lift _ (idealModulePullbackι I f) (idealModulePullbackι_quotient I f)

/-- The comparison retains the actual ideal inclusion. -/
@[reassoc (attr := simp)]
lemma idealModulePullbackHom_ι (I : Y.IdealSheafData) (f : X ⟶ Y) :
    idealModulePullbackHom I f ≫ idealModuleι (I.comap f) = idealModulePullbackι I f :=
  kernel.lift_ι _ _ _

/-- The comparison carries pulled-back ideal sections to their scheme images. -/
lemma idealModulePullbackHom_unit (I : Y.IdealSheafData) (f : X ⟶ Y)
    (U : Y.Opens) (s : Γ(idealModule I, U)) :
    (idealModuleι (I.comap f)).app (f ⁻¹ᵁ U)
      ((idealModulePullbackHom I f).app (f ⁻¹ᵁ U)
        (((pullbackPushforwardAdjunction f).unit.app _).app U s)) =
      f.app U ((idealModuleι I).app U s) := by
  have h := congrArg (fun k ↦ k.app (f ⁻¹ᵁ U)
    (((pullbackPushforwardAdjunction f).unit.app _).app U s))
      (idealModulePullbackHom_ι I f)
  exact h.trans (idealModulePullbackι_unit I f U s)

/-- The general comparison agrees with the established open-restriction map. -/
lemma idealModulePullbackHom_open (I : Y.IdealSheafData) (f : X ⟶ Y)
    [IsOpenImmersion f] :
    (restrictFunctorIsoPullback f).hom.app (idealModule I) ≫
      idealModulePullbackHom I f = idealModuleRestrictHom I f := by
  apply (cancel_mono (idealModuleι (I.comap f))).mp
  rw [Category.assoc, idealModulePullbackHom_ι, idealModuleRestrictHom_ι]
  dsimp only [idealModulePullbackι, idealModuleRestrictι]
  rw [← Category.assoc, ← (restrictFunctorIsoPullback f).hom.naturality,
    Category.assoc, restrictPullbackUnitIso]

/-- The comparison is invertible for open immersions. -/
instance idealModulePullbackHom_isIso_of_isOpenImmersion (I : Y.IdealSheafData)
    (f : X ⟶ Y) [IsOpenImmersion f] : IsIso (idealModulePullbackHom I f) := by
  have : IsIso ((restrictFunctorIsoPullback f).hom.app (idealModule I) ≫
      idealModulePullbackHom I f) := by
    rw [idealModulePullbackHom_open]
    infer_instance
  exact IsIso.of_isIso_comp_left ((restrictFunctorIsoPullback f).hom.app _) _

/-- The comparison is invertible for the unit ideal along any morphism. -/
instance idealModulePullbackHom_top_isIso (f : X ⟶ Y) :
    IsIso (idealModulePullbackHom ⊤ f) := by
  have htop : IsIso (idealModuleι ((⊤ : Y.IdealSheafData).comap f)) := by
    rw [Scheme.IdealSheafData.comap_top]
    infer_instance
  have hcomp : IsIso (idealModulePullbackHom (⊤ : Y.IdealSheafData) f ≫
      idealModuleι ((⊤ : Y.IdealSheafData).comap f)) := by
    rw [idealModulePullbackHom_ι]
    dsimp only [idealModulePullbackι]
    infer_instance
  exact IsIso.of_isIso_comp_right _ (idealModuleι ((⊤ : Y.IdealSheafData).comap f))

end FLT.Mazur.FCurve
