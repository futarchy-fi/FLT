/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CoherentClosedReduction
public import Mathlib.Algebra.Category.ModuleCat.Products
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree
public import Mathlib.RingTheory.Localization.Finiteness

/-!
# Canonical scalar coordinates at the integral generic point

Closed pushforward respects the structure-stalk scalar map. Coherent stalks are
finite over their actual local rings, giving finite bases at integral generic points.
The resulting finite free stalk coordinates extend to actual neighborhood comparisons.
Canonical residue transport identifies their rank in the dimension-one case.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Opposite
open Scheme.Modules FLT.Mazur.FCurve FLT.Mazur.FCurve.CoherentDevissage

universe u

namespace FLT.Mazur.CoherentGenericCoordinates

open AnnihilatorSubsheaf CoherentGenericIdealEmbedding

variable {X Y : Scheme.{u}}

/-- The structure-module stalk has its canonical function-field coordinates. -/
def structureGenericCoordinates [IsIntegral X] :
    (structureModule X).presheaf.stalk (genericPoint X) ≃ₗ[X.functionField] X.functionField :=
  structureStalkLinearEquiv _

/-- The canonical additive equivalence of actual closed-pushforward stalks. -/
def closedStalkAddEquiv (i : Y ⟶ X) [IsClosedImmersion i] (G : Y.Modules) (y : Y) :
    ((pushforward i).obj G).presheaf.stalk (i y) ≃+ G.presheaf.stalk y :=
  (closedPushforwardStalkIso i G y).addCommGroupIsoToAddEquiv

/-- Closed pushforward preserves germs through its canonical additive stalk comparison. -/
lemma closedStalk_germ (i : Y ⟶ X) [IsClosedImmersion i] (G : Y.Modules)
    (y : Y) (U : X.Opens) (hy : i y ∈ U) (m : Γ((pushforward i).obj G, U)) :
    closedStalkAddEquiv i G y
        (((pushforward i).obj G).presheaf.germ U (i y) hy m) =
      G.presheaf.germ (i ⁻¹ᵁ U) y hy m :=
  congr($(TopCat.Presheaf.stalkPushforward_germ AddCommGrpCat i.base G.presheaf U y hy) m)

/-- The canonical closed-pushforward comparison respects the actual scalar map. -/
lemma closedStalk_smul (i : Y ⟶ X) [IsClosedImmersion i] (G : Y.Modules)
    (y : Y) (r : X.presheaf.stalk (i y))
    (m : ((pushforward i).obj G).presheaf.stalk (i y)) :
    closedStalkAddEquiv i G y (r • m) =
      i.stalkMap y r • closedStalkAddEquiv i G y m := by
  obtain ⟨U, hy, a, n, rfl, rfl⟩ := comparison_common_germs ((pushforward i).obj G) (i y) r m
  erw [← ((pushforward i).obj G).val.germ_smul, closedStalk_germ, closedStalk_germ]
  rw [Scheme.Hom.germ_stalkMap_apply]
  exact G.val.germ_smul y (i ⁻¹ᵁ U) hy (i.app U a) n

attribute [local instance] specStalkAlgebra specStalkBaseModule specStalkBaseTower

/-- A coherent affine stalk is finite over its actual structure stalk. -/
lemma affine_stalk_finite {R : CommRingCat.{u}}
    (G : (Spec R).Modules) [G.IsFinitePresentation] (x : Spec R) :
    Module.Finite ((Spec R).presheaf.stalk x) (G.presheaf.stalk x) := by
  have : Module.Finite R Γ(G, ⊤) := affineCoherent_finite_sections G
  have : IsLocalization x.asIdeal.primeCompl ((Spec R).presheaf.stalk x) :=
    StructureSheaf.IsLocalization.to_stalk R x
  exact Module.Finite.of_isLocalizedModule x.asIdeal.primeCompl (specGermLinear G x)

/-- Finiteness of a coherent stalk transports from an actual affine chart. -/
theorem coherent_stalk_finite
    (G : X.Modules) [G.IsFinitePresentation] (x : X) :
    Module.Finite (X.presheaf.stalk x) (G.presheaf.stalk x) := by
  obtain ⟨_, ⟨U, hU, rfl⟩, hx, _⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open
    (show x ∈ (⊤ : X.Opens) from trivial) isOpen_univ
  have hy := hU.fromSpec_primeIdealOf ⟨x, hx⟩
  generalize hU.primeIdealOf ⟨x, hx⟩ = y at hy
  change hU.fromSpec y = x at hy
  subst x
  have := coherentPresentation_restrict hU.fromSpec G
  have := affine_stalk_finite (G.restrict hU.fromSpec) y
  let e : (G.restrict hU.fromSpec).presheaf.stalk y →ₛₗ[(inv (hU.fromSpec.stalkMap y)).hom]
      G.presheaf.stalk (hU.fromSpec y) :=
    { __ := (comparisonRestrictStalk hU.fromSpec y G).toAddMonoidHom
      map_smul' := comparisonRestrictStalk_smul hU.fromSpec y G }
  exact Module.Finite.of_surjective e (comparisonRestrictStalk hU.fromSpec y G).surjective

/-- The finite basis is chosen on the given coherent stalk over the function field. -/
def genericBasis [IsIntegral X]
    (G : X.Modules) [G.IsFinitePresentation] :
    Module.Basis (Fin (Module.finrank X.functionField (G.presheaf.stalk (genericPoint X))))
      X.functionField (G.presheaf.stalk (genericPoint X)) := by
  have := coherent_stalk_finite G (genericPoint X)
  exact Module.finBasis _ _

/-- Stalks retain their structure-ring action functorially. -/
def linearStalk (x : X) : X.Modules ⥤ ModuleCat (X.presheaf.stalk x) where
  obj M := ModuleCat.of _ (M.presheaf.stalk x)
  map f := ModuleCat.ofHom (comparisonStalkLinear f x)
  map_id M := by ext m; exact congr($(CategoryTheory.Functor.map_id (stalk x) M) m)
  map_comp f g := by ext m; exact congr($(Functor.map_comp (stalk x) f g) m)

instance linearStalk_finiteLimits (x : X) : PreservesFiniteLimits (linearStalk x) := by
  let V := forget₂ (ModuleCat (X.presheaf.stalk x)) AddCommGrpCat
  have : PreservesFiniteLimits (linearStalk x ⋙ V) := comparisonStalk_finiteLimits x
  exact preservesFiniteLimits_of_reflects_of_preserves (linearStalk x) V

/-- The finite free sheaf is the actual coproduct of structure modules. -/
abbrev finiteFree (X : Scheme.{u}) (r : ℕ) : X.Modules :=
  SheafOfModules.free (R := X.ringCatSheaf) (ULift.{u} (Fin r))

instance finiteFree_coherent (X : Scheme.{u}) (r : ℕ) :
    (finiteFree X r).IsFinitePresentation := by
  let q := (SheafOfModules.free.generatingSections
    (R := X.ringCatSheaf) (ULift.{u} (Fin r))).localGeneratorsData.quasiCoherentData
  have hq : q.IsFinitePresentation := by
    constructor
    intro i
    constructor
    · constructor
      change Finite (ULift.{u} (Fin r))
      infer_instance
    · constructor
      change Finite (ULift.{u} Empty)
      infer_instance
  exact { exists_quasicoherentData := ⟨q, hq⟩ }

attribute [local instance] HasBiproduct.of_hasProduct

/-- The finite coproduct and finite product are canonically the same sheaf. -/
def finiteFreeProductIso (X : Scheme.{u}) (r : ℕ) :
    finiteFree X r ≅ ∏ᶜ (fun _ : ULift.{u} (Fin r) ↦ structureModule X) :=
  (biproduct.isoCoproduct (fun _ : ULift.{u} (Fin r) ↦ structureModule X)).symm ≪≫
    biproduct.isoProduct _

/-- Finite free stalk coordinates preserve the actual structure-stalk scalars. -/
def finiteFreeStalkCoordinates (x : X) (r : ℕ) :
    (finiteFree X r).presheaf.stalk x ≃ₗ[X.presheaf.stalk x]
      (ULift.{u} (Fin r) → X.presheaf.stalk x) :=
  ((linearStalk x).mapIso (finiteFreeProductIso X r) ≪≫
    PreservesProduct.iso (linearStalk x) _ ≪≫ ModuleCat.piIsoPi _).toLinearEquiv |>.trans
      (LinearEquiv.piCongrRight fun _ ↦ structureStalkLinearEquiv x)

/-- The chosen finite basis supplies the stalk map used by the neighborhood theorem. -/
def genericFreeCoordinates [IsIntegral X]
    (G : X.Modules) [G.IsFinitePresentation] :
    (finiteFree X (Module.finrank X.functionField
      (G.presheaf.stalk (genericPoint X)))).presheaf.stalk (genericPoint X) ≃ₗ[X.functionField]
        G.presheaf.stalk (genericPoint X) :=
  (finiteFreeStalkCoordinates (genericPoint X) _).trans
    (((genericBasis G).reindex Equiv.ulift.symm).equivFun.symm)

/-- The actual finite free comparison exists on a neighborhood of the generic point. -/
theorem exists_generic_free_comparison [IsLocallyNoetherian X] [IsIntegral X]
    (G : X.Modules) [G.IsFinitePresentation] :
    ∃ C : CoherentStalkNeighborhood
      (finiteFree X (Module.finrank X.functionField (G.presheaf.stalk (genericPoint X))))
      G (genericPoint X) (genericFreeCoordinates G).toLinearMap,
      IsIso C.map ∧ IsZero (kernel C.map) ∧ IsZero (cokernel C.map) :=
  exists_coherent_comparison_neighborhood _ G _ (genericFreeCoordinates G)

section Descent

variable (I : X.IdealSheafData) [IsIntegral I.subscheme]
  (F : X.Modules) [F.IsFinitePresentation]
  (hF : StalkAnnihilated F (I.subschemeι (genericPoint I.subscheme)))

/-- The closed generic stalk map identifies the ambient residue field with the function field. -/
def residueFieldIso :
    X.residueField (I.subschemeι (genericPoint I.subscheme)) ≃+* I.subscheme.functionField :=
  (Ideal.quotEquivOfEq ((CoherentClosedReduction.generic_stalkIdeal I).symm.trans
    (CoherentClosedReduction.stalkIdeal_eq_ker I _))).trans
      (RingHom.quotientKerEquivOfSurjective
        (I.subschemeι.stalkMap_surjective (genericPoint I.subscheme)))

/-- The field identification is induced by the original closed-immersion stalk map. -/
lemma residueFieldIso_residue (a : X.presheaf.stalk (I.subschemeι (genericPoint I.subscheme))) :
    residueFieldIso I (X.residue _ a) = I.subschemeι.stalkMap (genericPoint I.subscheme) a := by
  change ((Ideal.quotEquivOfEq _).trans (RingHom.quotientKerEquivOfSurjective _))
    (Ideal.Quotient.mk _ a) = _
  rw [RingEquiv.trans_apply, Ideal.quotEquivOfEq_mk]
  exact RingHom.quotientKerEquivOfSurjective_apply_mk _ a

variable [IsLocallyNoetherian X]

/-- The additive generic identification uses only closed pushforward and the A3 embedding. -/
def descentStalkAddEquiv :
    (CoherentClosedReduction.descent I F).presheaf.stalk (genericPoint I.subscheme) ≃+
      F.presheaf.stalk (I.subschemeι (genericPoint I.subscheme)) :=
  (closedStalkAddEquiv I.subschemeι (CoherentClosedReduction.descent I F)
    (genericPoint I.subscheme)).symm.trans
      (CoherentClosedReduction.embeddingStalkEquiv I F hF).toAddEquiv

/-- Ambient scalar transport across the constructed descent identification. -/
lemma descentStalk_smul (a : X.presheaf.stalk (I.subschemeι (genericPoint I.subscheme)))
    (m : (CoherentClosedReduction.descent I F).presheaf.stalk (genericPoint I.subscheme)) :
    descentStalkAddEquiv I F hF (I.subschemeι.stalkMap (genericPoint I.subscheme) a • m) =
      a • descentStalkAddEquiv I F hF m := by
  let e := closedStalkAddEquiv I.subschemeι (CoherentClosedReduction.descent I F)
    (genericPoint I.subscheme)
  have he : e.symm (I.subschemeι.stalkMap (genericPoint I.subscheme) a • m) =
      a • e.symm m := by
    apply e.injective
    rw [e.apply_symm_apply, closedStalk_smul, e.apply_symm_apply]
  change CoherentClosedReduction.embeddingStalkEquiv I F hF (e.symm _) =
    a • CoherentClosedReduction.embeddingStalkEquiv I F hF (e.symm m)
  rw [he]
  exact (CoherentClosedReduction.embeddingStalkEquiv I F hF).map_smul a _

/-- The descended generic stalk has the ambient residue action through the canonical field map. -/
@[instance_reducible]
def descentResidueModule :
    Module (X.residueField (I.subschemeι (genericPoint I.subscheme)))
      ((CoherentClosedReduction.descent I F).presheaf.stalk (genericPoint I.subscheme)) :=
  Module.compHom _ (residueFieldIso I).toRingHom

/-- The constructed generic identification is linear for the original residue action. -/
def descentResidueEquiv :
    letI := descentResidueModule I F
    letI := residueModule F _ hF
    (CoherentClosedReduction.descent I F).presheaf.stalk (genericPoint I.subscheme) ≃ₗ[
      X.residueField (I.subschemeι (genericPoint I.subscheme))]
        F.presheaf.stalk (I.subschemeι (genericPoint I.subscheme)) := by
  letI := descentResidueModule I F
  letI := residueModule F _ hF
  exact
    { __ := descentStalkAddEquiv I F hF
      map_smul' := fun c m ↦ by
        obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective c
        change descentStalkAddEquiv I F hF (residueFieldIso I (X.residue _ a) • m) = _
        rw [residueFieldIso_residue]
        exact descentStalk_smul I F hF a m }

/-- The chosen function-field basis becomes a basis of the original residue stalk. -/
def ambientResidueBasis :
    letI := residueModule F _ hF
    Module.Basis (Fin (Module.finrank I.subscheme.functionField
      ((CoherentClosedReduction.descent I F).presheaf.stalk (genericPoint I.subscheme))))
      (X.residueField (I.subschemeι (genericPoint I.subscheme)))
      (F.presheaf.stalk (I.subschemeι (genericPoint I.subscheme))) := by
  letI := descentResidueModule I F
  letI := residueModule F _ hF
  let b := (genericBasis (CoherentClosedReduction.descent I F)).mapCoeffs
    (residueFieldIso I).symm (fun c m ↦ by
      change residueFieldIso I ((residueFieldIso I).symm c) • m = c • m
      rw [RingEquiv.apply_symm_apply])
  exact b.map (descentResidueEquiv I F hF)

/-- The actual rank used by the local comparison is one under the original dimension hypothesis. -/
theorem comparison_rank_one
    (hd : letI := residueModule F _ hF
      Module.finrank (X.residueField (I.subschemeι (genericPoint I.subscheme)))
        (F.presheaf.stalk (I.subschemeι (genericPoint I.subscheme))) = 1) :
    Module.finrank I.subscheme.functionField
      ((CoherentClosedReduction.descent I F).presheaf.stalk (genericPoint I.subscheme)) = 1 :=
  multiplicity_one F _ hF hd _ (ambientResidueBasis I F hF)

/-- Apply the actual generic comparison to the coherent sheaf constructed in A3. -/
theorem exists_descent_free_comparison :
    ∃ C : CoherentStalkNeighborhood
      (finiteFree I.subscheme (Module.finrank I.subscheme.functionField
        ((CoherentClosedReduction.descent I F).presheaf.stalk (genericPoint I.subscheme))))
      (CoherentClosedReduction.descent I F) (genericPoint I.subscheme)
      (genericFreeCoordinates (CoherentClosedReduction.descent I F)).toLinearMap,
      IsIso C.map ∧ IsZero (kernel C.map) ∧ IsZero (cokernel C.map) := by
  have := LocallyOfFiniteType.isLocallyNoetherian I.subschemeι
  exact exists_generic_free_comparison (CoherentClosedReduction.descent I F)

end Descent

end FLT.Mazur.CoherentGenericCoordinates
