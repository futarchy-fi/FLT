/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineHilbertPrincipalTensorModel

/-!
# Actual source coefficients on principal tensor relation charts

Transport the original two endpoint pullbacks into the literal localization
ring. Evaluation along any chart morphism recovers the original geometric
pullback. These are local multiplicative maps, not a global descent coaction.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TensorProduct
namespace FLT.Mazur.HilbertChart.AffineRestriction
open CartierAbel SchemePicard FCurve Approximation AffineProductTensorCoordinates
set_option backward.isDefEq.respectTransparency false
variable {R : Type} [CommRing R] [Algebra.FiniteType ℤ R] {X : Scheme}
  (f : X ⟶ Spec (.of R)) [IsProper f] [Flat f] [GeometricallyIntegral f]
  [SmoothOfRelativeDimension 1 f] {L : X.Modules} (hL : AmpleLineBundle L)
  (d : ℕ) (V : Over (Spec (.of R))) [IsAffine V.left]
  (c : (relativeFppfSheaf f).obj.obj (op V))
  {A : Over (Spec (.of R))} [IsAffine A.left] (k : A ⟶ variableHilbertTest f d V)
  [IsOpenImmersion k.left]
local notation "Z" => relation f hL d V c k
local notation "p" => fst f hL d V c k
local notation "q" => snd f hL d V c k
local notation "j" => Over.Hom.left (toEnvelope f hL d V c k)
local notation "Y" => Over.left (prod A V)
/-- The algebra induced by the original structural morphism. -/
local instance localizedSourceAlgebra : Algebra R Γ(A.left, ⊤) :=
  affineBaseSectionAlgebra A.hom
/-- The algebra induced by the original structural morphism. -/
local instance localizedTranslationAlgebra : Algebra R Γ(V.left, ⊤) :=
  affineBaseSectionAlgebra V.hom
variable (t : Γ(A.left, ⊤) ⊗[R] Γ(V.left, ⊤)) (U : (relation f hL d V c k).left.Opens)
  (hU : (toEnvelope f hL d V c k).left ''ᵁ U =
    (prod A V).left.basicOpen ((tensorIso A V).hom t))

/-- The actual chart's coefficient ring, identified with its literal tensor localization. -/
def principalTensorSectionsIso : Γ(U.toScheme, ⊤) ≅ CommRingCat.of (Localization.Away t) :=
  (Scheme.Γ.mapIso (principalTensorIso f hL d V c k t U hU).op).symm ≪≫
    Scheme.ΓSpecIso (.of (Localization.Away t))

/-- The original first endpoint induces a multiplicative map into the localized tensor ring. -/
def localizedSourceMap : Γ(A.left, ⊤) →+* Localization.Away t :=
  (principalTensorSectionsIso f hL d V c k t U hU).hom.hom.comp
    (U.ι ≫ (p).left).appTop.hom

/-- The original test endpoint induces the other actual multiplicative coefficient map. -/
def localizedTestMap : Γ(A.left, ⊤) →+* Localization.Away t :=
  (principalTensorSectionsIso f hL d V c k t U hU).hom.hom.comp
    (U.ι ≫ (q).left).appTop.hom

/-- Evaluate literal localized coefficients along an actual morphism into the relation chart. -/
def localizedEvaluation {B : Scheme} (g : B ⟶ U.toScheme) :
    Localization.Away t →+* Γ(B, ⊤) :=
  g.appTop.hom.comp (principalTensorSectionsIso f hL d V c k t U hU).inv.hom

/-- Evaluation of source coefficients is exactly the original first endpoint pullback. -/
theorem localizedEvaluation_source {B : Scheme} (g : B ⟶ U.toScheme) (a : Γ(A.left, ⊤)) :
    localizedEvaluation f hL d V c k t U hU g
      (localizedSourceMap f hL d V c k t U hU a) =
        (g ≫ U.ι ≫ (p).left).appTop a := by
  change g.appTop ((principalTensorSectionsIso f hL d V c k t U hU).inv
    ((principalTensorSectionsIso f hL d V c k t U hU).hom _)) = _
  rw [Iso.hom_inv_id_apply]
  rfl

/-- Evaluation of test coefficients retains the original second endpoint pullback. -/
theorem localizedEvaluation_test {B : Scheme} (g : B ⟶ U.toScheme) (a : Γ(A.left, ⊤)) :
    localizedEvaluation f hL d V c k t U hU g
      (localizedTestMap f hL d V c k t U hU a) =
        (g ≫ U.ι ≫ (q).left).appTop a := by
  change g.appTop ((principalTensorSectionsIso f hL d V c k t U hU).inv
    ((principalTensorSectionsIso f hL d V c k t U hU).hom _)) = _
  rw [Iso.hom_inv_id_apply]
  rfl

/-- The two original endpoint maps agree on structural scalars from R. -/
theorem localizedSourceMap_scalar (r : R) :
    localizedSourceMap f hL d V c k t U hU (algebraMap R Γ(A.left, ⊤) r) =
      localizedTestMap f hL d V c k t U hU (algebraMap R Γ(A.left, ⊤) r) := by
  have hp : (p).left ≫ A.hom = (Z).hom := (p).w
  have hq : (q).left ≫ A.hom = (Z).hom := (q).w
  change (principalTensorSectionsIso f hL d V c k t U hU).hom
    ((U.ι ≫ (p).left).appTop (A.hom.appTop ((Scheme.ΓSpecIso (.of R)).inv r))) =
    (principalTensorSectionsIso f hL d V c k t U hU).hom
    ((U.ι ≫ (q).left).appTop (A.hom.appTop ((Scheme.ΓSpecIso (.of R)).inv r)))
  congr 1
  change (U.ι ≫ (p).left ≫ A.hom).appTop _ = (U.ι ≫ (q).left ≫ A.hom).appTop _
  rw [hp, hq]

end FLT.Mazur.HilbertChart.AffineRestriction
