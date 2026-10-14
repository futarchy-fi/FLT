/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.EllipticFiniteCoefficientPointSection

/-!
# Equal stage indices preserve the actual coefficient model

The canonical index transport preserves the coefficient projection and the
full proper section. This lets retained charts target the named final model.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
namespace FLT.Mazur.WeierstrassDividedDepth
universe u
variable {K : Type u} [Field K] (A : ValuationSubring K)
  {W : WeierstrassCurve A} {π : A} (hπ : π ≠ 0) {start n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (S : Type u) [CommRing S] [Algebra A S]
  (i j : ℕ) (hi : i ≤ n) (hj : j ≤ n) (he : i = j)

/-- Equal stage indices give the identity identification of the actual coefficient models. -/
def finiteTensorIndexIso : finiteGlobalTensorModel hπ data S i hi ≅
    finiteGlobalTensorModel hπ data S j hj := by
  subst j
  exact Iso.refl _

/-- Index transport retains the original coefficient projection. -/
@[reassoc] theorem finiteTensorIndexIso_structure :
    (finiteTensorIndexIso A hπ data S i j hi hj he).hom ≫
      pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap A S)))
        (finiteGlobalStructure hπ data j hj) =
      pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap A S)))
        (finiteGlobalStructure hπ data i hi) := by
  subst j
  exact Category.id_comp _

/-- Index transport preserves the complete actual proper coefficient section. -/
@[reassoc] theorem finiteCoefficientPointSection_index
    (P : (W.map (algebraMap A K)).toProjective.Point) :
    finiteCoefficientPointSection A hπ data i hi S P ≫
      (finiteTensorIndexIso A hπ data S i j hi hj he).hom =
        finiteCoefficientPointSection A hπ data j hj S P := by
  subst j
  exact Category.comp_id _

end FLT.Mazur.WeierstrassDividedDepth
