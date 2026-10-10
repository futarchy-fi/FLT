/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedFiniteTensorGeometry
public import FLT.Mazur.WeierstrassSuccessiveXResidueNodeGeometry

/-!
# Ordered node neighborhoods in the actual finite residue atlas

The two full ordered node charts embed in the finite integral model's
residue base change. Their union is exactly the inverse image of the
original successive integral atlas chart, with its coefficient structure.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits IsLocalRing
namespace FLT.Mazur.WeierstrassDividedDepth
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] [IsDomain R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n depth : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (D : SplitNodeDepth W π depth) (j : ℕ) (hj : j + 1 ≤ n)
  (hk0 : 0 < start + j) (hk : 2 * (start + j + 1) ≤ depth)
open WeierstrassSuccessiveX
local notation "K" => ResidueField R
local notation "e" => data (Fin.mk (j + 1) (Nat.lt_succ_of_le hj))
local notation "N" => MiddleNodeOpen (residue R (Data.b6 e))
local notation "a" => residueMiddleFirstNodeChart D (start + j) hk0 hk
  (Data.b3 e) (Data.b4 e) (Data.b6 e) (Data.factor3 e) (Data.factor4 e)
local notation "b" => residueMiddleSecondNodeChart D (start + j) hk0 hk
  (Data.b3 e) (Data.b4 e) (Data.b6 e) (Data.factor3 e) (Data.factor4 e)
local notation "c" => finiteSuccessiveTensorChart hπ data K j hj
local notation "E₀" => initialExterior (data (Fin.mk 0 (Nat.zero_lt_succ n)))
local notation "q" => Spec.map (CommRingCat.ofHom (algebraMap R K))

/-- The first ordered full node neighborhood in the actual finite residue model. -/
def finiteResidueFirstNode : Spec (.of N) ⟶ finiteTensorModel hπ data K (j + 1) hj :=
  a ≫ c

/-- The opposite ordered full node neighborhood in the same finite residue model. -/
def finiteResidueSecondNode : Spec (.of N) ⟶ finiteTensorModel hπ data K (j + 1) hj :=
  b ≫ c

instance finiteResidueFirstNode_isOpenImmersion :
    IsOpenImmersion (finiteResidueFirstNode hπ data D j hj hk0 hk) :=
  inferInstanceAs (IsOpenImmersion (_ ≫ _))

instance finiteResidueSecondNode_isOpenImmersion :
    IsOpenImmersion (finiteResidueSecondNode hπ data D j hj hk0 hk) :=
  inferInstanceAs (IsOpenImmersion (_ ≫ _))

/-- The two ordered node charts cover exactly the original successive atlas preimage. -/
theorem finiteResidueNodes_range :
    Set.range (finiteResidueFirstNode hπ data D j hj hk0 hk) ∪
      Set.range (finiteResidueSecondNode hπ data D j hj hk0 hk) =
        (pullback.snd q (finiteStructure hπ data (j + 1) hj)) ⁻¹'
          Set.range (finiteAtlasMap hπ data E₀ (j + 1) hj 1) := by
  rw [← finiteSuccessiveTensorChart_range]
  ext z
  constructor
  · rintro (⟨p, rfl⟩ | ⟨p, rfl⟩)
    · exact ⟨a p, rfl⟩
    · exact ⟨b p, rfl⟩
  · rintro ⟨p, rfl⟩
    rcases residueMiddleNodeCharts_cover D (start + j) hk0 hk
      (Data.b3 e) (Data.b4 e) (Data.b6 e) (Data.factor3 e) (Data.factor4 e) p with
      ⟨t, rfl⟩ | ⟨t, rfl⟩
    · exact Or.inl ⟨t, rfl⟩
    · exact Or.inr ⟨t, rfl⟩

/-- The first full finite node chart retains its residue-field structure. -/
@[reassoc] theorem finiteResidueFirstNode_structure :
    finiteResidueFirstNode hπ data D j hj hk0 hk ≫ pullback.fst _ _ =
      Spec.map (CommRingCat.ofHom (algebraMap K N)) := by
  rw [finiteResidueFirstNode, Category.assoc, finiteSuccessiveTensorChart_structure]
  exact residueMiddleFirstNodeChart_structure D (start + j) hk0 hk
    (Data.b3 e) (Data.b4 e) (Data.b6 e) (Data.factor3 e) (Data.factor4 e)

/-- The opposite ordered finite node retains the same residue-field structure. -/
@[reassoc] theorem finiteResidueSecondNode_structure :
    finiteResidueSecondNode hπ data D j hj hk0 hk ≫ pullback.fst _ _ =
      Spec.map (CommRingCat.ofHom (algebraMap K N)) := by
  rw [finiteResidueSecondNode, Category.assoc, finiteSuccessiveTensorChart_structure]
  exact residueMiddleSecondNodeChart_structure D (start + j) hk0 hk
    (Data.b3 e) (Data.b4 e) (Data.b6 e) (Data.factor3 e) (Data.factor4 e)

end FLT.Mazur.WeierstrassDividedDepth
