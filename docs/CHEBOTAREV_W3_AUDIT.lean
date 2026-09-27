/- Run with `LEAN_NUM_THREADS=4 lake env lean docs/CHEBOTAREV_W3_AUDIT.lean`.
Each declaration must use only propext, Classical.choice and Quot.sound.
The final cover theorem deliberately retains its explicit W2 hypothesis. -/
import FLT.GaloisRepresentation.HardlyRamified.Chebotarev.FiniteMonoidCover

#print GaloisRepresentation.Chebotarev.W2Statement
#check GaloisRepresentation.B5Inputs.powerFrobCover
#print axioms GaloisRepresentation.Chebotarev.exists_finiteGalois_monoid_factorization
#print axioms GaloisRepresentation.Chebotarev.exists_pow_restrictScalars_eq
#print axioms GaloisRepresentation.Chebotarev.exists_isConj_pow_restrict_QFrob
#print axioms GaloisRepresentation.Chebotarev.exists_restrict_eq_conj_pow_QFrob
#print axioms GaloisRepresentation.B5Inputs.powerFrobCover
