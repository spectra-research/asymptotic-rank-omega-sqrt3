/- Adapted from PolMul/Superadditivity.lean of an earlier formalisation
   (commit 51c6e6b6e8b8d7226c6a828dba618ae1de5b5f8a).
   Uses Foundations tensor definitions; declarations are renamed under OM. -/
import Lib.OM.PolMul.Superadditivity.SA2
import Lib.OM.PolMul.Superadditivity.SA3
import Lib.OM.PolMul.Superadditivity.SA4

/-!
# Superadditivity

SA.1 supplies the isomorphic-summand estimate. SA.2 projects tensor products
onto word types and removes the polynomial overhead. SA.3 applies the binary
bound to Strassen's tensor, and SA.4 pairs the six permuted spectral points.
-/

