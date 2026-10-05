import JSPProblem.Hyper
namespace JSP140
set_option maxHeartbeats 1000000
attribute [local instance] Classical.propDecidable
variable {β γ : Type*} [DecidableEq β] [Fintype β] [DecidableEq γ]
open scoped BigOperators
-- reuse from Nibble by importing? instead: minimal reproduction using the file's defs
import JSPProblem.Nibble
