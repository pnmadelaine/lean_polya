import .info

namespace polya

meta inductive contrad
| none : contrad
| eq_diseq : Π {lhs rhs}, eq_data lhs rhs → diseq_data lhs rhs → contrad
| ineqs : Π {lhs rhs}, ineq_info lhs rhs → ineq_data lhs rhs → contrad
| sign : Π {e}, sign_data e → sign_data e → contrad
| strict_ineq_self : Π {e}, ineq_data e e → contrad
| sum_form : Π {sfc}, sum_form_proof sfc → contrad

meta def contrad.to_format : contrad → format
| contrad.none := "no contradiction"
| (@contrad.eq_diseq lhs rhs _ _) := "eq_diseq"
| (@contrad.ineqs lhs rhs _ _) := "ineqs"
| (@contrad.sign e _ _) := "sign"
| (@contrad.strict_ineq_self e _) := "strict_ineq_self"
| (@contrad.sum_form _ sfcd) := "sum_form"

meta instance contrad.has_to_format : has_to_format contrad :=
⟨contrad.to_format⟩

end polya
