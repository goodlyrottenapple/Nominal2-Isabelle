theory FiniteType
imports "../Nominal2"
begin

typedef ('a::pt, 'b::fs) ffun = "{f::'a => 'b. finite (supp f)}"
apply(rule_tac x="\<lambda>_. undefined::'b::fs" in exI)
apply(auto)
apply(rule_tac S="supp (undefined::'b::fs)" in supports_finite)
apply(simp add: supports_def)
apply(perm_simp)
apply(simp add: fresh_def[symmetric])
apply(simp add: swap_fresh_fresh)
apply(simp add: finite_supp)
done




end
