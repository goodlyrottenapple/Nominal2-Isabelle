theory QuotientSet
imports 
  "../Nominal2"
begin

lemma supp_quot:
  "(supp (R, x)) supports (R `` {x})"
unfolding supports_def
unfolding fresh_def[symmetric]
apply(perm_simp)
apply(simp add: swap_fresh_fresh)
done

lemma
  assumes "equiv UNIV R"
  and "(x, y) \<in> R"
  shows "R `` {x} = R `` {y}"
using assms
by (rule equiv_class_eq)

lemma s1:
  assumes "equiv UNIV R"
  and "(x, y) \<in> R"
  shows "a \<sharp> (R `` {x}) \<longleftrightarrow> a \<sharp> (R `` {y})"
using assms
apply(subst equiv_class_eq)
apply(auto)
done

lemma s2:
  fixes x::"'a::fs"
  assumes "equiv UNIV R"
  and     "supp R = {}"
  shows "\<Inter>{supp y | y. (x, y) \<in> R} supports (R `` {x})"
unfolding supports_def
apply(rule allI)+
apply(rule impI)
apply(rule swap_fresh_fresh)
apply(drule conjunct1)
apply(auto)[1]
apply(subst s1)
apply(rule assms)
apply(assumption)
apply(rule supports_fresh)
apply(rule supp_quot)
apply(simp add: supp_Pair finite_supp assms)
apply(simp add: supp_Pair assms)
apply(drule conjunct2)
apply(auto)[1]
apply(subst s1)
apply(rule assms)
apply(assumption)
apply(rule supports_fresh)
apply(rule supp_quot)
apply(simp add: supp_Pair finite_supp assms)
apply(simp add: supp_Pair assms)
done

lemma s3:
  fixes S::"'a::fs set"
  assumes "finite S"
  and "S \<noteq> {}"
  and "a \<sharp> S"
  shows "\<exists>x \<in> S. a \<sharp> x"
using assms
apply(auto simp add: fresh_def)
apply(subst (asm) supp_of_finite_sets)
apply(auto)
done

(*
lemma supp_inter:
  fixes x::"'a::fs"
  assumes "equiv UNIV R"
  and     "supp R = {}"
  shows "supp (R `` {x}) = \<Inter>{supp y | y. (x, y) \<in> R}"
apply(rule finite_supp_unique)
apply(rule s2)
apply(rule assms)
apply(rule assms)
apply(metis (lam_lifting, no_types) at_base_infinite finite_UNIV)
*)

  



end



