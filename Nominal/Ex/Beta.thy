theory Beta
imports 
  "../Nominal2"
begin


atom_decl name


nominal_datatype lam =
  Var "name"
| App "lam" "lam"
| Lam x::"name" l::"lam"  binds x in l ("Lam [_]. _" [100, 100] 100)

section {* capture-avoiding substitution *}

nominal_function
  subst :: "lam \<Rightarrow> name \<Rightarrow> lam \<Rightarrow> lam"  ("_ [_ ::= _]" [90, 90, 90] 90)
where
  "(Var x)[y ::= s] = (if x = y then s else (Var x))"
| "(App t1 t2)[y ::= s] = App (t1[y ::= s]) (t2[y ::= s])"
| "\<lbrakk>atom x \<sharp> y; atom x \<sharp> s\<rbrakk> \<Longrightarrow> (Lam [x]. t)[y ::= s] = Lam [x].(t[y ::= s])"
  unfolding eqvt_def subst_graph_def
  apply (rule, perm_simp, rule)
  apply(rule TrueI)
  apply(auto simp add: lam.distinct lam.eq_iff)
  apply(rule_tac y="a" and c="(aa, b)" in lam.strong_exhaust)
  apply(blast)+
  apply(simp_all add: fresh_star_def fresh_Pair_elim)
  apply (erule_tac c="(ya,sa)" in Abs_lst1_fcb2)
  apply(simp_all add: Abs_fresh_iff)
  apply(simp add: fresh_star_def fresh_Pair)
  apply(simp add: eqvt_at_def atom_eqvt fresh_star_Pair perm_supp_eq)
  apply(simp add: eqvt_at_def atom_eqvt fresh_star_Pair perm_supp_eq)
done

nominal_termination (eqvt)
  by lexicographic_order

lemma forget:
  shows "atom x \<sharp> t \<Longrightarrow> t[x ::= s] = t"
  by (nominal_induct t avoiding: x s rule: lam.strong_induct)
     (auto simp add: lam.fresh fresh_at_base)

lemma fresh_fact:
  fixes z::"name"
  assumes a: "atom z \<sharp> s"
      and b: "z = y \<or> atom z \<sharp> t"
  shows "atom z \<sharp> t[y ::= s]"
  using a b
  by (nominal_induct t avoiding: z y s rule: lam.strong_induct)
     (auto simp add: lam.fresh fresh_at_base)

lemma substitution_lemma:  
  assumes a: "x \<noteq> y" "atom x \<sharp> u"
  shows "t[x ::= s][y ::= u] = t[y ::= u][x ::= s[y ::= u]]"
using a 
by (nominal_induct t avoiding: x y s u rule: lam.strong_induct)
   (auto simp add: fresh_fact forget)

inductive
  beta :: "lam \<Rightarrow> lam \<Rightarrow> bool" ("_ \<rightarrow> _")
where
  beta_beta:  "atom x \<sharp> s \<Longrightarrow> App (Lam [x].t) s \<rightarrow> t[x ::= s]"
| beta_Lam:   "t \<rightarrow> s \<Longrightarrow> Lam [x].t \<rightarrow> Lam [x].s"
| beta_App1:  "t \<rightarrow> s \<Longrightarrow> App t u \<rightarrow> App s u"
| beta_App2:  "t \<rightarrow> s \<Longrightarrow> App u t \<rightarrow> App u s"

equivariance beta

nominal_inductive beta
  avoids beta_beta: "x" 
       | beta_Lam: "x"
by (simp_all add: fresh_star_def fresh_Pair lam.fresh fresh_fact)

inductive
  equ :: "lam \<Rightarrow> lam \<Rightarrow> bool" ("_ \<approx> _")
where
  equ_beta:  "atom x \<sharp> s \<Longrightarrow> App (Lam [x].t) s \<approx> t[x ::= s]"
| equ_refl:  "t \<approx> t"
| equ_sym:   "t \<approx> s \<Longrightarrow> s \<approx> t"
| equ_trans: "\<lbrakk>t1 \<approx> t2; t2 \<approx> t3\<rbrakk> \<Longrightarrow> t1 \<approx> t3"
| equ_Lam:   "t \<approx> s \<Longrightarrow> Lam [x].t \<approx> Lam [x].s"
| equ_App1:  "t \<approx> s \<Longrightarrow> App t u \<approx> App s u"
| equ_App2:  "t \<approx> s \<Longrightarrow> App u t \<approx> App u s"

equivariance equ

nominal_inductive equ
  avoids equ_beta: "x" 
       | equ_Lam: "x"
by (simp_all add: fresh_star_def fresh_Pair lam.fresh fresh_fact)

inductive
  equ2 :: "lam \<Rightarrow> lam \<Rightarrow> bool" ("_ \<approx>2 _")
where
  equ2_beta1:  "\<lbrakk>atom x \<sharp> (t2, s2); s1 \<approx>2 t1; t2 \<approx>2  s2\<rbrakk> \<Longrightarrow> App (Lam [x].t1) t2 \<approx>2 s1[x ::= s2]"
| equ2_beta2:  "\<lbrakk>atom x \<sharp> (t2, s2); s1 \<approx>2 t1; t2 \<approx>2  s2\<rbrakk> \<Longrightarrow> s1[x ::= s2] \<approx>2 App (Lam [x].t1) t2"
| equ2_Var:   "Var x \<approx>2 Var x"
| equ2_Lam:   "t \<approx>2 s \<Longrightarrow> Lam [x].t \<approx>2 Lam [x].s"
| equ2_App:   "\<lbrakk>t1 \<approx>2 s1; t2 \<approx>2 s2\<rbrakk> \<Longrightarrow> App t1 t2 \<approx>2 App s1 s2"

equivariance equ2

nominal_inductive equ2
  avoids equ2_beta1: "x"
       | equ2_beta2: "x" 
       | equ2_Lam: "x"
by (simp_all add: fresh_star_def fresh_Pair lam.fresh fresh_fact)

lemma equ2_refl:
  fixes t::"lam"
  shows "t \<approx>2 t"
apply(induct t rule: lam.induct)
apply(auto intro: equ2.intros)
done

lemma equ2_symm:
  fixes t s::"lam"
  assumes "t \<approx>2 s"
  shows "s \<approx>2 t"
using assms
apply(induct)
apply(auto intro: equ2.intros)
done

lemma equ2_trans:
  fixes t1 t2 t3::"lam"
  assumes "t1 \<approx>2 t2" "t2 \<approx>2 t3"
  shows "t1 \<approx>2 t3"
using assms
apply(nominal_induct t1 t2 avoiding: t3 rule: equ2.strong_induct)
defer
defer
apply(erule equ2.cases)
apply(auto)
apply(rule equ2_beta2)
apply(simp)
apply(simp)
apply(simp)
apply(rule equ2_refl)
defer
apply(rotate_tac 4)
apply(erule equ2.cases)
apply(auto)
oops

lemma "a \<noteq> x \<Longrightarrow> x \<noteq> y \<Longrightarrow> y \<noteq> a \<Longrightarrow> y \<noteq> b \<Longrightarrow> (App (App (Lam[x]. Lam[y]. (App (Var y) (Var x))) (Var a)) (Var b) \<approx> App (Var b) (Var a))"
  apply (rule equ_trans)
  apply (rule equ_App1)
  apply (rule equ_beta)
  apply (simp add: lam.fresh fresh_at_base)
  apply (subst subst.simps)
  apply (simp add: lam.fresh fresh_at_base)+
  apply (rule equ_trans)
  apply (rule equ_beta)
  apply (simp add: lam.fresh fresh_at_base)
  apply (simp add: equ_refl)
  done

lemma "\<not> (Var b \<approx>2 Var a) \<Longrightarrow> \<not> (App (App (Lam[x]. Lam[y]. (App (Var y) (Var x))) (Var a)) (Var b) \<approx>2 App (Var b) (Var a))"
  apply rule
  apply (erule equ2.cases)
  apply auto
  done

lemma [quot_respect]:
  shows "(op = ===> equ) Var Var"
  and   "(equ ===> equ ===> equ) App App"
  and   "(op = ===> equ ===> equ) Beta.Lam Beta.Lam"
unfolding fun_rel_def
by (auto intro: equ.intros)

lemma equ_subst1:
  assumes "t \<approx> s"
  shows "t[x ::= u] \<approx> s[x ::= u]"
using assms
apply(nominal_induct avoiding: x u rule: equ.strong_induct)
apply(simp)
apply(rule equ_trans)
apply(rule equ_beta)
apply(simp add: fresh_fact)
apply(subst (2) substitution_lemma)
apply(simp add: fresh_at_base)
apply(simp)
apply(rule equ_refl)
apply(rule equ_refl)
apply(auto intro: equ_sym)[1]
apply(blast intro: equ_trans)
apply(simp add: equ_Lam)
apply(simp add: equ_App1)
apply(simp add: equ_App2)
done

lemma equ_subst2:
  assumes "t \<approx> s"
  shows "u[x ::= t] \<approx> u[x ::= s]"
using assms
apply(nominal_induct u avoiding: x t s rule: lam.strong_induct)
apply(simp add: equ_refl)
apply(simp)
apply(smt equ_App1 equ_App2 equ_trans)
apply(simp)
apply(metis equ_Lam)
done

lemma [quot_respect]:
  shows "(equ ===> op = ===> equ ===> equ) subst subst"
unfolding fun_rel_def
by (metis equ_subst1 equ_subst2 equ_trans)

lemma [quot_respect]:
  shows "(op = ===> equ ===> equ) permute permute"
unfolding fun_rel_def
by (auto intro: eqvts)

quotient_type qlam = lam / equ
apply(rule equivpI)
apply(rule reflpI)
apply(simp add: equ_refl)
apply(rule sympI)
apply(simp add: equ_sym)
apply(rule transpI)
apply(auto intro: equ_trans)
done

quotient_definition "QVar::name \<Rightarrow> qlam" is Var
quotient_definition "QApp::qlam \<Rightarrow> qlam \<Rightarrow> qlam" is App
quotient_definition QLam ("QLam [_]._") 
  where "QLam::name \<Rightarrow> qlam \<Rightarrow> qlam" is Beta.Lam

lemmas qlam_strong_induct = lam.strong_induct[quot_lifted]
lemmas qlam_induct = lam.induct[quot_lifted]

instantiation qlam :: pt
begin

quotient_definition "permute_qlam::perm \<Rightarrow> qlam \<Rightarrow> qlam" 
  is "permute::perm \<Rightarrow> lam \<Rightarrow> lam"

instance
apply default
apply(descending)
apply(simp)
apply(rule equ_refl)
apply(descending)
apply(simp)
apply(rule equ_refl)
done

end

lemma qlam_perm[simp]:
  shows "p \<bullet> (QVar x) = QVar (p \<bullet> x)"
  and "p \<bullet> (QApp t s) = QApp (p \<bullet> t) (p \<bullet> s)"
  and "p \<bullet> (QLam [x].t) = QLam [p \<bullet> x].(p \<bullet> t)"
apply(descending)
apply(simp add: equ_refl)
apply(descending)
apply(simp add: equ_refl)
apply(descending)
apply(simp add: equ_refl)
done

lemma qlam_supports:
  shows "{atom x} supports (QVar x)"
  and   "supp (t, s) supports (QApp t s)"
  and   "supp (x, t) supports (QLam [x].t)"
unfolding supports_def fresh_def[symmetric]
by (auto simp add: swap_fresh_fresh)

lemma qlam_fs:
  fixes t::"qlam"
  shows "finite (supp t)"
apply(induct t rule: qlam_induct)
apply(rule supports_finite)
apply(rule qlam_supports)
apply(simp)
apply(rule supports_finite)
apply(rule qlam_supports)
apply(simp add: supp_Pair)
apply(rule supports_finite)
apply(rule qlam_supports)
apply(simp add: supp_Pair finite_supp)
done

instantiation qlam :: fs
begin

instance
apply(default)
apply(rule qlam_fs)
done

end

quotient_definition subst_qlam ("_[_ ::q= _]")
  where "subst_qlam::qlam \<Rightarrow> name \<Rightarrow> qlam \<Rightarrow> qlam" is subst  

lemma
  "(QVar x)[y ::q= s] = (if x = y then s else (QVar x))"
apply(descending)
apply(simp)
apply(auto intro: equ_refl)
done

lemma
  "(QApp t1 t2)[y ::q= s] = QApp (t1[y ::q= s]) (t2[y ::q= s])"
apply(descending)
apply(simp)
apply(rule equ_refl)
done

definition
  "Supp t = \<Inter>{supp s | s. s \<approx> t}"

lemma [quot_respect]:
  shows "(equ ===> op=) Supp Supp"
unfolding fun_rel_def
unfolding Supp_def
apply(rule allI)+
apply(rule impI)
apply(rule_tac f="Inter" in arg_cong)
apply(auto)
apply (metis equ_trans)
by (metis equivp_def qlam_equivp)

quotient_definition "supp_qlam::qlam \<Rightarrow> atom set" 
  is "Supp::lam \<Rightarrow> atom set"

lemma Supp_supp:
  "Supp t \<subseteq> supp t"
unfolding Supp_def
apply(auto)
apply(drule_tac x="supp t" in spec)
apply(auto simp add: equ_refl)
done

lemma Supp_Lam:
  "atom a \<notin> Supp (Lam [a].t)"
proof -
  have "atom a \<notin> supp (Lam [a].t)" by (simp add: lam.supp)
  then show ?thesis using Supp_supp
    by blast
qed

lemmas s = Supp_Lam[quot_lifted]

definition
  ssupp :: "atom set \<Rightarrow> 'a::pt \<Rightarrow> bool" ("_ ssupp _")
where
  "A ssupp x \<equiv> \<forall>p. (\<forall>a \<in> A. (p \<bullet> a) = a) \<longleftrightarrow> (p \<bullet> x) = x"

lemma ssupp_supports:
  "A ssupp x \<Longrightarrow> A supports x"
unfolding ssupp_def supports_def
apply(rule allI)+
apply(drule_tac x="(a \<rightleftharpoons> b)" in spec)
apply(auto)
by (metis swap_atom_simps(3))

lemma ssupp_supp:
  assumes a: "finite A"
  and     b: "A ssupp x"
  shows "supp x = A"
proof -
  { assume 0: "A - supp x \<noteq> {}"
    then obtain a where 1: "a \<in> A - supp x" by auto
    obtain a' where *: "a' \<in>  UNIV - A" and **: "sort_of a' = sort_of a"
      by (rule obtain_atom[OF a]) (auto)  
    have "(a \<rightleftharpoons> a') \<bullet> a = a'" using 1 ** * by (auto)
    then have w0: "(a \<rightleftharpoons> a') \<bullet> x \<noteq> x"
      using b unfolding ssupp_def 
      apply -
      apply(drule_tac x="(a \<rightleftharpoons> a')" in spec)
      apply(auto)
      using 1 *
      apply(auto)
      done
    have w1: "a \<sharp> x" unfolding fresh_def using 1 by auto 
    have w2: "a' \<sharp> x" using *
      apply(rule_tac supports_fresh)
      apply(rule ssupp_supports)
      apply(rule b)
      apply(rule a)
      apply(auto)
      done
    have "False" using w0 w1 w2 by (simp add: swap_fresh_fresh)
    then have "supp x = A" by simp }
  moreover
  { assume "A - supp x = {}"
    moreover
    have "supp x \<subseteq> A"
      apply(rule supp_is_subset)
      apply(rule ssupp_supports)
      apply(rule b)
      apply(rule a)
      done
    ultimately have "supp x = A"
      by blast
  }
  ultimately show "supp x = A" by blast
qed

lemma
  "(supp x) ssupp x"
unfolding ssupp_def
apply(auto)
apply(rule supp_perm_eq)
apply(simp add: fresh_star_def)
apply(auto)
apply(simp add: fresh_perm)
apply(simp add: fresh_perm[symmetric])
(*Tzevelekos 2008, section 2.1.2 property 2.5*)
oops

(* The above is not true. Take p=(a\<leftrightarrow>b) and x={a,b}, then the goal is provably false *)
lemma
  "b \<noteq> a \<Longrightarrow> \<not>(supp {a :: name,b}) ssupp {a,b}"
unfolding ssupp_def
apply (auto)
apply (intro exI[of _ "(a\<leftrightarrow>b) :: perm"])
apply (subgoal_tac "(a \<leftrightarrow> b) \<bullet> {a, b} = {a, b}")
apply simp
apply (subgoal_tac "supp {a, b} = {atom a, atom b}")
apply (simp add: flip_def)
apply (simp add: supp_of_finite_insert supp_at_base supp_set_empty)
apply blast
by (smt empty_eqvt flip_at_simps(1) flip_at_simps(2) insert_commute insert_eqvt)

function
  qsubst :: "qlam \<Rightarrow> name \<Rightarrow> qlam \<Rightarrow> qlam"  ("_ [_ ::qq= _]" [90, 90, 90] 90)
where
  "(QVar x)[y ::qq= s] = (if x = y then s else (QVar x))"
| "(QApp t1 t2)[y ::qq= s] = QApp (t1[y ::qq= s]) (t2[y ::qq= s])"
| "\<lbrakk>atom x \<sharp> y; atom x \<sharp> s\<rbrakk> \<Longrightarrow> (QLam [x]. t)[y ::qq= s] = QLam [x].(t[y ::qq= s])"
apply(simp_all add:)
oops


lemma
  assumes a: "Lam [x].t \<approx> s"
  shows "\<exists>x' t'. s = Lam [x']. t' \<and> t \<approx> t'"
using a
apply(induct s rule:lam.induct)
apply(erule equ.cases)
apply(auto)
apply(erule equ.cases)
apply(auto)



lemma
  "atom x \<sharp> y \<Longrightarrow> atom x \<notin> supp_qlam s \<Longrightarrow> (QLam [x].t)[y ::q= s] = QLam [x].(t[y ::q= s])"
apply(descending)
oops


lemma [eqvt]: "(p \<bullet> abs_qlam t) = abs_qlam (p \<bullet> t)"
 apply (subst fun_cong[OF fun_cong[OF meta_eq_to_obj_eq[OF permute_qlam_def]], of p, simplified])
 apply (subst Quotient_rel[OF Quotient_qlam, simplified equivp_reflp[OF qlam_equivp], simplified])
 by (metis Quotient_qlam equ_refl eqvt rep_abs_rsp_left)

lemma supports_abs_qlam:
  "(supp t) supports (abs_qlam t)"
unfolding supports_def
unfolding fresh_def[symmetric]
apply(auto)
apply(perm_simp)
apply(simp add: swap_fresh_fresh)
done

lemma rep_qlam_inverse:
  "abs_qlam (rep_qlam t) = t"
by (metis Quotient_abs_rep Quotient_qlam)

lemma supports_rep_qlam:
  "supp (rep_qlam t) supports t"
apply(subst (2) rep_qlam_inverse[symmetric])
apply(rule supports_abs_qlam)
done

 lemma supports_qvar:
  "{atom x} supports (QVar x)"
apply(subgoal_tac "supp (Var x) supports (abs_qlam (Var x))")
apply(simp add: lam.supp supp_at_base)
defer
apply(rule supports_abs_qlam)
apply(simp add: QVar_def)
done

section {* Supp *}

lemma s:
  assumes "s \<approx> t"
  shows "a \<sharp> (abs_qlam s) \<longleftrightarrow> a \<sharp> (abs_qlam t)"
using assms
by (metis Quotient_qlam Quotient_rel_abs)

lemma ss:
  "Supp t supports (abs_qlam t)"
apply(simp only: supports_def)
apply(rule allI)+
apply(rule impI)
apply(rule swap_fresh_fresh)
apply(drule conjunct1)
apply(auto)[1]
apply(simp add: Supp_def)
apply(auto)[1]
apply(simp add: s[symmetric])
apply(rule supports_fresh)
apply(rule supports_abs_qlam)
apply(simp add: finite_supp)
apply(simp)
apply(drule conjunct2)
apply(auto)[1]
apply(simp add: Supp_def)
apply(auto)[1]
apply(simp add: s[symmetric])
apply(rule supports_fresh)
apply(rule supports_abs_qlam)
apply(simp add: finite_supp)
apply(simp)
done

lemma
  fixes t::"qlam"
  shows "(supp x) supports (QVar x)"
apply(rule_tac x="QVar x" in Abs_qlam_cases)
apply(auto)
thm QVar_def
oops


 
section {* Size *}

definition
  "Size t = Least {size s | s. s \<approx> t}" 

lemma [quot_respect]:
  shows "(equ ===> op=) Size Size"
unfolding fun_rel_def
unfolding Size_def
apply(auto)
apply(rule_tac f="Least" in arg_cong)
apply(auto)
apply (metis equ_trans)
by (metis equivp_def qlam_equivp)

instantiation qlam :: size
begin

quotient_definition "size_qlam::qlam \<Rightarrow> nat" 
  is "Size::lam \<Rightarrow> nat"

instance
apply default
done

end

thm lam.size

lemma
  "size (QVar x) = 0"
apply(descending)
apply(simp add: Size_def)
apply(rule Least_equality)
apply(auto)
apply(simp add: Collect_def)
apply(rule_tac x="Var x" in exI)
apply(auto intro: equ_refl)
done

lemma
  "size (QLam [x].t) = Suc (size t)"
apply(descending)
apply(simp add: Size_def)
thm Least_Suc
apply(rule trans)
apply(rule_tac n="Suc (size t)" in Least_Suc)
apply(simp add: Collect_def)
apply(rule_tac x="Lam [x].t" in exI)
apply(auto intro: equ_refl)[1]
apply(simp add: Collect_def)
apply(auto)
defer
apply(simp add: Collect_def)
apply(rule_tac x="t" in exI)
apply(auto intro: equ_refl)[1]
apply(simp add: Collect_def)
defer
apply(simp add: Collect_def)
apply(auto)[1]

apply(auto)
done

term rep_qlam
lemmas qlam_size_def = Size_def[quot_lifted]

lemma [quot_preserve]:
  assumes "Quotient equ Abs Rep"
  shows "(id ---> Rep ---> id) fresh = fresh"
using assms
unfolding Quotient_def
apply(simp add: map_fun_def)
apply(simp add: comp_def fun_eq_iff)

sorry

lemma [simp]:
  shows "(QVar x)[y :::= s] = (if x = y then s else (QVar x))"
  and "(QApp t1 t2)[y :::= s] = QApp (t1[y :::= s]) (t2[y :::= s])"
  and "\<lbrakk>atom x \<sharp> y; atom x \<sharp> s\<rbrakk> \<Longrightarrow> (QLam [x]. t)[y :::= s] = QLam [x].(t[y :::= s])"
apply(lifting subst.simps(1))
apply(lifting subst.simps(2))
apply(lifting subst.simps(3))
done



end



